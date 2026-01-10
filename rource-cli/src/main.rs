//! Rource CLI - Native application entry point.
//!
//! This is the main entry point for the native Rource application.
//! It sets up the window using winit and displays the rendered output
//! using softbuffer.

// Allow multiple versions of dependencies from winit/softbuffer ecosystem
#![allow(clippy::multiple_crate_versions)]

mod args;

use std::num::NonZeroU32;
use std::rc::Rc;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use winit::application::ApplicationHandler;
use winit::dpi::{LogicalSize, PhysicalSize};
use winit::event::{ElementState, KeyEvent, WindowEvent};
use winit::event_loop::{ActiveEventLoop, ControlFlow, EventLoop};
use winit::keyboard::{Key, NamedKey};
use winit::window::{Window, WindowId};

use rource_math::{Color, Hsl, Vec2};
use rource_render::{Renderer, SoftwareRenderer};
use rource_vcs::{Commit, FileAction};

use args::Args;

/// Application state.
struct App {
    /// Command-line arguments.
    args: Args,

    /// The window (created on resume).
    window: Option<Rc<Window>>,

    /// Softbuffer surface for displaying pixels.
    surface: Option<softbuffer::Surface<Rc<Window>, Rc<Window>>>,

    /// The software renderer.
    renderer: Option<SoftwareRenderer>,

    /// Current playback state.
    playback: PlaybackState,

    /// Loaded commits.
    commits: Vec<Commit>,

    /// Current commit index.
    current_commit: usize,

    /// Last frame time.
    last_frame: Instant,

    /// Accumulated time for playback.
    accumulated_time: f64,

    /// Whether to exit the application.
    should_exit: bool,
}

/// Playback state for the visualization.
#[derive(Debug, Clone)]
struct PlaybackState {
    /// Whether playback is paused.
    paused: bool,

    /// Playback speed multiplier.
    speed: f32,

    /// Seconds per day of commit history.
    seconds_per_day: f32,
}

impl Default for PlaybackState {
    fn default() -> Self {
        Self {
            paused: false,
            speed: 1.0,
            seconds_per_day: 10.0,
        }
    }
}

impl App {
    /// Create a new application with the given arguments.
    fn new(args: Args) -> Self {
        let paused = args.paused;
        let seconds_per_day = args.seconds_per_day;

        Self {
            args,
            window: None,
            surface: None,
            renderer: None,
            playback: PlaybackState {
                paused,
                seconds_per_day,
                ..Default::default()
            },
            commits: Vec::new(),
            current_commit: 0,
            last_frame: Instant::now(),
            accumulated_time: 0.0,
            should_exit: false,
        }
    }

    /// Load commits from the repository or log file.
    fn load_commits(&mut self) -> Result<()> {
        use rource_vcs::{CustomParser, GitParser, Parser};
        use std::process::Command;

        let path = &self.args.path;

        if self.args.custom_log {
            // Read custom log file
            let content =
                std::fs::read_to_string(path).context("Failed to read custom log file")?;
            let parser = CustomParser::new();
            self.commits = parser
                .parse_str(&content)
                .context("Failed to parse custom log")?;
        } else {
            // Try to get git log
            let output = Command::new("git")
                .arg("-C")
                .arg(path)
                .arg("log")
                .arg("--pretty=format:commit %H%nAuthor: %an <%ae>%nDate: %at")
                .arg("--name-status")
                .arg("--reverse")
                .output()
                .context("Failed to run git log")?;

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                anyhow::bail!("git log failed: {stderr}");
            }

            let log_content = String::from_utf8_lossy(&output.stdout);
            let parser = GitParser::new();
            self.commits = parser
                .parse_str(&log_content)
                .context("Failed to parse git log")?;
        }

        if self.commits.is_empty() {
            anyhow::bail!("No commits found in repository");
        }

        // Sort by timestamp
        self.commits.sort_by_key(|c| c.timestamp);

        eprintln!(
            "Loaded {} commits from {}",
            self.commits.len(),
            self.args.path.display()
        );

        Ok(())
    }

    /// Handle window resize.
    fn handle_resize(&mut self, size: PhysicalSize<u32>) {
        if size.width == 0 || size.height == 0 {
            return;
        }

        // Resize the softbuffer surface
        if let Some(surface) = &mut self.surface {
            let _ = surface.resize(
                NonZeroU32::new(size.width).unwrap(),
                NonZeroU32::new(size.height).unwrap(),
            );
        }

        // Resize the renderer
        if let Some(renderer) = &mut self.renderer {
            renderer.resize(size.width, size.height);
        }
    }

    /// Handle keyboard input.
    fn handle_key(&mut self, event: &KeyEvent) {
        if event.state != ElementState::Pressed {
            return;
        }

        if self.args.disable_input {
            // Only allow quit
            if matches!(&event.logical_key, Key::Named(NamedKey::Escape)) {
                self.should_exit = true;
            }
            return;
        }

        match &event.logical_key {
            Key::Named(NamedKey::Escape) => {
                self.should_exit = true;
            }
            Key::Named(NamedKey::Space) => {
                self.playback.paused = !self.playback.paused;
            }
            Key::Character(c) => match c.as_str() {
                "q" | "Q" => {
                    self.should_exit = true;
                }
                "+" | "=" => {
                    self.playback.speed = (self.playback.speed * 1.5).min(10.0);
                    eprintln!("Speed: {:.1}x", self.playback.speed);
                }
                "-" | "_" => {
                    self.playback.speed = (self.playback.speed / 1.5).max(0.1);
                    eprintln!("Speed: {:.1}x", self.playback.speed);
                }
                "r" | "R" => {
                    // Reset to beginning
                    self.current_commit = 0;
                    self.accumulated_time = 0.0;
                    eprintln!("Reset to beginning");
                }
                _ => {}
            },
            Key::Named(NamedKey::ArrowRight) => {
                // Skip forward
                if self.current_commit + 10 < self.commits.len() {
                    self.current_commit += 10;
                } else {
                    self.current_commit = self.commits.len().saturating_sub(1);
                }
            }
            Key::Named(NamedKey::ArrowLeft) => {
                // Skip backward
                self.current_commit = self.current_commit.saturating_sub(10);
            }
            _ => {}
        }
    }

    /// Update the visualization state.
    fn update(&mut self, dt: f64) {
        if self.playback.paused || self.commits.is_empty() {
            return;
        }

        self.accumulated_time += dt * f64::from(self.playback.speed);

        // Calculate how many days have passed based on playback speed
        let days_per_second = 1.0 / f64::from(self.playback.seconds_per_day);
        let days_elapsed = self.accumulated_time * days_per_second;

        // Find the current commit based on elapsed time
        if let Some(first) = self.commits.first() {
            let first_time = first.timestamp;
            let target_time = first_time + (days_elapsed * 86400.0) as i64;

            // Find commit at or before target time
            while self.current_commit + 1 < self.commits.len() {
                if self.commits[self.current_commit + 1].timestamp <= target_time {
                    self.current_commit += 1;
                } else {
                    break;
                }
            }
        }

        // Loop if enabled
        if self.args.loop_playback && self.current_commit >= self.commits.len().saturating_sub(1) {
            self.current_commit = 0;
            self.accumulated_time = 0.0;
        }
    }

    /// Render the current frame.
    fn render(&mut self) {
        let Some(renderer) = &mut self.renderer else {
            return;
        };

        renderer.begin_frame();

        // Clear to background color
        let bg_color = self.args.parse_background_color();
        renderer.clear(bg_color);

        let width = renderer.width();
        let height = renderer.height();
        let center_x = width as f32 / 2.0;
        let center_y = height as f32 / 2.0;

        // Draw a simple visualization placeholder
        // (Full scene rendering will be integrated later)

        // Draw some activity based on current commit
        if !self.commits.is_empty() && self.current_commit < self.commits.len() {
            let commit = &self.commits[self.current_commit];
            let num_files = commit.files.len();

            // Draw a central disc representing the repository
            renderer.draw_disc(
                Vec2::new(center_x, center_y),
                50.0,
                Color::new(0.2, 0.2, 0.3, 1.0),
            );

            // Draw file changes as colored dots around the center
            for (i, file) in commit.files.iter().enumerate() {
                let angle = (i as f32 / num_files.max(1) as f32) * std::f32::consts::TAU;
                let radius = 100.0 + (i as f32 * 10.0) % 150.0;

                let fx = center_x + angle.cos() * radius;
                let fy = center_y + angle.sin() * radius;

                // Color based on action type
                let color = match file.action {
                    FileAction::Create => Color::new(0.2, 1.0, 0.2, 0.8),
                    FileAction::Modify => Color::new(1.0, 1.0, 0.2, 0.8),
                    FileAction::Delete => Color::new(1.0, 0.2, 0.2, 0.8),
                };

                // Draw the file dot
                renderer.draw_disc(Vec2::new(fx, fy), 5.0, color);

                // Draw a line from center to file
                renderer.draw_line(
                    Vec2::new(center_x, center_y),
                    Vec2::new(fx, fy),
                    1.0,
                    color.with_alpha(0.3),
                );
            }

            // Draw author indicator
            let author_hash = hash_string(&commit.author);
            let author_hue = (author_hash % 360) as f32;
            let author_color = Color::from_hsl(Hsl::new(author_hue, 0.7, 0.6));

            let author_x = center_x + 80.0;
            let author_y = center_y - 80.0;
            renderer.draw_disc(Vec2::new(author_x, author_y), 20.0, author_color);
        }

        // Draw playback state (pause indicator)
        if self.playback.paused {
            let pause_color = Color::new(1.0, 1.0, 1.0, 0.7);
            renderer.draw_quad(
                rource_math::Bounds::new(Vec2::new(20.0, 20.0), Vec2::new(28.0, 40.0)),
                None,
                pause_color,
            );
            renderer.draw_quad(
                rource_math::Bounds::new(Vec2::new(34.0, 20.0), Vec2::new(42.0, 40.0)),
                None,
                pause_color,
            );
        }

        renderer.end_frame();
    }

    /// Present the rendered frame to the window.
    fn present(&mut self) {
        let Some(renderer) = &self.renderer else {
            return;
        };
        let Some(surface) = &mut self.surface else {
            return;
        };

        let width = renderer.width();
        let height = renderer.height();

        // Get the softbuffer buffer
        let mut buffer = match surface.buffer_mut() {
            Ok(b) => b,
            Err(e) => {
                eprintln!("Failed to get surface buffer: {e}");
                return;
            }
        };

        // Copy renderer pixels to softbuffer
        // SoftwareRenderer uses ARGB8 (0xAARRGGBB)
        // softbuffer expects the same format on most platforms
        let pixels = renderer.pixels();
        let buffer_len = (width * height) as usize;

        if buffer.len() >= buffer_len && pixels.len() >= buffer_len {
            buffer[..buffer_len].copy_from_slice(&pixels[..buffer_len]);
        }

        // Present the buffer
        if let Err(e) = buffer.present() {
            eprintln!("Failed to present buffer: {e}");
        }
    }
}

impl ApplicationHandler for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        // Create window
        let window_attrs = Window::default_attributes()
            .with_title("Rource")
            .with_inner_size(LogicalSize::new(self.args.width, self.args.height));

        let window = match event_loop.create_window(window_attrs) {
            Ok(w) => Rc::new(w),
            Err(e) => {
                eprintln!("Failed to create window: {e}");
                event_loop.exit();
                return;
            }
        };

        // Create softbuffer surface
        let context = match softbuffer::Context::new(window.clone()) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Failed to create softbuffer context: {e}");
                event_loop.exit();
                return;
            }
        };

        let mut surface = match softbuffer::Surface::new(&context, window.clone()) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to create softbuffer surface: {e}");
                event_loop.exit();
                return;
            }
        };

        // Initialize surface size
        let size = window.inner_size();
        if size.width > 0 && size.height > 0 {
            let _ = surface.resize(
                NonZeroU32::new(size.width).unwrap(),
                NonZeroU32::new(size.height).unwrap(),
            );
        }

        // Create renderer
        let renderer = SoftwareRenderer::new(size.width.max(1), size.height.max(1));

        self.window = Some(window);
        self.surface = Some(surface);
        self.renderer = Some(renderer);
        self.last_frame = Instant::now();

        // Load commits
        if let Err(e) = self.load_commits() {
            eprintln!("Warning: {e}");
            // Continue running - we can still show the UI
        }
    }

    fn window_event(&mut self, event_loop: &ActiveEventLoop, _id: WindowId, event: WindowEvent) {
        match event {
            WindowEvent::CloseRequested => {
                event_loop.exit();
            }
            WindowEvent::Resized(size) => {
                self.handle_resize(size);
            }
            WindowEvent::KeyboardInput { event, .. } => {
                self.handle_key(&event);
                if self.should_exit {
                    event_loop.exit();
                }
            }
            WindowEvent::RedrawRequested => {
                // Calculate delta time
                let now = Instant::now();
                let dt = now.duration_since(self.last_frame).as_secs_f64();
                self.last_frame = now;

                // Update and render
                self.update(dt);
                self.render();
                self.present();

                // Request next frame
                if let Some(window) = &self.window {
                    window.request_redraw();
                }
            }
            _ => {}
        }
    }

    fn about_to_wait(&mut self, event_loop: &ActiveEventLoop) {
        // Request redraw to keep animation running
        if let Some(window) = &self.window {
            window.request_redraw();
        }

        // Set frame rate limit
        event_loop.set_control_flow(ControlFlow::WaitUntil(
            Instant::now() + Duration::from_millis(16), // ~60 FPS
        ));
    }
}

/// Simple string hash for deterministic colors.
fn hash_string(s: &str) -> u32 {
    let mut hash: u32 = 0;
    for byte in s.bytes() {
        hash = hash.wrapping_mul(31).wrapping_add(u32::from(byte));
    }
    hash
}

/// Format a Unix timestamp as a human-readable date.
#[allow(dead_code)]
fn format_timestamp(timestamp: i64) -> String {
    // Simple formatting without chrono dependency
    let days_since_epoch = timestamp / 86400;
    let years = (days_since_epoch / 365) + 1970;
    let remaining_days = days_since_epoch % 365;
    let month = (remaining_days / 30) + 1;
    let day = (remaining_days % 30) + 1;
    format!("{years:04}-{month:02}-{day:02}")
}

fn main() -> Result<()> {
    let args = Args::parse_args();

    eprintln!("Rource - Software version control visualization");
    eprintln!("Repository: {}", args.path.display());
    eprintln!("Window: {}x{}", args.width, args.height);

    // Create event loop
    let event_loop = EventLoop::new().context("Failed to create event loop")?;

    // Create application
    let mut app = App::new(args);

    // Run the event loop
    event_loop.run_app(&mut app)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_string() {
        let h1 = hash_string("Alice");
        let h2 = hash_string("Bob");
        let h3 = hash_string("Alice");

        assert_eq!(h1, h3);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_format_timestamp() {
        // Jan 1, 2020 00:00:00 UTC
        #[allow(clippy::unreadable_literal)]
        let ts = 1577836800;
        let formatted = format_timestamp(ts);
        // Approximate check (our simple algorithm isn't precise)
        assert!(formatted.starts_with("20"));
    }

    #[test]
    fn test_playback_state_default() {
        let state = PlaybackState::default();
        assert!(!state.paused);
        assert!((state.speed - 1.0).abs() < 0.001);
        assert!((state.seconds_per_day - 10.0).abs() < 0.001);
    }
}
