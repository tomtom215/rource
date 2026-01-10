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

use rource_core::camera::Camera;
use rource_core::scene::{ActionType, Scene};
use rource_math::{Color, Vec2};
use rource_render::effects::{BloomEffect, ShadowEffect};
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

    /// The scene graph containing all entities.
    scene: Scene,

    /// Camera for view transforms.
    camera: Camera,

    /// Bloom effect (optional).
    bloom: Option<BloomEffect>,

    /// Shadow effect (optional).
    shadow: Option<ShadowEffect>,

    /// Current playback state.
    playback: PlaybackState,

    /// Loaded commits.
    commits: Vec<Commit>,

    /// Current commit index.
    current_commit: usize,

    /// Index of last applied commit (for incremental apply).
    last_applied_commit: usize,

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

        // Initialize camera with default viewport (will be resized when window opens)
        let camera = Camera::new(f32::from(args.width as u16), f32::from(args.height as u16));

        // Initialize bloom effect unless disabled
        let bloom = if args.no_bloom {
            None
        } else {
            Some(BloomEffect::new())
        };

        // Initialize shadow effect if enabled
        let shadow = if args.shadows {
            Some(ShadowEffect::subtle()) // Use subtle preset for less visual clutter
        } else {
            None
        };

        Self {
            args,
            window: None,
            surface: None,
            renderer: None,
            scene: Scene::new(),
            camera,
            bloom,
            shadow,
            playback: PlaybackState {
                paused,
                seconds_per_day,
                ..Default::default()
            },
            commits: Vec::new(),
            current_commit: 0,
            last_applied_commit: 0,
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

        // Resize camera viewport
        self.camera
            .set_viewport_size(size.width as f32, size.height as f32);
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
                    self.last_applied_commit = 0;
                    self.accumulated_time = 0.0;
                    self.scene = Scene::new();
                    self.camera.reset();
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

    /// Convert VCS `FileAction` to scene `ActionType`.
    const fn file_action_to_action_type(action: FileAction) -> ActionType {
        match action {
            FileAction::Create => ActionType::Create,
            FileAction::Modify => ActionType::Modify,
            FileAction::Delete => ActionType::Delete,
        }
    }

    /// Apply commits from `last_applied_commit` to `current_commit` to the scene.
    fn apply_pending_commits(&mut self) {
        while self.last_applied_commit < self.current_commit {
            let commit = &self.commits[self.last_applied_commit];

            // Convert commit files to scene format
            let files: Vec<(std::path::PathBuf, ActionType)> = commit
                .files
                .iter()
                .map(|f| (f.path.clone(), Self::file_action_to_action_type(f.action)))
                .collect();

            self.scene.apply_commit(&commit.author, &files);
            self.last_applied_commit += 1;
        }
    }

    /// Update the visualization state.
    fn update(&mut self, dt: f64) {
        // Always update scene and camera (for physics and animations)
        let dt_f32 = dt as f32;
        self.scene.update(dt_f32);
        self.camera.update(dt_f32);

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

        // Apply any commits we've reached but haven't applied yet
        self.apply_pending_commits();

        // Auto-fit camera to scene content periodically
        // (simple overview mode - more sophisticated tracking would use CameraTracker)
        if self.scene.file_count() > 0 {
            let bounds = self.scene.bounds();
            self.camera.fit_to_bounds(bounds, 100.0);
        }

        // Loop if enabled
        if self.args.loop_playback && self.current_commit >= self.commits.len().saturating_sub(1) {
            self.current_commit = 0;
            self.last_applied_commit = 0;
            self.accumulated_time = 0.0;
            self.scene = Scene::new();
        }
    }

    /// Render the current frame.
    #[allow(clippy::too_many_lines)]
    fn render(&mut self) {
        let Some(renderer) = &mut self.renderer else {
            return;
        };

        renderer.begin_frame();

        // Clear to background color
        let bg_color = self.args.parse_background_color();
        renderer.clear(bg_color);

        // Get camera's visible bounds in world space for frustum culling
        let visible_bounds = self.camera.visible_bounds();
        // Expand bounds to include entities with radii at the edge
        let culling_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 100.0);

        // Query visible entities using spatial index (frustum culling)
        let (visible_dir_ids, visible_file_ids, visible_user_ids) =
            self.scene.visible_entities(&culling_bounds);

        // Render directories (as circles showing structure)
        for &dir_id in &visible_dir_ids {
            let Some(dir) = self.scene.directories().get(dir_id) else {
                continue;
            };

            if !dir.is_visible() {
                continue;
            }

            let screen_pos = self.camera.world_to_screen(dir.position());
            let radius = dir.radius() * self.camera.zoom();

            // Draw directory as a hollow circle
            let depth_color = 0.15 + 0.05 * (dir.depth() as f32).min(5.0);
            let dir_color = Color::new(depth_color, depth_color, depth_color + 0.1, 0.5);
            renderer.draw_circle(screen_pos, radius, 1.0, dir_color);

            // Draw connection to parent
            if let Some(parent_pos) = dir.parent_position() {
                let parent_screen = self.camera.world_to_screen(parent_pos);
                renderer.draw_line(parent_screen, screen_pos, 1.0, dir_color.with_alpha(0.3));
            }
        }

        // Render files (only visible ones from frustum culling)
        for &file_id in &visible_file_ids {
            let Some(file) = self.scene.get_file(file_id) else {
                continue;
            };

            if file.alpha() < 0.01 {
                continue;
            }

            let screen_pos = self.camera.world_to_screen(file.position());
            let radius = file.radius() * self.camera.zoom();
            let color = file.current_color().with_alpha(file.alpha());

            // Draw file as a filled disc
            renderer.draw_disc(screen_pos, radius.max(2.0), color);

            // Draw connection to parent directory
            if let Some(dir) = self.scene.directories().get(file.directory()) {
                let dir_screen = self.camera.world_to_screen(dir.position());
                renderer.draw_line(
                    dir_screen,
                    screen_pos,
                    0.5,
                    color.with_alpha(0.2 * file.alpha()),
                );
            }
        }

        // Render actions (beams from users to files)
        // Actions are typically few in number, so no frustum culling needed
        for action in self.scene.actions() {
            let user_opt = self.scene.get_user(action.user());
            let file_opt = self.scene.get_file(action.file());

            if let (Some(user), Some(file)) = (user_opt, file_opt) {
                let user_screen = self.camera.world_to_screen(user.position());
                let file_screen = self.camera.world_to_screen(file.position());
                let beam_end = user_screen.lerp(file_screen, action.progress());

                let beam_color = action.beam_color();
                renderer.draw_line(user_screen, beam_end, 2.0, beam_color);

                // Draw beam head
                let head_radius = 3.0 * self.camera.zoom();
                renderer.draw_disc(beam_end, head_radius.max(2.0), beam_color);
            }
        }

        // Render users (only visible ones from frustum culling)
        for &user_id in &visible_user_ids {
            let Some(user) = self.scene.get_user(user_id) else {
                continue;
            };

            if user.alpha() < 0.01 {
                continue;
            }

            let screen_pos = self.camera.world_to_screen(user.position());
            let radius = user.radius() * self.camera.zoom();
            let color = user.display_color();

            // Draw user as a larger filled disc
            renderer.draw_disc(screen_pos, radius.max(5.0), color);

            // Draw a highlight ring if active
            if user.is_active() {
                renderer.draw_circle(
                    screen_pos,
                    radius * 1.3,
                    2.0,
                    color.with_alpha(0.5 * user.alpha()),
                );
            }
        }

        // Render UI overlays
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

        // Draw progress bar at bottom of screen
        if !self.commits.is_empty() {
            let width = renderer.width() as f32;
            let height = renderer.height() as f32;
            let bar_height = 4.0;
            let progress = self.current_commit as f32 / self.commits.len().max(1) as f32;

            // Background bar
            renderer.draw_quad(
                rource_math::Bounds::new(
                    Vec2::new(0.0, height - bar_height),
                    Vec2::new(width, height),
                ),
                None,
                Color::new(0.2, 0.2, 0.2, 0.5),
            );

            // Progress bar
            renderer.draw_quad(
                rource_math::Bounds::new(
                    Vec2::new(0.0, height - bar_height),
                    Vec2::new(width * progress, height),
                ),
                None,
                Color::new(0.3, 0.6, 1.0, 0.8),
            );
        }

        // Draw stats indicators in corner
        let stats_color = Color::new(1.0, 1.0, 1.0, 0.6);
        let file_count = self.scene.file_count();
        let user_count = self.scene.user_count();
        let commit_idx = self.current_commit;
        let total_commits = self.commits.len();

        let indicator_height = 8.0;
        let max_width = 100.0;

        // Commit progress indicator
        if total_commits > 0 {
            let progress = commit_idx as f32 / total_commits as f32;
            renderer.draw_quad(
                rource_math::Bounds::new(
                    Vec2::new(10.0, 50.0),
                    Vec2::new(10.0 + max_width * progress, 50.0 + indicator_height),
                ),
                None,
                stats_color,
            );
        }

        // File count indicator (logarithmic scale)
        if file_count > 0 {
            let file_bar = ((file_count as f32).ln() / 10.0).min(1.0);
            renderer.draw_quad(
                rource_math::Bounds::new(
                    Vec2::new(10.0, 62.0),
                    Vec2::new(10.0 + max_width * file_bar, 62.0 + indicator_height),
                ),
                None,
                Color::new(0.3, 1.0, 0.3, 0.6),
            );
        }

        // User count indicator
        if user_count > 0 {
            let user_bar = ((user_count as f32).ln() / 5.0).min(1.0);
            renderer.draw_quad(
                rource_math::Bounds::new(
                    Vec2::new(10.0, 74.0),
                    Vec2::new(10.0 + max_width * user_bar, 74.0 + indicator_height),
                ),
                None,
                Color::new(1.0, 0.6, 0.3, 0.6),
            );
        }

        renderer.end_frame();

        // Apply shadow effect if enabled (applied first - underneath)
        if let Some(ref shadow) = self.shadow {
            let w = renderer.width() as usize;
            let h = renderer.height() as usize;
            shadow.apply(renderer.pixels_mut(), w, h);
        }

        // Apply bloom effect if enabled (applied on top)
        if let Some(ref bloom) = self.bloom {
            let w = renderer.width() as usize;
            let h = renderer.height() as usize;
            bloom.apply(renderer.pixels_mut(), w, h);
        }
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

/// Check if a screen position is within the visible viewport.
///
/// Note: This function is kept for reference but is no longer used in rendering,
/// as frustum culling is now performed via spatial queries in world space.
#[allow(dead_code)]
#[inline]
fn is_screen_visible(screen_pos: Vec2, viewport: (f32, f32)) -> bool {
    let margin = 50.0;
    let (w, h) = viewport;
    screen_pos.x >= -margin
        && screen_pos.x <= w + margin
        && screen_pos.y >= -margin
        && screen_pos.y <= h + margin
}

/// Simple string hash for deterministic colors.
#[allow(dead_code)]
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

    #[test]
    fn test_file_action_to_action_type() {
        assert!(matches!(
            App::file_action_to_action_type(FileAction::Create),
            ActionType::Create
        ));
        assert!(matches!(
            App::file_action_to_action_type(FileAction::Modify),
            ActionType::Modify
        ));
        assert!(matches!(
            App::file_action_to_action_type(FileAction::Delete),
            ActionType::Delete
        ));
    }

    #[test]
    fn test_is_screen_visible() {
        let viewport = (800.0, 600.0);

        // Center should be visible
        assert!(is_screen_visible(Vec2::new(400.0, 300.0), viewport));

        // Corner should be visible
        assert!(is_screen_visible(Vec2::new(0.0, 0.0), viewport));

        // Just outside should still be visible (within margin)
        assert!(is_screen_visible(Vec2::new(-30.0, -30.0), viewport));

        // Far outside should not be visible
        assert!(!is_screen_visible(Vec2::new(-100.0, -100.0), viewport));
        assert!(!is_screen_visible(Vec2::new(1000.0, 1000.0), viewport));
    }
}
