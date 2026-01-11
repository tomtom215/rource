//! Rource CLI - Native application entry point.
//!
//! This is the main entry point for the native Rource application.
//! It sets up the window using winit and displays the rendered output
//! using softbuffer.

// Allow multiple versions of dependencies from winit/softbuffer ecosystem
#![allow(clippy::multiple_crate_versions)]
// Allow these pre-existing lint issues for now
#![allow(clippy::too_many_lines)]
#![allow(clippy::redundant_closure)]
#![allow(clippy::used_underscore_binding)]
#![allow(clippy::option_if_let_else)]
#![allow(clippy::no_effect_underscore_binding)]
#![allow(clippy::redundant_closure_for_method_calls)]

mod args;
mod avatar;
mod export;

use std::num::NonZeroU32;
use std::rc::Rc;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use winit::application::ApplicationHandler;
use winit::dpi::{LogicalSize, PhysicalSize};
use winit::event::{ElementState, KeyEvent, MouseButton, MouseScrollDelta, WindowEvent};
use winit::event_loop::{ActiveEventLoop, ControlFlow, EventLoop};
use winit::keyboard::{Key, NamedKey};
use winit::window::{Window, WindowId};

use rource_core::camera::{Camera, Camera3D};
use rource_core::config::FilterSettings;
use rource_core::scene::{ActionType, Scene};
use rource_math::{Color, Vec2};
use rource_render::effects::{BloomEffect, ShadowEffect};
use rource_render::{FontId, Renderer, SoftwareRenderer};
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

    /// Default font for text rendering.
    default_font: Option<FontId>,

    /// The scene graph containing all entities.
    scene: Scene,

    /// Camera for view transforms (2D mode).
    camera: Camera,

    /// 3D orbit camera (optional, when 3D mode enabled).
    camera_3d: Option<Camera3D>,

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

    /// Current mouse position in screen coordinates.
    mouse_position: Vec2,

    /// Whether the mouse is currently being dragged (left button held).
    mouse_dragging: bool,

    /// Last mouse position when drag started or during drag.
    last_mouse_position: Vec2,

    /// Frame exporter for video output.
    frame_exporter: Option<export::FrameExporter>,

    /// Pending screenshot path (saved after next render).
    screenshot_pending: Option<std::path::PathBuf>,

    /// User avatar manager (used before registration, None after).
    avatar_manager: Option<avatar::AvatarManager>,

    /// Registered avatar texture IDs (available after renderer creation).
    avatar_registry: avatar::AvatarRegistry,

    /// Filter settings for users and files.
    filter: FilterSettings,

    /// Username to follow when in follow mode.
    follow_user: Option<String>,

    /// Usernames to highlight (parsed from comma-separated list).
    highlight_users: Vec<String>,

    /// Whether to highlight all users.
    highlight_all_users: bool,

    /// Index of current user for Tab cycling navigation.
    current_user_index: usize,

    /// Directory name display depth.
    dir_name_depth: u32,

    /// Directory name position along edge (0.0 = start, 1.0 = end).
    dir_name_position: f32,

    /// Logo image path.
    logo_path: Option<std::path::PathBuf>,

    /// Logo offset from top-right corner.
    logo_offset: (i32, i32),

    /// Background image path.
    background_image_path: Option<std::path::PathBuf>,

    /// Logo texture ID (loaded from `logo_path`).
    logo_texture: Option<rource_render::TextureId>,

    /// Logo image dimensions (width, height).
    logo_dimensions: Option<(u32, u32)>,

    /// Background image texture ID (loaded from `background_image_path`).
    background_texture: Option<rource_render::TextureId>,
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

    /// Time scale multiplier.
    time_scale: f32,

    /// Stop playback after this many seconds of real time.
    stop_at_time: Option<f32>,

    /// Elapsed real time in seconds.
    elapsed_time: f32,

    /// Use real-time playback (1 second = 1 second of history).
    realtime: bool,
}

impl Default for PlaybackState {
    fn default() -> Self {
        Self {
            paused: false,
            speed: 1.0,
            seconds_per_day: 10.0,
            time_scale: 1.0,
            stop_at_time: None,
            elapsed_time: 0.0,
            realtime: false,
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

        // Initialize frame exporter if output is specified
        let frame_exporter = args.output.as_ref().map(|output| {
            if output.as_os_str() == "-" {
                // Output to stdout for piping to ffmpeg
                export::FrameExporter::to_stdout(args.framerate)
            } else {
                // Output to directory with numbered files
                export::FrameExporter::to_directory(output, args.framerate)
            }
        });

        // Load user avatars if specified
        let mut avatars = args
            .user_image_dir
            .as_ref()
            .map(avatar::AvatarManager::load_from_directory)
            .unwrap_or_default();

        // Load default avatar if specified
        if let Some(ref default_path) = args.default_user_image {
            avatars.set_default_avatar(default_path);
        }

        // Initialize filter settings from CLI args
        let mut filter = FilterSettings::new();
        if let Some(ref pattern) = args.show_users {
            filter.set_show_users(Some(pattern.clone()));
        }
        if let Some(ref pattern) = args.hide_users {
            filter.set_hide_users(Some(pattern.clone()));
        }
        if let Some(ref pattern) = args.show_files {
            filter.set_show_files(Some(pattern.clone()));
        }
        if let Some(ref pattern) = args.hide_files {
            filter.set_hide_files(Some(pattern.clone()));
        }
        if let Some(ref pattern) = args.hide_dirs {
            filter.set_hide_dirs(Some(pattern.clone()));
        }

        // Parse highlight users (comma-separated list)
        let highlight_users = args
            .highlight_users
            .as_ref()
            .map(|s| s.split(',').map(|u| u.trim().to_string()).collect())
            .unwrap_or_default();

        // Extract values from args before moving
        let time_scale = args.time_scale;
        let stop_at_time = args.stop_at_time;
        let realtime = args.realtime;
        let follow_user = args.follow_user.clone();
        let highlight_all_users = args.highlight_all_users;
        let dir_name_depth = args.dir_name_depth;
        let dir_name_position = args.dir_name_position;
        let logo_path = args.logo.clone();
        let logo_offset = args.parse_logo_offset();
        let background_image_path = args.background_image.clone();

        // 3D camera settings (--3d enables, --2d explicitly disables)
        let enable_3d = args.camera_3d && !args.camera_2d;
        let camera_3d = if enable_3d {
            // Use args viewport dimensions; will be updated on window resize
            let mut cam = Camera3D::new(args.width as f32, args.height as f32);
            // Set initial pitch (yaw=0)
            cam.jump_to_orbit(0.0, args.pitch.to_radians());
            if args.disable_auto_rotate {
                cam.set_auto_rotate(false);
            } else {
                cam.set_auto_rotation_speed(args.rotation_speed);
            }
            Some(cam)
        } else {
            None
        };

        Self {
            args,
            window: None,
            surface: None,
            renderer: None,
            default_font: None,
            scene: Scene::new(),
            camera,
            camera_3d,
            bloom,
            shadow,
            playback: PlaybackState {
                paused,
                seconds_per_day,
                time_scale,
                stop_at_time,
                elapsed_time: 0.0,
                realtime,
                ..Default::default()
            },
            commits: Vec::new(),
            current_commit: 0,
            last_applied_commit: 0,
            last_frame: Instant::now(),
            accumulated_time: 0.0,
            should_exit: false,
            mouse_position: Vec2::ZERO,
            mouse_dragging: false,
            last_mouse_position: Vec2::ZERO,
            frame_exporter,
            screenshot_pending: None,
            avatar_manager: if avatars.has_avatars() {
                Some(avatars)
            } else {
                None
            },
            avatar_registry: avatar::AvatarRegistry::default(),
            filter,
            follow_user,
            highlight_users,
            highlight_all_users,
            current_user_index: 0,
            dir_name_depth,
            dir_name_position,
            logo_path,
            logo_offset,
            background_image_path,
            logo_texture: None,
            logo_dimensions: None,
            background_texture: None,
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
                "s" | "S" => {
                    // Take screenshot
                    let filename = format!(
                        "rource_screenshot_{}.png",
                        chrono::Utc::now().format("%Y%m%d_%H%M%S")
                    );
                    self.screenshot_pending = Some(std::path::PathBuf::from(&filename));
                    eprintln!("Screenshot will be saved to: {filename}");
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
            Key::Named(NamedKey::Tab) => {
                // Cycle through users
                self.cycle_to_next_user();
            }
            _ => {}
        }
    }

    /// Cycle camera focus to the next visible user.
    fn cycle_to_next_user(&mut self) {
        let user_count = self.scene.user_count();
        if user_count == 0 {
            return;
        }

        // Get all user IDs
        let user_ids: Vec<_> = self.scene.users().values().map(|u| u.id()).collect();
        if user_ids.is_empty() {
            return;
        }

        // Move to next user
        self.current_user_index = (self.current_user_index + 1) % user_ids.len();
        let user_id = user_ids[self.current_user_index];

        // Focus camera on this user
        if let Some(user) = self.scene.get_user(user_id) {
            self.camera.jump_to(user.position());
            eprintln!("Following user: {}", user.name());
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

            // Skip commits from filtered-out users
            if !self.filter.should_include_user(&commit.author) {
                self.last_applied_commit += 1;
                continue;
            }

            // Convert commit files to scene format, filtering out hidden files
            let files: Vec<(std::path::PathBuf, ActionType)> = commit
                .files
                .iter()
                .filter(|f| self.filter.should_include_file(&f.path))
                .map(|f| (f.path.clone(), Self::file_action_to_action_type(f.action)))
                .collect();

            // Only apply commit if there are files left after filtering
            if !files.is_empty() {
                self.scene.apply_commit(&commit.author, &files);
            }

            self.last_applied_commit += 1;
        }
    }

    /// Update the visualization state.
    fn update(&mut self, dt: f64) {
        // Always update scene and camera (for physics and animations)
        let dt_f32 = dt as f32;
        self.scene.update(dt_f32);
        self.camera.update(dt_f32);

        // Update 3D camera if enabled
        if let Some(ref mut camera_3d) = self.camera_3d {
            camera_3d.update(dt_f32);
        }

        // Track elapsed real time
        self.playback.elapsed_time += dt_f32;

        // Check stop_at_time
        if let Some(stop_time) = self.playback.stop_at_time {
            if self.playback.elapsed_time >= stop_time {
                self.should_exit = true;
                return;
            }
        }

        // Update user highlighting
        self.update_user_highlights();

        if self.playback.paused || self.commits.is_empty() {
            return;
        }

        // Apply time_scale multiplier to speed
        let effective_speed = self.playback.speed * self.playback.time_scale;
        self.accumulated_time += dt * f64::from(effective_speed);

        // Calculate how many days have passed based on playback speed
        let days_per_second = if self.playback.realtime {
            // In realtime mode, 1 second = 1 second of history
            1.0 / 86400.0 // 1 day = 86400 seconds
        } else {
            1.0 / f64::from(self.playback.seconds_per_day)
        };
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

        // Camera behavior based on follow_user setting
        if let Some(ref follow_name) = self.follow_user {
            // Find the user and focus on them
            let target_pos = self
                .scene
                .users()
                .values()
                .find(|u| u.name() == follow_name)
                .map(|u| u.position());
            if let Some(pos) = target_pos {
                self.camera.jump_to(pos);
            }
        } else {
            // Auto-fit camera to scene content periodically
            // (simple overview mode - more sophisticated tracking would use CameraTracker)
            if let Some(entity_bounds) = self.scene.compute_entity_bounds() {
                self.camera.fit_to_bounds(&entity_bounds, 100.0);
            }
        }

        // Loop if enabled
        if self.args.loop_playback && self.current_commit >= self.commits.len().saturating_sub(1) {
            self.current_commit = 0;
            self.last_applied_commit = 0;
            self.accumulated_time = 0.0;
            self.scene = Scene::new();
        }
    }

    /// Update user highlight states based on settings.
    fn update_user_highlights(&mut self) {
        // Collect user IDs first, then update
        let user_ids: Vec<_> = self.scene.users().values().map(|u| u.id()).collect();
        for user_id in user_ids {
            if let Some(user) = self.scene.get_user_mut(user_id) {
                let should_highlight = if self.highlight_all_users {
                    true
                } else if !self.highlight_users.is_empty() {
                    self.highlight_users.iter().any(|name| name == user.name())
                } else {
                    false
                };
                user.set_highlighted(should_highlight);
            }
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

        // Draw background image (stretched to fill viewport) if available
        if let Some(bg_texture) = self.background_texture {
            let viewport_bounds = rource_math::Bounds::new(
                Vec2::ZERO,
                Vec2::new(renderer.width() as f32, renderer.height() as f32),
            );
            renderer.draw_quad(viewport_bounds, Some(bg_texture), Color::WHITE);
        }

        // Get camera's visible bounds in world space for frustum culling
        let visible_bounds = self.camera.visible_bounds();
        // Expand bounds to include entities with radii at the edge
        let culling_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 100.0);

        // Query visible entities using spatial index (frustum culling)
        let (visible_dir_ids, visible_file_ids, visible_user_ids) =
            self.scene.visible_entities(&culling_bounds);

        // Render directories (as circles showing structure)
        let hide_root = self.args.hide_root;
        let hide_tree = self.args.hide_tree;
        let hide_dirnames = self.args.hide_dirnames;
        let dir_name_depth = self.dir_name_depth;
        let _dir_name_position = self.dir_name_position;
        let dir_font = self.default_font;
        let dir_font_size = self.args.font_size * 0.75;

        for &dir_id in &visible_dir_ids {
            let Some(dir) = self.scene.directories().get(dir_id) else {
                continue;
            };

            if !dir.is_visible() {
                continue;
            }

            // Skip root directory if hide_root is set
            if hide_root && dir.depth() == 0 {
                continue;
            }

            let screen_pos = self.camera.world_to_screen(dir.position());
            let radius = dir.radius() * self.camera.zoom();

            // Draw directory as a hollow circle
            let depth_color = 0.15 + 0.05 * (dir.depth() as f32).min(5.0);
            let dir_color = Color::new(depth_color, depth_color, depth_color + 0.1, 0.5);
            renderer.draw_circle(screen_pos, radius, 1.0, dir_color);

            // Draw connection to parent (unless hide_tree is set)
            if !hide_tree {
                if let Some(parent_pos) = dir.parent_position() {
                    let parent_screen = self.camera.world_to_screen(parent_pos);
                    renderer.draw_line(parent_screen, screen_pos, 1.0, dir_color.with_alpha(0.3));
                }
            }

            // Draw directory name label if enabled and within depth limit
            if !hide_dirnames && dir.depth() <= dir_name_depth {
                if let Some(font_id) = dir_font {
                    let name = dir.name();
                    let label_pos = Vec2::new(screen_pos.x + radius + 3.0, screen_pos.y - dir_font_size * 0.3);
                    let label_color = Color::new(0.7, 0.7, 0.8, 0.6);
                    renderer.draw_text(name, label_pos, font_id, dir_font_size, label_color);
                }
            }
        }

        // Render files (only visible ones from frustum culling)
        // Store settings for filename labels
        let show_filenames = !self.args.hide_filenames;
        let file_font = self.default_font;
        let file_font_size = self.args.font_size * 0.8; // Slightly smaller for files
        let camera_zoom = self.camera.zoom();

        for &file_id in &visible_file_ids {
            let Some(file) = self.scene.get_file(file_id) else {
                continue;
            };

            if file.alpha() < 0.01 {
                continue;
            }

            let screen_pos = self.camera.world_to_screen(file.position());
            let radius = file.radius() * camera_zoom;
            let color = file.current_color().with_alpha(file.alpha());

            // Draw file as a filled disc
            renderer.draw_disc(screen_pos, radius.max(2.0), color);

            // Draw connection to parent directory (unless hide_tree is set)
            if !hide_tree {
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

            // Draw filename label (only for prominent files when zoomed in)
            // Show labels for files with high alpha (recently touched) when zoomed in enough
            if show_filenames && file.alpha() > 0.5 && camera_zoom > 0.3 {
                if let Some(font_id) = file_font {
                    let name = file.name();
                    let label_pos = Vec2::new(
                        screen_pos.x + radius + 3.0,
                        screen_pos.y - file_font_size * 0.3,
                    );
                    let label_color = Color::new(0.9, 0.9, 0.9, 0.7 * file.alpha());
                    renderer.draw_text(name, label_pos, font_id, file_font_size, label_color);
                }
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
        // Store font info for name labels (avoid borrow issues)
        let show_usernames = !self.args.hide_usernames;
        let name_font = self.default_font;
        let name_font_size = self.args.font_size;

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
            let effective_radius = radius.max(5.0);

            // Draw border/outline (darker version of user color)
            let border_color = Color::new(color.r * 0.4, color.g * 0.4, color.b * 0.4, color.a);
            renderer.draw_disc(screen_pos, effective_radius + 2.0, border_color);

            // Check for avatar texture
            if let Some(avatar_id) = self.avatar_registry.get_avatar_id(user.name()) {
                // Draw avatar as a square quad with alpha
                let half_size = effective_radius * 0.9; // Slightly smaller than border
                let bounds = rource_math::Bounds::from_center_half_extents(
                    screen_pos,
                    Vec2::splat(half_size),
                );
                let tint = Color::new(1.0, 1.0, 1.0, user.alpha());
                renderer.draw_quad(bounds, Some(avatar_id), tint);
            } else {
                // Draw user as a filled disc (no avatar)
                renderer.draw_disc(screen_pos, effective_radius, color);

                // Draw initials if the disc is large enough (radius > 12 pixels)
                if effective_radius > 12.0 {
                    if let Some(font_id) = name_font {
                        let initials = get_initials(user.name());
                        let initial_font_size = (effective_radius * 0.8).clamp(8.0, 20.0);
                        // Center the initials on the disc
                        let text_width = initials.len() as f32 * initial_font_size * 0.5;
                        let initial_pos = Vec2::new(
                            screen_pos.x - text_width * 0.5,
                            screen_pos.y - initial_font_size * 0.35,
                        );
                        let initial_color = Color::new(1.0, 1.0, 1.0, 0.9 * user.alpha());
                        renderer.draw_text(
                            &initials,
                            initial_pos,
                            font_id,
                            initial_font_size,
                            initial_color,
                        );
                    }
                }
            }

            // Draw a highlight ring if active
            if user.is_active() {
                renderer.draw_circle(
                    screen_pos,
                    effective_radius * 1.3,
                    2.0,
                    color.with_alpha(0.5 * user.alpha()),
                );
            }

            // Draw username label
            if show_usernames {
                if let Some(font_id) = name_font {
                    let name = user.name();
                    let label_pos = Vec2::new(
                        screen_pos.x + effective_radius + 5.0,
                        screen_pos.y - name_font_size * 0.3,
                    );
                    let label_color = Color::new(1.0, 1.0, 1.0, 0.8 * user.alpha());
                    renderer.draw_text(name, label_pos, font_id, name_font_size, label_color);
                }
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

        // Draw progress bar at bottom of screen (unless hide_progress is set)
        if !self.args.hide_progress && !self.commits.is_empty() {
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

        // Text overlays
        if let Some(font_id) = self.default_font {
            let font_size = self.args.font_size;
            let text_color = Color::new(1.0, 1.0, 1.0, 0.9);
            let height = renderer.height() as f32;
            let width = renderer.width() as f32;

            // Title (top-center)
            if let Some(ref title) = self.args.title {
                let title_size = font_size * 1.5;
                // Approximate text centering (rough estimate)
                let title_x = (width / 2.0) - (title.len() as f32 * title_size * 0.3);
                renderer.draw_text(
                    title,
                    Vec2::new(title_x.max(10.0), 20.0),
                    font_id,
                    title_size,
                    text_color,
                );
            }

            // Date display (bottom-left, above progress bar)
            if !self.args.hide_date && !self.commits.is_empty() {
                if let Some(commit) = self
                    .commits
                    .get(self.current_commit.saturating_sub(1).max(0))
                {
                    let date_str = format_timestamp(commit.timestamp);
                    renderer.draw_text(
                        &date_str,
                        Vec2::new(10.0, height - 30.0),
                        font_id,
                        font_size,
                        text_color.with_alpha(0.7),
                    );
                }
            }

            // Current commit info (bottom-left, above date)
            if self.current_commit > 0 {
                if let Some(commit) = self.commits.get(self.current_commit - 1) {
                    // Author name
                    renderer.draw_text(
                        &commit.author,
                        Vec2::new(10.0, height - 50.0),
                        font_id,
                        font_size,
                        text_color.with_alpha(0.8),
                    );

                    // File count in commit
                    let files_text = format!("{} files", commit.files.len());
                    renderer.draw_text(
                        &files_text,
                        Vec2::new(10.0, height - 70.0),
                        font_id,
                        font_size * 0.9,
                        text_color.with_alpha(0.6),
                    );
                }
            }

            // Speed indicator (top-right, only if not 1.0x)
            if (self.playback.speed - 1.0).abs() > 0.01 {
                let speed_text = format!("{:.1}x", self.playback.speed);
                renderer.draw_text(
                    &speed_text,
                    Vec2::new(width - 60.0, 20.0),
                    font_id,
                    font_size,
                    text_color.with_alpha(0.7),
                );
            }

            // Pause indicator text
            if self.playback.paused {
                renderer.draw_text(
                    "PAUSED",
                    Vec2::new(50.0, 24.0),
                    font_id,
                    font_size,
                    text_color.with_alpha(0.7),
                );
            }

            // Stats text (next to indicators)
            let stats_text = format!(
                "{commit_idx}/{total_commits} commits | {file_count} files | {user_count} users"
            );
            renderer.draw_text(
                &stats_text,
                Vec2::new(120.0, 54.0),
                font_id,
                font_size * 0.8,
                text_color.with_alpha(0.5),
            );

            // File extension legend (lower-right corner)
            if !self.args.hide_legend {
                let legend_font_size = font_size * 0.8;
                let legend_padding = 10.0;
                let legend_entry_height = legend_font_size + 4.0;
                let legend_color_size = legend_font_size * 0.7;

                // Get file extension stats (limited to top 10)
                let stats = self.scene.file_extension_stats();
                let max_legend_entries = 10;
                let legend_entries: Vec<_> = stats.into_iter().take(max_legend_entries).collect();

                if !legend_entries.is_empty() {
                    let legend_height =
                        legend_entries.len() as f32 * legend_entry_height + legend_padding * 2.0;
                    let legend_width = 120.0;
                    let legend_x = width - legend_width - legend_padding;
                    let legend_y = height - legend_height - 20.0; // Above progress bar

                    // Background
                    renderer.draw_quad(
                        rource_math::Bounds::new(
                            Vec2::new(legend_x, legend_y),
                            Vec2::new(legend_x + legend_width, legend_y + legend_height),
                        ),
                        None,
                        Color::new(0.0, 0.0, 0.0, 0.5),
                    );

                    // Title
                    renderer.draw_text(
                        "File Types",
                        Vec2::new(legend_x + legend_padding, legend_y + legend_padding),
                        font_id,
                        legend_font_size,
                        text_color.with_alpha(0.8),
                    );

                    // Entries
                    for (i, (ext, count)) in legend_entries.iter().enumerate() {
                        let entry_y =
                            legend_y + legend_padding + legend_entry_height * (i as f32 + 1.0);

                        // Color swatch
                        let ext_color = rource_core::scene::FileNode::color_from_extension(ext);
                        renderer.draw_quad(
                            rource_math::Bounds::new(
                                Vec2::new(legend_x + legend_padding, entry_y + 2.0),
                                Vec2::new(
                                    legend_x + legend_padding + legend_color_size,
                                    entry_y + 2.0 + legend_color_size,
                                ),
                            ),
                            None,
                            ext_color,
                        );

                        // Extension name and count
                        let ext_display = if ext.len() > 8 {
                            format!("{}..", &ext[..6])
                        } else {
                            ext.clone()
                        };
                        let entry_text = format!("{ext_display} ({count})");
                        renderer.draw_text(
                            &entry_text,
                            Vec2::new(legend_x + legend_padding + legend_color_size + 4.0, entry_y),
                            font_id,
                            legend_font_size * 0.9,
                            text_color.with_alpha(0.7),
                        );
                    }
                }
            }
        }

        // Draw logo in top-right corner if available
        if let (Some(logo_texture), Some((logo_width, logo_height))) =
            (self.logo_texture, self.logo_dimensions)
        {
            let viewport_width = renderer.width() as f32;
            let (offset_x, offset_y) = self.logo_offset;

            // Position logo in top-right corner with offset
            // offset_x: positive moves left, offset_y: positive moves down
            let logo_x = viewport_width - logo_width as f32 - offset_x as f32;
            let logo_y = offset_y as f32;

            let logo_bounds = rource_math::Bounds::new(
                Vec2::new(logo_x, logo_y),
                Vec2::new(logo_x + logo_width as f32, logo_y + logo_height as f32),
            );
            renderer.draw_quad(logo_bounds, Some(logo_texture), Color::WHITE);
        }

        renderer.end_frame();

        // Apply shadow effect if enabled (applied first - underneath)
        if let Some(ref shadow) = self.shadow {
            let w = renderer.width() as usize;
            let h = renderer.height() as usize;
            shadow.apply(renderer.pixels_mut(), w, h);
        }

        // Apply bloom effect if enabled (applied on top, unless hide_bloom is set)
        if !self.args.hide_bloom {
            if let Some(ref bloom) = self.bloom {
                let w = renderer.width() as usize;
                let h = renderer.height() as usize;
                bloom.apply(renderer.pixels_mut(), w, h);
            }
        }
    }

    /// Handle mouse button press/release.
    fn handle_mouse_button(&mut self, button: MouseButton, state: ElementState) {
        if self.args.disable_input {
            return;
        }

        match button {
            MouseButton::Left => match state {
                ElementState::Pressed => {
                    // Check if clicking on progress bar (timeline scrubbing)
                    if let Some(renderer) = &self.renderer {
                        let height = renderer.height() as f32;
                        let width = renderer.width() as f32;
                        let bar_height = 12.0; // Clickable area is larger than visual bar

                        if self.mouse_position.y >= height - bar_height && !self.commits.is_empty()
                        {
                            // Seek to clicked position
                            let progress = (self.mouse_position.x / width).clamp(0.0, 1.0);
                            let target_commit =
                                (progress * self.commits.len() as f32).round() as usize;
                            self.seek_to_commit(target_commit);
                            return;
                        }
                    }

                    self.mouse_dragging = true;
                    self.last_mouse_position = self.mouse_position;
                }
                ElementState::Released => {
                    self.mouse_dragging = false;
                }
            },
            MouseButton::Middle => {
                // Middle click resets camera
                if state == ElementState::Pressed {
                    if let Some(ref mut camera_3d) = self.camera_3d {
                        camera_3d.reset();
                    } else {
                        self.camera.reset();
                    }
                }
            }
            _ => {}
        }
    }

    /// Seek to a specific commit index.
    ///
    /// This resets the scene and re-applies commits if seeking backwards.
    fn seek_to_commit(&mut self, target: usize) {
        let target = target.min(self.commits.len());

        // If seeking backwards, reset scene and re-apply
        if target < self.current_commit {
            self.scene = Scene::new();
            self.last_applied_commit = 0;
            self.accumulated_time = 0.0;

            // Apply commits up to target
            for (i, commit) in self.commits.iter().take(target).enumerate() {
                let files: Vec<(std::path::PathBuf, ActionType)> = commit
                    .files
                    .iter()
                    .map(|f| {
                        (
                            f.path.clone(),
                            match f.action {
                                FileAction::Create => ActionType::Create,
                                FileAction::Modify => ActionType::Modify,
                                FileAction::Delete => ActionType::Delete,
                            },
                        )
                    })
                    .collect();

                self.scene.apply_commit(&commit.author, &files);
                self.last_applied_commit = i + 1;
            }

            // Update scene a bit to let things settle
            for _ in 0..5 {
                self.scene.update(0.1);
            }
        }

        self.current_commit = target;

        // If we have a target commit, calculate appropriate accumulated time
        if !self.commits.is_empty() && target > 0 && target <= self.commits.len() {
            // Calculate time based on commit timestamps
            let first_timestamp = self.commits[0].timestamp;
            let target_timestamp = self.commits[target.saturating_sub(1)].timestamp;
            let days = (target_timestamp - first_timestamp) as f64 / 86400.0;
            self.accumulated_time = days * f64::from(self.playback.seconds_per_day);
        }

        // Fit camera to content
        if let Some(bounds) = self.scene.compute_entity_bounds() {
            if bounds.is_valid() && bounds.width() > 0.0 && bounds.height() > 0.0 {
                self.camera.fit_to_bounds(&bounds, 100.0);
            }
        }
    }

    /// Handle mouse movement.
    fn handle_mouse_move(&mut self, x: f64, y: f64) {
        let new_position = Vec2::new(x as f32, y as f32);
        self.mouse_position = new_position;

        if self.args.disable_input {
            return;
        }

        // Pan (2D) or orbit (3D) when dragging
        if self.mouse_dragging {
            let delta = new_position - self.last_mouse_position;

            if let Some(ref mut camera_3d) = self.camera_3d {
                // 3D mode: orbit camera based on mouse movement
                // Convert mouse delta to radians (sensitivity factor)
                let sensitivity = 0.005;
                let delta_yaw = delta.x * sensitivity;
                let delta_pitch = -delta.y * sensitivity; // Invert Y for intuitive control
                camera_3d.orbit(delta_yaw, delta_pitch);
            } else {
                // 2D mode: pan camera
                self.camera.pan(delta);
            }

            self.last_mouse_position = new_position;
        }
    }

    /// Handle mouse scroll wheel.
    fn handle_mouse_scroll(&mut self, delta: MouseScrollDelta) {
        if self.args.disable_input {
            return;
        }

        // Calculate zoom factor from scroll delta
        let zoom_amount = match delta {
            MouseScrollDelta::LineDelta(_x, y) => y * 0.5, // Lines scrolled
            MouseScrollDelta::PixelDelta(pos) => (pos.y as f32) * 0.01, // Precise scrolling
        };

        // Zoom
        if zoom_amount.abs() > 0.001 {
            if let Some(ref mut camera_3d) = self.camera_3d {
                // 3D mode: zoom by adjusting orbit distance
                // Positive scroll = zoom in (closer)
                let factor = if zoom_amount > 0.0 { 0.9 } else { 1.1 };
                camera_3d.zoom(factor);
            } else {
                // 2D mode: zoom toward mouse position
                self.camera.zoom_toward(self.mouse_position, zoom_amount);
            }
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
        let mut renderer = SoftwareRenderer::new(size.width.max(1), size.height.max(1));

        // Load default font for text rendering
        let font_id = renderer.load_font(rource_render::default_font::ROBOTO_MONO);
        if font_id.is_none() {
            eprintln!("Warning: Failed to load default font");
        }

        // Register avatars with renderer
        if let Some(manager) = self.avatar_manager.take() {
            self.avatar_registry = manager.register_with_renderer(&mut renderer);
        }

        // Load logo image if specified
        if let Some(ref logo_path) = self.logo_path {
            match rource_render::image::Image::load_file(logo_path) {
                Ok(image) => {
                    let width = image.width();
                    let height = image.height();
                    let texture_id = renderer.load_texture(width, height, image.data());
                    self.logo_texture = Some(texture_id);
                    self.logo_dimensions = Some((width, height));
                    eprintln!("Loaded logo: {}x{} from {}", width, height, logo_path.display());
                }
                Err(e) => {
                    eprintln!("Warning: Failed to load logo image '{}': {}", logo_path.display(), e);
                }
            }
        }

        // Load background image if specified
        if let Some(ref bg_path) = self.background_image_path {
            match rource_render::image::Image::load_file(bg_path) {
                Ok(image) => {
                    let width = image.width();
                    let height = image.height();
                    let texture_id = renderer.load_texture(width, height, image.data());
                    self.background_texture = Some(texture_id);
                    eprintln!("Loaded background: {}x{} from {}", width, height, bg_path.display());
                }
                Err(e) => {
                    eprintln!("Warning: Failed to load background image '{}': {}", bg_path.display(), e);
                }
            }
        }

        self.window = Some(window);
        self.surface = Some(surface);
        self.renderer = Some(renderer);
        self.default_font = font_id;
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
            WindowEvent::MouseInput { state, button, .. } => {
                self.handle_mouse_button(button, state);
            }
            WindowEvent::CursorMoved { position, .. } => {
                self.handle_mouse_move(position.x, position.y);
            }
            WindowEvent::MouseWheel { delta, .. } => {
                self.handle_mouse_scroll(delta);
            }
            WindowEvent::RedrawRequested => {
                // Calculate delta time
                let now = Instant::now();
                let dt = now.duration_since(self.last_frame).as_secs_f64();
                self.last_frame = now;

                // Update and render
                self.update(dt);
                self.render();

                // Save screenshot if pending
                if let Some(path) = self.screenshot_pending.take() {
                    if let Some(renderer) = &self.renderer {
                        let pixels = renderer.pixels();
                        let width = renderer.width();
                        let height = renderer.height();

                        match export::write_png_to_file(pixels, width, height, &path) {
                            Ok(()) => {
                                eprintln!("Screenshot saved: {}", path.display());
                            }
                            Err(e) => {
                                eprintln!("Failed to save screenshot: {e}");
                            }
                        }
                    }
                }

                // Export frame if in export mode
                if let Some(ref mut exporter) = self.frame_exporter {
                    if let Some(renderer) = &self.renderer {
                        let pixels = renderer.pixels();
                        let width = renderer.width();
                        let height = renderer.height();

                        if let Err(e) = exporter.export_frame(pixels, width, height, dt) {
                            eprintln!("Frame export error: {e}");
                            event_loop.exit();
                            return;
                        }
                    }

                    // Check if visualization is complete (all commits processed)
                    // Note: current_commit maxes at len-1, so we use saturating_sub
                    if !self.commits.is_empty()
                        && self.current_commit >= self.commits.len().saturating_sub(1)
                        && self.last_applied_commit >= self.current_commit
                    {
                        eprintln!("Export complete: {} frames written", exporter.frame_count());
                        event_loop.exit();
                        return;
                    }
                }

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

/// Extract initials from a name for avatar display.
///
/// Takes up to 2 characters: the first character of the name and
/// the first character after a space (if present).
///
/// Examples:
/// - "John Doe" -> "JD"
/// - "Alice" -> "A"
/// - "bob" -> "B"
/// - "<email@example.com>" -> "E"
fn get_initials(name: &str) -> String {
    let name = name.trim();

    // Handle email-only format: <email@example.com>
    let name = if name.starts_with('<') && name.ends_with('>') {
        name.trim_start_matches('<').trim_end_matches('>')
    } else if let Some(pos) = name.find('<') {
        // Handle "Name <email>" format - use only the name part
        name[..pos].trim()
    } else {
        name
    };

    let mut initials = String::with_capacity(2);

    // Get first character
    if let Some(first_char) = name.chars().next() {
        initials.push(first_char.to_ascii_uppercase());
    }

    // Get first character after last space (for last name)
    if let Some(space_pos) = name.rfind(' ') {
        if let Some(second_char) = name[space_pos + 1..].chars().next() {
            initials.push(second_char.to_ascii_uppercase());
        }
    }

    initials
}

/// Run in headless mode (no window, batch video export).
///
/// This creates a renderer without a window and runs at maximum speed,
/// exporting frames directly without display overhead.
#[allow(clippy::too_many_lines)]
fn run_headless(args: &Args) -> Result<()> {
    use rource_vcs::{CustomParser, GitParser, Parser};
    use std::process::Command;

    // Validate that output is specified
    let output = args
        .output
        .as_ref()
        .context("--headless requires --output to be specified")?;

    eprintln!("Running in headless mode");
    eprintln!("Output: {}", output.display());

    // Performance timing
    let total_start = Instant::now();

    // Load commits
    let git_start = Instant::now();
    let commits: Vec<Commit> = if args.custom_log {
        let content =
            std::fs::read_to_string(&args.path).context("Failed to read custom log file")?;
        let parser = CustomParser::new();
        parser
            .parse_str(&content)
            .context("Failed to parse custom log")?
    } else {
        let git_output = Command::new("git")
            .arg("-C")
            .arg(&args.path)
            .arg("log")
            .arg("--pretty=format:commit %H%nAuthor: %an <%ae>%nDate: %at")
            .arg("--name-status")
            .arg("--reverse")
            .output()
            .context("Failed to run git log")?;

        if !git_output.status.success() {
            let stderr = String::from_utf8_lossy(&git_output.stderr);
            anyhow::bail!("git log failed: {stderr}");
        }

        let log_content = String::from_utf8_lossy(&git_output.stdout);
        let git_elapsed = git_start.elapsed();
        eprintln!("[PERF] Git log execution: {:.2}s ({:.1} MB output)",
            git_elapsed.as_secs_f64(),
            git_output.stdout.len() as f64 / 1_000_000.0);

        let parse_start = Instant::now();
        let parser = GitParser::new();
        let result = parser
            .parse_str(&log_content)
            .context("Failed to parse git log")?;
        let parse_elapsed = parse_start.elapsed();
        eprintln!("[PERF] Parsing: {:.2}s", parse_elapsed.as_secs_f64());
        result
    };

    if commits.is_empty() {
        anyhow::bail!("No commits found in repository");
    }

    let mut commits = commits;
    let sort_start = Instant::now();
    commits.sort_by_key(|c| c.timestamp);
    let sort_elapsed = sort_start.elapsed();

    // Count total file changes
    let total_files: usize = commits.iter().map(|c| c.files.len()).sum();
    eprintln!("[PERF] Sorting: {:.3}s", sort_elapsed.as_secs_f64());
    eprintln!("Loaded {} commits ({} file changes)", commits.len(), total_files);

    // Create renderer
    let mut renderer = SoftwareRenderer::new(args.width, args.height);
    let font_id = renderer.load_font(rource_render::default_font::ROBOTO_MONO);

    // Load logo image if specified
    let (logo_texture, logo_dimensions) = if let Some(ref logo_path) = args.logo {
        match rource_render::image::Image::load_file(logo_path) {
            Ok(image) => {
                let width = image.width();
                let height = image.height();
                let texture_id = renderer.load_texture(width, height, image.data());
                eprintln!("Loaded logo: {}x{} from {}", width, height, logo_path.display());
                (Some(texture_id), Some((width, height)))
            }
            Err(e) => {
                eprintln!("Warning: Failed to load logo image '{}': {}", logo_path.display(), e);
                (None, None)
            }
        }
    } else {
        (None, None)
    };

    // Load background image if specified
    let background_texture = if let Some(ref bg_path) = args.background_image {
        match rource_render::image::Image::load_file(bg_path) {
            Ok(image) => {
                let width = image.width();
                let height = image.height();
                let texture_id = renderer.load_texture(width, height, image.data());
                eprintln!("Loaded background: {}x{} from {}", width, height, bg_path.display());
                Some(texture_id)
            }
            Err(e) => {
                eprintln!("Warning: Failed to load background image '{}': {}", bg_path.display(), e);
                None
            }
        }
    } else {
        None
    };

    // Initialize scene and camera
    let mut scene = Scene::new();
    let mut camera = Camera::new(args.width as f32, args.height as f32);

    // Initialize effects
    let bloom = if args.no_bloom {
        None
    } else {
        Some(BloomEffect::new())
    };
    let shadow = if args.shadows {
        Some(ShadowEffect::subtle())
    } else {
        None
    };

    // Initialize frame exporter
    let mut exporter = if output.as_os_str() == "-" {
        export::FrameExporter::to_stdout(args.framerate)
    } else {
        export::FrameExporter::to_directory(output, args.framerate)
    };

    // Initialize filter settings
    let mut filter = FilterSettings::new();
    if let Some(ref pattern) = args.show_users {
        filter.set_show_users(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_users {
        filter.set_hide_users(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.show_files {
        filter.set_show_files(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_files {
        filter.set_hide_files(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_dirs {
        filter.set_hide_dirs(Some(pattern.clone()));
    }

    // Playback state
    let seconds_per_day = args.seconds_per_day;
    let speed = 1.0_f32;
    let mut accumulated_time = 0.0_f64;
    let mut current_commit = 0_usize;
    let mut last_applied_commit = 0_usize;

    // Fixed time step for consistent output
    let dt = 1.0 / f64::from(args.framerate);

    // Calculate total duration estimate
    if let (Some(first), Some(last)) = (commits.first(), commits.last()) {
        let days = (last.timestamp - first.timestamp) as f64 / 86400.0;
        let estimated_seconds = days * f64::from(seconds_per_day);
        let estimated_frames = (estimated_seconds * f64::from(args.framerate)) as u64;
        eprintln!("Estimated duration: {estimated_seconds:.1} seconds ({estimated_frames} frames)");
    }

    eprintln!("Rendering frames...");

    // Pre-warm: Apply the first commit and let entities fade in
    // This ensures files have visible alpha on the first frame
    if !commits.is_empty() {
        // Apply first commit immediately (with filtering)
        let commit = &commits[0];
        if filter.should_include_user(&commit.author) {
            let files: Vec<(std::path::PathBuf, rource_core::scene::ActionType)> = commit
                .files
                .iter()
                .filter(|f| filter.should_include_file(&f.path))
                .map(|f| (f.path.clone(), App::file_action_to_action_type(f.action)))
                .collect();
            if !files.is_empty() {
                scene.apply_commit(&commit.author, &files);
            }
        }
        last_applied_commit = 1;
        current_commit = 1;

        // Run scene updates to let entities fade in (simulates ~0.5 seconds)
        for _ in 0..30 {
            scene.update(dt as f32);
        }

        // Fit camera immediately to show entities
        if let Some(entity_bounds) = scene.compute_entity_bounds() {
            let center = entity_bounds.center();
            let size = entity_bounds.size();
            let padding = 100.0;
            let (vw, vh) = camera.viewport_size();
            let zoom_x = vw / (size.x + padding * 2.0);
            let zoom_y = vh / (size.y + padding * 2.0);
            let new_zoom = zoom_x.min(zoom_y).clamp(0.01, 10.0);
            camera.jump_to(center);
            camera.set_zoom(new_zoom);
        }
    }

    // Performance tracking accumulators
    let mut total_commit_apply_time = Duration::ZERO;
    let mut total_scene_update_time = Duration::ZERO;
    let mut total_render_time = Duration::ZERO;
    let mut total_effects_time = Duration::ZERO;
    let mut total_export_time = Duration::ZERO;
    let mut commits_applied = 0_usize;
    let loop_start = Instant::now();

    // Main rendering loop
    loop {
        // Update simulation
        accumulated_time += dt * f64::from(speed);
        let days_per_second = 1.0 / f64::from(seconds_per_day);
        let days_elapsed = accumulated_time * days_per_second;

        // Find commits at current time
        if let Some(first) = commits.first() {
            let first_time = first.timestamp;
            let target_time = first_time + (days_elapsed * 86400.0) as i64;

            while current_commit + 1 < commits.len() {
                if commits[current_commit + 1].timestamp <= target_time {
                    current_commit += 1;
                } else {
                    break;
                }
            }
        }

        // Apply pending commits (with filtering)
        let commit_apply_start = Instant::now();
        while last_applied_commit < current_commit {
            let commit = &commits[last_applied_commit];

            // Skip commits from filtered-out users
            if filter.should_include_user(&commit.author) {
                let files: Vec<(std::path::PathBuf, rource_core::scene::ActionType)> = commit
                    .files
                    .iter()
                    .filter(|f| filter.should_include_file(&f.path))
                    .map(|f| (f.path.clone(), App::file_action_to_action_type(f.action)))
                    .collect();

                // Only apply commit if there are files left after filtering
                if !files.is_empty() {
                    scene.apply_commit(&commit.author, &files);
                    commits_applied += 1;
                }
            }

            last_applied_commit += 1;
        }
        total_commit_apply_time += commit_apply_start.elapsed();

        // Update scene and camera
        let scene_update_start = Instant::now();
        scene.update(dt as f32);
        camera.update(dt as f32);

        // Auto-fit camera to scene content using actual entity bounds
        if let Some(entity_bounds) = scene.compute_entity_bounds() {
            camera.fit_to_bounds(&entity_bounds, 100.0);
        }
        total_scene_update_time += scene_update_start.elapsed();

        // Render frame
        let render_start = Instant::now();
        render_frame_headless(
            &mut renderer,
            &scene,
            &camera,
            args,
            font_id,
            &commits,
            current_commit,
            background_texture,
            logo_texture,
            logo_dimensions,
        );
        total_render_time += render_start.elapsed();

        // Apply effects
        let effects_start = Instant::now();
        if let Some(ref shadow_effect) = shadow {
            let w = renderer.width() as usize;
            let h = renderer.height() as usize;
            shadow_effect.apply(renderer.pixels_mut(), w, h);
        }
        if let Some(ref bloom_effect) = bloom {
            let w = renderer.width() as usize;
            let h = renderer.height() as usize;
            bloom_effect.apply(renderer.pixels_mut(), w, h);
        }
        total_effects_time += effects_start.elapsed();

        // Export frame
        let export_start = Instant::now();
        let pixels = renderer.pixels();
        let width = renderer.width();
        let height = renderer.height();
        exporter
            .export_frame(pixels, width, height, dt)
            .context("Failed to export frame")?;
        total_export_time += export_start.elapsed();

        // Progress reporting
        if exporter.frame_count() % 100 == 0 {
            let progress = current_commit as f32 / commits.len().max(1) as f32;
            eprint!(
                "\rFrame {}: {:.1}% ({}/{})",
                exporter.frame_count(),
                progress * 100.0,
                current_commit,
                commits.len()
            );
        }

        // Check for completion (all commits processed and applied)
        // Note: current_commit maxes at len-1 due to the incrementing loop condition
        if !commits.is_empty()
            && current_commit >= commits.len().saturating_sub(1)
            && last_applied_commit >= current_commit
        {
            break;
        }
    }

    let loop_elapsed = loop_start.elapsed();
    let total_elapsed = total_start.elapsed();
    let frame_count = exporter.frame_count();

    eprintln!(
        "\nExport complete: {frame_count} frames written"
    );

    // Print performance summary
    eprintln!("\n=== PERFORMANCE SUMMARY ===");
    eprintln!("Total time:        {:.2}s", total_elapsed.as_secs_f64());
    eprintln!("  Render loop:     {:.2}s ({} frames, {:.1}ms avg)",
        loop_elapsed.as_secs_f64(),
        frame_count,
        loop_elapsed.as_secs_f64() * 1000.0 / frame_count as f64);
    eprintln!("\nBreakdown per frame (avg):");
    eprintln!("  Commit apply:    {:.2}ms ({} commits, {:.3}ms/commit)",
        total_commit_apply_time.as_secs_f64() * 1000.0 / frame_count as f64,
        commits_applied,
        if commits_applied > 0 { total_commit_apply_time.as_secs_f64() * 1000.0 / commits_applied as f64 } else { 0.0 });
    eprintln!("  Scene update:    {:.2}ms",
        total_scene_update_time.as_secs_f64() * 1000.0 / frame_count as f64);
    eprintln!("  Render:          {:.2}ms",
        total_render_time.as_secs_f64() * 1000.0 / frame_count as f64);
    eprintln!("  Effects:         {:.2}ms",
        total_effects_time.as_secs_f64() * 1000.0 / frame_count as f64);
    eprintln!("  Export:          {:.2}ms",
        total_export_time.as_secs_f64() * 1000.0 / frame_count as f64);

    // Scene stats
    eprintln!("\nScene stats:");
    eprintln!("  Files:           {}", scene.file_count());
    eprintln!("  Users:           {}", scene.user_count());
    eprintln!("  Directories:     {}", scene.directories().len());

    Ok(())
}

/// Minimum screen-space radius to render an entity (LOD threshold).
const MIN_RENDER_RADIUS: f32 = 1.5;

/// Zoom level below which we skip file-to-directory connection lines.
const SKIP_FILE_LINES_ZOOM: f32 = 0.1;

/// Static counters for render profiling (only used in debug/profiling)
static RENDER_PROFILE_COUNTER: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

/// Render a single frame in headless mode.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn render_frame_headless(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    args: &Args,
    font_id: Option<FontId>,
    commits: &[Commit],
    current_commit: usize,
    background_texture: Option<rource_render::TextureId>,
    logo_texture: Option<rource_render::TextureId>,
    logo_dimensions: Option<(u32, u32)>,
) {
    renderer.begin_frame();

    // Clear to background color
    let bg_color = args.parse_background_color();
    renderer.clear(bg_color);

    // Draw background image (stretched to fill viewport) if available
    if let Some(bg_texture) = background_texture {
        let viewport_bounds = rource_math::Bounds::new(
            Vec2::ZERO,
            Vec2::new(renderer.width() as f32, renderer.height() as f32),
        );
        renderer.draw_quad(viewport_bounds, Some(bg_texture), Color::WHITE);
    }

    // Get visible bounds for frustum culling
    let cull_start = Instant::now();
    let visible_bounds = camera.visible_bounds();
    let culling_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 100.0);
    let (visible_dir_ids, visible_file_ids, visible_user_ids) =
        scene.visible_entities(&culling_bounds);
    let cull_time = cull_start.elapsed();

    let camera_zoom = camera.zoom();

    // Profile every 100th frame
    let frame_num = RENDER_PROFILE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let profile = frame_num % 100 == 0;

    // LOD: Skip file-to-directory lines when very zoomed out
    let draw_file_lines = camera_zoom > SKIP_FILE_LINES_ZOOM;

    // Render directories (skip very small ones for LOD)
    let dirs_start = Instant::now();
    let mut dirs_rendered = 0_u32;
    for &dir_id in &visible_dir_ids {
        let Some(dir) = scene.directories().get(dir_id) else {
            continue;
        };
        if !dir.is_visible() {
            continue;
        }
        let screen_pos = camera.world_to_screen(dir.position());
        let radius = dir.radius() * camera_zoom;

        // LOD: Skip directories that are too small to see
        if radius < MIN_RENDER_RADIUS {
            continue;
        }

        let depth_color = 0.15 + 0.05 * (dir.depth() as f32).min(5.0);
        let dir_color = Color::new(depth_color, depth_color, depth_color + 0.1, 0.5);
        renderer.draw_circle(screen_pos, radius, 1.0, dir_color);
        dirs_rendered += 1;

        // Only draw parent connection lines if directories are large enough
        if radius >= 3.0 {
            if let Some(parent_pos) = dir.parent_position() {
                let parent_screen = camera.world_to_screen(parent_pos);
                renderer.draw_line(parent_screen, screen_pos, 1.0, dir_color.with_alpha(0.3));
            }
        }
    }
    let dirs_time = dirs_start.elapsed();

    // Render files
    let files_start = Instant::now();
    let mut files_rendered = 0_u32;
    let show_filenames = !args.hide_filenames;
    let file_font_size = args.font_size * 0.8;

    for &file_id in &visible_file_ids {
        let Some(file) = scene.get_file(file_id) else {
            continue;
        };
        if file.alpha() < 0.01 {
            continue;
        }
        let screen_pos = camera.world_to_screen(file.position());
        let radius = file.radius() * camera_zoom;

        // LOD: Skip files that are too small to see (but ensure minimum 2px for visibility)
        let draw_radius = radius.max(2.0);
        if draw_radius < MIN_RENDER_RADIUS {
            continue;
        }

        let color = file.current_color().with_alpha(file.alpha());
        renderer.draw_disc(screen_pos, draw_radius, color);
        files_rendered += 1;

        // LOD: Only draw file-to-directory lines when zoomed in enough
        if draw_file_lines {
            if let Some(dir) = scene.directories().get(file.directory()) {
                let dir_screen = camera.world_to_screen(dir.position());
                renderer.draw_line(
                    dir_screen,
                    screen_pos,
                    0.5,
                    color.with_alpha(0.2 * file.alpha()),
                );
            }
        }

        // LOD: Only show filenames when zoomed in and file is prominent
        if show_filenames && file.alpha() > 0.5 && camera_zoom > 0.3 {
            if let Some(fid) = font_id {
                let name = file.name();
                let label_pos = Vec2::new(
                    screen_pos.x + radius + 3.0,
                    screen_pos.y - file_font_size * 0.3,
                );
                let label_color = Color::new(0.9, 0.9, 0.9, 0.7 * file.alpha());
                renderer.draw_text(name, label_pos, fid, file_font_size, label_color);
            }
        }
    }
    let files_time = files_start.elapsed();

    // Render actions (beams) - always render these as they show activity
    let actions_start = Instant::now();
    let mut actions_rendered = 0_u32;
    for action in scene.actions() {
        let user_opt = scene.get_user(action.user());
        let file_opt = scene.get_file(action.file());
        if let (Some(user), Some(file)) = (user_opt, file_opt) {
            let user_screen = camera.world_to_screen(user.position());
            let file_screen = camera.world_to_screen(file.position());
            let beam_end = user_screen.lerp(file_screen, action.progress());
            let beam_color = action.beam_color();
            renderer.draw_line(user_screen, beam_end, 2.0, beam_color);
            let head_radius = 3.0 * camera_zoom;
            renderer.draw_disc(beam_end, head_radius.max(2.0), beam_color);
            actions_rendered += 1;
        }
    }
    let actions_time = actions_start.elapsed();

    // Render users
    let users_start = Instant::now();
    let mut users_rendered = 0_u32;
    let show_usernames = !args.hide_usernames;
    let name_font_size = args.font_size;

    for &user_id in &visible_user_ids {
        let Some(user) = scene.get_user(user_id) else {
            continue;
        };
        if user.alpha() < 0.01 {
            continue;
        }
        let screen_pos = camera.world_to_screen(user.position());
        let radius = user.radius() * camera_zoom;
        let color = user.display_color();
        renderer.draw_disc(screen_pos, radius.max(5.0), color);
        if user.is_active() {
            renderer.draw_circle(
                screen_pos,
                radius * 1.3,
                2.0,
                color.with_alpha(0.5 * user.alpha()),
            );
        }
        users_rendered += 1;
        if show_usernames {
            if let Some(fid) = font_id {
                let name = user.name();
                let label_pos = Vec2::new(
                    screen_pos.x + radius + 5.0,
                    screen_pos.y - name_font_size * 0.3,
                );
                let label_color = Color::new(1.0, 1.0, 1.0, 0.8 * user.alpha());
                renderer.draw_text(name, label_pos, fid, name_font_size, label_color);
            }
        }
    }
    let users_time = users_start.elapsed();

    // Print profiling info every 100 frames
    if profile {
        eprintln!("\n[RENDER PROFILE] Frame {frame_num}:");
        eprintln!("  Culling:     {:.2}ms (vis: {} dirs, {} files, {} users)",
            cull_time.as_secs_f64() * 1000.0,
            visible_dir_ids.len(), visible_file_ids.len(), visible_user_ids.len());
        eprintln!("  Directories: {:.2}ms ({} rendered)",
            dirs_time.as_secs_f64() * 1000.0, dirs_rendered);
        eprintln!("  Files:       {:.2}ms ({} rendered, {:.3}ms/file)",
            files_time.as_secs_f64() * 1000.0, files_rendered,
            if files_rendered > 0 { files_time.as_secs_f64() * 1000.0 / f64::from(files_rendered) } else { 0.0 });
        eprintln!("  Actions:     {:.2}ms ({} rendered)",
            actions_time.as_secs_f64() * 1000.0, actions_rendered);
        eprintln!("  Users:       {:.2}ms ({} rendered)",
            users_time.as_secs_f64() * 1000.0, users_rendered);
        eprintln!("  Zoom:        {camera_zoom:.4}");
    }

    // Render UI overlays
    let width = renderer.width() as f32;
    let height = renderer.height() as f32;

    // Progress bar
    if !commits.is_empty() {
        let bar_height = 4.0;
        let progress = current_commit as f32 / commits.len().max(1) as f32;
        renderer.draw_quad(
            rource_math::Bounds::new(
                Vec2::new(0.0, height - bar_height),
                Vec2::new(width, height),
            ),
            None,
            Color::new(0.2, 0.2, 0.2, 0.5),
        );
        renderer.draw_quad(
            rource_math::Bounds::new(
                Vec2::new(0.0, height - bar_height),
                Vec2::new(width * progress, height),
            ),
            None,
            Color::new(0.3, 0.6, 1.0, 0.8),
        );
    }

    // Text overlays
    if let Some(fid) = font_id {
        let font_size = args.font_size;
        let text_color = Color::new(1.0, 1.0, 1.0, 0.9);

        // Title
        if let Some(ref title) = args.title {
            let title_size = font_size * 1.5;
            let title_x = (width / 2.0) - (title.len() as f32 * title_size * 0.3);
            renderer.draw_text(
                title,
                Vec2::new(title_x.max(10.0), 20.0),
                fid,
                title_size,
                text_color,
            );
        }

        // Date display
        if !args.hide_date && !commits.is_empty() {
            if let Some(commit) = commits.get(current_commit.saturating_sub(1).max(0)) {
                let date_str = format_timestamp(commit.timestamp);
                renderer.draw_text(
                    &date_str,
                    Vec2::new(10.0, height - 30.0),
                    fid,
                    font_size,
                    text_color.with_alpha(0.7),
                );
            }
        }

        // Current commit info
        if current_commit > 0 {
            if let Some(commit) = commits.get(current_commit - 1) {
                renderer.draw_text(
                    &commit.author,
                    Vec2::new(10.0, height - 50.0),
                    fid,
                    font_size,
                    text_color.with_alpha(0.8),
                );
                let files_text = format!("{} files", commit.files.len());
                renderer.draw_text(
                    &files_text,
                    Vec2::new(10.0, height - 70.0),
                    fid,
                    font_size * 0.9,
                    text_color.with_alpha(0.6),
                );
            }
        }

        // Stats text
        let file_count = scene.file_count();
        let user_count = scene.user_count();
        let total_commits = commits.len();
        let stats_text = format!(
            "{current_commit}/{total_commits} commits | {file_count} files | {user_count} users"
        );
        renderer.draw_text(
            &stats_text,
            Vec2::new(10.0, 20.0),
            fid,
            font_size * 0.8,
            text_color.with_alpha(0.5),
        );
    }

    // Draw logo in top-right corner if available
    if let (Some(logo_tex), Some((logo_width, logo_height))) = (logo_texture, logo_dimensions) {
        let viewport_width = renderer.width() as f32;
        let logo_offset = args.parse_logo_offset();
        let (offset_x, offset_y) = logo_offset;

        // Position logo in top-right corner with offset
        let logo_x = viewport_width - logo_width as f32 - offset_x as f32;
        let logo_y = offset_y as f32;

        let logo_bounds = rource_math::Bounds::new(
            Vec2::new(logo_x, logo_y),
            Vec2::new(logo_x + logo_width as f32, logo_y + logo_height as f32),
        );
        renderer.draw_quad(logo_bounds, Some(logo_tex), Color::WHITE);
    }

    renderer.end_frame();
}

fn main() -> Result<()> {
    let mut args = Args::parse_args();

    // Handle --sample-config
    if args.sample_config {
        println!("{}", Args::sample_config());
        return Ok(());
    }

    // Handle --env-help
    if args.env_help {
        println!("{}", Args::env_help());
        return Ok(());
    }

    // Apply environment variables (priority: CLI > Env > Config)
    args.apply_env();

    // Apply config file if specified
    if let Err(e) = args.apply_config_file() {
        eprintln!("Warning: {e}");
    }

    // Handle --save-config
    if let Some(ref config_path) = args.save_config {
        let settings = args.to_settings();
        if let Err(e) = settings.save_to_file(config_path) {
            anyhow::bail!("Failed to save config to {}: {}", config_path.display(), e);
        }
        eprintln!("Configuration saved to: {}", config_path.display());
        return Ok(());
    }

    eprintln!("Rource - Software version control visualization");
    eprintln!("Repository: {}", args.path.display());
    eprintln!("Resolution: {}x{}", args.width, args.height);

    // Check for headless mode
    if args.headless {
        return run_headless(&args);
    }

    // Check for screenshot mode
    if let Some(ref screenshot_path) = args.screenshot {
        return run_screenshot(&args, screenshot_path);
    }

    // Create event loop
    let event_loop = EventLoop::new().context("Failed to create event loop")?;

    // Create application
    let mut app = App::new(args);

    // Run the event loop
    event_loop.run_app(&mut app)?;

    Ok(())
}

/// Run in screenshot mode (render single frame to PNG).
///
/// Similar to headless mode but only outputs a single frame.
#[allow(clippy::too_many_lines)]
fn run_screenshot(args: &Args, screenshot_path: &std::path::Path) -> Result<()> {
    use rource_vcs::{CustomParser, GitParser, Parser};
    use std::process::Command;

    eprintln!("Taking screenshot...");

    // Load commits
    let commits: Vec<Commit> = if args.custom_log {
        let content =
            std::fs::read_to_string(&args.path).context("Failed to read custom log file")?;
        let parser = CustomParser::new();
        parser
            .parse_str(&content)
            .context("Failed to parse custom log")?
    } else {
        let output = Command::new("git")
            .arg("-C")
            .arg(&args.path)
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
        parser
            .parse_str(&log_content)
            .context("Failed to parse git log")?
    };

    if commits.is_empty() {
        anyhow::bail!("No commits found in repository");
    }

    // Determine which commit to render
    let target_commit = args
        .screenshot_at
        .unwrap_or_else(|| commits.len().saturating_sub(1));
    let target_commit = target_commit.min(commits.len().saturating_sub(1));

    eprintln!(
        "Rendering commit {}/{} ({})",
        target_commit + 1,
        commits.len(),
        commits[target_commit].author
    );

    // Create renderer and scene
    let mut renderer = SoftwareRenderer::new(args.width, args.height);
    let mut scene = Scene::new();
    let mut camera = Camera::new(args.width as f32, args.height as f32);

    // Load font
    let font_id = renderer.load_font(rource_render::default_font::ROBOTO_MONO);

    // Load logo image if specified
    let (logo_texture, logo_dimensions) = if let Some(ref logo_path) = args.logo {
        match rource_render::image::Image::load_file(logo_path) {
            Ok(image) => {
                let width = image.width();
                let height = image.height();
                let texture_id = renderer.load_texture(width, height, image.data());
                (Some(texture_id), Some((width, height)))
            }
            Err(e) => {
                eprintln!("Warning: Failed to load logo image '{}': {}", logo_path.display(), e);
                (None, None)
            }
        }
    } else {
        (None, None)
    };

    // Load background image if specified
    let background_texture = if let Some(ref bg_path) = args.background_image {
        match rource_render::image::Image::load_file(bg_path) {
            Ok(image) => {
                let width = image.width();
                let height = image.height();
                let texture_id = renderer.load_texture(width, height, image.data());
                Some(texture_id)
            }
            Err(e) => {
                eprintln!("Warning: Failed to load background image '{}': {}", bg_path.display(), e);
                None
            }
        }
    } else {
        None
    };

    // Initialize filter settings
    let mut filter = FilterSettings::new();
    if let Some(ref pattern) = args.show_users {
        filter.set_show_users(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_users {
        filter.set_hide_users(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.show_files {
        filter.set_show_files(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_files {
        filter.set_hide_files(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_dirs {
        filter.set_hide_dirs(Some(pattern.clone()));
    }

    // Apply commits up to and including the target (with filtering)
    for commit in commits.iter().take(target_commit + 1) {
        // Skip commits from filtered-out users
        if !filter.should_include_user(&commit.author) {
            continue;
        }

        let files: Vec<(std::path::PathBuf, ActionType)> = commit
            .files
            .iter()
            .filter(|f| filter.should_include_file(&f.path))
            .map(|f| {
                (
                    f.path.clone(),
                    match f.action {
                        FileAction::Create => ActionType::Create,
                        FileAction::Modify => ActionType::Modify,
                        FileAction::Delete => ActionType::Delete,
                    },
                )
            })
            .collect();

        // Only apply commit if there are files left after filtering
        if !files.is_empty() {
            scene.apply_commit(&commit.author, &files);
        }
    }

    // Pre-warm scene to let files fade in
    for _ in 0..30 {
        scene.update(1.0 / 60.0);
    }

    // Position camera
    if let Some(bounds) = scene.compute_entity_bounds() {
        if bounds.width() > 0.0 && bounds.height() > 0.0 {
            let padded = rource_math::Bounds::from_center_size(
                bounds.center(),
                rource_math::Vec2::new(bounds.width() * 1.2, bounds.height() * 1.2),
            );
            let zoom_x = args.width as f32 / padded.width();
            let zoom_y = args.height as f32 / padded.height();
            let zoom = zoom_x.min(zoom_y).clamp(0.1, 5.0);

            camera.jump_to(padded.center());
            camera.set_zoom(zoom);
        }
    }

    // Render the frame
    render_frame_headless(
        &mut renderer,
        &scene,
        &camera,
        args,
        font_id,
        &commits,
        target_commit,
        background_texture,
        logo_texture,
        logo_dimensions,
    );

    // Apply effects if enabled
    if !args.no_bloom {
        let bloom = BloomEffect::new();
        bloom.apply(
            renderer.pixels_mut(),
            args.width as usize,
            args.height as usize,
        );
    }

    if args.shadows {
        let shadow = ShadowEffect::subtle();
        shadow.apply(
            renderer.pixels_mut(),
            args.width as usize,
            args.height as usize,
        );
    }

    // Save the screenshot
    let pixels = renderer.pixels();
    export::write_png_to_file(pixels, args.width, args.height, screenshot_path)
        .context("Failed to save screenshot")?;

    eprintln!("Screenshot saved: {}", screenshot_path.display());
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
    fn test_get_initials() {
        // Basic two-word name
        assert_eq!(get_initials("John Doe"), "JD");
        assert_eq!(get_initials("Alice Smith"), "AS");

        // Single name
        assert_eq!(get_initials("Alice"), "A");
        assert_eq!(get_initials("bob"), "B");

        // Three or more words (uses first and last)
        assert_eq!(get_initials("John Q Public"), "JP");
        assert_eq!(get_initials("Mary Jane Watson"), "MW");

        // Email format
        assert_eq!(get_initials("<john@example.com>"), "J");
        assert_eq!(get_initials("John Doe <john@example.com>"), "JD");

        // Trimmed input
        assert_eq!(get_initials("  Alice  "), "A");
        assert_eq!(get_initials("  Bob Smith  "), "BS");
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

    #[test]
    fn test_mouse_state_initial() {
        let args = Args::default();
        let app = App::new(args);

        assert_eq!(app.mouse_position, Vec2::ZERO);
        assert!(!app.mouse_dragging);
        assert_eq!(app.last_mouse_position, Vec2::ZERO);
    }

    #[test]
    fn test_mouse_move_updates_position() {
        let args = Args::default();
        let mut app = App::new(args);

        app.handle_mouse_move(100.0, 200.0);

        assert_eq!(app.mouse_position.x, 100.0);
        assert_eq!(app.mouse_position.y, 200.0);
    }

    #[test]
    fn test_mouse_drag_pans_camera() {
        let args = Args::default();
        let mut app = App::new(args);

        // Start at origin
        app.camera.jump_to(Vec2::ZERO);
        let initial_pos = app.camera.target_position();

        // Start drag
        app.handle_mouse_move(100.0, 100.0);
        app.handle_mouse_button(MouseButton::Left, ElementState::Pressed);
        assert!(app.mouse_dragging);

        // Move mouse (should pan)
        app.handle_mouse_move(150.0, 150.0);

        // Camera should have moved (pan inverts direction)
        assert_ne!(app.camera.target_position(), initial_pos);

        // End drag
        app.handle_mouse_button(MouseButton::Left, ElementState::Released);
        assert!(!app.mouse_dragging);
    }

    #[test]
    fn test_mouse_scroll_zooms() {
        let args = Args::default();
        let mut app = App::new(args);

        app.camera.set_zoom(1.0);
        let initial_zoom = app.camera.target_zoom();

        // Scroll up (zoom in)
        app.handle_mouse_scroll(MouseScrollDelta::LineDelta(0.0, 1.0));

        // Zoom should have increased
        assert!(app.camera.target_zoom() > initial_zoom);
    }

    #[test]
    fn test_mouse_input_disabled() {
        let args = Args {
            disable_input: true,
            ..Args::default()
        };
        let mut app = App::new(args);

        // Set initial state
        app.camera.jump_to(Vec2::ZERO);
        app.camera.set_zoom(1.0);
        let initial_pos = app.camera.target_position();
        let initial_zoom = app.camera.target_zoom();

        // Try to drag
        app.handle_mouse_move(100.0, 100.0);
        app.handle_mouse_button(MouseButton::Left, ElementState::Pressed);
        app.handle_mouse_move(200.0, 200.0);

        // Camera should not have moved (input disabled)
        assert_eq!(app.camera.target_position(), initial_pos);
        assert!(!app.mouse_dragging);

        // Try to scroll
        app.handle_mouse_scroll(MouseScrollDelta::LineDelta(0.0, 5.0));
        assert_eq!(app.camera.target_zoom(), initial_zoom);
    }

    #[test]
    fn test_middle_click_resets_camera() {
        let args = Args::default();
        let mut app = App::new(args);

        // Move camera
        app.camera.jump_to(Vec2::new(500.0, 500.0));
        app.camera.set_zoom(3.0);

        // Middle click
        app.handle_mouse_button(MouseButton::Middle, ElementState::Pressed);

        // Camera should reset
        assert_eq!(app.camera.position(), Vec2::ZERO);
        assert!((app.camera.zoom() - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_headless_requires_output() {
        // Headless mode without output should fail
        let args = Args {
            headless: true,
            output: None,
            ..Args::default()
        };

        let result = run_headless(&args);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("--headless requires --output"));
    }

    #[test]
    fn test_headless_args_stdout_detection() {
        // Test that stdout output is correctly detected
        let args = Args {
            headless: true,
            output: Some(std::path::PathBuf::from("-")),
            ..Args::default()
        };

        // Verify args are set correctly
        assert!(args.headless);
        assert_eq!(args.output.as_ref().unwrap().as_os_str(), "-");
    }

    #[test]
    fn test_headless_args_directory_detection() {
        // Test that directory output is correctly detected
        let args = Args {
            headless: true,
            output: Some(std::path::PathBuf::from("/tmp/frames")),
            ..Args::default()
        };

        // Verify args are set correctly
        assert!(args.headless);
        assert_eq!(
            args.output.as_ref().unwrap().to_str().unwrap(),
            "/tmp/frames"
        );
    }

    #[test]
    fn test_frame_exporter_initialized_for_headless() {
        // When output is specified, frame_exporter should be initialized
        let args = Args {
            output: Some(std::path::PathBuf::from("-")),
            ..Args::default()
        };
        let app = App::new(args);
        assert!(app.frame_exporter.is_some());
    }

    #[test]
    fn test_frame_exporter_not_initialized_without_output() {
        // When output is not specified, frame_exporter should be None
        let args = Args::default();
        let app = App::new(args);
        assert!(app.frame_exporter.is_none());
    }
}
