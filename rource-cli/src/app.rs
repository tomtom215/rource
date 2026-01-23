// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Application state and playback management for Rource CLI.
//!
//! This module contains the main application state struct and playback
//! configuration for the visualization.

use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;

use rource_core::camera::{Camera, Camera3D};
use rource_core::config::{FilterSettings, WatermarkSettings};
use rource_core::scene::Scene;
use rource_core::{DirId, FileId, UserId};
use rource_math::Vec2;
use rource_render::effects::{BloomEffect, ShadowEffect};
use rource_render::Renderer;
use rource_render::{FontId, SoftwareRenderer, TextureId};
use rource_vcs::Commit;
use winit::window::Window;

use crate::args::Args;
use crate::avatar;
use crate::export;
use crate::input::MouseState;

// ============================================================================
// Helper Functions (testable without App instance)
// ============================================================================

#[allow(dead_code)]
mod helpers {
    /// Parses a comma-separated list of usernames into a vector.
    ///
    /// Trims whitespace from each entry and filters out empty strings.
    ///
    /// # Arguments
    /// * `input` - Comma-separated list of usernames
    ///
    /// # Returns
    /// Vector of trimmed, non-empty usernames.
    ///
    /// # Example
    /// ```ignore
    /// let users = parse_highlight_users("alice, bob, charlie");
    /// assert_eq!(users, vec!["alice", "bob", "charlie"]);
    /// ```
    #[must_use]
    pub fn parse_highlight_users(input: &str) -> Vec<String> {
        input
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(String::from)
            .collect()
    }

    /// Determines whether 3D camera mode should be enabled.
    ///
    /// 3D mode is enabled when the `--3d` flag is set AND the `--2d` flag
    /// is not set (2D takes precedence).
    ///
    /// # Arguments
    /// * `camera_3d_flag` - Whether `--3d` flag was passed
    /// * `camera_2d_flag` - Whether `--2d` flag was passed
    ///
    /// # Returns
    /// `true` if 3D camera should be used.
    #[inline]
    #[must_use]
    pub fn should_enable_3d_camera(camera_3d_flag: bool, camera_2d_flag: bool) -> bool {
        camera_3d_flag && !camera_2d_flag
    }

    /// Checks if the visualization has completed processing all commits.
    ///
    /// The visualization is complete when:
    /// 1. There are commits loaded
    /// 2. The current commit index is at or past the last commit
    /// 3. The last applied commit matches or exceeds the current commit
    ///
    /// # Arguments
    /// * `commits_len` - Total number of commits
    /// * `current_commit` - Current commit index
    /// * `last_applied_commit` - Index of last applied commit
    ///
    /// # Returns
    /// `true` if visualization is complete.
    #[inline]
    #[must_use]
    pub fn is_visualization_complete(
        commits_len: usize,
        current_commit: usize,
        last_applied_commit: usize,
    ) -> bool {
        commits_len > 0
            && current_commit >= commits_len.saturating_sub(1)
            && last_applied_commit >= current_commit
    }

    /// Validates that bloom effect should be enabled.
    ///
    /// # Arguments
    /// * `no_bloom_flag` - Whether `--no-bloom` flag was passed
    ///
    /// # Returns
    /// `true` if bloom should be enabled (i.e., not disabled).
    #[inline]
    #[must_use]
    pub fn should_enable_bloom(no_bloom_flag: bool) -> bool {
        !no_bloom_flag
    }

    /// Validates that shadow effect should be enabled.
    ///
    /// # Arguments
    /// * `shadows_flag` - Whether `--shadows` flag was passed
    ///
    /// # Returns
    /// `true` if shadows should be enabled.
    #[inline]
    #[must_use]
    pub fn should_enable_shadows(shadows_flag: bool) -> bool {
        shadows_flag
    }

    /// Determines if output should be piped to stdout.
    ///
    /// # Arguments
    /// * `output_path` - The output path string
    ///
    /// # Returns
    /// `true` if output path is "-" (stdout).
    #[inline]
    #[must_use]
    pub fn is_stdout_output(output_path: &str) -> bool {
        output_path == "-"
    }

    /// Calculates the initial visibility buffer capacity based on expected size.
    ///
    /// Provides reasonable defaults that handle typical repository sizes
    /// without excessive initial allocation.
    ///
    /// # Arguments
    /// * `buffer_type` - Type of buffer ("dirs", "files", or "users")
    ///
    /// # Returns
    /// Initial capacity for the buffer.
    #[inline]
    #[must_use]
    pub fn initial_buffer_capacity(buffer_type: &str) -> usize {
        match buffer_type {
            "dirs" => 1000,
            "files" => 5000,
            // Default capacity for users and any unknown type
            _ => 100,
        }
    }

    /// Validates a playback speed value.
    ///
    /// # Arguments
    /// * `seconds_per_day` - Seconds of real time per day of commit history
    ///
    /// # Returns
    /// `true` if the speed is valid (positive and finite).
    #[inline]
    #[must_use]
    pub fn is_valid_playback_speed(seconds_per_day: f32) -> bool {
        seconds_per_day.is_finite() && seconds_per_day > 0.0
    }

    /// Validates a time scale value.
    ///
    /// # Arguments
    /// * `time_scale` - The time scale multiplier
    ///
    /// # Returns
    /// `true` if the time scale is valid (positive and finite).
    #[inline]
    #[must_use]
    pub fn is_valid_time_scale(time_scale: f32) -> bool {
        time_scale.is_finite() && time_scale > 0.0
    }
}

/// Playback state for the visualization.
#[derive(Debug, Clone)]
pub struct PlaybackState {
    /// Whether playback is paused.
    pub paused: bool,

    /// Playback speed multiplier.
    pub speed: f32,

    /// Seconds per day of commit history.
    pub seconds_per_day: f32,

    /// Time scale multiplier.
    pub time_scale: f32,

    /// Stop playback after this many seconds of real time.
    pub stop_at_time: Option<f32>,

    /// Elapsed real time in seconds.
    pub elapsed_time: f32,

    /// Use real-time playback (1 second = 1 second of history).
    pub realtime: bool,
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

impl PlaybackState {
    /// Create a new playback state from command-line arguments.
    #[must_use]
    pub fn from_args(args: &Args) -> Self {
        Self {
            paused: args.paused,
            seconds_per_day: args.seconds_per_day,
            time_scale: args.time_scale,
            stop_at_time: args.stop_at_time,
            elapsed_time: 0.0,
            realtime: args.realtime,
            ..Default::default()
        }
    }
}

/// Main application state.
pub struct App {
    /// Command-line arguments.
    pub args: Args,

    /// The window (created on resume).
    pub window: Option<Rc<Window>>,

    /// Softbuffer surface for displaying pixels.
    pub surface: Option<softbuffer::Surface<Rc<Window>, Rc<Window>>>,

    /// The software renderer.
    pub renderer: Option<SoftwareRenderer>,

    /// Default font for text rendering.
    pub default_font: Option<FontId>,

    /// The scene graph containing all entities.
    pub scene: Scene,

    /// Camera for view transforms (2D mode).
    pub camera: Camera,

    /// 3D orbit camera (optional, when 3D mode enabled).
    pub camera_3d: Option<Camera3D>,

    /// Bloom effect (optional).
    pub bloom: Option<BloomEffect>,

    /// Shadow effect (optional).
    pub shadow: Option<ShadowEffect>,

    /// Current playback state.
    pub playback: PlaybackState,

    /// Loaded commits.
    pub commits: Vec<Commit>,

    /// Current commit index.
    pub current_commit: usize,

    /// Index of last applied commit (for incremental apply).
    pub last_applied_commit: usize,

    /// Last frame time.
    pub last_frame: Instant,

    /// Accumulated time for playback.
    pub accumulated_time: f64,

    /// Whether to exit the application.
    pub should_exit: bool,

    /// Mouse input state.
    pub mouse: MouseState,

    /// Frame exporter for video output.
    pub frame_exporter: Option<export::FrameExporter>,

    /// Pending screenshot path (saved after next render).
    pub screenshot_pending: Option<PathBuf>,

    /// User avatar manager (used before registration, None after).
    pub avatar_manager: Option<avatar::AvatarManager>,

    /// Registered avatar texture IDs (available after renderer creation).
    pub avatar_registry: avatar::AvatarRegistry,

    /// Filter settings for users and files.
    pub filter: FilterSettings,

    /// Username to follow when in follow mode.
    pub follow_user: Option<String>,

    /// Usernames to highlight (parsed from comma-separated list).
    pub highlight_users: Vec<String>,

    /// Whether to highlight all users.
    pub highlight_all_users: bool,

    /// Index of current user for Tab cycling navigation.
    pub current_user_index: usize,

    /// Directory name display depth.
    pub dir_name_depth: u32,

    /// Logo image path.
    pub logo_path: Option<PathBuf>,

    /// Logo offset from top-right corner.
    pub logo_offset: (i32, i32),

    /// Background image path.
    pub background_image_path: Option<PathBuf>,

    /// Logo texture ID (loaded from `logo_path`).
    pub logo_texture: Option<TextureId>,

    /// Logo image dimensions (width, height).
    pub logo_dimensions: Option<(u32, u32)>,

    /// Background image texture ID (loaded from `background_image_path`).
    pub background_texture: Option<TextureId>,

    /// Watermark configuration.
    pub watermark: WatermarkSettings,

    // ==========================================================================
    // Zero-Allocation Visibility Buffers (Phase 8 Optimization)
    // ==========================================================================
    // These buffers are reused each frame to avoid allocations in visible_entities_into().
    // At 60 FPS, this eliminates ~180 allocations/second.
    /// Reusable buffer for visible directory IDs.
    pub visible_dirs_buffer: Vec<DirId>,

    /// Reusable buffer for visible file IDs.
    pub visible_files_buffer: Vec<FileId>,

    /// Reusable buffer for visible user IDs.
    pub visible_users_buffer: Vec<UserId>,

    /// Reusable buffer for file label candidates (avoids per-frame allocation).
    /// Stores: (`FileId`, `screen_pos`, radius, alpha, priority)
    pub file_label_candidates_buffer: Vec<(FileId, Vec2, f32, f32, f32)>,
}

impl App {
    /// Create a new application with the given arguments.
    #[must_use]
    pub fn new(args: Args) -> Self {
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
            Some(ShadowEffect::subtle())
        } else {
            None
        };

        // Initialize frame exporter if output is specified
        let frame_exporter = args.output.as_ref().map(|output| {
            if output.as_os_str() == "-" {
                export::FrameExporter::to_stdout(args.framerate)
            } else {
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
        let filter = Self::build_filter(&args);

        // Parse highlight users (comma-separated list)
        let highlight_users = args
            .highlight_users
            .as_ref()
            .map(|s| s.split(',').map(|u| u.trim().to_string()).collect())
            .unwrap_or_default();

        // Extract values from args
        let follow_user = args.follow_user.clone();
        let highlight_all_users = args.highlight_all_users;
        let dir_name_depth = args.dir_name_depth;
        let logo_path = args.logo.clone();
        let logo_offset = args.parse_logo_offset();
        let background_image_path = args.background_image.clone();

        // 3D camera settings (--3d enables, --2d explicitly disables)
        let enable_3d = args.camera_3d && !args.camera_2d;
        let camera_3d = if enable_3d {
            let mut cam = Camera3D::new(args.width as f32, args.height as f32);
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

        let playback = PlaybackState::from_args(&args);

        // Build watermark settings before moving args
        let watermark = args.build_watermark_settings();

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
            playback,
            commits: Vec::new(),
            current_commit: 0,
            last_applied_commit: 0,
            last_frame: Instant::now(),
            accumulated_time: 0.0,
            should_exit: false,
            mouse: MouseState::new(),
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
            logo_path,
            logo_offset,
            background_image_path,
            logo_texture: None,
            logo_dimensions: None,
            background_texture: None,
            watermark,
            // Pre-allocate visibility buffers to avoid per-frame allocations
            // Capacity of 1000 handles typical repository sizes; grows if needed
            visible_dirs_buffer: Vec::with_capacity(1000),
            visible_files_buffer: Vec::with_capacity(5000),
            visible_users_buffer: Vec::with_capacity(100),
            // Pre-allocate label candidates buffer for file label collision detection
            file_label_candidates_buffer: Vec::with_capacity(256),
        }
    }

    /// Build filter settings from command-line arguments.
    fn build_filter(args: &Args) -> FilterSettings {
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
        filter
    }

    /// Get the viewport size from the renderer.
    #[must_use]
    pub fn viewport_size(&self) -> Option<(f32, f32)> {
        self.renderer
            .as_ref()
            .map(|r| (r.width() as f32, r.height() as f32))
    }

    /// Check if the visualization has completed (all commits processed).
    #[must_use]
    pub fn is_complete(&self) -> bool {
        !self.commits.is_empty()
            && self.current_commit >= self.commits.len().saturating_sub(1)
            && self.last_applied_commit >= self.current_commit
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use helpers::*;
    use rource_math::Vec2;

    // ========================================================================
    // Parse Highlight Users Tests
    // ========================================================================

    #[test]
    fn test_parse_highlight_users_basic() {
        let users = parse_highlight_users("alice,bob,charlie");
        assert_eq!(users, vec!["alice", "bob", "charlie"]);
    }

    #[test]
    fn test_parse_highlight_users_with_spaces() {
        let users = parse_highlight_users("alice, bob , charlie");
        assert_eq!(users, vec!["alice", "bob", "charlie"]);
    }

    #[test]
    fn test_parse_highlight_users_empty() {
        let users = parse_highlight_users("");
        assert!(users.is_empty());
    }

    #[test]
    fn test_parse_highlight_users_single() {
        let users = parse_highlight_users("alice");
        assert_eq!(users, vec!["alice"]);
    }

    #[test]
    fn test_parse_highlight_users_empty_entries() {
        let users = parse_highlight_users("alice,,bob,");
        assert_eq!(users, vec!["alice", "bob"]);
    }

    #[test]
    fn test_parse_highlight_users_only_spaces() {
        let users = parse_highlight_users("  ,  ,  ");
        assert!(users.is_empty());
    }

    // ========================================================================
    // 3D Camera Mode Tests
    // ========================================================================

    #[test]
    fn test_should_enable_3d_camera_both_false() {
        assert!(!should_enable_3d_camera(false, false));
    }

    #[test]
    fn test_should_enable_3d_camera_3d_only() {
        assert!(should_enable_3d_camera(true, false));
    }

    #[test]
    fn test_should_enable_3d_camera_2d_only() {
        assert!(!should_enable_3d_camera(false, true));
    }

    #[test]
    fn test_should_enable_3d_camera_both_true() {
        // 2D takes precedence
        assert!(!should_enable_3d_camera(true, true));
    }

    // ========================================================================
    // Visualization Complete Tests
    // ========================================================================

    #[test]
    fn test_is_visualization_complete_empty() {
        assert!(!is_visualization_complete(0, 0, 0));
    }

    #[test]
    fn test_is_visualization_complete_single_commit() {
        assert!(is_visualization_complete(1, 0, 0));
    }

    #[test]
    fn test_is_visualization_complete_in_progress() {
        assert!(!is_visualization_complete(10, 5, 5));
    }

    #[test]
    fn test_is_visualization_complete_at_end() {
        assert!(is_visualization_complete(10, 9, 9));
    }

    #[test]
    fn test_is_visualization_complete_last_not_applied() {
        assert!(!is_visualization_complete(10, 9, 8));
    }

    // ========================================================================
    // Effect Enable Tests
    // ========================================================================

    #[test]
    fn test_should_enable_bloom_default() {
        assert!(should_enable_bloom(false));
    }

    #[test]
    fn test_should_enable_bloom_disabled() {
        assert!(!should_enable_bloom(true));
    }

    #[test]
    fn test_should_enable_shadows_default() {
        assert!(!should_enable_shadows(false));
    }

    #[test]
    fn test_should_enable_shadows_enabled() {
        assert!(should_enable_shadows(true));
    }

    // ========================================================================
    // Stdout Output Tests
    // ========================================================================

    #[test]
    fn test_is_stdout_output_dash() {
        assert!(is_stdout_output("-"));
    }

    #[test]
    fn test_is_stdout_output_path() {
        assert!(!is_stdout_output("/tmp/output"));
    }

    #[test]
    fn test_is_stdout_output_relative() {
        assert!(!is_stdout_output("output"));
    }

    // ========================================================================
    // Buffer Capacity Tests
    // ========================================================================

    #[test]
    fn test_initial_buffer_capacity_dirs() {
        assert_eq!(initial_buffer_capacity("dirs"), 1000);
    }

    #[test]
    fn test_initial_buffer_capacity_files() {
        assert_eq!(initial_buffer_capacity("files"), 5000);
    }

    #[test]
    fn test_initial_buffer_capacity_default() {
        // Users and unknown types use default capacity
        assert_eq!(initial_buffer_capacity("users"), 100);
        assert_eq!(initial_buffer_capacity("unknown"), 100);
        assert_eq!(initial_buffer_capacity(""), 100);
    }

    // ========================================================================
    // Playback Speed Validation Tests
    // ========================================================================

    #[test]
    fn test_is_valid_playback_speed_positive() {
        assert!(is_valid_playback_speed(10.0));
    }

    #[test]
    fn test_is_valid_playback_speed_zero() {
        assert!(!is_valid_playback_speed(0.0));
    }

    #[test]
    fn test_is_valid_playback_speed_negative() {
        assert!(!is_valid_playback_speed(-5.0));
    }

    #[test]
    fn test_is_valid_playback_speed_infinity() {
        assert!(!is_valid_playback_speed(f32::INFINITY));
    }

    #[test]
    fn test_is_valid_playback_speed_nan() {
        assert!(!is_valid_playback_speed(f32::NAN));
    }

    // ========================================================================
    // Time Scale Validation Tests
    // ========================================================================

    #[test]
    fn test_is_valid_time_scale_positive() {
        assert!(is_valid_time_scale(1.0));
    }

    #[test]
    fn test_is_valid_time_scale_zero() {
        assert!(!is_valid_time_scale(0.0));
    }

    #[test]
    fn test_is_valid_time_scale_negative() {
        assert!(!is_valid_time_scale(-1.0));
    }

    #[test]
    fn test_is_valid_time_scale_large() {
        assert!(is_valid_time_scale(100.0));
    }

    // ========================================================================
    // PlaybackState and App Tests (existing)
    // ========================================================================

    #[test]
    fn test_playback_state_default() {
        let state = PlaybackState::default();
        assert!(!state.paused);
        assert!((state.speed - 1.0).abs() < 0.001);
        assert!((state.seconds_per_day - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_app_new() {
        let args = Args::default();
        let app = App::new(args);
        assert_eq!(app.mouse.position, Vec2::ZERO);
        assert!(!app.mouse.dragging);
        assert!(app.commits.is_empty());
        assert_eq!(app.current_commit, 0);
    }

    #[test]
    fn test_app_frame_exporter_with_output() {
        let args = Args {
            output: Some(PathBuf::from("-")),
            ..Args::default()
        };
        let app = App::new(args);
        assert!(app.frame_exporter.is_some());
    }

    #[test]
    fn test_app_frame_exporter_without_output() {
        let args = Args::default();
        let app = App::new(args);
        assert!(app.frame_exporter.is_none());
    }

    #[test]
    fn test_is_complete_empty() {
        let args = Args::default();
        let app = App::new(args);
        assert!(!app.is_complete()); // Empty commits means not complete
    }
}
