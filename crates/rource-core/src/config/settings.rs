//! Settings for the Rource visualization.
//!
//! This module provides a unified configuration structure that can be used
//! by both native CLI and WebAssembly applications.

use regex_lite::Regex;
use rource_math::Color;
use std::path::Path;

/// Camera mode for the visualization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CameraModeSetting {
    /// Overview mode - camera fits all content.
    #[default]
    Overview,
    /// Track mode - camera follows active users.
    Track,
    /// Follow mode - camera follows a specific user.
    Follow,
}

impl CameraModeSetting {
    /// Parse from a string representation.
    #[must_use]
    pub fn parse(s: &str) -> Self {
        match s.to_lowercase().as_str() {
            "track" => Self::Track,
            "follow" => Self::Follow,
            _ => Self::Overview,
        }
    }

    /// Convert to string.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Overview => "overview",
            Self::Track => "track",
            Self::Follow => "follow",
        }
    }
}

/// Display settings for visual elements.
#[derive(Debug, Clone)]
pub struct DisplaySettings {
    /// Window/viewport width in pixels.
    pub width: u32,
    /// Window/viewport height in pixels.
    pub height: u32,
    /// Run in fullscreen mode.
    pub fullscreen: bool,
    /// Background color.
    pub background_color: Color,
    /// Font size for labels.
    pub font_size: f32,
    /// Enable bloom/glow effect.
    pub bloom_enabled: bool,
    /// Bloom intensity (0.0 - 2.0).
    pub bloom_intensity: f32,
    /// Enable drop shadows.
    pub shadows_enabled: bool,
}

impl Default for DisplaySettings {
    fn default() -> Self {
        Self {
            width: 1280,
            height: 720,
            fullscreen: false,
            background_color: Color::BLACK,
            font_size: 12.0,
            bloom_enabled: true,
            bloom_intensity: 1.0,
            shadows_enabled: false,
        }
    }
}

/// Playback settings for animation timing.
#[derive(Debug, Clone)]
pub struct PlaybackSettings {
    /// Seconds of real time per day of commit history.
    pub seconds_per_day: f32,
    /// Auto-skip to next commit after this many seconds of inactivity.
    pub auto_skip_seconds: f32,
    /// Start playback from this timestamp (Unix epoch).
    pub start_timestamp: Option<i64>,
    /// Stop playback at this timestamp (Unix epoch).
    pub stop_timestamp: Option<i64>,
    /// Loop the visualization when reaching the end.
    pub loop_playback: bool,
    /// Start in paused state.
    pub start_paused: bool,
    /// Time scale multiplier (1.0 = normal, 2.0 = double speed).
    pub time_scale: f32,
    /// Stop playback after this many seconds of real time.
    pub stop_at_time: Option<f32>,
    /// Use real-time playback (1 second = 1 second of history).
    pub realtime: bool,
}

impl Default for PlaybackSettings {
    fn default() -> Self {
        Self {
            seconds_per_day: 10.0,
            auto_skip_seconds: 3.0,
            start_timestamp: None,
            stop_timestamp: None,
            loop_playback: false,
            start_paused: false,
            time_scale: 1.0,
            stop_at_time: None,
            realtime: false,
        }
    }
}

/// Visibility settings for UI elements.
#[derive(Debug, Clone, Default)]
#[allow(clippy::struct_excessive_bools)]
pub struct VisibilitySettings {
    /// Hide file names.
    pub hide_filenames: bool,
    /// Hide user names.
    pub hide_usernames: bool,
    /// Hide the date display.
    pub hide_date: bool,
    /// Hide the progress bar.
    pub hide_progress: bool,
    /// Hide the file extension legend.
    pub hide_legend: bool,
    /// Hide directory names/labels.
    pub hide_dirnames: bool,
    /// Hide the root directory node.
    pub hide_root: bool,
    /// Hide the tree structure (connecting lines).
    pub hide_tree: bool,
    /// Hide the bloom/glow effect (runtime visibility, not same as `bloom_enabled`).
    pub hide_bloom: bool,
    /// Hide the mouse cursor during visualization.
    pub hide_mouse: bool,
    /// Show FPS counter.
    pub show_fps: bool,
}

/// Limit settings for performance control.
#[derive(Debug, Clone)]
pub struct LimitSettings {
    /// Maximum number of files to display (0 = unlimited).
    pub max_files: usize,
    /// Maximum number of users to display (0 = unlimited).
    pub max_users: usize,
    /// Time in seconds before idle files fade out.
    pub file_idle_time: f32,
    /// Time in seconds before idle users fade out.
    pub user_idle_time: f32,
}

impl Default for LimitSettings {
    fn default() -> Self {
        Self {
            max_files: 0,
            max_users: 0,
            file_idle_time: 60.0,
            user_idle_time: 10.0,
        }
    }
}

/// Camera settings.
#[derive(Debug, Clone)]
pub struct CameraSettings {
    /// Camera mode (overview, track, follow).
    pub mode: CameraModeSetting,
    /// Minimum zoom level.
    pub min_zoom: f32,
    /// Maximum zoom level.
    pub max_zoom: f32,
    /// Camera smoothness (0.0 = instant, 1.0 = very slow).
    pub smoothness: f32,
    /// Padding around content when auto-fitting.
    pub padding: f32,
    /// Username to follow when in follow mode.
    pub follow_user: Option<String>,
    /// Username(s) to highlight (comma-separated).
    pub highlight_users: Option<String>,
    /// Highlight all users (overrides `highlight_users`).
    pub highlight_all_users: bool,
    /// Enable 3D perspective camera mode.
    pub enable_3d: bool,
    /// Initial pitch angle in degrees (3D mode only).
    pub pitch: f32,
    /// Auto-rotation speed in radians per second (3D mode only).
    pub rotation_speed: f32,
    /// Disable automatic camera rotation (3D mode only).
    pub disable_auto_rotate: bool,
}

impl Default for CameraSettings {
    fn default() -> Self {
        Self {
            mode: CameraModeSetting::Overview,
            min_zoom: 0.01,
            max_zoom: 10.0,
            smoothness: 0.85,
            padding: 100.0,
            follow_user: None,
            highlight_users: None,
            highlight_all_users: false,
            enable_3d: false,
            pitch: -17.0,
            rotation_speed: 0.05,
            disable_auto_rotate: false,
        }
    }
}

/// Input settings.
#[derive(Debug, Clone)]
pub struct InputSettings {
    /// Disable all user input (for automated playback).
    pub disable_input: bool,
    /// Mouse sensitivity for pan/zoom.
    pub mouse_sensitivity: f32,
}

impl InputSettings {
    /// Default mouse sensitivity.
    const DEFAULT_MOUSE_SENSITIVITY: f32 = 1.0;
}

impl Default for InputSettings {
    fn default() -> Self {
        Self {
            disable_input: false,
            mouse_sensitivity: Self::DEFAULT_MOUSE_SENSITIVITY,
        }
    }
}

/// Export settings for video/screenshot output.
#[derive(Debug, Clone)]
pub struct ExportSettings {
    /// Output path for video frames.
    pub output_path: Option<String>,
    /// Frame rate for video export.
    pub framerate: u32,
    /// Screenshot output path.
    pub screenshot_path: Option<String>,
}

impl Default for ExportSettings {
    fn default() -> Self {
        Self {
            output_path: None,
            framerate: 60,
            screenshot_path: None,
        }
    }
}

/// Title and caption settings.
#[derive(Debug, Clone)]
pub struct TitleSettings {
    /// Main title to display.
    pub title: Option<String>,
    /// Font size for the title.
    pub title_font_size: f32,
    /// Title color.
    pub title_color: Color,
}

impl Default for TitleSettings {
    fn default() -> Self {
        Self {
            title: None,
            title_font_size: 24.0,
            title_color: Color::WHITE,
        }
    }
}

/// Directory display settings.
#[derive(Debug, Clone)]
pub struct DirectorySettings {
    /// Depth of directory names to display (0 = none, 1 = immediate parent, etc.).
    pub name_depth: u32,
    /// Position of directory name along the edge (0.0 = start, 1.0 = end).
    pub name_position: f32,
}

impl Default for DirectorySettings {
    fn default() -> Self {
        Self {
            name_depth: 1,
            name_position: 0.5,
        }
    }
}

/// Overlay settings for logo and background images.
#[derive(Debug, Clone, Default)]
pub struct OverlaySettings {
    /// Path to logo image file.
    pub logo_path: Option<String>,
    /// Logo position offset from top-right corner (x, y).
    pub logo_offset: (i32, i32),
    /// Path to background image file.
    pub background_image: Option<String>,
}

/// Filter settings for users and files.
///
/// Allows filtering entities by regex patterns. The "show" patterns include
/// matching entities, while "hide" patterns exclude them. If both are specified,
/// "hide" takes precedence over "show".
#[derive(Debug, Clone, Default)]
pub struct FilterSettings {
    /// Regex pattern to match users that should be shown.
    /// If set, only users matching this pattern are displayed.
    show_users: Option<String>,

    /// Regex pattern to match users that should be hidden.
    /// Takes precedence over `show_users`.
    hide_users: Option<String>,

    /// Regex pattern to match file paths that should be shown.
    /// If set, only files matching this pattern are displayed.
    show_files: Option<String>,

    /// Regex pattern to match file paths that should be hidden.
    /// Takes precedence over `show_files`.
    hide_files: Option<String>,

    /// Regex pattern to match directory paths to exclude.
    /// Entire directory trees matching this pattern are excluded.
    hide_dirs: Option<String>,

    /// Compiled regex for `show_users` (lazily compiled).
    #[allow(clippy::type_complexity)]
    show_users_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `hide_users` (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_users_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `show_files` (lazily compiled).
    #[allow(clippy::type_complexity)]
    show_files_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `hide_files` (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_files_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `hide_dirs` (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_dirs_regex: Option<Result<Regex, String>>,
}

impl FilterSettings {
    /// Creates new filter settings with no filters.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the user show filter.
    #[must_use]
    pub fn with_show_users(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.show_users = Some(pattern);
            self.show_users_regex = None; // Clear cached regex
        }
        self
    }

    /// Sets the user hide filter.
    #[must_use]
    pub fn with_hide_users(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.hide_users = Some(pattern);
            self.hide_users_regex = None;
        }
        self
    }

    /// Sets the file show filter.
    #[must_use]
    pub fn with_show_files(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.show_files = Some(pattern);
            self.show_files_regex = None;
        }
        self
    }

    /// Sets the file hide filter.
    #[must_use]
    pub fn with_hide_files(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.hide_files = Some(pattern);
            self.hide_files_regex = None;
        }
        self
    }

    /// Sets the directory hide filter.
    #[must_use]
    pub fn with_hide_dirs(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.hide_dirs = Some(pattern);
            self.hide_dirs_regex = None;
        }
        self
    }

    /// Sets the user show filter (mutable).
    pub fn set_show_users(&mut self, pattern: Option<String>) {
        self.show_users = pattern.filter(|s| !s.is_empty());
        self.show_users_regex = None;
    }

    /// Sets the user hide filter (mutable).
    pub fn set_hide_users(&mut self, pattern: Option<String>) {
        self.hide_users = pattern.filter(|s| !s.is_empty());
        self.hide_users_regex = None;
    }

    /// Sets the file show filter (mutable).
    pub fn set_show_files(&mut self, pattern: Option<String>) {
        self.show_files = pattern.filter(|s| !s.is_empty());
        self.show_files_regex = None;
    }

    /// Sets the file hide filter (mutable).
    pub fn set_hide_files(&mut self, pattern: Option<String>) {
        self.hide_files = pattern.filter(|s| !s.is_empty());
        self.hide_files_regex = None;
    }

    /// Sets the directory hide filter (mutable).
    pub fn set_hide_dirs(&mut self, pattern: Option<String>) {
        self.hide_dirs = pattern.filter(|s| !s.is_empty());
        self.hide_dirs_regex = None;
    }

    /// Returns the `show_users` pattern.
    #[must_use]
    pub fn show_users_pattern(&self) -> Option<&str> {
        self.show_users.as_deref()
    }

    /// Returns the `hide_users` pattern.
    #[must_use]
    pub fn hide_users_pattern(&self) -> Option<&str> {
        self.hide_users.as_deref()
    }

    /// Returns the `show_files` pattern.
    #[must_use]
    pub fn show_files_pattern(&self) -> Option<&str> {
        self.show_files.as_deref()
    }

    /// Returns the `hide_files` pattern.
    #[must_use]
    pub fn hide_files_pattern(&self) -> Option<&str> {
        self.hide_files.as_deref()
    }

    /// Returns the `hide_dirs` pattern.
    #[must_use]
    pub fn hide_dirs_pattern(&self) -> Option<&str> {
        self.hide_dirs.as_deref()
    }

    /// Compiles a regex pattern, caching the result.
    #[allow(clippy::ref_option)] // Using &Option here for ergonomic self.field references
    fn compile_regex<'a>(
        pattern: &Option<String>,
        cached: &'a mut Option<Result<Regex, String>>,
    ) -> Option<Result<&'a Regex, &'a str>> {
        if pattern.is_none() {
            return None;
        }

        if cached.is_none() {
            let result = pattern
                .as_ref()
                .map(|p| Regex::new(p).map_err(|e| e.to_string()))
                .unwrap();
            *cached = Some(result);
        }

        cached.as_ref().map(|r| r.as_ref().map_err(String::as_str))
    }

    /// Checks if a user should be included based on filter settings.
    ///
    /// Returns `true` if the user should be shown, `false` if filtered out.
    pub fn should_include_user(&mut self, name: &str) -> bool {
        // Check hide filter first (takes precedence)
        if let Some(Ok(regex)) = Self::compile_regex(&self.hide_users, &mut self.hide_users_regex) {
            if regex.is_match(name) {
                return false;
            }
        }

        // Check show filter
        if let Some(Ok(regex)) = Self::compile_regex(&self.show_users, &mut self.show_users_regex) {
            return regex.is_match(name);
        }

        true // No filters or invalid regex = show all
    }

    /// Checks if a file should be included based on filter settings.
    ///
    /// Returns `true` if the file should be shown, `false` if filtered out.
    pub fn should_include_file(&mut self, path: &Path) -> bool {
        let path_str = path.to_string_lossy();

        // Check directory hide filter first
        if let Some(Ok(regex)) = Self::compile_regex(&self.hide_dirs, &mut self.hide_dirs_regex) {
            // Check if any component of the path matches the directory filter
            for ancestor in path.ancestors() {
                if ancestor.as_os_str().is_empty() {
                    continue;
                }
                let ancestor_str = ancestor.to_string_lossy();
                if regex.is_match(&ancestor_str) {
                    return false;
                }
            }
        }

        // Check file hide filter
        if let Some(Ok(regex)) = Self::compile_regex(&self.hide_files, &mut self.hide_files_regex) {
            if regex.is_match(&path_str) {
                return false;
            }
        }

        // Check file show filter
        if let Some(Ok(regex)) = Self::compile_regex(&self.show_files, &mut self.show_files_regex) {
            return regex.is_match(&path_str);
        }

        true // No filters or invalid regex = show all
    }

    /// Validates filter patterns and returns errors for invalid regexes.
    #[must_use]
    pub fn validate(&mut self) -> Vec<String> {
        let mut errors = Vec::new();

        // Validate each filter pattern
        if let Some(pattern) = &self.show_users {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for show-users: {pattern}"));
            }
        }
        if let Some(pattern) = &self.hide_users {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for hide-users: {pattern}"));
            }
        }
        if let Some(pattern) = &self.show_files {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for show-files: {pattern}"));
            }
        }
        if let Some(pattern) = &self.hide_files {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for hide-files: {pattern}"));
            }
        }
        if let Some(pattern) = &self.hide_dirs {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for hide-dirs: {pattern}"));
            }
        }

        errors
    }

    /// Returns true if any filters are configured.
    #[must_use]
    pub fn has_filters(&self) -> bool {
        self.show_users.is_some()
            || self.hide_users.is_some()
            || self.show_files.is_some()
            || self.hide_files.is_some()
            || self.hide_dirs.is_some()
    }
}

/// Complete settings for the Rource visualization.
///
/// This struct contains all configuration options organized into logical groups.
/// It can be constructed from CLI arguments, config files, or programmatically.
#[derive(Debug, Clone, Default)]
pub struct Settings {
    /// Display and visual settings.
    pub display: DisplaySettings,
    /// Playback timing settings.
    pub playback: PlaybackSettings,
    /// UI element visibility.
    pub visibility: VisibilitySettings,
    /// Performance limits.
    pub limits: LimitSettings,
    /// Camera behavior.
    pub camera: CameraSettings,
    /// Input handling.
    pub input: InputSettings,
    /// Export options.
    pub export: ExportSettings,
    /// Title and captions.
    pub title: TitleSettings,
    /// Directory display settings.
    pub directory: DirectorySettings,
    /// Overlay settings (logo, background).
    pub overlay: OverlaySettings,
    /// Filter settings for users and files.
    pub filter: FilterSettings,
}

impl Settings {
    /// Creates a new Settings with default values.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates settings optimized for high performance (large repositories).
    #[must_use]
    pub fn high_performance() -> Self {
        Self {
            display: DisplaySettings {
                bloom_enabled: false,
                shadows_enabled: false,
                ..Default::default()
            },
            limits: LimitSettings {
                max_files: 1000,
                max_users: 50,
                file_idle_time: 30.0,
                ..Default::default()
            },
            ..Default::default()
        }
    }

    /// Creates settings for video export (fixed framerate, no input).
    #[must_use]
    pub fn video_export(output_path: &str, framerate: u32) -> Self {
        Self {
            input: InputSettings {
                disable_input: true,
                ..Default::default()
            },
            export: ExportSettings {
                output_path: Some(output_path.to_string()),
                framerate,
                ..Default::default()
            },
            ..Default::default()
        }
    }

    /// Sets the display dimensions.
    #[must_use]
    pub fn with_dimensions(mut self, width: u32, height: u32) -> Self {
        self.display.width = width;
        self.display.height = height;
        self
    }

    /// Sets the background color.
    #[must_use]
    pub fn with_background(mut self, color: Color) -> Self {
        self.display.background_color = color;
        self
    }

    /// Sets the playback speed (seconds per day).
    #[must_use]
    pub fn with_speed(mut self, seconds_per_day: f32) -> Self {
        self.playback.seconds_per_day = seconds_per_day;
        self
    }

    /// Enables or disables bloom effect.
    #[must_use]
    pub fn with_bloom(mut self, enabled: bool) -> Self {
        self.display.bloom_enabled = enabled;
        self
    }

    /// Sets the camera mode.
    #[must_use]
    pub fn with_camera_mode(mut self, mode: CameraModeSetting) -> Self {
        self.camera.mode = mode;
        self
    }

    /// Sets the title.
    #[must_use]
    pub fn with_title(mut self, title: impl Into<String>) -> Self {
        self.title.title = Some(title.into());
        self
    }

    /// Enables loop playback.
    #[must_use]
    pub fn with_loop(mut self, enabled: bool) -> Self {
        self.playback.loop_playback = enabled;
        self
    }

    /// Sets the filter settings.
    #[must_use]
    pub fn with_filter(mut self, filter: FilterSettings) -> Self {
        self.filter = filter;
        self
    }

    /// Sets a user filter (hide matching users).
    #[must_use]
    pub fn with_hide_users(mut self, pattern: impl Into<String>) -> Self {
        self.filter = self.filter.with_hide_users(pattern);
        self
    }

    /// Sets a file filter (hide matching files).
    #[must_use]
    pub fn with_hide_files(mut self, pattern: impl Into<String>) -> Self {
        self.filter = self.filter.with_hide_files(pattern);
        self
    }

    /// Validates settings and returns any errors.
    #[must_use]
    pub fn validate(&self) -> Vec<String> {
        let mut errors = Vec::new();

        if self.display.width == 0 {
            errors.push("Display width cannot be 0".to_string());
        }
        if self.display.height == 0 {
            errors.push("Display height cannot be 0".to_string());
        }
        if self.playback.seconds_per_day <= 0.0 {
            errors.push("Seconds per day must be positive".to_string());
        }
        if self.camera.min_zoom <= 0.0 {
            errors.push("Minimum zoom must be positive".to_string());
        }
        if self.camera.max_zoom <= self.camera.min_zoom {
            errors.push("Maximum zoom must be greater than minimum zoom".to_string());
        }
        if self.export.framerate == 0 {
            errors.push("Framerate cannot be 0".to_string());
        }

        // Validate filter patterns
        let mut filter_copy = self.filter.clone();
        errors.extend(filter_copy.validate());

        errors
    }

    /// Returns true if settings are valid.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.validate().is_empty()
    }

    /// Generates a TOML configuration string from the current settings.
    ///
    /// This can be used to save the current configuration to a file.
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn to_config_string(&self) -> String {
        let mut config = String::new();

        config.push_str("# Rource Configuration File\n");
        config.push_str("# Generated by rource --save-config\n\n");

        // Display settings
        config.push_str("# Display settings\n");
        config.push_str(&format!("width = {}\n", self.display.width));
        config.push_str(&format!("height = {}\n", self.display.height));
        config.push_str(&format!("fullscreen = {}\n", self.display.fullscreen));
        config.push_str(&format!(
            "background_color = \"{:02X}{:02X}{:02X}\"\n",
            (self.display.background_color.r * 255.0) as u8,
            (self.display.background_color.g * 255.0) as u8,
            (self.display.background_color.b * 255.0) as u8
        ));
        config.push_str(&format!("font_size = {:.1}\n", self.display.font_size));
        config.push_str(&format!("bloom_enabled = {}\n", self.display.bloom_enabled));
        config.push_str(&format!(
            "bloom_intensity = {:.1}\n",
            self.display.bloom_intensity
        ));
        config.push_str(&format!(
            "shadows_enabled = {}\n",
            self.display.shadows_enabled
        ));
        config.push('\n');

        // Playback settings
        config.push_str("# Playback settings\n");
        config.push_str(&format!(
            "seconds_per_day = {:.1}\n",
            self.playback.seconds_per_day
        ));
        config.push_str(&format!(
            "auto_skip_seconds = {:.1}\n",
            self.playback.auto_skip_seconds
        ));
        config.push_str(&format!("loop_playback = {}\n", self.playback.loop_playback));
        config.push_str(&format!("start_paused = {}\n", self.playback.start_paused));
        config.push_str(&format!("time_scale = {:.1}\n", self.playback.time_scale));
        config.push_str(&format!("realtime = {}\n", self.playback.realtime));
        if let Some(stop_at) = self.playback.stop_at_time {
            config.push_str(&format!("stop_at_time = {:.1}\n", stop_at));
        }
        config.push('\n');

        // Visibility settings
        config.push_str("# Visibility settings\n");
        config.push_str(&format!(
            "hide_filenames = {}\n",
            self.visibility.hide_filenames
        ));
        config.push_str(&format!(
            "hide_usernames = {}\n",
            self.visibility.hide_usernames
        ));
        config.push_str(&format!("hide_date = {}\n", self.visibility.hide_date));
        config.push_str(&format!("hide_progress = {}\n", self.visibility.hide_progress));
        config.push_str(&format!("hide_legend = {}\n", self.visibility.hide_legend));
        config.push_str(&format!("hide_dirnames = {}\n", self.visibility.hide_dirnames));
        config.push_str(&format!("hide_root = {}\n", self.visibility.hide_root));
        config.push_str(&format!("hide_tree = {}\n", self.visibility.hide_tree));
        config.push_str(&format!("hide_bloom = {}\n", self.visibility.hide_bloom));
        config.push_str(&format!("hide_mouse = {}\n", self.visibility.hide_mouse));
        config.push_str(&format!("show_fps = {}\n", self.visibility.show_fps));
        config.push('\n');

        // Camera settings
        config.push_str("# Camera settings\n");
        config.push_str(&format!("camera_mode = \"{}\"\n", self.camera.mode.as_str()));
        config.push_str(&format!("min_zoom = {:.2}\n", self.camera.min_zoom));
        config.push_str(&format!("max_zoom = {:.2}\n", self.camera.max_zoom));
        config.push_str(&format!("camera_smoothness = {:.2}\n", self.camera.smoothness));
        config.push_str(&format!("camera_padding = {:.1}\n", self.camera.padding));
        if let Some(ref user) = self.camera.follow_user {
            config.push_str(&format!("follow_user = \"{}\"\n", user));
        }
        if let Some(ref users) = self.camera.highlight_users {
            config.push_str(&format!("highlight_users = \"{}\"\n", users));
        }
        config.push_str(&format!(
            "highlight_all_users = {}\n",
            self.camera.highlight_all_users
        ));
        config.push_str(&format!("camera_3d = {}\n", self.camera.enable_3d));
        config.push_str(&format!("camera_pitch = {:.1}\n", self.camera.pitch));
        config.push_str(&format!(
            "camera_rotation_speed = {:.2}\n",
            self.camera.rotation_speed
        ));
        config.push_str(&format!(
            "camera_disable_auto_rotate = {}\n",
            self.camera.disable_auto_rotate
        ));
        config.push('\n');

        // Directory settings
        config.push_str("# Directory settings\n");
        config.push_str(&format!(
            "dir_name_depth = {}\n",
            self.directory.name_depth
        ));
        config.push_str(&format!(
            "dir_name_position = {:.2}\n",
            self.directory.name_position
        ));
        config.push('\n');

        // Overlay settings
        config.push_str("# Overlay settings\n");
        if let Some(ref path) = self.overlay.logo_path {
            config.push_str(&format!("logo = \"{}\"\n", path));
        }
        if self.overlay.logo_offset != (0, 0) {
            config.push_str(&format!(
                "logo_offset = \"{}x{}\"\n",
                self.overlay.logo_offset.0, self.overlay.logo_offset.1
            ));
        }
        if let Some(ref path) = self.overlay.background_image {
            config.push_str(&format!("background_image = \"{}\"\n", path));
        }
        config.push('\n');

        // Limit settings
        config.push_str("# Limit settings\n");
        config.push_str(&format!("max_files = {}\n", self.limits.max_files));
        config.push_str(&format!("max_users = {}\n", self.limits.max_users));
        config.push_str(&format!("file_idle_time = {:.1}\n", self.limits.file_idle_time));
        config.push_str(&format!("user_idle_time = {:.1}\n", self.limits.user_idle_time));
        config.push('\n');

        // Export settings
        config.push_str("# Export settings\n");
        config.push_str(&format!("framerate = {}\n", self.export.framerate));
        if let Some(ref path) = self.export.output_path {
            config.push_str(&format!("output_path = \"{}\"\n", path));
        }
        config.push('\n');

        // Title settings
        config.push_str("# Title settings\n");
        if let Some(ref title) = self.title.title {
            config.push_str(&format!("title = \"{}\"\n", title));
        }
        config.push_str(&format!(
            "title_font_size = {:.1}\n",
            self.title.title_font_size
        ));
        config.push_str(&format!(
            "title_color = \"{:02X}{:02X}{:02X}\"\n",
            (self.title.title_color.r * 255.0) as u8,
            (self.title.title_color.g * 255.0) as u8,
            (self.title.title_color.b * 255.0) as u8
        ));
        config.push('\n');

        // Filter settings
        config.push_str("# Filter settings (regex patterns)\n");
        if let Some(pattern) = self.filter.show_users_pattern() {
            config.push_str(&format!("show_users = \"{}\"\n", pattern));
        }
        if let Some(pattern) = self.filter.hide_users_pattern() {
            config.push_str(&format!("hide_users = \"{}\"\n", pattern));
        }
        if let Some(pattern) = self.filter.show_files_pattern() {
            config.push_str(&format!("show_files = \"{}\"\n", pattern));
        }
        if let Some(pattern) = self.filter.hide_files_pattern() {
            config.push_str(&format!("hide_files = \"{}\"\n", pattern));
        }
        if let Some(pattern) = self.filter.hide_dirs_pattern() {
            config.push_str(&format!("hide_dirs = \"{}\"\n", pattern));
        }

        config
    }

    /// Saves the current settings to a TOML configuration file.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be written.
    pub fn save_to_file(&self, path: &std::path::Path) -> std::io::Result<()> {
        std::fs::write(path, self.to_config_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_settings_default() {
        let settings = Settings::new();
        assert_eq!(settings.display.width, 1280);
        assert_eq!(settings.display.height, 720);
        assert!(settings.display.bloom_enabled);
        assert!(!settings.playback.loop_playback);
    }

    #[test]
    fn test_settings_builder() {
        let settings = Settings::new()
            .with_dimensions(1920, 1080)
            .with_bloom(false)
            .with_speed(5.0)
            .with_title("My Project");

        assert_eq!(settings.display.width, 1920);
        assert_eq!(settings.display.height, 1080);
        assert!(!settings.display.bloom_enabled);
        assert!((settings.playback.seconds_per_day - 5.0).abs() < 0.01);
        assert_eq!(settings.title.title, Some("My Project".to_string()));
    }

    #[test]
    fn test_settings_high_performance() {
        let settings = Settings::high_performance();
        assert!(!settings.display.bloom_enabled);
        assert!(!settings.display.shadows_enabled);
        assert_eq!(settings.limits.max_files, 1000);
    }

    #[test]
    fn test_settings_video_export() {
        let settings = Settings::video_export("/tmp/frames", 30);
        assert!(settings.input.disable_input);
        assert_eq!(settings.export.output_path, Some("/tmp/frames".to_string()));
        assert_eq!(settings.export.framerate, 30);
    }

    #[test]
    fn test_settings_validation() {
        let mut settings = Settings::new();
        assert!(settings.is_valid());

        settings.display.width = 0;
        let errors = settings.validate();
        assert!(!errors.is_empty());
        assert!(errors[0].contains("width"));
    }

    #[test]
    fn test_camera_mode_parse() {
        assert_eq!(
            CameraModeSetting::parse("overview"),
            CameraModeSetting::Overview
        );
        assert_eq!(CameraModeSetting::parse("TRACK"), CameraModeSetting::Track);
        assert_eq!(
            CameraModeSetting::parse("follow"),
            CameraModeSetting::Follow
        );
        assert_eq!(
            CameraModeSetting::parse("invalid"),
            CameraModeSetting::Overview
        );
    }

    #[test]
    fn test_camera_mode_as_str() {
        assert_eq!(CameraModeSetting::Overview.as_str(), "overview");
        assert_eq!(CameraModeSetting::Track.as_str(), "track");
        assert_eq!(CameraModeSetting::Follow.as_str(), "follow");
    }

    #[test]
    fn test_display_settings_default() {
        let display = DisplaySettings::default();
        assert_eq!(display.width, 1280);
        assert_eq!(display.height, 720);
        assert!(!display.fullscreen);
        assert!(display.bloom_enabled);
    }

    #[test]
    fn test_playback_settings_default() {
        let playback = PlaybackSettings::default();
        assert!((playback.seconds_per_day - 10.0).abs() < 0.01);
        assert!((playback.auto_skip_seconds - 3.0).abs() < 0.01);
        assert!(!playback.loop_playback);
    }

    #[test]
    fn test_limit_settings_default() {
        let limits = LimitSettings::default();
        assert_eq!(limits.max_files, 0); // 0 = unlimited
        assert_eq!(limits.max_users, 0);
    }

    #[test]
    fn test_filter_settings_default() {
        let filter = FilterSettings::default();
        assert!(!filter.has_filters());
        assert!(filter.show_users_pattern().is_none());
        assert!(filter.hide_users_pattern().is_none());
    }

    #[test]
    fn test_filter_settings_builder() {
        let filter = FilterSettings::new()
            .with_hide_users("bot.*")
            .with_show_files(r"\.rs$");

        assert!(filter.has_filters());
        assert_eq!(filter.hide_users_pattern(), Some("bot.*"));
        assert_eq!(filter.show_files_pattern(), Some(r"\.rs$"));
    }

    #[test]
    fn test_filter_user_inclusion() {
        let mut filter = FilterSettings::new().with_hide_users("bot.*");

        assert!(filter.should_include_user("alice"));
        assert!(filter.should_include_user("Bob"));
        assert!(!filter.should_include_user("bot123"));
        assert!(!filter.should_include_user("bot-ci"));
    }

    #[test]
    fn test_filter_user_show_only() {
        let mut filter = FilterSettings::new().with_show_users("^(alice|bob)$");

        assert!(filter.should_include_user("alice"));
        assert!(filter.should_include_user("bob"));
        assert!(!filter.should_include_user("charlie"));
        assert!(!filter.should_include_user("alice_smith")); // Exact match only
    }

    #[test]
    fn test_filter_user_hide_precedence() {
        // Hide takes precedence over show
        let mut filter = FilterSettings::new()
            .with_show_users(".*")
            .with_hide_users("^bot$");

        assert!(filter.should_include_user("alice"));
        assert!(!filter.should_include_user("bot"));
    }

    #[test]
    fn test_filter_file_inclusion() {
        use std::path::PathBuf;

        let mut filter = FilterSettings::new().with_hide_files(r"\.log$");

        assert!(filter.should_include_file(&PathBuf::from("src/main.rs")));
        assert!(filter.should_include_file(&PathBuf::from("README.md")));
        assert!(!filter.should_include_file(&PathBuf::from("debug.log")));
        assert!(!filter.should_include_file(&PathBuf::from("logs/app.log")));
    }

    #[test]
    fn test_filter_file_show_only() {
        use std::path::PathBuf;

        let mut filter = FilterSettings::new().with_show_files(r"\.rs$");

        assert!(filter.should_include_file(&PathBuf::from("src/main.rs")));
        assert!(filter.should_include_file(&PathBuf::from("lib.rs")));
        assert!(!filter.should_include_file(&PathBuf::from("README.md")));
        assert!(!filter.should_include_file(&PathBuf::from("Cargo.toml")));
    }

    #[test]
    fn test_filter_dir_exclusion() {
        use std::path::PathBuf;

        let mut filter = FilterSettings::new().with_hide_dirs("node_modules|target");

        assert!(filter.should_include_file(&PathBuf::from("src/main.rs")));
        assert!(!filter.should_include_file(&PathBuf::from("node_modules/pkg/index.js")));
        assert!(!filter.should_include_file(&PathBuf::from("target/debug/app")));
    }

    #[test]
    fn test_filter_validation() {
        let mut valid = FilterSettings::new().with_hide_users(".*");
        assert!(valid.validate().is_empty());

        let mut invalid = FilterSettings::new().with_hide_users("[invalid");
        let errors = invalid.validate();
        assert!(!errors.is_empty());
        assert!(errors[0].contains("hide-users"));
    }

    #[test]
    fn test_settings_with_filter() {
        let settings = Settings::new()
            .with_hide_users("bot.*")
            .with_hide_files(r"\.log$");

        assert!(settings.filter.has_filters());
        assert_eq!(settings.filter.hide_users_pattern(), Some("bot.*"));
    }

    #[test]
    fn test_settings_validation_with_invalid_filter() {
        let settings = Settings::new().with_hide_users("[invalid");
        let errors = settings.validate();
        assert!(!errors.is_empty());
        assert!(errors.iter().any(|e| e.contains("hide-users")));
    }

    // Tests for new feature parity settings

    #[test]
    fn test_visibility_settings_new_fields() {
        let mut vis = VisibilitySettings::default();
        assert!(!vis.hide_dirnames);
        assert!(!vis.hide_root);
        assert!(!vis.hide_tree);
        assert!(!vis.hide_bloom);
        assert!(!vis.hide_mouse);

        vis.hide_dirnames = true;
        vis.hide_root = true;
        vis.hide_tree = true;
        vis.hide_bloom = true;
        vis.hide_mouse = true;

        assert!(vis.hide_dirnames);
        assert!(vis.hide_root);
        assert!(vis.hide_tree);
        assert!(vis.hide_bloom);
        assert!(vis.hide_mouse);
    }

    #[test]
    fn test_playback_settings_time_controls() {
        let playback = PlaybackSettings::default();
        assert!((playback.time_scale - 1.0).abs() < 0.01);
        assert!(playback.stop_at_time.is_none());
        assert!(!playback.realtime);

        let custom = PlaybackSettings {
            time_scale: 2.0,
            stop_at_time: Some(60.0),
            realtime: true,
            ..Default::default()
        };
        assert!((custom.time_scale - 2.0).abs() < 0.01);
        assert_eq!(custom.stop_at_time, Some(60.0));
        assert!(custom.realtime);
    }

    #[test]
    fn test_camera_settings_follow_user() {
        let camera = CameraSettings::default();
        assert!(camera.follow_user.is_none());
        assert!(camera.highlight_users.is_none());
        assert!(!camera.highlight_all_users);

        let custom = CameraSettings {
            follow_user: Some("alice".to_string()),
            highlight_users: Some("bob,charlie".to_string()),
            highlight_all_users: true,
            ..Default::default()
        };
        assert_eq!(custom.follow_user, Some("alice".to_string()));
        assert_eq!(custom.highlight_users, Some("bob,charlie".to_string()));
        assert!(custom.highlight_all_users);
    }

    #[test]
    fn test_directory_settings_default() {
        let dir = DirectorySettings::default();
        assert_eq!(dir.name_depth, 1);
        assert!((dir.name_position - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_overlay_settings_default() {
        let overlay = OverlaySettings::default();
        assert!(overlay.logo_path.is_none());
        assert_eq!(overlay.logo_offset, (0, 0));
        assert!(overlay.background_image.is_none());
    }

    #[test]
    fn test_to_config_string() {
        let settings = Settings::new()
            .with_dimensions(1920, 1080)
            .with_bloom(true)
            .with_title("Test Project");

        let config = settings.to_config_string();

        assert!(config.contains("width = 1920"));
        assert!(config.contains("height = 1080"));
        assert!(config.contains("bloom_enabled = true"));
        assert!(config.contains("title = \"Test Project\""));
        assert!(config.contains("time_scale = 1.0"));
        assert!(config.contains("hide_dirnames = false"));
    }

    #[test]
    fn test_to_config_string_with_all_new_settings() {
        let mut settings = Settings::new();
        settings.playback.time_scale = 2.0;
        settings.playback.stop_at_time = Some(120.0);
        settings.playback.realtime = true;
        settings.visibility.hide_dirnames = true;
        settings.visibility.hide_bloom = true;
        settings.camera.follow_user = Some("alice".to_string());
        settings.camera.highlight_all_users = true;
        settings.directory.name_depth = 3;
        settings.overlay.logo_path = Some("/path/to/logo.png".to_string());
        settings.overlay.logo_offset = (10, 20);

        let config = settings.to_config_string();

        assert!(config.contains("time_scale = 2.0"));
        assert!(config.contains("stop_at_time = 120.0"));
        assert!(config.contains("realtime = true"));
        assert!(config.contains("hide_dirnames = true"));
        assert!(config.contains("hide_bloom = true"));
        assert!(config.contains("follow_user = \"alice\""));
        assert!(config.contains("highlight_all_users = true"));
        assert!(config.contains("dir_name_depth = 3"));
        assert!(config.contains("logo = \"/path/to/logo.png\""));
        assert!(config.contains("logo_offset = \"10x20\""));
    }
}
