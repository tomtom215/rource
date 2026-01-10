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
}

impl Default for CameraSettings {
    fn default() -> Self {
        Self {
            mode: CameraModeSetting::Overview,
            min_zoom: 0.01,
            max_zoom: 10.0,
            smoothness: 0.85,
            padding: 100.0,
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

    /// Compiled regex for show_users (lazily compiled).
    #[allow(clippy::type_complexity)]
    show_users_regex: Option<Result<Regex, String>>,

    /// Compiled regex for hide_users (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_users_regex: Option<Result<Regex, String>>,

    /// Compiled regex for show_files (lazily compiled).
    #[allow(clippy::type_complexity)]
    show_files_regex: Option<Result<Regex, String>>,

    /// Compiled regex for hide_files (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_files_regex: Option<Result<Regex, String>>,

    /// Compiled regex for hide_dirs (lazily compiled).
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

    /// Returns the show_users pattern.
    #[must_use]
    pub fn show_users_pattern(&self) -> Option<&str> {
        self.show_users.as_deref()
    }

    /// Returns the hide_users pattern.
    #[must_use]
    pub fn hide_users_pattern(&self) -> Option<&str> {
        self.hide_users.as_deref()
    }

    /// Returns the show_files pattern.
    #[must_use]
    pub fn show_files_pattern(&self) -> Option<&str> {
        self.show_files.as_deref()
    }

    /// Returns the hide_files pattern.
    #[must_use]
    pub fn hide_files_pattern(&self) -> Option<&str> {
        self.hide_files.as_deref()
    }

    /// Returns the hide_dirs pattern.
    #[must_use]
    pub fn hide_dirs_pattern(&self) -> Option<&str> {
        self.hide_dirs.as_deref()
    }

    /// Compiles a regex pattern, caching the result.
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
        if let Some(result) = Self::compile_regex(&self.hide_users, &mut self.hide_users_regex) {
            match result {
                Ok(regex) if regex.is_match(name) => return false,
                Err(_) => {} // Invalid regex, don't filter
                _ => {}
            }
        }

        // Check show filter
        if let Some(result) = Self::compile_regex(&self.show_users, &mut self.show_users_regex) {
            match result {
                Ok(regex) => return regex.is_match(name),
                Err(_) => {} // Invalid regex, don't filter
            }
        }

        true // No filters or invalid regex = show all
    }

    /// Checks if a file should be included based on filter settings.
    ///
    /// Returns `true` if the file should be shown, `false` if filtered out.
    pub fn should_include_file(&mut self, path: &Path) -> bool {
        let path_str = path.to_string_lossy();

        // Check directory hide filter first
        if let Some(result) = Self::compile_regex(&self.hide_dirs, &mut self.hide_dirs_regex) {
            match result {
                Ok(regex) => {
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
                Err(_) => {} // Invalid regex, don't filter
            }
        }

        // Check file hide filter
        if let Some(result) = Self::compile_regex(&self.hide_files, &mut self.hide_files_regex) {
            match result {
                Ok(regex) if regex.is_match(&path_str) => return false,
                Err(_) => {} // Invalid regex, don't filter
                _ => {}
            }
        }

        // Check file show filter
        if let Some(result) = Self::compile_regex(&self.show_files, &mut self.show_files_regex) {
            match result {
                Ok(regex) => return regex.is_match(&path_str),
                Err(_) => {} // Invalid regex, don't filter
            }
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
}
