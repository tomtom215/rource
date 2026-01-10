//! Settings for the Rource visualization.
//!
//! This module provides a unified configuration structure that can be used
//! by both native CLI and WebAssembly applications.

use rource_math::Color;

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
}
