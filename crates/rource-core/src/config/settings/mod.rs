//! Settings for the Rource visualization.
//!
//! This module provides a unified configuration structure that can be used
//! by both native CLI and WebAssembly applications.

mod camera;
mod directory;
mod display;
mod export;
mod filter;
mod input;
mod layout;
mod limits;
mod overlay;
mod playback;
mod title;
mod visibility;

pub use camera::{CameraModeSetting, CameraSettings};
pub use directory::DirectorySettings;
pub use display::DisplaySettings;
pub use export::ExportSettings;
pub use filter::FilterSettings;
pub use input::InputSettings;
pub use layout::LayoutSettings;
pub use limits::LimitSettings;
pub use overlay::OverlaySettings;
pub use playback::PlaybackSettings;
pub use title::TitleSettings;
pub use visibility::VisibilitySettings;

use rource_math::Color;

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
    /// Layout settings for radial tree visualization.
    pub layout: LayoutSettings,
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
        config.push_str(&format!(
            "loop_playback = {}\n",
            self.playback.loop_playback
        ));
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
        config.push_str(&format!(
            "hide_progress = {}\n",
            self.visibility.hide_progress
        ));
        config.push_str(&format!("hide_legend = {}\n", self.visibility.hide_legend));
        config.push_str(&format!(
            "hide_dirnames = {}\n",
            self.visibility.hide_dirnames
        ));
        config.push_str(&format!("hide_root = {}\n", self.visibility.hide_root));
        config.push_str(&format!("hide_tree = {}\n", self.visibility.hide_tree));
        config.push_str(&format!("hide_bloom = {}\n", self.visibility.hide_bloom));
        config.push_str(&format!("hide_mouse = {}\n", self.visibility.hide_mouse));
        config.push_str(&format!("show_fps = {}\n", self.visibility.show_fps));
        config.push('\n');

        // Camera settings
        config.push_str("# Camera settings\n");
        config.push_str(&format!(
            "camera_mode = \"{}\"\n",
            self.camera.mode.as_str()
        ));
        config.push_str(&format!("min_zoom = {:.2}\n", self.camera.min_zoom));
        config.push_str(&format!("max_zoom = {:.2}\n", self.camera.max_zoom));
        config.push_str(&format!(
            "camera_smoothness = {:.2}\n",
            self.camera.smoothness
        ));
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
        config.push_str(&format!("dir_name_depth = {}\n", self.directory.name_depth));
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
        config.push_str(&format!(
            "file_idle_time = {:.1}\n",
            self.limits.file_idle_time
        ));
        config.push_str(&format!(
            "user_idle_time = {:.1}\n",
            self.limits.user_idle_time
        ));
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
