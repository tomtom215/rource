// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Configuration file parsing for Rource.
//!
//! This module provides TOML configuration file support, allowing users to
//! specify settings in a configuration file instead of command-line arguments.
//!
//! # Example Configuration File
//!
//! ```toml
//! # rource.toml
//!
//! [display]
//! width = 1920
//! height = 1080
//! fullscreen = false
//! background_color = "#000000"
//! font_size = 12.0
//! bloom_enabled = true
//! bloom_intensity = 1.0
//! shadows_enabled = false
//!
//! [playback]
//! seconds_per_day = 10.0
//! auto_skip_seconds = 3.0
//! loop_playback = false
//!
//! [camera]
//! mode = "overview"  # overview, track, or follow
//! min_zoom = 0.01
//! max_zoom = 10.0
//! padding = 100.0
//!
//! [visibility]
//! hide_filenames = false
//! hide_usernames = false
//! hide_date = false
//! hide_progress = false
//! hide_legend = false
//! show_fps = false
//!
//! [limits]
//! max_files = 0  # 0 = unlimited
//! max_users = 0
//! file_idle_time = 60.0
//! user_idle_time = 10.0
//!
//! [title]
//! title = "My Project"
//! title_font_size = 24.0
//! title_color = "#FFFFFF"
//!
//! [export]
//! framerate = 60
//! ```

use crate::config::{
    CameraModeSetting, CameraSettings, DisplaySettings, ExportSettings, FilterSettings,
    InputSettings, LayoutSettings, LimitSettings, PlaybackSettings, Settings, TitleSettings,
    VisibilitySettings,
};
use rource_math::Color;
use serde::Deserialize;
use std::path::Path;

/// Error type for configuration file parsing.
#[derive(Debug)]
pub enum ConfigError {
    /// Failed to read the configuration file.
    IoError(std::io::Error),
    /// Failed to parse the TOML content.
    ParseError(toml::de::Error),
    /// Invalid configuration value.
    ValidationError(String),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IoError(e) => write!(f, "Failed to read config file: {e}"),
            Self::ParseError(e) => write!(f, "Failed to parse config file: {e}"),
            Self::ValidationError(msg) => write!(f, "Invalid configuration: {msg}"),
        }
    }
}

impl std::error::Error for ConfigError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::IoError(e) => Some(e),
            Self::ParseError(e) => Some(e),
            Self::ValidationError(_) => None,
        }
    }
}

impl From<std::io::Error> for ConfigError {
    fn from(err: std::io::Error) -> Self {
        Self::IoError(err)
    }
}

impl From<toml::de::Error> for ConfigError {
    fn from(err: toml::de::Error) -> Self {
        Self::ParseError(err)
    }
}

/// TOML representation of display settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlDisplaySettings {
    width: Option<u32>,
    height: Option<u32>,
    fullscreen: Option<bool>,
    background_color: Option<String>,
    font_size: Option<f32>,
    bloom_enabled: Option<bool>,
    bloom_intensity: Option<f32>,
    shadows_enabled: Option<bool>,
}

/// TOML representation of playback settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlPlaybackSettings {
    seconds_per_day: Option<f32>,
    auto_skip_seconds: Option<f32>,
    start_timestamp: Option<i64>,
    stop_timestamp: Option<i64>,
    loop_playback: Option<bool>,
    start_paused: Option<bool>,
    time_scale: Option<f32>,
    stop_at_time: Option<f32>,
    realtime: Option<bool>,
}

/// TOML representation of visibility settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlVisibilitySettings {
    hide_filenames: Option<bool>,
    hide_usernames: Option<bool>,
    hide_date: Option<bool>,
    hide_progress: Option<bool>,
    hide_legend: Option<bool>,
    hide_dirnames: Option<bool>,
    hide_root: Option<bool>,
    hide_tree: Option<bool>,
    hide_bloom: Option<bool>,
    hide_mouse: Option<bool>,
    show_fps: Option<bool>,
}

/// TOML representation of limit settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlLimitSettings {
    max_files: Option<usize>,
    max_users: Option<usize>,
    file_idle_time: Option<f32>,
    user_idle_time: Option<f32>,
}

/// TOML representation of camera settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlCameraSettings {
    mode: Option<String>,
    min_zoom: Option<f32>,
    max_zoom: Option<f32>,
    smoothness: Option<f32>,
    padding: Option<f32>,
    follow_user: Option<String>,
    highlight_users: Option<String>,
    highlight_all_users: Option<bool>,
    enable_3d: Option<bool>,
    pitch: Option<f32>,
    rotation_speed: Option<f32>,
    disable_auto_rotate: Option<bool>,
}

/// TOML representation of input settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlInputSettings {
    disable_input: Option<bool>,
    mouse_sensitivity: Option<f32>,
}

/// TOML representation of export settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlExportSettings {
    output_path: Option<String>,
    framerate: Option<u32>,
    screenshot_path: Option<String>,
}

/// TOML representation of title settings.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlTitleSettings {
    title: Option<String>,
    title_font_size: Option<f32>,
    title_color: Option<String>,
}

/// Root TOML configuration structure.
#[derive(Debug, Deserialize, Default)]
#[serde(default)]
struct TomlConfig {
    display: TomlDisplaySettings,
    playback: TomlPlaybackSettings,
    visibility: TomlVisibilitySettings,
    limits: TomlLimitSettings,
    camera: TomlCameraSettings,
    input: TomlInputSettings,
    export: TomlExportSettings,
    title: TomlTitleSettings,
}

/// Parse a hex color string (e.g., "#FFFFFF" or "FFFFFF") to a Color.
fn parse_hex_color(s: &str) -> Result<Color, ConfigError> {
    let hex = s.trim_start_matches('#');
    if hex.len() != 6 {
        return Err(ConfigError::ValidationError(format!(
            "Invalid color format: '{s}'. Expected 6-digit hex (e.g., #FFFFFF)"
        )));
    }

    let r = u8::from_str_radix(&hex[0..2], 16).map_err(|_| {
        ConfigError::ValidationError(format!("Invalid red component in color: '{s}'"))
    })?;
    let g = u8::from_str_radix(&hex[2..4], 16).map_err(|_| {
        ConfigError::ValidationError(format!("Invalid green component in color: '{s}'"))
    })?;
    let b = u8::from_str_radix(&hex[4..6], 16).map_err(|_| {
        ConfigError::ValidationError(format!("Invalid blue component in color: '{s}'"))
    })?;

    Ok(Color::from_rgb8(r, g, b))
}

impl TomlConfig {
    /// Convert to Settings, using defaults for any missing values.
    #[allow(clippy::too_many_lines)]
    fn to_settings(&self) -> Result<Settings, ConfigError> {
        let defaults = Settings::default();

        // Display settings
        let display = DisplaySettings {
            width: self.display.width.unwrap_or(defaults.display.width),
            height: self.display.height.unwrap_or(defaults.display.height),
            fullscreen: self
                .display
                .fullscreen
                .unwrap_or(defaults.display.fullscreen),
            background_color: self
                .display
                .background_color
                .as_ref()
                .map(|s| parse_hex_color(s))
                .transpose()?
                .unwrap_or(defaults.display.background_color),
            font_size: self.display.font_size.unwrap_or(defaults.display.font_size),
            bloom_enabled: self
                .display
                .bloom_enabled
                .unwrap_or(defaults.display.bloom_enabled),
            bloom_intensity: self
                .display
                .bloom_intensity
                .unwrap_or(defaults.display.bloom_intensity),
            shadows_enabled: self
                .display
                .shadows_enabled
                .unwrap_or(defaults.display.shadows_enabled),
        };

        // Playback settings
        let playback = PlaybackSettings {
            seconds_per_day: self
                .playback
                .seconds_per_day
                .unwrap_or(defaults.playback.seconds_per_day),
            auto_skip_seconds: self
                .playback
                .auto_skip_seconds
                .unwrap_or(defaults.playback.auto_skip_seconds),
            start_timestamp: self
                .playback
                .start_timestamp
                .or(defaults.playback.start_timestamp),
            stop_timestamp: self
                .playback
                .stop_timestamp
                .or(defaults.playback.stop_timestamp),
            loop_playback: self
                .playback
                .loop_playback
                .unwrap_or(defaults.playback.loop_playback),
            start_paused: self
                .playback
                .start_paused
                .unwrap_or(defaults.playback.start_paused),
            time_scale: self
                .playback
                .time_scale
                .unwrap_or(defaults.playback.time_scale),
            stop_at_time: self
                .playback
                .stop_at_time
                .or(defaults.playback.stop_at_time),
            realtime: self.playback.realtime.unwrap_or(defaults.playback.realtime),
        };

        // Visibility settings
        let visibility = VisibilitySettings {
            hide_filenames: self
                .visibility
                .hide_filenames
                .unwrap_or(defaults.visibility.hide_filenames),
            hide_usernames: self
                .visibility
                .hide_usernames
                .unwrap_or(defaults.visibility.hide_usernames),
            hide_date: self
                .visibility
                .hide_date
                .unwrap_or(defaults.visibility.hide_date),
            hide_progress: self
                .visibility
                .hide_progress
                .unwrap_or(defaults.visibility.hide_progress),
            hide_legend: self
                .visibility
                .hide_legend
                .unwrap_or(defaults.visibility.hide_legend),
            hide_dirnames: self
                .visibility
                .hide_dirnames
                .unwrap_or(defaults.visibility.hide_dirnames),
            hide_root: self
                .visibility
                .hide_root
                .unwrap_or(defaults.visibility.hide_root),
            hide_tree: self
                .visibility
                .hide_tree
                .unwrap_or(defaults.visibility.hide_tree),
            hide_bloom: self
                .visibility
                .hide_bloom
                .unwrap_or(defaults.visibility.hide_bloom),
            hide_mouse: self
                .visibility
                .hide_mouse
                .unwrap_or(defaults.visibility.hide_mouse),
            show_fps: self
                .visibility
                .show_fps
                .unwrap_or(defaults.visibility.show_fps),
        };

        // Limit settings
        let limits = LimitSettings {
            max_files: self.limits.max_files.unwrap_or(defaults.limits.max_files),
            max_users: self.limits.max_users.unwrap_or(defaults.limits.max_users),
            file_idle_time: self
                .limits
                .file_idle_time
                .unwrap_or(defaults.limits.file_idle_time),
            user_idle_time: self
                .limits
                .user_idle_time
                .unwrap_or(defaults.limits.user_idle_time),
        };

        // Camera settings
        let camera = CameraSettings {
            mode: self
                .camera
                .mode
                .as_ref()
                .map_or(defaults.camera.mode, |s| CameraModeSetting::parse(s)),
            min_zoom: self.camera.min_zoom.unwrap_or(defaults.camera.min_zoom),
            max_zoom: self.camera.max_zoom.unwrap_or(defaults.camera.max_zoom),
            smoothness: self.camera.smoothness.unwrap_or(defaults.camera.smoothness),
            padding: self.camera.padding.unwrap_or(defaults.camera.padding),
            follow_user: self
                .camera
                .follow_user
                .clone()
                .or(defaults.camera.follow_user),
            highlight_users: self
                .camera
                .highlight_users
                .clone()
                .or(defaults.camera.highlight_users),
            highlight_all_users: self
                .camera
                .highlight_all_users
                .unwrap_or(defaults.camera.highlight_all_users),
            enable_3d: self.camera.enable_3d.unwrap_or(defaults.camera.enable_3d),
            pitch: self.camera.pitch.unwrap_or(defaults.camera.pitch),
            rotation_speed: self
                .camera
                .rotation_speed
                .unwrap_or(defaults.camera.rotation_speed),
            disable_auto_rotate: self
                .camera
                .disable_auto_rotate
                .unwrap_or(defaults.camera.disable_auto_rotate),
        };

        // Input settings
        let input = InputSettings {
            disable_input: self
                .input
                .disable_input
                .unwrap_or(defaults.input.disable_input),
            mouse_sensitivity: self
                .input
                .mouse_sensitivity
                .unwrap_or(defaults.input.mouse_sensitivity),
        };

        // Export settings
        let export = ExportSettings {
            output_path: self
                .export
                .output_path
                .clone()
                .or(defaults.export.output_path),
            framerate: self.export.framerate.unwrap_or(defaults.export.framerate),
            screenshot_path: self
                .export
                .screenshot_path
                .clone()
                .or(defaults.export.screenshot_path),
        };

        // Title settings
        let title = TitleSettings {
            title: self.title.title.clone().or(defaults.title.title),
            title_font_size: self
                .title
                .title_font_size
                .unwrap_or(defaults.title.title_font_size),
            title_color: self
                .title
                .title_color
                .as_ref()
                .map(|s| parse_hex_color(s))
                .transpose()?
                .unwrap_or(defaults.title.title_color),
        };

        // Directory settings (using defaults for now - can be extended in config format)
        let directory = defaults.directory;

        // Overlay settings (using defaults for now - can be extended in config format)
        let overlay = defaults.overlay;

        Ok(Settings {
            display,
            playback,
            visibility,
            limits,
            camera,
            input,
            export,
            title,
            directory,
            overlay,
            filter: FilterSettings::default(),
            layout: LayoutSettings::default(),
        })
    }
}

/// Load settings from a TOML configuration file.
///
/// # Arguments
///
/// * `path` - Path to the TOML configuration file.
///
/// # Returns
///
/// Returns `Settings` populated from the configuration file, with defaults
/// for any missing values.
///
/// # Errors
///
/// Returns an error if the file cannot be read or parsed.
pub fn load_config_file<P: AsRef<Path>>(path: P) -> Result<Settings, ConfigError> {
    let content = std::fs::read_to_string(path)?;
    parse_config(&content)
}

/// Parse a TOML configuration string into Settings.
///
/// # Arguments
///
/// * `content` - TOML configuration content.
///
/// # Returns
///
/// Returns `Settings` populated from the TOML content.
///
/// # Errors
///
/// Returns an error if the TOML cannot be parsed.
pub fn parse_config(content: &str) -> Result<Settings, ConfigError> {
    let config: TomlConfig = toml::from_str(content)?;
    let settings = config.to_settings()?;

    // Validate the resulting settings
    let errors = settings.validate();
    if !errors.is_empty() {
        return Err(ConfigError::ValidationError(errors.join("; ")));
    }

    Ok(settings)
}

/// Merge settings from a config file with existing settings.
///
/// Values from the config file override the base settings.
/// This is useful for layering: defaults -> config file -> CLI args.
///
/// # Arguments
///
/// * `base` - Base settings to start from.
/// * `path` - Path to the TOML configuration file.
///
/// # Returns
///
/// Returns merged settings.
#[allow(clippy::too_many_lines)]
pub fn merge_config_file<P: AsRef<Path>>(base: Settings, path: P) -> Result<Settings, ConfigError> {
    let content = std::fs::read_to_string(path)?;
    let config: TomlConfig = toml::from_str(&content)?;

    // Only override values that are explicitly set in the config file
    let display = DisplaySettings {
        width: config.display.width.unwrap_or(base.display.width),
        height: config.display.height.unwrap_or(base.display.height),
        fullscreen: config.display.fullscreen.unwrap_or(base.display.fullscreen),
        background_color: config
            .display
            .background_color
            .as_ref()
            .map(|s| parse_hex_color(s))
            .transpose()?
            .unwrap_or(base.display.background_color),
        font_size: config.display.font_size.unwrap_or(base.display.font_size),
        bloom_enabled: config
            .display
            .bloom_enabled
            .unwrap_or(base.display.bloom_enabled),
        bloom_intensity: config
            .display
            .bloom_intensity
            .unwrap_or(base.display.bloom_intensity),
        shadows_enabled: config
            .display
            .shadows_enabled
            .unwrap_or(base.display.shadows_enabled),
    };

    let playback = PlaybackSettings {
        seconds_per_day: config
            .playback
            .seconds_per_day
            .unwrap_or(base.playback.seconds_per_day),
        auto_skip_seconds: config
            .playback
            .auto_skip_seconds
            .unwrap_or(base.playback.auto_skip_seconds),
        start_timestamp: config
            .playback
            .start_timestamp
            .or(base.playback.start_timestamp),
        stop_timestamp: config
            .playback
            .stop_timestamp
            .or(base.playback.stop_timestamp),
        loop_playback: config
            .playback
            .loop_playback
            .unwrap_or(base.playback.loop_playback),
        start_paused: config
            .playback
            .start_paused
            .unwrap_or(base.playback.start_paused),
        time_scale: config
            .playback
            .time_scale
            .unwrap_or(base.playback.time_scale),
        stop_at_time: config.playback.stop_at_time.or(base.playback.stop_at_time),
        realtime: config.playback.realtime.unwrap_or(base.playback.realtime),
    };

    let visibility = VisibilitySettings {
        hide_filenames: config
            .visibility
            .hide_filenames
            .unwrap_or(base.visibility.hide_filenames),
        hide_usernames: config
            .visibility
            .hide_usernames
            .unwrap_or(base.visibility.hide_usernames),
        hide_date: config
            .visibility
            .hide_date
            .unwrap_or(base.visibility.hide_date),
        hide_progress: config
            .visibility
            .hide_progress
            .unwrap_or(base.visibility.hide_progress),
        hide_legend: config
            .visibility
            .hide_legend
            .unwrap_or(base.visibility.hide_legend),
        hide_dirnames: config
            .visibility
            .hide_dirnames
            .unwrap_or(base.visibility.hide_dirnames),
        hide_root: config
            .visibility
            .hide_root
            .unwrap_or(base.visibility.hide_root),
        hide_tree: config
            .visibility
            .hide_tree
            .unwrap_or(base.visibility.hide_tree),
        hide_bloom: config
            .visibility
            .hide_bloom
            .unwrap_or(base.visibility.hide_bloom),
        hide_mouse: config
            .visibility
            .hide_mouse
            .unwrap_or(base.visibility.hide_mouse),
        show_fps: config
            .visibility
            .show_fps
            .unwrap_or(base.visibility.show_fps),
    };

    let limits = LimitSettings {
        max_files: config.limits.max_files.unwrap_or(base.limits.max_files),
        max_users: config.limits.max_users.unwrap_or(base.limits.max_users),
        file_idle_time: config
            .limits
            .file_idle_time
            .unwrap_or(base.limits.file_idle_time),
        user_idle_time: config
            .limits
            .user_idle_time
            .unwrap_or(base.limits.user_idle_time),
    };

    let camera = CameraSettings {
        mode: config
            .camera
            .mode
            .as_ref()
            .map_or(base.camera.mode, |s| CameraModeSetting::parse(s)),
        min_zoom: config.camera.min_zoom.unwrap_or(base.camera.min_zoom),
        max_zoom: config.camera.max_zoom.unwrap_or(base.camera.max_zoom),
        smoothness: config.camera.smoothness.unwrap_or(base.camera.smoothness),
        padding: config.camera.padding.unwrap_or(base.camera.padding),
        follow_user: config
            .camera
            .follow_user
            .clone()
            .or(base.camera.follow_user),
        highlight_users: config
            .camera
            .highlight_users
            .clone()
            .or(base.camera.highlight_users),
        highlight_all_users: config
            .camera
            .highlight_all_users
            .unwrap_or(base.camera.highlight_all_users),
        enable_3d: config.camera.enable_3d.unwrap_or(base.camera.enable_3d),
        pitch: config.camera.pitch.unwrap_or(base.camera.pitch),
        rotation_speed: config
            .camera
            .rotation_speed
            .unwrap_or(base.camera.rotation_speed),
        disable_auto_rotate: config
            .camera
            .disable_auto_rotate
            .unwrap_or(base.camera.disable_auto_rotate),
    };

    let input = InputSettings {
        disable_input: config
            .input
            .disable_input
            .unwrap_or(base.input.disable_input),
        mouse_sensitivity: config
            .input
            .mouse_sensitivity
            .unwrap_or(base.input.mouse_sensitivity),
    };

    let export = ExportSettings {
        output_path: config
            .export
            .output_path
            .clone()
            .or(base.export.output_path),
        framerate: config.export.framerate.unwrap_or(base.export.framerate),
        screenshot_path: config
            .export
            .screenshot_path
            .clone()
            .or(base.export.screenshot_path),
    };

    let title = TitleSettings {
        title: config.title.title.clone().or(base.title.title),
        title_font_size: config
            .title
            .title_font_size
            .unwrap_or(base.title.title_font_size),
        title_color: config
            .title
            .title_color
            .as_ref()
            .map(|s| parse_hex_color(s))
            .transpose()?
            .unwrap_or(base.title.title_color),
    };

    // Directory and overlay settings from base (not yet supported in config file format)
    let directory = base.directory;
    let overlay = base.overlay;

    let settings = Settings {
        display,
        playback,
        visibility,
        limits,
        camera,
        input,
        export,
        title,
        directory,
        overlay,
        filter: FilterSettings::default(),
        layout: LayoutSettings::default(),
    };

    let errors = settings.validate();
    if !errors.is_empty() {
        return Err(ConfigError::ValidationError(errors.join("; ")));
    }

    Ok(settings)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty_config() {
        let config = "";
        let settings = parse_config(config).unwrap();
        assert_eq!(settings.display.width, 1280);
        assert_eq!(settings.display.height, 720);
    }

    #[test]
    fn test_parse_display_settings() {
        let config = r"
            [display]
            width = 1920
            height = 1080
            fullscreen = true
            bloom_enabled = false
        ";
        let settings = parse_config(config).unwrap();
        assert_eq!(settings.display.width, 1920);
        assert_eq!(settings.display.height, 1080);
        assert!(settings.display.fullscreen);
        assert!(!settings.display.bloom_enabled);
    }

    #[test]
    fn test_parse_hex_color() {
        let color = parse_hex_color("#FF0000").unwrap();
        assert!((color.r - 1.0).abs() < 0.01);
        assert!(color.g.abs() < 0.01);
        assert!(color.b.abs() < 0.01);

        let color = parse_hex_color("00FF00").unwrap();
        assert!(color.r.abs() < 0.01);
        assert!((color.g - 1.0).abs() < 0.01);
        assert!(color.b.abs() < 0.01);
    }

    #[test]
    fn test_parse_invalid_color() {
        assert!(parse_hex_color("invalid").is_err());
        assert!(parse_hex_color("#FFF").is_err());
    }

    #[test]
    fn test_parse_playback_settings() {
        let config = r"
            [playback]
            seconds_per_day = 5.0
            loop_playback = true
            start_paused = true
        ";
        let settings = parse_config(config).unwrap();
        assert!((settings.playback.seconds_per_day - 5.0).abs() < 0.01);
        assert!(settings.playback.loop_playback);
        assert!(settings.playback.start_paused);
    }

    #[test]
    fn test_parse_camera_settings() {
        let config = r#"
            [camera]
            mode = "track"
            min_zoom = 0.1
            max_zoom = 5.0
        "#;
        let settings = parse_config(config).unwrap();
        assert_eq!(settings.camera.mode, CameraModeSetting::Track);
        assert!((settings.camera.min_zoom - 0.1).abs() < 0.01);
        assert!((settings.camera.max_zoom - 5.0).abs() < 0.01);
    }

    #[test]
    fn test_parse_visibility_settings() {
        let config = r"
            [visibility]
            hide_filenames = true
            hide_usernames = true
            show_fps = true
        ";
        let settings = parse_config(config).unwrap();
        assert!(settings.visibility.hide_filenames);
        assert!(settings.visibility.hide_usernames);
        assert!(settings.visibility.show_fps);
    }

    #[test]
    fn test_parse_title_settings() {
        let config = r##"
            [title]
            title = "My Project"
            title_font_size = 32.0
            title_color = "#FF5500"
        "##;
        let settings = parse_config(config).unwrap();
        assert_eq!(settings.title.title, Some("My Project".to_string()));
        assert!((settings.title.title_font_size - 32.0).abs() < 0.01);
    }

    #[test]
    fn test_parse_complete_config() {
        let config = r##"
            [display]
            width = 1920
            height = 1080
            background_color = "#1A1A2E"
            bloom_enabled = true
            bloom_intensity = 0.8

            [playback]
            seconds_per_day = 2.0
            auto_skip_seconds = 1.0

            [camera]
            mode = "overview"
            padding = 150.0

            [title]
            title = "Rource Demo"
        "##;
        let settings = parse_config(config).unwrap();
        assert_eq!(settings.display.width, 1920);
        assert!((settings.playback.seconds_per_day - 2.0).abs() < 0.01);
        assert_eq!(settings.title.title, Some("Rource Demo".to_string()));
    }

    #[test]
    fn test_invalid_toml() {
        let config = "not valid toml [[[";
        assert!(parse_config(config).is_err());
    }

    #[test]
    fn test_validation_error() {
        let config = r"
            [display]
            width = 0
        ";
        let result = parse_config(config);
        assert!(result.is_err());
        if let Err(ConfigError::ValidationError(msg)) = result {
            assert!(msg.contains("width"));
        } else {
            panic!("Expected validation error");
        }
    }
}
