//! Environment variable configuration for Rource.
//!
//! This module allows configuring Rource via environment variables with the `ROURCE_` prefix.
//! Environment variables provide a convenient way to configure Rource in CI/CD pipelines,
//! containers, and scripts without needing config files.
//!
//! # Environment Variables
//!
//! All environment variables use the `ROURCE_` prefix. Boolean values accept:
//! - True: `1`, `true`, `yes`, `on`
//! - False: `0`, `false`, `no`, `off`
//!
//! ## Display Settings
//! - `ROURCE_WIDTH` - Window width in pixels (default: 1280)
//! - `ROURCE_HEIGHT` - Window height in pixels (default: 720)
//! - `ROURCE_FULLSCREEN` - Run in fullscreen mode (default: false)
//! - `ROURCE_BACKGROUND_COLOR` - Background color as hex (default: #000000)
//! - `ROURCE_FONT_SIZE` - Font size for labels (default: 12.0)
//! - `ROURCE_BLOOM_ENABLED` - Enable bloom/glow effect (default: true)
//! - `ROURCE_BLOOM_INTENSITY` - Bloom intensity 0.0-2.0 (default: 1.0)
//! - `ROURCE_SHADOWS_ENABLED` - Enable drop shadows (default: false)
//!
//! ## Playback Settings
//! - `ROURCE_SECONDS_PER_DAY` - Real seconds per day of history (default: 10.0)
//! - `ROURCE_AUTO_SKIP_SECONDS` - Seconds before auto-skipping idle (default: 3.0)
//! - `ROURCE_START_TIMESTAMP` - Unix timestamp to start from
//! - `ROURCE_STOP_TIMESTAMP` - Unix timestamp to stop at
//! - `ROURCE_LOOP_PLAYBACK` - Loop when reaching end (default: false)
//! - `ROURCE_START_PAUSED` - Start in paused state (default: false)
//!
//! ## Visibility Settings
//! - `ROURCE_HIDE_FILENAMES` - Hide file names (default: false)
//! - `ROURCE_HIDE_USERNAMES` - Hide user names (default: false)
//! - `ROURCE_HIDE_DATE` - Hide date display (default: false)
//! - `ROURCE_HIDE_PROGRESS` - Hide progress bar (default: false)
//! - `ROURCE_HIDE_LEGEND` - Hide file extension legend (default: false)
//! - `ROURCE_SHOW_FPS` - Show FPS counter (default: false)
//!
//! ## Limit Settings
//! - `ROURCE_MAX_FILES` - Maximum files to display, 0=unlimited (default: 0)
//! - `ROURCE_MAX_USERS` - Maximum users to display, 0=unlimited (default: 0)
//! - `ROURCE_FILE_IDLE_TIME` - Seconds before files fade out (default: 60.0)
//! - `ROURCE_USER_IDLE_TIME` - Seconds before users fade out (default: 10.0)
//!
//! ## Camera Settings
//! - `ROURCE_CAMERA_MODE` - Camera mode: overview, track, follow (default: overview)
//! - `ROURCE_MIN_ZOOM` - Minimum zoom level (default: 0.01)
//! - `ROURCE_MAX_ZOOM` - Maximum zoom level (default: 10.0)
//! - `ROURCE_CAMERA_SMOOTHNESS` - Camera smoothness 0.0-1.0 (default: 0.85)
//! - `ROURCE_CAMERA_PADDING` - Padding when auto-fitting (default: 100.0)
//!
//! ## Input Settings
//! - `ROURCE_DISABLE_INPUT` - Disable all user input (default: false)
//! - `ROURCE_MOUSE_SENSITIVITY` - Mouse sensitivity (default: 1.0)
//!
//! ## Export Settings
//! - `ROURCE_OUTPUT_PATH` - Output path for video frames
//! - `ROURCE_FRAMERATE` - Video export framerate (default: 60)
//! - `ROURCE_SCREENSHOT_PATH` - Screenshot output path
//!
//! ## Title Settings
//! - `ROURCE_TITLE` - Title to display
//! - `ROURCE_TITLE_FONT_SIZE` - Title font size (default: 24.0)
//! - `ROURCE_TITLE_COLOR` - Title color as hex (default: #FFFFFF)
//!
//! ## Filter Settings
//! - `ROURCE_SHOW_USERS` - Regex pattern for users to show
//! - `ROURCE_HIDE_USERS` - Regex pattern for users to hide
//! - `ROURCE_SHOW_FILES` - Regex pattern for files to show
//! - `ROURCE_HIDE_FILES` - Regex pattern for files to hide
//! - `ROURCE_HIDE_DIRS` - Regex pattern for directories to hide
//!
//! # Example
//!
//! ```bash
//! export ROURCE_WIDTH=1920
//! export ROURCE_HEIGHT=1080
//! export ROURCE_BLOOM_ENABLED=true
//! export ROURCE_SECONDS_PER_DAY=5.0
//! export ROURCE_TITLE="My Project"
//! rource /path/to/repo
//! ```
//!
//! # Usage
//!
//! ```ignore
//! use rource_core::config::{load_env, merge_env, Settings};
//!
//! // Load settings from environment only
//! let settings = load_env();
//!
//! // Or merge environment with existing settings
//! let base = Settings::default();
//! let settings = merge_env(base);
//! ```

use crate::config::{
    CameraModeSetting, CameraSettings, DisplaySettings, ExportSettings, InputSettings,
    LimitSettings, PlaybackSettings, Settings, TitleSettings, VisibilitySettings,
};
use rource_math::Color;
use std::env;

/// Prefix for all Rource environment variables.
const ENV_PREFIX: &str = "ROURCE_";

/// Read an environment variable with the ROURCE_ prefix.
fn read_env(name: &str) -> Option<String> {
    env::var(format!("{ENV_PREFIX}{name}")).ok()
}

/// Parse a boolean from an environment variable value.
///
/// Accepts: 1, true, yes, on (case-insensitive) for true.
/// Accepts: 0, false, no, off (case-insensitive) for false.
fn parse_bool(value: &str) -> Option<bool> {
    match value.to_lowercase().as_str() {
        "1" | "true" | "yes" | "on" => Some(true),
        "0" | "false" | "no" | "off" => Some(false),
        _ => None,
    }
}

/// Parse a hex color string (e.g., "#FFFFFF" or "FFFFFF") to a Color.
fn parse_hex_color(s: &str) -> Option<Color> {
    let hex = s.trim_start_matches('#');
    if hex.len() != 6 {
        return None;
    }

    let r = u8::from_str_radix(&hex[0..2], 16).ok()?;
    let g = u8::from_str_radix(&hex[2..4], 16).ok()?;
    let b = u8::from_str_radix(&hex[4..6], 16).ok()?;

    Some(Color::from_rgb8(r, g, b))
}

/// Load settings from environment variables.
///
/// Returns a `Settings` struct with values from environment variables,
/// falling back to defaults for any unset variables.
///
/// # Example
///
/// ```ignore
/// use rource_core::config::load_env;
///
/// std::env::set_var("ROURCE_WIDTH", "1920");
/// std::env::set_var("ROURCE_HEIGHT", "1080");
///
/// let settings = load_env();
/// assert_eq!(settings.display.width, 1920);
/// ```
#[must_use]
pub fn load_env() -> Settings {
    merge_env(Settings::default())
}

/// Merge environment variables with existing settings.
///
/// Environment variables override the corresponding values in `base`.
/// This allows layering: defaults -> config file -> env vars -> CLI args.
///
/// # Arguments
///
/// * `base` - Base settings to start from.
///
/// # Returns
///
/// Returns settings with environment variable overrides applied.
///
/// # Example
///
/// ```ignore
/// use rource_core::config::{merge_env, Settings};
///
/// std::env::set_var("ROURCE_BLOOM_ENABLED", "false");
///
/// let base = Settings::default();
/// let settings = merge_env(base);
/// assert!(!settings.display.bloom_enabled);
/// ```
#[must_use]
#[allow(clippy::too_many_lines)] // Config merging intentionally handles all settings in one function
pub fn merge_env(base: Settings) -> Settings {
    // Display settings
    let display = DisplaySettings {
        width: read_env("WIDTH")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.display.width),
        height: read_env("HEIGHT")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.display.height),
        fullscreen: read_env("FULLSCREEN")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.display.fullscreen),
        background_color: read_env("BACKGROUND_COLOR")
            .and_then(|v| parse_hex_color(&v))
            .unwrap_or(base.display.background_color),
        font_size: read_env("FONT_SIZE")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.display.font_size),
        bloom_enabled: read_env("BLOOM_ENABLED")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.display.bloom_enabled),
        bloom_intensity: read_env("BLOOM_INTENSITY")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.display.bloom_intensity),
        shadows_enabled: read_env("SHADOWS_ENABLED")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.display.shadows_enabled),
    };

    // Playback settings
    let playback = PlaybackSettings {
        seconds_per_day: read_env("SECONDS_PER_DAY")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.playback.seconds_per_day),
        auto_skip_seconds: read_env("AUTO_SKIP_SECONDS")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.playback.auto_skip_seconds),
        start_timestamp: read_env("START_TIMESTAMP")
            .and_then(|v| v.parse().ok())
            .or(base.playback.start_timestamp),
        stop_timestamp: read_env("STOP_TIMESTAMP")
            .and_then(|v| v.parse().ok())
            .or(base.playback.stop_timestamp),
        loop_playback: read_env("LOOP_PLAYBACK")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.playback.loop_playback),
        start_paused: read_env("START_PAUSED")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.playback.start_paused),
    };

    // Visibility settings
    let visibility = VisibilitySettings {
        hide_filenames: read_env("HIDE_FILENAMES")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.visibility.hide_filenames),
        hide_usernames: read_env("HIDE_USERNAMES")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.visibility.hide_usernames),
        hide_date: read_env("HIDE_DATE")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.visibility.hide_date),
        hide_progress: read_env("HIDE_PROGRESS")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.visibility.hide_progress),
        hide_legend: read_env("HIDE_LEGEND")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.visibility.hide_legend),
        show_fps: read_env("SHOW_FPS")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.visibility.show_fps),
    };

    // Limit settings
    let limits = LimitSettings {
        max_files: read_env("MAX_FILES")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.limits.max_files),
        max_users: read_env("MAX_USERS")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.limits.max_users),
        file_idle_time: read_env("FILE_IDLE_TIME")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.limits.file_idle_time),
        user_idle_time: read_env("USER_IDLE_TIME")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.limits.user_idle_time),
    };

    // Camera settings
    let camera = CameraSettings {
        mode: read_env("CAMERA_MODE")
            .map_or(base.camera.mode, |v| CameraModeSetting::parse(&v)),
        min_zoom: read_env("MIN_ZOOM")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.camera.min_zoom),
        max_zoom: read_env("MAX_ZOOM")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.camera.max_zoom),
        smoothness: read_env("CAMERA_SMOOTHNESS")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.camera.smoothness),
        padding: read_env("CAMERA_PADDING")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.camera.padding),
    };

    // Input settings
    let input = InputSettings {
        disable_input: read_env("DISABLE_INPUT")
            .and_then(|v| parse_bool(&v))
            .unwrap_or(base.input.disable_input),
        mouse_sensitivity: read_env("MOUSE_SENSITIVITY")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.input.mouse_sensitivity),
    };

    // Export settings
    let export = ExportSettings {
        output_path: read_env("OUTPUT_PATH").or(base.export.output_path),
        framerate: read_env("FRAMERATE")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.export.framerate),
        screenshot_path: read_env("SCREENSHOT_PATH").or(base.export.screenshot_path),
    };

    // Title settings
    let title = TitleSettings {
        title: read_env("TITLE").or(base.title.title),
        title_font_size: read_env("TITLE_FONT_SIZE")
            .and_then(|v| v.parse().ok())
            .unwrap_or(base.title.title_font_size),
        title_color: read_env("TITLE_COLOR")
            .and_then(|v| parse_hex_color(&v))
            .unwrap_or(base.title.title_color),
    };

    // Filter settings
    let mut filter = base.filter;
    if let Some(pattern) = read_env("SHOW_USERS") {
        filter.set_show_users(Some(pattern));
    }
    if let Some(pattern) = read_env("HIDE_USERS") {
        filter.set_hide_users(Some(pattern));
    }
    if let Some(pattern) = read_env("SHOW_FILES") {
        filter.set_show_files(Some(pattern));
    }
    if let Some(pattern) = read_env("HIDE_FILES") {
        filter.set_hide_files(Some(pattern));
    }
    if let Some(pattern) = read_env("HIDE_DIRS") {
        filter.set_hide_dirs(Some(pattern));
    }

    Settings {
        display,
        playback,
        visibility,
        limits,
        camera,
        input,
        export,
        title,
        filter,
    }
}

/// Returns a list of all recognized environment variable names.
///
/// Useful for documentation and debugging.
#[must_use]
pub fn env_var_names() -> Vec<&'static str> {
    vec![
        "ROURCE_WIDTH",
        "ROURCE_HEIGHT",
        "ROURCE_FULLSCREEN",
        "ROURCE_BACKGROUND_COLOR",
        "ROURCE_FONT_SIZE",
        "ROURCE_BLOOM_ENABLED",
        "ROURCE_BLOOM_INTENSITY",
        "ROURCE_SHADOWS_ENABLED",
        "ROURCE_SECONDS_PER_DAY",
        "ROURCE_AUTO_SKIP_SECONDS",
        "ROURCE_START_TIMESTAMP",
        "ROURCE_STOP_TIMESTAMP",
        "ROURCE_LOOP_PLAYBACK",
        "ROURCE_START_PAUSED",
        "ROURCE_HIDE_FILENAMES",
        "ROURCE_HIDE_USERNAMES",
        "ROURCE_HIDE_DATE",
        "ROURCE_HIDE_PROGRESS",
        "ROURCE_HIDE_LEGEND",
        "ROURCE_SHOW_FPS",
        "ROURCE_MAX_FILES",
        "ROURCE_MAX_USERS",
        "ROURCE_FILE_IDLE_TIME",
        "ROURCE_USER_IDLE_TIME",
        "ROURCE_CAMERA_MODE",
        "ROURCE_MIN_ZOOM",
        "ROURCE_MAX_ZOOM",
        "ROURCE_CAMERA_SMOOTHNESS",
        "ROURCE_CAMERA_PADDING",
        "ROURCE_DISABLE_INPUT",
        "ROURCE_MOUSE_SENSITIVITY",
        "ROURCE_OUTPUT_PATH",
        "ROURCE_FRAMERATE",
        "ROURCE_SCREENSHOT_PATH",
        "ROURCE_TITLE",
        "ROURCE_TITLE_FONT_SIZE",
        "ROURCE_TITLE_COLOR",
        "ROURCE_SHOW_USERS",
        "ROURCE_HIDE_USERS",
        "ROURCE_SHOW_FILES",
        "ROURCE_HIDE_FILES",
        "ROURCE_HIDE_DIRS",
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Use a mutex to ensure env var tests don't interfere with each other
    static ENV_MUTEX: Mutex<()> = Mutex::new(());

    fn with_env<F, R>(vars: &[(&str, &str)], f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let _guard = ENV_MUTEX.lock().unwrap();

        // Set environment variables
        for (key, value) in vars {
            env::set_var(format!("{ENV_PREFIX}{key}"), value);
        }

        let result = f();

        // Clean up environment variables
        for (key, _) in vars {
            env::remove_var(format!("{ENV_PREFIX}{key}"));
        }

        result
    }

    #[test]
    fn test_load_env_defaults() {
        let _guard = ENV_MUTEX.lock().unwrap();
        // Clear any existing ROURCE_ vars
        for name in env_var_names() {
            env::remove_var(name);
        }

        let settings = load_env();
        assert_eq!(settings.display.width, 1280);
        assert_eq!(settings.display.height, 720);
        assert!(settings.display.bloom_enabled);
    }

    #[test]
    fn test_load_env_display() {
        with_env(&[("WIDTH", "1920"), ("HEIGHT", "1080")], || {
            let settings = load_env();
            assert_eq!(settings.display.width, 1920);
            assert_eq!(settings.display.height, 1080);
        });
    }

    #[test]
    fn test_parse_bool_true() {
        assert_eq!(parse_bool("1"), Some(true));
        assert_eq!(parse_bool("true"), Some(true));
        assert_eq!(parse_bool("TRUE"), Some(true));
        assert_eq!(parse_bool("yes"), Some(true));
        assert_eq!(parse_bool("YES"), Some(true));
        assert_eq!(parse_bool("on"), Some(true));
        assert_eq!(parse_bool("ON"), Some(true));
    }

    #[test]
    fn test_parse_bool_false() {
        assert_eq!(parse_bool("0"), Some(false));
        assert_eq!(parse_bool("false"), Some(false));
        assert_eq!(parse_bool("FALSE"), Some(false));
        assert_eq!(parse_bool("no"), Some(false));
        assert_eq!(parse_bool("NO"), Some(false));
        assert_eq!(parse_bool("off"), Some(false));
        assert_eq!(parse_bool("OFF"), Some(false));
    }

    #[test]
    fn test_parse_bool_invalid() {
        assert_eq!(parse_bool("maybe"), None);
        assert_eq!(parse_bool(""), None);
        assert_eq!(parse_bool("2"), None);
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

        let color = parse_hex_color("#0000FF").unwrap();
        assert!(color.r.abs() < 0.01);
        assert!(color.g.abs() < 0.01);
        assert!((color.b - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_parse_hex_color_invalid() {
        assert!(parse_hex_color("invalid").is_none());
        assert!(parse_hex_color("#FFF").is_none());
        assert!(parse_hex_color("#GGGGGG").is_none());
    }

    #[test]
    fn test_load_env_bloom() {
        with_env(&[("BLOOM_ENABLED", "false")], || {
            let settings = load_env();
            assert!(!settings.display.bloom_enabled);
        });

        with_env(&[("BLOOM_ENABLED", "1")], || {
            let settings = load_env();
            assert!(settings.display.bloom_enabled);
        });
    }

    #[test]
    fn test_load_env_playback() {
        with_env(
            &[("SECONDS_PER_DAY", "5.0"), ("LOOP_PLAYBACK", "true")],
            || {
                let settings = load_env();
                assert!((settings.playback.seconds_per_day - 5.0).abs() < 0.01);
                assert!(settings.playback.loop_playback);
            },
        );
    }

    #[test]
    fn test_load_env_camera() {
        with_env(&[("CAMERA_MODE", "track"), ("MIN_ZOOM", "0.1")], || {
            let settings = load_env();
            assert_eq!(settings.camera.mode, CameraModeSetting::Track);
            assert!((settings.camera.min_zoom - 0.1).abs() < 0.01);
        });
    }

    #[test]
    fn test_load_env_title() {
        with_env(&[("TITLE", "My Project"), ("TITLE_COLOR", "#FF5500")], || {
            let settings = load_env();
            assert_eq!(settings.title.title, Some("My Project".to_string()));
        });
    }

    #[test]
    fn test_load_env_filters() {
        with_env(&[("HIDE_USERS", "bot.*"), ("HIDE_FILES", "\\.lock$")], || {
            let settings = load_env();
            assert_eq!(settings.filter.hide_users_pattern(), Some("bot.*"));
            assert_eq!(settings.filter.hide_files_pattern(), Some("\\.lock$"));
        });
    }

    #[test]
    fn test_merge_env() {
        let base = Settings::new()
            .with_dimensions(1920, 1080)
            .with_bloom(true);

        with_env(&[("WIDTH", "2560"), ("BLOOM_ENABLED", "false")], || {
            let settings = merge_env(base);
            // Width should be overridden by env
            assert_eq!(settings.display.width, 2560);
            // Height should come from base
            assert_eq!(settings.display.height, 1080);
            // Bloom should be overridden by env
            assert!(!settings.display.bloom_enabled);
        });
    }

    #[test]
    fn test_env_var_names() {
        let names = env_var_names();
        assert!(names.contains(&"ROURCE_WIDTH"));
        assert!(names.contains(&"ROURCE_BLOOM_ENABLED"));
        assert!(names.contains(&"ROURCE_SECONDS_PER_DAY"));
        assert!(names.contains(&"ROURCE_TITLE"));
        assert!(names.len() >= 40); // Ensure we have all the vars
    }

    #[test]
    fn test_invalid_numeric_fallback() {
        with_env(&[("WIDTH", "not_a_number")], || {
            let settings = load_env();
            // Should fall back to default
            assert_eq!(settings.display.width, 1280);
        });
    }

    #[test]
    fn test_visibility_settings() {
        with_env(
            &[
                ("HIDE_FILENAMES", "yes"),
                ("HIDE_USERNAMES", "1"),
                ("SHOW_FPS", "on"),
            ],
            || {
                let settings = load_env();
                assert!(settings.visibility.hide_filenames);
                assert!(settings.visibility.hide_usernames);
                assert!(settings.visibility.show_fps);
            },
        );
    }

    #[test]
    fn test_export_settings() {
        with_env(
            &[
                ("OUTPUT_PATH", "/tmp/frames"),
                ("FRAMERATE", "30"),
                ("SCREENSHOT_PATH", "/tmp/screenshot.png"),
            ],
            || {
                let settings = load_env();
                assert_eq!(
                    settings.export.output_path,
                    Some("/tmp/frames".to_string())
                );
                assert_eq!(settings.export.framerate, 30);
                assert_eq!(
                    settings.export.screenshot_path,
                    Some("/tmp/screenshot.png".to_string())
                );
            },
        );
    }
}
