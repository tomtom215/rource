//! Command-line argument parsing for Rource.
//!
//! This module provides CLI argument parsing using clap, along with
//! configuration file loading and environment variable support.
//!
//! ## Module Organization
//!
//! | Module | Description |
//! |--------|-------------|
//! | `config_methods` | Config file and env variable loading |
//! | `help_text` | Sample config and env help text |
//! | `helpers` | Parsing and validation helpers |

#![allow(clippy::too_many_lines)]

mod config_methods;
mod help_text;
mod helpers;

use clap::Parser;
use rource_core::config::{
    CameraModeSetting, CameraSettings, DirectorySettings, DisplaySettings, ExportSettings,
    FilterSettings, InputSettings, LayoutSettings, LimitSettings, OverlaySettings,
    PlaybackSettings, Settings, TitleSettings, VisibilitySettings,
};
use std::path::PathBuf;

// Re-export helper functions for public use
pub use helpers::{parse_hex_color, validate_dimension, validate_framerate};

// Re-export help text functions
pub use help_text::{env_help, sample_config};

use helpers::{parse_date, parse_offset, validate_font_size, validate_seconds_per_day};

/// Rource - Software version control visualization tool.
///
/// A complete rewrite of Gource in Rust with WebAssembly support.
#[derive(Parser, Debug, Default)]
#[command(name = "rource")]
#[command(author, version, about, long_about = None)]
#[allow(clippy::struct_excessive_bools)]
pub struct Args {
    /// Path to git repository or log file.
    ///
    /// If not specified, uses the current directory.
    #[arg(default_value = ".")]
    pub path: PathBuf,

    /// Window width in pixels.
    #[arg(short = 'W', long, default_value_t = 1280)]
    pub width: u32,

    /// Window height in pixels.
    #[arg(short = 'H', long, default_value_t = 720)]
    pub height: u32,

    /// Run in fullscreen mode.
    #[arg(short, long)]
    pub fullscreen: bool,

    /// Seconds per day of commit history.
    ///
    /// Lower values = faster playback. Default is 10 seconds per day.
    #[arg(short, long, default_value_t = 10.0)]
    pub seconds_per_day: f32,

    /// Auto-skip to the next commit if nothing happens for this many seconds.
    #[arg(long, default_value_t = 3.0)]
    pub auto_skip_seconds: f32,

    /// Start playback from this date (YYYY-MM-DD).
    #[arg(long)]
    pub start_date: Option<String>,

    /// Stop playback at this date (YYYY-MM-DD).
    #[arg(long)]
    pub stop_date: Option<String>,

    /// Title to display at the top of the visualization.
    #[arg(short, long)]
    pub title: Option<String>,

    /// Background color in hex format (e.g., "000000" for black).
    #[arg(long, default_value = "000000")]
    pub background_color: String,

    /// Font size for file names.
    #[arg(long, default_value_t = 12.0)]
    pub font_size: f32,

    /// Disable bloom effect.
    #[arg(long)]
    pub no_bloom: bool,

    /// Enable drop shadows.
    #[arg(long)]
    pub shadows: bool,

    /// Hide filenames.
    #[arg(long)]
    pub hide_filenames: bool,

    /// Hide user names.
    #[arg(long)]
    pub hide_usernames: bool,

    /// Hide the date display.
    #[arg(long)]
    pub hide_date: bool,

    /// Hide the file extension legend.
    #[arg(long)]
    pub hide_legend: bool,

    /// Hide directory names/labels.
    #[arg(long)]
    pub hide_dirnames: bool,

    /// Hide the progress bar.
    #[arg(long)]
    pub hide_progress: bool,

    /// Hide the root directory node.
    #[arg(long)]
    pub hide_root: bool,

    /// Hide the tree structure (connecting lines between directories and files).
    #[arg(long)]
    pub hide_tree: bool,

    /// Hide the bloom/glow effect at runtime.
    #[arg(long)]
    pub hide_bloom: bool,

    /// Hide the mouse cursor during visualization.
    #[arg(long)]
    pub hide_mouse: bool,

    /// Maximum number of files to display (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    pub max_files: usize,

    /// Maximum number of users to display (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    pub max_users: usize,

    /// Regex pattern to show only matching users.
    ///
    /// Only users whose names match this pattern will be displayed.
    #[arg(long, value_name = "REGEX")]
    pub show_users: Option<String>,

    /// Regex pattern to hide matching users.
    ///
    /// Users whose names match this pattern will be hidden.
    /// Takes precedence over --show-users.
    #[arg(long, value_name = "REGEX")]
    pub hide_users: Option<String>,

    /// Regex pattern to show only matching files.
    ///
    /// Only files whose paths match this pattern will be displayed.
    #[arg(long, value_name = "REGEX")]
    pub show_files: Option<String>,

    /// Regex pattern to hide matching files.
    ///
    /// Files whose paths match this pattern will be hidden.
    /// Takes precedence over --show-files.
    #[arg(long, value_name = "REGEX")]
    pub hide_files: Option<String>,

    /// Regex pattern to hide matching directories.
    ///
    /// Entire directory trees matching this pattern will be excluded.
    /// Useful for filtering out build directories, `node_modules`, etc.
    #[arg(long, value_name = "REGEX")]
    pub hide_dirs: Option<String>,

    /// Camera mode: overview, track, or follow.
    #[arg(long, default_value = "overview")]
    pub camera_mode: String,

    /// Username to follow when camera mode is "follow".
    ///
    /// The camera will track this specific user throughout the visualization.
    #[arg(long, value_name = "USERNAME")]
    pub follow_user: Option<String>,

    /// Enable 3D perspective camera mode with orbit controls.
    ///
    /// When enabled, the visualization uses a 3D perspective camera that
    /// orbits around the scene. Use mouse drag to rotate, scroll to zoom.
    #[arg(long = "3d")]
    pub camera_3d: bool,

    /// Force 2D orthographic camera mode (default).
    ///
    /// Explicitly disable 3D mode and use the standard 2D camera.
    #[arg(long = "2d")]
    pub camera_2d: bool,

    /// Initial camera pitch angle in degrees (3D mode only).
    ///
    /// Controls the vertical viewing angle. 0 = horizontal, -90 = top-down.
    /// Default is -17 degrees for a slight downward angle.
    #[arg(long, default_value_t = -17.0, value_name = "DEGREES")]
    pub pitch: f32,

    /// Camera auto-rotation speed in radians per second (3D mode only).
    ///
    /// When non-zero, the camera slowly rotates around the scene when idle.
    /// Set to 0 to disable auto-rotation.
    #[arg(long, default_value_t = 0.05, value_name = "SPEED")]
    pub rotation_speed: f32,

    /// Disable automatic camera rotation (3D mode only).
    ///
    /// Prevents the camera from rotating automatically when idle.
    #[arg(long)]
    pub disable_auto_rotate: bool,

    /// Username(s) to highlight (comma-separated).
    ///
    /// Highlighted users appear with enhanced visibility.
    #[arg(long, value_name = "USERNAMES")]
    pub highlight_users: Option<String>,

    /// Highlight all users.
    #[arg(long)]
    pub highlight_all_users: bool,

    /// Directory name display depth (0 = none, 1 = immediate parent, etc.).
    #[arg(long, default_value_t = 1)]
    pub dir_name_depth: u32,

    /// Position of directory name along edge (0.0 = start, 1.0 = end).
    #[arg(long, default_value_t = 0.5)]
    pub dir_name_position: f32,

    /// Time scale multiplier (1.0 = normal, 2.0 = double speed).
    #[arg(long, default_value_t = 1.0)]
    pub time_scale: f32,

    /// Stop playback after this many seconds of real time.
    #[arg(long, value_name = "SECONDS")]
    pub stop_at_time: Option<f32>,

    /// Use real-time playback (1 second = 1 second of history).
    #[arg(long)]
    pub realtime: bool,

    /// Path to logo image to display in top-right corner.
    #[arg(long, value_name = "FILE")]
    pub logo: Option<PathBuf>,

    /// Logo position offset from top-right corner (e.g., "10x20").
    #[arg(long, value_name = "XxY", default_value = "0x0")]
    pub logo_offset: String,

    /// Path to background image.
    #[arg(long, value_name = "FILE")]
    pub background_image: Option<PathBuf>,

    /// Save current configuration to a TOML file and exit.
    #[arg(long, value_name = "FILE")]
    pub save_config: Option<PathBuf>,

    /// Loop the visualization.
    #[arg(short = 'L', long)]
    pub loop_playback: bool,

    /// Start paused.
    #[arg(long)]
    pub paused: bool,

    /// Disable mouse/keyboard controls.
    #[arg(long)]
    pub disable_input: bool,

    /// Use a custom log format (pipe-delimited).
    #[arg(long)]
    pub custom_log: bool,

    /// Output PPM frames to this path for video export.
    #[arg(short, long)]
    pub output: Option<PathBuf>,

    /// Frame rate for video export.
    #[arg(long, default_value_t = 60)]
    pub framerate: u32,

    /// Run in headless mode (no window, for batch video export).
    ///
    /// Requires --output to be specified. Runs at maximum speed without display.
    #[arg(long)]
    pub headless: bool,

    /// Save a screenshot to this file and exit.
    ///
    /// Supports PNG format. Renders the visualization at the specified position
    /// and saves a single frame.
    #[arg(long)]
    pub screenshot: Option<PathBuf>,

    /// For screenshot mode: which commit index to render (0-based).
    ///
    /// If not specified, renders the final state (all commits applied).
    #[arg(long)]
    pub screenshot_at: Option<usize>,

    /// Path to a TOML configuration file.
    ///
    /// Command-line arguments override config file settings.
    #[arg(short = 'c', long)]
    pub config: Option<PathBuf>,

    /// Print a sample configuration file and exit.
    #[arg(long)]
    pub sample_config: bool,

    /// Print environment variable help and exit.
    #[arg(long)]
    pub env_help: bool,

    /// Directory containing user avatar images.
    ///
    /// Images should be named after usernames (e.g., "John Doe.png").
    /// Names are matched case-insensitively.
    #[arg(long)]
    pub user_image_dir: Option<PathBuf>,

    /// Default user avatar image.
    ///
    /// Used when a user doesn't have a specific avatar.
    #[arg(long)]
    pub default_user_image: Option<PathBuf>,
}

impl Args {
    /// Parse command-line arguments.
    pub fn parse_args() -> Self {
        Self::parse()
    }

    /// Validate all arguments and return an error if any are invalid.
    ///
    /// This should be called after parsing to catch issues that clap's type
    /// system doesn't enforce (e.g., minimum values, cross-field validation).
    pub fn validate(&self) -> Result<(), String> {
        validate_dimension(self.width, "width")?;
        validate_dimension(self.height, "height")?;
        validate_framerate(self.framerate)?;
        validate_seconds_per_day(self.seconds_per_day)?;
        validate_font_size(self.font_size)?;

        // Validate hex color can be parsed
        if parse_hex_color(&self.background_color).is_none() {
            return Err(format!(
                "Invalid background color '{}'. Expected 6-character hex string (e.g., 'FF0000' or '#FF0000')",
                self.background_color
            ));
        }

        // Validate headless mode requires output
        if self.headless && self.output.is_none() {
            return Err(
                "--headless requires --output to specify frame output directory".to_string(),
            );
        }

        Ok(())
    }

    /// Parse the background color from hex string.
    pub fn parse_background_color(&self) -> rource_math::Color {
        parse_hex_color(&self.background_color).unwrap_or(rource_math::Color::BLACK)
    }

    /// Parse the logo offset from `XxY` format.
    ///
    /// Returns (x, y) offset values. Defaults to (0, 0) if parsing fails.
    #[must_use]
    pub fn parse_logo_offset(&self) -> (i32, i32) {
        parse_offset(&self.logo_offset).unwrap_or((0, 0))
    }

    /// Convert CLI arguments to a Settings struct.
    ///
    /// This is used for --save-config to export current settings.
    #[must_use]
    pub fn to_settings(&self) -> Settings {
        let display = DisplaySettings {
            width: self.width,
            height: self.height,
            fullscreen: self.fullscreen,
            background_color: self.parse_background_color(),
            font_size: self.font_size,
            bloom_enabled: !self.no_bloom,
            bloom_intensity: 1.0,
            shadows_enabled: self.shadows,
        };

        let playback = PlaybackSettings {
            seconds_per_day: self.seconds_per_day,
            auto_skip_seconds: 3.0,
            start_timestamp: self.start_date.clone().and_then(|d| parse_date(&d)),
            stop_timestamp: self.stop_date.clone().and_then(|d| parse_date(&d)),
            loop_playback: self.loop_playback,
            start_paused: self.paused,
            time_scale: self.time_scale,
            stop_at_time: self.stop_at_time,
            realtime: self.realtime,
        };

        let visibility = VisibilitySettings {
            hide_filenames: self.hide_filenames,
            hide_usernames: self.hide_usernames,
            hide_date: self.hide_date,
            hide_progress: self.hide_progress,
            hide_legend: self.hide_legend,
            hide_dirnames: self.hide_dirnames,
            hide_root: self.hide_root,
            hide_tree: self.hide_tree,
            hide_bloom: self.hide_bloom,
            hide_mouse: self.hide_mouse,
            show_fps: false,
        };

        let limits = LimitSettings {
            max_files: self.max_files,
            max_users: self.max_users,
            file_idle_time: 0.0, // Use default
            user_idle_time: 0.0, // Use default
        };

        let camera = CameraSettings {
            mode: CameraModeSetting::parse(&self.camera_mode),
            min_zoom: 0.01,
            max_zoom: 10.0,
            smoothness: 0.85,
            padding: 100.0,
            follow_user: self.follow_user.clone(),
            highlight_users: self.highlight_users.clone(),
            highlight_all_users: self.highlight_all_users,
            enable_3d: self.camera_3d && !self.camera_2d,
            pitch: self.pitch,
            rotation_speed: self.rotation_speed,
            disable_auto_rotate: self.disable_auto_rotate,
        };

        let input = InputSettings {
            disable_input: self.disable_input,
            mouse_sensitivity: 1.0,
        };

        let export = ExportSettings {
            output_path: self.output.as_ref().map(|p| p.display().to_string()),
            framerate: self.framerate,
            screenshot_path: self.screenshot.as_ref().map(|p| p.display().to_string()),
        };

        let title = TitleSettings {
            title: self.title.clone(),
            title_font_size: self.font_size * 1.5,
            title_color: rource_math::Color::WHITE,
        };

        let directory = DirectorySettings {
            name_depth: self.dir_name_depth,
            name_position: self.dir_name_position,
        };

        let overlay = OverlaySettings {
            logo_path: self.logo.as_ref().map(|p| p.display().to_string()),
            logo_offset: self.parse_logo_offset(),
            background_image: self
                .background_image
                .as_ref()
                .map(|p| p.display().to_string()),
        };

        let mut filter = FilterSettings::new();
        if let Some(ref pattern) = self.show_users {
            filter.set_show_users(Some(pattern.clone()));
        }
        if let Some(ref pattern) = self.hide_users {
            filter.set_hide_users(Some(pattern.clone()));
        }
        if let Some(ref pattern) = self.show_files {
            filter.set_show_files(Some(pattern.clone()));
        }
        if let Some(ref pattern) = self.hide_files {
            filter.set_hide_files(Some(pattern.clone()));
        }
        if let Some(ref pattern) = self.hide_dirs {
            filter.set_hide_dirs(Some(pattern.clone()));
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
            directory,
            overlay,
            filter,
            layout: LayoutSettings::default(),
        }
    }

    /// Generate a sample config file content.
    #[must_use]
    pub fn sample_config() -> &'static str {
        sample_config()
    }

    /// Generate environment variable help text.
    #[must_use]
    pub fn env_help() -> &'static str {
        env_help()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Mutex to serialize tests that modify environment variables
    // This prevents race conditions when tests run in parallel
    static ENV_MUTEX: Mutex<()> = Mutex::new(());

    #[test]
    fn test_default_args() {
        // Verify defaults compile correctly
        // Note: Args::default() uses Rust's Default trait which gives 0 for numerics.
        // The clap default_value_t is only used when parsing CLI args.
        let args = Args::default();

        // These are Default trait values, not clap defaults
        assert_eq!(args.width, 0); // Default is 0, clap default_value_t is 1280
        assert_eq!(args.height, 0); // Default is 0, clap default_value_t is 720
        assert!(args.show_users.is_none());
        assert!(args.hide_users.is_none());
        // Test new fields
        assert!(!args.hide_dirnames);
        assert!(!args.hide_root);
        assert!(!args.hide_tree);
        assert!(!args.hide_bloom);
        assert!(!args.hide_mouse);
        assert_eq!(args.time_scale, 0.0); // Default trait gives 0
        assert!(args.stop_at_time.is_none());
        assert!(!args.realtime);
        assert!(args.follow_user.is_none());
        assert!(args.highlight_users.is_none());
        assert!(!args.highlight_all_users);
        assert_eq!(args.dir_name_depth, 0); // Default trait gives 0
        assert!((args.dir_name_position).abs() < 0.01); // Default trait gives 0.0
        assert!(args.logo.is_none());
        assert!(args.background_image.is_none());
        assert!(args.save_config.is_none());
    }

    #[test]
    fn test_to_settings_conversion() {
        // Create args with proper values for conversion
        let args = Args {
            width: 1920,
            height: 1080,
            time_scale: 2.0,
            stop_at_time: Some(60.0),
            realtime: true,
            hide_dirnames: true,
            hide_bloom: true,
            follow_user: Some("alice".to_string()),
            highlight_all_users: true,
            dir_name_depth: 3,
            dir_name_position: 0.75,
            ..Args::default()
        };

        let settings = args.to_settings();

        assert_eq!(settings.display.width, 1920);
        assert_eq!(settings.display.height, 1080);
        assert!((settings.playback.time_scale - 2.0).abs() < 0.01);
        assert_eq!(settings.playback.stop_at_time, Some(60.0));
        assert!(settings.playback.realtime);
        assert!(settings.visibility.hide_dirnames);
        assert!(settings.visibility.hide_bloom);
        assert_eq!(settings.camera.follow_user, Some("alice".to_string()));
        assert!(settings.camera.highlight_all_users);
        assert_eq!(settings.directory.name_depth, 3);
        assert!((settings.directory.name_position - 0.75).abs() < 0.01);
    }

    #[test]
    fn test_parse_logo_offset() {
        let args = Args {
            logo_offset: "10x20".to_string(),
            ..Args::default()
        };
        assert_eq!(args.parse_logo_offset(), (10, 20));

        let args = Args {
            logo_offset: "0x0".to_string(),
            ..Args::default()
        };
        assert_eq!(args.parse_logo_offset(), (0, 0));

        let args = Args {
            logo_offset: "invalid".to_string(),
            ..Args::default()
        };
        assert_eq!(args.parse_logo_offset(), (0, 0));
    }

    #[test]
    fn test_config_file_parsing() {
        // Create a temp config file
        let config_content = r#"
width = 1920
height = 1080
seconds_per_day = 5.0
title = "Test Project"
no_bloom = true
"#;

        let temp_dir = std::env::temp_dir();
        let config_path = temp_dir.join("test_rource_config.toml");
        std::fs::write(&config_path, config_content).unwrap();

        // Use explicit default values that match CLI defaults
        let mut args = Args {
            path: PathBuf::from("."),
            width: 1280,
            height: 720,
            seconds_per_day: 10.0,
            background_color: "000000".to_string(),
            font_size: 12.0,
            camera_mode: "overview".to_string(),
            framerate: 60,
            config: Some(config_path.clone()),
            ..Args::default()
        };

        args.apply_config_file().unwrap();

        assert_eq!(args.width, 1920);
        assert_eq!(args.height, 1080);
        assert!((args.seconds_per_day - 5.0).abs() < 0.01);
        assert_eq!(args.title, Some("Test Project".to_string()));
        assert!(args.no_bloom);

        // Clean up
        let _ = std::fs::remove_file(&config_path);
    }

    #[test]
    fn test_config_file_cli_override() {
        // CLI args should override config - non-default value should be preserved
        let config_content = r"
width = 1920
";

        let temp_dir = std::env::temp_dir();
        let config_path = temp_dir.join("test_rource_config2.toml");
        std::fs::write(&config_path, config_content).unwrap();

        let mut args = Args {
            path: PathBuf::from("."),
            width: 800, // Explicitly set via CLI (non-default)
            height: 720,
            seconds_per_day: 10.0,
            background_color: "000000".to_string(),
            font_size: 12.0,
            camera_mode: "overview".to_string(),
            framerate: 60,
            config: Some(config_path.clone()),
            ..Args::default()
        };

        args.apply_config_file().unwrap();

        // CLI value should be preserved since it's not the default
        assert_eq!(args.width, 800);

        // Clean up
        let _ = std::fs::remove_file(&config_path);
    }

    #[test]
    fn test_env_vars_applied() {
        // Lock mutex to prevent parallel test interference with env vars
        let _guard = ENV_MUTEX.lock().unwrap();

        // Set environment variables
        std::env::set_var("ROURCE_WIDTH", "1920");
        std::env::set_var("ROURCE_HEIGHT", "1080");
        std::env::set_var("ROURCE_BLOOM_ENABLED", "false");

        let mut args = Args {
            path: PathBuf::from("."),
            width: 1280,
            height: 720,
            seconds_per_day: 10.0,
            background_color: "000000".to_string(),
            font_size: 12.0,
            camera_mode: "overview".to_string(),
            framerate: 60,
            ..Args::default()
        };

        args.apply_env();

        // Env should override defaults
        assert_eq!(args.width, 1920);
        assert_eq!(args.height, 1080);
        assert!(args.no_bloom);

        // Clean up
        std::env::remove_var("ROURCE_WIDTH");
        std::env::remove_var("ROURCE_HEIGHT");
        std::env::remove_var("ROURCE_BLOOM_ENABLED");
    }

    #[test]
    fn test_env_vars_cli_override() {
        // Lock mutex to prevent parallel test interference with env vars
        let _guard = ENV_MUTEX.lock().unwrap();

        // CLI args should override env
        std::env::set_var("ROURCE_WIDTH", "1920");

        let mut args = Args {
            path: PathBuf::from("."),
            width: 800, // Explicitly set via CLI (non-default)
            height: 720,
            seconds_per_day: 10.0,
            background_color: "000000".to_string(),
            font_size: 12.0,
            camera_mode: "overview".to_string(),
            framerate: 60,
            ..Args::default()
        };

        args.apply_env();

        // CLI value (800) should be preserved since it's not the default (1280)
        assert_eq!(args.width, 800);

        // Clean up
        std::env::remove_var("ROURCE_WIDTH");
    }

    #[test]
    fn test_args_validate() {
        // Valid args
        let args = Args {
            width: 1280,
            height: 720,
            framerate: 60,
            seconds_per_day: 10.0,
            font_size: 12.0,
            background_color: "000000".to_string(),
            ..Args::default()
        };
        assert!(args.validate().is_ok());

        // Invalid width
        let args = Args {
            width: 0,
            height: 720,
            framerate: 60,
            seconds_per_day: 10.0,
            font_size: 12.0,
            background_color: "000000".to_string(),
            ..Args::default()
        };
        assert!(args.validate().is_err());

        // Invalid background color
        let args = Args {
            width: 1280,
            height: 720,
            framerate: 60,
            seconds_per_day: 10.0,
            font_size: 12.0,
            background_color: "invalid".to_string(),
            ..Args::default()
        };
        assert!(args.validate().is_err());

        // Headless without output
        let args = Args {
            width: 1280,
            height: 720,
            framerate: 60,
            seconds_per_day: 10.0,
            font_size: 12.0,
            background_color: "000000".to_string(),
            headless: true,
            output: None,
            ..Args::default()
        };
        assert!(args.validate().is_err());
    }
}
