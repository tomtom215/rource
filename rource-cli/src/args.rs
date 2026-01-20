//! Command-line argument parsing for Rource.

#![allow(clippy::too_many_lines)]

use clap::Parser;
use rource_core::config::{
    CameraModeSetting, CameraSettings, DirectorySettings, DisplaySettings, ExportSettings,
    FilterSettings, InputSettings, LimitSettings, OverlaySettings, PlaybackSettings, Settings,
    TitleSettings, VisibilitySettings,
};
use std::path::PathBuf;

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
        }
    }

    /// Apply settings from a TOML config file.
    ///
    /// CLI arguments take precedence over config file settings.
    #[allow(clippy::too_many_lines)] // Config merging requires handling all settings
    pub fn apply_config_file(&mut self) -> Result<(), String> {
        let Some(config_path) = &self.config else {
            return Ok(());
        };

        let content = std::fs::read_to_string(config_path)
            .map_err(|e| format!("Failed to read config file: {e}"))?;

        let config: toml::Table = content
            .parse()
            .map_err(|e| format!("Failed to parse config file: {e}"))?;

        // Apply settings from config (CLI args override these)
        if let Some(toml::Value::Integer(v)) = config.get("width") {
            if self.width == 1280 {
                // Only apply if default
                self.width = *v as u32;
            }
        }
        if let Some(toml::Value::Integer(v)) = config.get("height") {
            if self.height == 720 {
                self.height = *v as u32;
            }
        }
        if let Some(toml::Value::Float(v)) = config.get("seconds_per_day") {
            if (self.seconds_per_day - 10.0).abs() < 0.01 {
                self.seconds_per_day = *v as f32;
            }
        }
        if let Some(toml::Value::String(v)) = config.get("background_color") {
            if self.background_color == "000000" {
                self.background_color.clone_from(v);
            }
        }
        if let Some(toml::Value::String(v)) = config.get("title") {
            if self.title.is_none() {
                self.title = Some(v.clone());
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("no_bloom") {
            if !self.no_bloom {
                self.no_bloom = *v;
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("shadows") {
            if !self.shadows {
                self.shadows = *v;
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("fullscreen") {
            if !self.fullscreen {
                self.fullscreen = *v;
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("hide_filenames") {
            if !self.hide_filenames {
                self.hide_filenames = *v;
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("hide_usernames") {
            if !self.hide_usernames {
                self.hide_usernames = *v;
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("hide_date") {
            if !self.hide_date {
                self.hide_date = *v;
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("loop") {
            if !self.loop_playback {
                self.loop_playback = *v;
            }
        }
        if let Some(toml::Value::Boolean(v)) = config.get("paused") {
            if !self.paused {
                self.paused = *v;
            }
        }
        if let Some(toml::Value::Float(v)) = config.get("font_size") {
            if (self.font_size - 12.0).abs() < 0.01 {
                self.font_size = *v as f32;
            }
        }
        if let Some(toml::Value::String(v)) = config.get("camera_mode") {
            if self.camera_mode == "overview" {
                self.camera_mode.clone_from(v);
            }
        }
        if let Some(toml::Value::Integer(v)) = config.get("framerate") {
            if self.framerate == 60 {
                self.framerate = *v as u32;
            }
        }

        // Filter settings
        if let Some(toml::Value::String(v)) = config.get("show_users") {
            if self.show_users.is_none() {
                self.show_users = Some(v.clone());
            }
        }
        if let Some(toml::Value::String(v)) = config.get("hide_users") {
            if self.hide_users.is_none() {
                self.hide_users = Some(v.clone());
            }
        }
        if let Some(toml::Value::String(v)) = config.get("show_files") {
            if self.show_files.is_none() {
                self.show_files = Some(v.clone());
            }
        }
        if let Some(toml::Value::String(v)) = config.get("hide_files") {
            if self.hide_files.is_none() {
                self.hide_files = Some(v.clone());
            }
        }
        if let Some(toml::Value::String(v)) = config.get("hide_dirs") {
            if self.hide_dirs.is_none() {
                self.hide_dirs = Some(v.clone());
            }
        }

        Ok(())
    }

    /// Apply settings from environment variables.
    ///
    /// Environment variables use the ROURCE_ prefix (e.g., `ROURCE_WIDTH`, `ROURCE_SECONDS_PER_DAY`).
    /// CLI arguments take precedence over environment variables.
    #[allow(clippy::too_many_lines)] // Env merging requires handling all settings
    pub fn apply_env(&mut self) {
        use rource_core::config::load_env;

        let env_settings = load_env();

        // Display settings - only apply if CLI is at default
        if self.width == 1280 && env_settings.display.width != 1280 {
            self.width = env_settings.display.width;
        }
        if self.height == 720 && env_settings.display.height != 720 {
            self.height = env_settings.display.height;
        }
        if !self.fullscreen && env_settings.display.fullscreen {
            self.fullscreen = true;
        }
        if self.background_color == "000000" {
            // Convert color back to hex string
            let c = &env_settings.display.background_color;
            if c.r > 0.0 || c.g > 0.0 || c.b > 0.0 {
                self.background_color = format!(
                    "{:02X}{:02X}{:02X}",
                    (c.r * 255.0) as u8,
                    (c.g * 255.0) as u8,
                    (c.b * 255.0) as u8
                );
            }
        }
        if (self.font_size - 12.0).abs() < 0.01
            && (env_settings.display.font_size - 12.0).abs() > 0.01
        {
            self.font_size = env_settings.display.font_size;
        }
        if !self.no_bloom && !env_settings.display.bloom_enabled {
            self.no_bloom = true;
        }
        if !self.shadows && env_settings.display.shadows_enabled {
            self.shadows = true;
        }

        // Playback settings
        if (self.seconds_per_day - 10.0).abs() < 0.01
            && (env_settings.playback.seconds_per_day - 10.0).abs() > 0.01
        {
            self.seconds_per_day = env_settings.playback.seconds_per_day;
        }
        if (self.auto_skip_seconds - 3.0).abs() < 0.01
            && (env_settings.playback.auto_skip_seconds - 3.0).abs() > 0.01
        {
            self.auto_skip_seconds = env_settings.playback.auto_skip_seconds;
        }
        if !self.loop_playback && env_settings.playback.loop_playback {
            self.loop_playback = true;
        }
        if !self.paused && env_settings.playback.start_paused {
            self.paused = true;
        }

        // Visibility settings
        if !self.hide_filenames && env_settings.visibility.hide_filenames {
            self.hide_filenames = true;
        }
        if !self.hide_usernames && env_settings.visibility.hide_usernames {
            self.hide_usernames = true;
        }
        if !self.hide_date && env_settings.visibility.hide_date {
            self.hide_date = true;
        }
        if !self.hide_legend && env_settings.visibility.hide_legend {
            self.hide_legend = true;
        }

        // Limit settings
        if self.max_files == 0 && env_settings.limits.max_files > 0 {
            self.max_files = env_settings.limits.max_files;
        }
        if self.max_users == 0 && env_settings.limits.max_users > 0 {
            self.max_users = env_settings.limits.max_users;
        }

        // Camera settings
        if self.camera_mode == "overview"
            && env_settings.camera.mode != rource_core::config::CameraModeSetting::Overview
        {
            self.camera_mode = env_settings.camera.mode.as_str().to_string();
        }

        // Input settings
        if !self.disable_input && env_settings.input.disable_input {
            self.disable_input = true;
        }

        // Export settings
        if self.output.is_none() {
            if let Some(path) = &env_settings.export.output_path {
                self.output = Some(PathBuf::from(path));
            }
        }
        if self.framerate == 60 && env_settings.export.framerate != 60 {
            self.framerate = env_settings.export.framerate;
        }
        if self.screenshot.is_none() {
            if let Some(path) = &env_settings.export.screenshot_path {
                self.screenshot = Some(PathBuf::from(path));
            }
        }

        // Title settings
        if self.title.is_none() {
            self.title.clone_from(&env_settings.title.title);
        }

        // Filter settings
        if self.show_users.is_none() {
            if let Some(pattern) = env_settings.filter.show_users_pattern() {
                self.show_users = Some(pattern.to_string());
            }
        }
        if self.hide_users.is_none() {
            if let Some(pattern) = env_settings.filter.hide_users_pattern() {
                self.hide_users = Some(pattern.to_string());
            }
        }
        if self.show_files.is_none() {
            if let Some(pattern) = env_settings.filter.show_files_pattern() {
                self.show_files = Some(pattern.to_string());
            }
        }
        if self.hide_files.is_none() {
            if let Some(pattern) = env_settings.filter.hide_files_pattern() {
                self.hide_files = Some(pattern.to_string());
            }
        }
        if self.hide_dirs.is_none() {
            if let Some(pattern) = env_settings.filter.hide_dirs_pattern() {
                self.hide_dirs = Some(pattern.to_string());
            }
        }
    }

    /// Generate a sample config file content.
    #[must_use]
    pub fn sample_config() -> &'static str {
        r#"# Rource Configuration File
# https://github.com/tomtom215/rource

# Display settings
width = 1280
height = 720
fullscreen = false
background_color = "000000"
font_size = 12.0

# Playback settings
seconds_per_day = 10.0
paused = false
loop = false

# Visual effects
no_bloom = false
shadows = false

# UI visibility
hide_filenames = false
hide_usernames = false
hide_date = false

# Camera
camera_mode = "overview"  # overview, track, or follow

# Title (uncomment to use)
# title = "My Project"

# Video export settings
framerate = 60

# Filtering (regex patterns, uncomment to use)
# show_users = "^(alice|bob)$"     # Only show these users
# hide_users = "bot.*|ci-.*"       # Hide bot and CI users
# show_files = "\\.rs$"            # Only show Rust files
# hide_files = "\\.log$|\\.tmp$"   # Hide log and temp files
# hide_dirs = "node_modules|target|build"  # Hide build directories
"#
    }

    /// Generate environment variable help text.
    #[must_use]
    pub fn env_help() -> &'static str {
        r#"Rource Environment Variables

All settings can be configured via environment variables with the ROURCE_ prefix.
Environment variables are overridden by CLI arguments but override config files.

Configuration Priority (highest to lowest):
  1. CLI arguments
  2. Environment variables
  3. Config file (--config)
  4. Defaults

Boolean values accept: 1, true, yes, on (for true) or 0, false, no, off (for false)
Color values use hex format: #FFFFFF or FFFFFF

DISPLAY SETTINGS
  ROURCE_WIDTH              Window width in pixels (default: 1280)
  ROURCE_HEIGHT             Window height in pixels (default: 720)
  ROURCE_FULLSCREEN         Run in fullscreen mode (default: false)
  ROURCE_BACKGROUND_COLOR   Background color as hex (default: #000000)
  ROURCE_FONT_SIZE          Font size for labels (default: 12.0)
  ROURCE_BLOOM_ENABLED      Enable bloom/glow effect (default: true)
  ROURCE_BLOOM_INTENSITY    Bloom intensity 0.0-2.0 (default: 1.0)
  ROURCE_SHADOWS_ENABLED    Enable drop shadows (default: false)

PLAYBACK SETTINGS
  ROURCE_SECONDS_PER_DAY    Real seconds per day of history (default: 10.0)
  ROURCE_AUTO_SKIP_SECONDS  Seconds before auto-skipping idle (default: 3.0)
  ROURCE_START_TIMESTAMP    Unix timestamp to start from
  ROURCE_STOP_TIMESTAMP     Unix timestamp to stop at
  ROURCE_LOOP_PLAYBACK      Loop when reaching end (default: false)
  ROURCE_START_PAUSED       Start in paused state (default: false)

VISIBILITY SETTINGS
  ROURCE_HIDE_FILENAMES     Hide file names (default: false)
  ROURCE_HIDE_USERNAMES     Hide user names (default: false)
  ROURCE_HIDE_DATE          Hide date display (default: false)
  ROURCE_HIDE_PROGRESS      Hide progress bar (default: false)
  ROURCE_HIDE_LEGEND        Hide file extension legend (default: false)
  ROURCE_SHOW_FPS           Show FPS counter (default: false)

LIMIT SETTINGS
  ROURCE_MAX_FILES          Maximum files to display, 0=unlimited (default: 0)
  ROURCE_MAX_USERS          Maximum users to display, 0=unlimited (default: 0)
  ROURCE_FILE_IDLE_TIME     Seconds before files fade out (default: 60.0)
  ROURCE_USER_IDLE_TIME     Seconds before users fade out (default: 10.0)

CAMERA SETTINGS
  ROURCE_CAMERA_MODE        Camera mode: overview, track, follow (default: overview)
  ROURCE_MIN_ZOOM           Minimum zoom level (default: 0.01)
  ROURCE_MAX_ZOOM           Maximum zoom level (default: 10.0)
  ROURCE_CAMERA_SMOOTHNESS  Camera smoothness 0.0-1.0 (default: 0.85)
  ROURCE_CAMERA_PADDING     Padding when auto-fitting (default: 100.0)

INPUT SETTINGS
  ROURCE_DISABLE_INPUT      Disable all user input (default: false)
  ROURCE_MOUSE_SENSITIVITY  Mouse sensitivity (default: 1.0)

EXPORT SETTINGS
  ROURCE_OUTPUT_PATH        Output path for video frames
  ROURCE_FRAMERATE          Video export framerate (default: 60)
  ROURCE_SCREENSHOT_PATH    Screenshot output path

TITLE SETTINGS
  ROURCE_TITLE              Title to display
  ROURCE_TITLE_FONT_SIZE    Title font size (default: 24.0)
  ROURCE_TITLE_COLOR        Title color as hex (default: #FFFFFF)

FILTER SETTINGS
  ROURCE_SHOW_USERS         Regex pattern for users to show
  ROURCE_HIDE_USERS         Regex pattern for users to hide
  ROURCE_SHOW_FILES         Regex pattern for files to show
  ROURCE_HIDE_FILES         Regex pattern for files to hide
  ROURCE_HIDE_DIRS          Regex pattern for directories to hide

EXAMPLE USAGE
  export ROURCE_WIDTH=1920
  export ROURCE_HEIGHT=1080
  export ROURCE_BLOOM_ENABLED=false
  export ROURCE_SECONDS_PER_DAY=5.0
  export ROURCE_TITLE="My Project"
  rource /path/to/repo
"#
    }
}

/// Parse a hex color string (e.g., "FF0000" or "#FF0000") to a Color.
fn parse_hex_color(s: &str) -> Option<rource_math::Color> {
    let s = s.trim_start_matches('#');
    if s.len() != 6 {
        return None;
    }

    let r = u8::from_str_radix(&s[0..2], 16).ok()?;
    let g = u8::from_str_radix(&s[2..4], 16).ok()?;
    let b = u8::from_str_radix(&s[4..6], 16).ok()?;

    Some(rource_math::Color::new(
        f32::from(r) / 255.0,
        f32::from(g) / 255.0,
        f32::from(b) / 255.0,
        1.0,
    ))
}

/// Validate dimension (width/height) is within reasonable bounds.
///
/// Returns an error message if validation fails.
pub fn validate_dimension(value: u32, name: &str) -> Result<(), String> {
    const MIN_DIMENSION: u32 = 16;
    const MAX_DIMENSION: u32 = 16384;

    if value < MIN_DIMENSION {
        return Err(format!(
            "{name} must be at least {MIN_DIMENSION} pixels, got {value}"
        ));
    }
    if value > MAX_DIMENSION {
        return Err(format!(
            "{name} must be at most {MAX_DIMENSION} pixels, got {value}"
        ));
    }
    Ok(())
}

/// Validate framerate is within reasonable bounds.
///
/// Returns an error message if validation fails.
pub fn validate_framerate(value: u32) -> Result<(), String> {
    const MIN_FRAMERATE: u32 = 1;
    const MAX_FRAMERATE: u32 = 240;

    if value < MIN_FRAMERATE {
        return Err(format!(
            "framerate must be at least {MIN_FRAMERATE} FPS, got {value}"
        ));
    }
    if value > MAX_FRAMERATE {
        return Err(format!(
            "framerate must be at most {MAX_FRAMERATE} FPS, got {value}"
        ));
    }
    Ok(())
}

/// Validate `seconds_per_day` is a positive value.
///
/// Returns an error message if validation fails.
#[allow(dead_code)] // Used by Args::validate()
fn validate_seconds_per_day(value: f32) -> Result<(), String> {
    const MIN_SECONDS: f32 = 0.001;

    if !value.is_finite() {
        return Err(format!(
            "seconds_per_day must be a finite number, got {value}"
        ));
    }
    if value < MIN_SECONDS {
        return Err(format!(
            "seconds_per_day must be at least {MIN_SECONDS}, got {value}"
        ));
    }
    Ok(())
}

/// Validate font size is within reasonable bounds.
///
/// Returns an error message if validation fails.
#[allow(dead_code)] // Used by Args::validate()
fn validate_font_size(value: f32) -> Result<(), String> {
    const MIN_SIZE: f32 = 4.0;
    const MAX_SIZE: f32 = 200.0;

    if !value.is_finite() {
        return Err(format!("font_size must be a finite number, got {value}"));
    }
    if value < MIN_SIZE {
        return Err(format!(
            "font_size must be at least {MIN_SIZE}, got {value}"
        ));
    }
    if value > MAX_SIZE {
        return Err(format!("font_size must be at most {MAX_SIZE}, got {value}"));
    }
    Ok(())
}

/// Parse an offset string in `XxY` or `X,Y` format.
fn parse_offset(s: &str) -> Option<(i32, i32)> {
    let s = s.trim();
    if s.is_empty() || s == "0x0" || s == "0,0" {
        return Some((0, 0));
    }

    // Try "XxY" format
    if let Some((x_str, y_str)) = s.split_once('x') {
        let x = x_str.trim().parse().ok()?;
        let y = y_str.trim().parse().ok()?;
        return Some((x, y));
    }

    // Try "X,Y" format
    if let Some((x_str, y_str)) = s.split_once(',') {
        let x = x_str.trim().parse().ok()?;
        let y = y_str.trim().parse().ok()?;
        return Some((x, y));
    }

    None
}

/// Parse a date string in "YYYY-MM-DD" format to a Unix timestamp.
fn parse_date(s: &str) -> Option<i64> {
    use chrono::NaiveDate;

    let date = NaiveDate::parse_from_str(s.trim(), "%Y-%m-%d").ok()?;
    let datetime = date.and_hms_opt(0, 0, 0)?;
    Some(datetime.and_utc().timestamp())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Mutex to serialize tests that modify environment variables
    // This prevents race conditions when tests run in parallel
    static ENV_MUTEX: Mutex<()> = Mutex::new(());

    #[test]
    fn test_parse_hex_color() {
        let white = parse_hex_color("FFFFFF").unwrap();
        assert!((white.r - 1.0).abs() < 0.01);
        assert!((white.g - 1.0).abs() < 0.01);
        assert!((white.b - 1.0).abs() < 0.01);

        let red = parse_hex_color("FF0000").unwrap();
        assert!((red.r - 1.0).abs() < 0.01);
        assert!((red.g).abs() < 0.01);
        assert!((red.b).abs() < 0.01);

        let with_hash = parse_hex_color("#00FF00").unwrap();
        assert!((with_hash.g - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_parse_hex_color_invalid() {
        assert!(parse_hex_color("").is_none());
        assert!(parse_hex_color("FFF").is_none());
        assert!(parse_hex_color("GGGGGG").is_none());
    }

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
    fn test_sample_config() {
        let sample = Args::sample_config();
        assert!(sample.contains("width"));
        assert!(sample.contains("seconds_per_day"));
        assert!(sample.contains("background_color"));
    }

    #[test]
    fn test_env_help() {
        let help = Args::env_help();
        assert!(help.contains("ROURCE_WIDTH"));
        assert!(help.contains("ROURCE_SECONDS_PER_DAY"));
        assert!(help.contains("ROURCE_BLOOM_ENABLED"));
        assert!(help.contains("DISPLAY SETTINGS"));
        assert!(help.contains("PLAYBACK SETTINGS"));
        assert!(help.contains("FILTER SETTINGS"));
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
    fn test_validate_dimension() {
        // Valid dimensions
        assert!(validate_dimension(1280, "width").is_ok());
        assert!(validate_dimension(16, "width").is_ok());
        assert!(validate_dimension(16384, "width").is_ok());

        // Invalid dimensions
        assert!(validate_dimension(0, "width").is_err());
        assert!(validate_dimension(15, "width").is_err());
        assert!(validate_dimension(16385, "width").is_err());
    }

    #[test]
    fn test_validate_framerate() {
        // Valid framerates
        assert!(validate_framerate(60).is_ok());
        assert!(validate_framerate(1).is_ok());
        assert!(validate_framerate(240).is_ok());

        // Invalid framerates
        assert!(validate_framerate(0).is_err());
        assert!(validate_framerate(241).is_err());
    }

    #[test]
    fn test_validate_seconds_per_day() {
        // Valid values
        assert!(validate_seconds_per_day(10.0).is_ok());
        assert!(validate_seconds_per_day(0.001).is_ok());
        assert!(validate_seconds_per_day(1000.0).is_ok());

        // Invalid values
        assert!(validate_seconds_per_day(0.0).is_err());
        assert!(validate_seconds_per_day(-1.0).is_err());
        assert!(validate_seconds_per_day(f32::NAN).is_err());
        assert!(validate_seconds_per_day(f32::INFINITY).is_err());
    }

    #[test]
    fn test_validate_font_size() {
        // Valid sizes
        assert!(validate_font_size(12.0).is_ok());
        assert!(validate_font_size(4.0).is_ok());
        assert!(validate_font_size(200.0).is_ok());

        // Invalid sizes
        assert!(validate_font_size(3.9).is_err());
        assert!(validate_font_size(201.0).is_err());
        assert!(validate_font_size(-1.0).is_err());
        assert!(validate_font_size(f32::NAN).is_err());
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
