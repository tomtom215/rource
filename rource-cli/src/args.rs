//! Command-line argument parsing for Rource.

use clap::Parser;
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

    /// Parse the background color from hex string.
    pub fn parse_background_color(&self) -> rource_math::Color {
        parse_hex_color(&self.background_color).unwrap_or(rource_math::Color::BLACK)
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
        if (self.font_size - 12.0).abs() < 0.01 && (env_settings.display.font_size - 12.0).abs() > 0.01 {
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
        if self.camera_mode == "overview" && env_settings.camera.mode != rource_core::config::CameraModeSetting::Overview {
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

#[cfg(test)]
mod tests {
    use super::*;

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
        let args = Args {
            path: PathBuf::from("."),
            width: 1280,
            height: 720,
            fullscreen: false,
            seconds_per_day: 10.0,
            auto_skip_seconds: 3.0,
            start_date: None,
            stop_date: None,
            title: None,
            background_color: "000000".to_string(),
            font_size: 12.0,
            no_bloom: false,
            shadows: false,
            hide_filenames: false,
            hide_usernames: false,
            hide_date: false,
            hide_legend: false,
            max_files: 0,
            max_users: 0,
            show_users: None,
            hide_users: None,
            show_files: None,
            hide_files: None,
            hide_dirs: None,
            camera_mode: "overview".to_string(),
            loop_playback: false,
            paused: false,
            disable_input: false,
            custom_log: false,
            output: None,
            framerate: 60,
            headless: false,
            screenshot: None,
            screenshot_at: None,
            config: None,
            sample_config: false,
            env_help: false,
            user_image_dir: None,
            default_user_image: None,
        };

        assert_eq!(args.width, 1280);
        assert_eq!(args.height, 720);
        assert!(args.show_users.is_none());
        assert!(args.hide_users.is_none());
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
        let config_content = r#"
width = 1920
"#;

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
}
