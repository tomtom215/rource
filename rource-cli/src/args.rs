//! Command-line argument parsing for Rource.

use clap::Parser;
use std::path::PathBuf;

/// Rource - Software version control visualization tool.
///
/// A complete rewrite of Gource in Rust with WebAssembly support.
#[derive(Parser, Debug)]
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

    /// Maximum number of files to display (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    pub max_files: usize,

    /// Maximum number of users to display (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    pub max_users: usize,

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
            max_files: 0,
            max_users: 0,
            camera_mode: "overview".to_string(),
            loop_playback: false,
            paused: false,
            disable_input: false,
            custom_log: false,
            output: None,
            framerate: 60,
        };

        assert_eq!(args.width, 1280);
        assert_eq!(args.height, 720);
    }
}
