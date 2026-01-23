// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Help text and sample configuration content.
//!
//! This module contains static help text strings for environment variable
//! documentation and sample configuration files.

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
  ROURCE_MIN_ZOOM           Minimum zoom level (default: 0.05, prevents LOD culling)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sample_config() {
        let sample = sample_config();
        assert!(sample.contains("width"));
        assert!(sample.contains("seconds_per_day"));
        assert!(sample.contains("background_color"));
    }

    #[test]
    fn test_env_help() {
        let help = env_help();
        assert!(help.contains("ROURCE_WIDTH"));
        assert!(help.contains("ROURCE_SECONDS_PER_DAY"));
        assert!(help.contains("ROURCE_BLOOM_ENABLED"));
        assert!(help.contains("DISPLAY SETTINGS"));
        assert!(help.contains("PLAYBACK SETTINGS"));
        assert!(help.contains("FILTER SETTINGS"));
    }
}
