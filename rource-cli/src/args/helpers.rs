// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Helper functions for argument parsing and validation.
//!
//! This module contains utility functions for parsing colors, offsets, dates,
//! and validating argument values.

use rource_math::Color;

/// Parse a hex color string (e.g., "FF0000" or "#FF0000") to a Color.
pub fn parse_hex_color(s: &str) -> Option<Color> {
    let s = s.trim_start_matches('#');
    if s.len() != 6 {
        return None;
    }

    let r = u8::from_str_radix(&s[0..2], 16).ok()?;
    let g = u8::from_str_radix(&s[2..4], 16).ok()?;
    let b = u8::from_str_radix(&s[4..6], 16).ok()?;

    Some(Color::new(
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
pub fn validate_seconds_per_day(value: f32) -> Result<(), String> {
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
pub fn validate_font_size(value: f32) -> Result<(), String> {
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
pub fn parse_offset(s: &str) -> Option<(i32, i32)> {
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
pub fn parse_date(s: &str) -> Option<i64> {
    use chrono::NaiveDate;

    let date = NaiveDate::parse_from_str(s.trim(), "%Y-%m-%d").ok()?;
    let datetime = date.and_hms_opt(0, 0, 0)?;
    Some(datetime.and_utc().timestamp())
}

// ============================================================================
// Additional Helper Functions
// ============================================================================
// Note: These functions are designed for future use and are tested below.
// They follow the established pattern of extracting pure functions for testability.

/// Validate camera mode string.
/// # Arguments
/// * `mode` - Camera mode string (overview, track, follow)
///
/// # Returns
/// `true` if the mode string is valid
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn is_valid_camera_mode(mode: &str) -> bool {
    matches!(
        mode.to_lowercase().as_str(),
        "overview" | "track" | "follow"
    )
}

/// Check if watermark should be enabled based on settings.
///
/// Watermark is enabled if either the flag is set or text is provided.
///
/// # Arguments
/// * `watermark_flag` - Explicit watermark enable flag
/// * `watermark_text` - Optional watermark text
///
/// # Returns
/// `true` if watermark should be enabled
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn should_enable_watermark(watermark_flag: bool, watermark_text: Option<&String>) -> bool {
    watermark_flag || watermark_text.is_some()
}

/// Determine if 3D camera mode should be enabled.
///
/// 3D is enabled only if --3d is set and --2d is not set.
///
/// # Arguments
/// * `camera_3d` - Whether --3d flag was set
/// * `camera_2d` - Whether --2d flag was set
///
/// # Returns
/// `true` if 3D camera should be enabled
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn should_enable_3d_camera(camera_3d: bool, camera_2d: bool) -> bool {
    camera_3d && !camera_2d
}

/// Parse comma-separated usernames into a list.
///
/// # Arguments
/// * `s` - Comma-separated string of usernames
///
/// # Returns
/// Vector of trimmed usernames
#[allow(dead_code)]
#[must_use]
pub fn parse_comma_separated(s: &str) -> Vec<String> {
    if s.trim().is_empty() {
        return Vec::new();
    }
    s.split(',')
        .map(|part| part.trim().to_string())
        .filter(|part| !part.is_empty())
        .collect()
}

/// Calculate title font size from base font size.
///
/// Title is rendered at 1.5x the base font size.
///
/// # Arguments
/// * `base_font_size` - Base font size for regular text
///
/// # Returns
/// Font size for title text
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn calculate_title_font_size(base_font_size: f32) -> f32 {
    base_font_size * 1.5
}

/// Validate watermark position string.
///
/// # Arguments
/// * `pos` - Position string (top-left, top-right, bottom-left, bottom-right)
///
/// # Returns
/// `true` if the position string is valid
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn is_valid_watermark_position(pos: &str) -> bool {
    matches!(
        pos.to_lowercase().as_str(),
        "top-left" | "top-right" | "bottom-left" | "bottom-right"
    )
}

/// Clamp watermark opacity to valid range [0.0, 1.0].
///
/// # Arguments
/// * `opacity` - Input opacity value
///
/// # Returns
/// Clamped opacity value
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn clamp_watermark_opacity(opacity: f32) -> f32 {
    if opacity.is_nan() {
        return 0.5; // Default
    }
    opacity.clamp(0.0, 1.0)
}

/// Clamp directory name position to valid range [0.0, 1.0].
///
/// # Arguments
/// * `position` - Input position value (0.0 = start of edge, 1.0 = end)
///
/// # Returns
/// Clamped position value
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn clamp_dir_name_position(position: f32) -> f32 {
    if position.is_nan() {
        return 0.5; // Default
    }
    position.clamp(0.0, 1.0)
}

/// Validate pitch angle for 3D camera (degrees).
///
/// # Arguments
/// * `pitch` - Pitch angle in degrees
///
/// # Returns
/// `true` if the pitch is within valid range [-90, 90]
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn is_valid_pitch(pitch: f32) -> bool {
    pitch.is_finite() && (-90.0..=90.0).contains(&pitch)
}

/// Clamp pitch angle to valid range [-90, 90] degrees.
///
/// # Arguments
/// * `pitch` - Input pitch angle in degrees
///
/// # Returns
/// Clamped pitch angle
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn clamp_pitch(pitch: f32) -> f32 {
    if pitch.is_nan() {
        return -17.0; // Default
    }
    pitch.clamp(-90.0, 90.0)
}

/// Validate time scale value.
///
/// # Arguments
/// * `scale` - Time scale multiplier
///
/// # Returns
/// `true` if the scale is valid (positive finite number)
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn is_valid_time_scale(scale: f32) -> bool {
    scale.is_finite() && scale > 0.0
}

/// Clamp time scale to valid range [0.01, 100.0].
///
/// # Arguments
/// * `scale` - Input time scale
///
/// # Returns
/// Clamped time scale
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn clamp_time_scale(scale: f32) -> f32 {
    if !scale.is_finite() || scale <= 0.0 {
        return 1.0; // Default
    }
    scale.clamp(0.01, 100.0)
}

/// Validate directory name depth.
///
/// # Arguments
/// * `depth` - Directory depth value
///
/// # Returns
/// `true` if depth is within reasonable range [0, 10]
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn is_valid_dir_name_depth(depth: u32) -> bool {
    depth <= 10
}

/// Check if a path looks like a custom log file (not a directory).
///
/// # Arguments
/// * `path` - Path to check
///
/// # Returns
/// `true` if path appears to be a file (has extension or doesn't exist as directory)
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn looks_like_custom_log(path: &std::path::Path) -> bool {
    // If path has a common log extension, treat as custom log
    // If no extension, check if it's a file
    path.extension().map_or_else(
        || path.is_file(),
        |ext| {
            let ext_str = ext.to_string_lossy().to_lowercase();
            matches!(ext_str.as_str(), "log" | "txt" | "csv" | "tsv")
        },
    )
}

/// Validate that headless mode has output path.
///
/// # Arguments
/// * `headless` - Whether headless mode is enabled
/// * `output` - Optional output path
///
/// # Returns
/// `Ok(())` if valid, `Err` with message if invalid
#[allow(dead_code)]
#[inline]
pub fn validate_headless_output(
    headless: bool,
    output: Option<&std::path::PathBuf>,
) -> Result<(), String> {
    if headless && output.is_none() {
        Err("--headless requires --output to specify frame output directory".to_string())
    } else {
        Ok(())
    }
}

/// Convert a color to CSS hex string format.
///
/// # Arguments
/// * `color` - Color to convert
///
/// # Returns
/// Hex color string without # prefix (e.g., "FF0000")
#[allow(dead_code)]
#[inline]
#[must_use]
pub fn color_to_css_hex(color: &Color) -> String {
    format!(
        "{:02X}{:02X}{:02X}",
        (color.r * 255.0).round() as u8,
        (color.g * 255.0).round() as u8,
        (color.b * 255.0).round() as u8
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    // ========================================================================
    // Original Parse/Validate Tests
    // ========================================================================

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
    fn test_parse_offset() {
        assert_eq!(parse_offset("10x20"), Some((10, 20)));
        assert_eq!(parse_offset("0x0"), Some((0, 0)));
        assert_eq!(parse_offset("10,20"), Some((10, 20)));
        assert_eq!(parse_offset(""), Some((0, 0)));
        assert_eq!(parse_offset("invalid"), None);
    }

    #[test]
    fn test_parse_date() {
        // Valid date
        let ts = parse_date("2024-01-15").unwrap();
        assert!(ts > 0);

        // Invalid dates
        assert!(parse_date("invalid").is_none());
        assert!(parse_date("2024/01/15").is_none());
    }

    // ========================================================================
    // Additional Helper Function Tests
    // ========================================================================

    #[test]
    fn test_is_valid_camera_mode() {
        assert!(is_valid_camera_mode("overview"));
        assert!(is_valid_camera_mode("track"));
        assert!(is_valid_camera_mode("follow"));
        assert!(is_valid_camera_mode("OVERVIEW")); // Case insensitive
        assert!(is_valid_camera_mode("Track"));
        assert!(!is_valid_camera_mode("invalid"));
        assert!(!is_valid_camera_mode(""));
    }

    #[test]
    fn test_should_enable_watermark() {
        let text = "text".to_string();
        // Flag only
        assert!(should_enable_watermark(true, None));
        // Text only
        assert!(should_enable_watermark(false, Some(&text)));
        // Both
        assert!(should_enable_watermark(true, Some(&text)));
        // Neither
        assert!(!should_enable_watermark(false, None));
    }

    #[test]
    fn test_should_enable_3d_camera() {
        // --3d only
        assert!(should_enable_3d_camera(true, false));
        // --2d overrides --3d
        assert!(!should_enable_3d_camera(true, true));
        // Neither
        assert!(!should_enable_3d_camera(false, false));
        // --2d only
        assert!(!should_enable_3d_camera(false, true));
    }

    #[test]
    fn test_parse_comma_separated() {
        assert_eq!(
            parse_comma_separated("alice,bob,charlie"),
            vec!["alice", "bob", "charlie"]
        );
        assert_eq!(
            parse_comma_separated("alice, bob, charlie"),
            vec!["alice", "bob", "charlie"]
        );
        assert_eq!(parse_comma_separated("single"), vec!["single"]);
        assert!(parse_comma_separated("").is_empty());
        assert!(parse_comma_separated("   ").is_empty());
    }

    #[test]
    fn test_parse_comma_separated_empty_parts() {
        // Empty parts are filtered out
        assert_eq!(parse_comma_separated("alice,,bob"), vec!["alice", "bob"]);
        assert_eq!(parse_comma_separated(",alice,"), vec!["alice"]);
    }

    #[test]
    fn test_calculate_title_font_size() {
        assert!((calculate_title_font_size(12.0) - 18.0).abs() < 0.01);
        assert!((calculate_title_font_size(10.0) - 15.0).abs() < 0.01);
        assert!((calculate_title_font_size(0.0) - 0.0).abs() < 0.01);
    }

    #[test]
    fn test_is_valid_watermark_position() {
        assert!(is_valid_watermark_position("top-left"));
        assert!(is_valid_watermark_position("top-right"));
        assert!(is_valid_watermark_position("bottom-left"));
        assert!(is_valid_watermark_position("bottom-right"));
        assert!(is_valid_watermark_position("TOP-LEFT")); // Case insensitive
        assert!(!is_valid_watermark_position("center"));
        assert!(!is_valid_watermark_position(""));
        assert!(!is_valid_watermark_position("topleft")); // No hyphen
    }

    #[test]
    fn test_clamp_watermark_opacity() {
        assert!((clamp_watermark_opacity(0.5) - 0.5).abs() < 0.01);
        assert!((clamp_watermark_opacity(0.0) - 0.0).abs() < 0.01);
        assert!((clamp_watermark_opacity(1.0) - 1.0).abs() < 0.01);
        assert!((clamp_watermark_opacity(-0.5) - 0.0).abs() < 0.01); // Clamped to 0
        assert!((clamp_watermark_opacity(1.5) - 1.0).abs() < 0.01); // Clamped to 1
        assert!((clamp_watermark_opacity(f32::NAN) - 0.5).abs() < 0.01); // Default
    }

    #[test]
    fn test_clamp_dir_name_position() {
        assert!((clamp_dir_name_position(0.5) - 0.5).abs() < 0.01);
        assert!((clamp_dir_name_position(0.0) - 0.0).abs() < 0.01);
        assert!((clamp_dir_name_position(1.0) - 1.0).abs() < 0.01);
        assert!((clamp_dir_name_position(-0.5) - 0.0).abs() < 0.01); // Clamped
        assert!((clamp_dir_name_position(1.5) - 1.0).abs() < 0.01); // Clamped
        assert!((clamp_dir_name_position(f32::NAN) - 0.5).abs() < 0.01); // Default
    }

    #[test]
    fn test_is_valid_pitch() {
        assert!(is_valid_pitch(0.0));
        assert!(is_valid_pitch(-17.0));
        assert!(is_valid_pitch(-90.0));
        assert!(is_valid_pitch(90.0));
        assert!(!is_valid_pitch(-91.0));
        assert!(!is_valid_pitch(91.0));
        assert!(!is_valid_pitch(f32::NAN));
        assert!(!is_valid_pitch(f32::INFINITY));
    }

    #[test]
    fn test_clamp_pitch() {
        assert!((clamp_pitch(0.0) - 0.0).abs() < 0.01);
        assert!((clamp_pitch(-17.0) - (-17.0)).abs() < 0.01);
        assert!((clamp_pitch(-100.0) - (-90.0)).abs() < 0.01); // Clamped
        assert!((clamp_pitch(100.0) - 90.0).abs() < 0.01); // Clamped
        assert!((clamp_pitch(f32::NAN) - (-17.0)).abs() < 0.01); // Default
    }

    #[test]
    fn test_is_valid_time_scale() {
        assert!(is_valid_time_scale(1.0));
        assert!(is_valid_time_scale(0.5));
        assert!(is_valid_time_scale(2.0));
        assert!(!is_valid_time_scale(0.0));
        assert!(!is_valid_time_scale(-1.0));
        assert!(!is_valid_time_scale(f32::NAN));
        assert!(!is_valid_time_scale(f32::INFINITY));
    }

    #[test]
    fn test_clamp_time_scale() {
        assert!((clamp_time_scale(1.0) - 1.0).abs() < 0.01);
        assert!((clamp_time_scale(2.0) - 2.0).abs() < 0.01);
        assert!((clamp_time_scale(0.001) - 0.01).abs() < 0.01); // Clamped to min
        assert!((clamp_time_scale(200.0) - 100.0).abs() < 0.01); // Clamped to max
        assert!((clamp_time_scale(0.0) - 1.0).abs() < 0.01); // Default
        assert!((clamp_time_scale(-1.0) - 1.0).abs() < 0.01); // Default
        assert!((clamp_time_scale(f32::NAN) - 1.0).abs() < 0.01); // Default
    }

    #[test]
    fn test_is_valid_dir_name_depth() {
        assert!(is_valid_dir_name_depth(0));
        assert!(is_valid_dir_name_depth(1));
        assert!(is_valid_dir_name_depth(10));
        assert!(!is_valid_dir_name_depth(11));
        assert!(!is_valid_dir_name_depth(100));
    }

    #[test]
    fn test_looks_like_custom_log_extensions() {
        assert!(looks_like_custom_log(&PathBuf::from("data.log")));
        assert!(looks_like_custom_log(&PathBuf::from("commits.txt")));
        assert!(looks_like_custom_log(&PathBuf::from("data.csv")));
        assert!(looks_like_custom_log(&PathBuf::from("data.tsv")));
    }

    #[test]
    fn test_looks_like_custom_log_no_extension() {
        // Without file system check, we can only test extension-based logic
        // Files without extensions need to exist to determine if they're files
        let path = PathBuf::from("no_extension");
        // This will return false if path doesn't exist and has no extension
        let _ = looks_like_custom_log(&path);
    }

    #[test]
    fn test_validate_headless_output() {
        let output_path = PathBuf::from("/tmp");
        // Valid: headless with output
        assert!(validate_headless_output(true, Some(&output_path)).is_ok());
        // Valid: not headless
        assert!(validate_headless_output(false, None).is_ok());
        // Invalid: headless without output
        assert!(validate_headless_output(true, None).is_err());
    }

    #[test]
    fn test_color_to_css_hex() {
        let white = Color::new(1.0, 1.0, 1.0, 1.0);
        assert_eq!(color_to_css_hex(&white), "FFFFFF");

        let red = Color::new(1.0, 0.0, 0.0, 1.0);
        assert_eq!(color_to_css_hex(&red), "FF0000");

        let black = Color::new(0.0, 0.0, 0.0, 1.0);
        assert_eq!(color_to_css_hex(&black), "000000");

        let half_gray = Color::new(0.5, 0.5, 0.5, 1.0);
        // 0.5 * 255 = 127.5 -> rounds to 128 = 0x80
        assert_eq!(color_to_css_hex(&half_gray), "808080");
    }

    #[test]
    fn test_color_roundtrip() {
        // Test that parsing and formatting a color gives consistent results
        let original_hex = "FF5500";
        let color = parse_hex_color(original_hex).unwrap();
        let result_hex = color_to_css_hex(&color);
        assert_eq!(result_hex, original_hex);
    }
}
