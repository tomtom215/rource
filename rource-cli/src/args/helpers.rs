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
}
