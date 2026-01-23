// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Configuration loading methods for Args.
//!
//! This module contains methods for loading settings from config files
//! and environment variables.
//!
//! ## Helper Functions
//!
//! This module exports testable helper functions for configuration processing:
//! - [`is_at_default_f32`] - Check if a float value is at its default
//! - [`is_at_default_string`] - Check if a string value is at its default
//! - [`color_to_hex_string`] - Convert a Color to hex string representation

use std::path::PathBuf;

use rource_math::Color;

use super::Args;

// ============================================================================
// Helper Functions (testable without Args instance)
// ============================================================================

/// Helper functions for configuration processing.
///
/// These functions encapsulate pure computations that can be unit tested
/// without requiring a full Args or config file context.
#[allow(dead_code)]
#[allow(clippy::wildcard_imports)]
mod helpers {
    use super::*;

    /// Default epsilon for floating-point comparisons.
    pub const DEFAULT_EPSILON: f32 = 0.01;

    /// Checks if a floating-point value is at its default within an epsilon.
    ///
    /// # Arguments
    /// * `value` - The current value to check
    /// * `default` - The default value to compare against
    /// * `epsilon` - Maximum difference to consider equal (default: 0.01)
    ///
    /// # Returns
    /// `true` if `|value - default| < epsilon`
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::is_at_default_f32;
    /// assert!(is_at_default_f32(10.0, 10.0, 0.01));
    /// assert!(is_at_default_f32(10.005, 10.0, 0.01));
    /// assert!(!is_at_default_f32(10.5, 10.0, 0.01));
    /// ```
    #[inline]
    #[must_use]
    pub fn is_at_default_f32(value: f32, default: f32, epsilon: f32) -> bool {
        (value - default).abs() < epsilon
    }

    /// Checks if a string value matches its default.
    ///
    /// # Arguments
    /// * `value` - The current value to check
    /// * `default` - The default value to compare against
    ///
    /// # Returns
    /// `true` if the strings are equal.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::is_at_default_string;
    /// assert!(is_at_default_string("000000", "000000"));
    /// assert!(!is_at_default_string("FFFFFF", "000000"));
    /// ```
    #[inline]
    #[must_use]
    pub fn is_at_default_string(value: &str, default: &str) -> bool {
        value == default
    }

    /// Checks if an integer value matches its default.
    ///
    /// # Arguments
    /// * `value` - The current value to check
    /// * `default` - The default value to compare against
    ///
    /// # Returns
    /// `true` if the values are equal.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::is_at_default_u32;
    /// assert!(is_at_default_u32(1280, 1280));
    /// assert!(!is_at_default_u32(1920, 1280));
    /// ```
    #[inline]
    #[must_use]
    pub fn is_at_default_u32(value: u32, default: u32) -> bool {
        value == default
    }

    /// Converts a Color to a hex string representation.
    ///
    /// The output format is uppercase hex without a leading `#`, e.g., "FF00AA".
    ///
    /// # Arguments
    /// * `color` - The color to convert
    ///
    /// # Returns
    /// A 6-character hex string representing the RGB components.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::color_to_hex_string;
    /// use rource_math::Color;
    /// assert_eq!(color_to_hex_string(&Color::BLACK), "000000");
    /// assert_eq!(color_to_hex_string(&Color::WHITE), "FFFFFF");
    /// assert_eq!(color_to_hex_string(&Color::new(1.0, 0.0, 0.0, 1.0)), "FF0000");
    /// ```
    #[inline]
    #[must_use]
    pub fn color_to_hex_string(color: &Color) -> String {
        format!(
            "{:02X}{:02X}{:02X}",
            (color.r * 255.0) as u8,
            (color.g * 255.0) as u8,
            (color.b * 255.0) as u8
        )
    }

    /// Checks if a Color is non-black (has any RGB component > 0).
    ///
    /// This is used to determine if a background color from environment
    /// settings should override the default black background.
    ///
    /// # Arguments
    /// * `color` - The color to check
    ///
    /// # Returns
    /// `true` if any of r, g, or b is greater than 0.0.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::is_non_black_color;
    /// use rource_math::Color;
    /// assert!(!is_non_black_color(&Color::BLACK));
    /// assert!(is_non_black_color(&Color::WHITE));
    /// assert!(is_non_black_color(&Color::new(0.5, 0.0, 0.0, 1.0)));
    /// ```
    #[inline]
    #[must_use]
    pub fn is_non_black_color(color: &Color) -> bool {
        color.r > 0.0 || color.g > 0.0 || color.b > 0.0
    }

    /// Validates that a dimension value is reasonable for display.
    ///
    /// Returns the value clamped to a reasonable range [1, 16384].
    ///
    /// # Arguments
    /// * `value` - The dimension value to validate
    ///
    /// # Returns
    /// The clamped dimension value.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::clamp_dimension;
    /// assert_eq!(clamp_dimension(0), 1);
    /// assert_eq!(clamp_dimension(1920), 1920);
    /// assert_eq!(clamp_dimension(100000), 16384);
    /// ```
    #[inline]
    #[must_use]
    pub fn clamp_dimension(value: u32) -> u32 {
        value.clamp(1, 16384)
    }

    /// Validates that a framerate value is reasonable.
    ///
    /// Returns the value clamped to [1, 240].
    ///
    /// # Arguments
    /// * `value` - The framerate value to validate
    ///
    /// # Returns
    /// The clamped framerate value.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::clamp_framerate;
    /// assert_eq!(clamp_framerate(0), 1);
    /// assert_eq!(clamp_framerate(60), 60);
    /// assert_eq!(clamp_framerate(1000), 240);
    /// ```
    #[inline]
    #[must_use]
    pub fn clamp_framerate(value: u32) -> u32 {
        value.clamp(1, 240)
    }

    /// Validates that a font size is reasonable.
    ///
    /// Returns the value clamped to [4.0, 72.0].
    ///
    /// # Arguments
    /// * `value` - The font size to validate
    ///
    /// # Returns
    /// The clamped font size.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::clamp_font_size;
    /// assert!((clamp_font_size(1.0) - 4.0).abs() < 0.001);
    /// assert!((clamp_font_size(12.0) - 12.0).abs() < 0.001);
    /// assert!((clamp_font_size(100.0) - 72.0).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn clamp_font_size(value: f32) -> f32 {
        value.clamp(4.0, 72.0)
    }

    /// Validates that a playback speed is reasonable.
    ///
    /// Returns the value clamped to [0.01, 1000.0].
    ///
    /// # Arguments
    /// * `value` - The seconds per day value to validate
    ///
    /// # Returns
    /// The clamped playback speed.
    ///
    /// # Examples
    /// ```
    /// use rource::args::config_methods::clamp_seconds_per_day;
    /// assert!((clamp_seconds_per_day(0.001) - 0.01).abs() < 0.001);
    /// assert!((clamp_seconds_per_day(10.0) - 10.0).abs() < 0.001);
    /// assert!((clamp_seconds_per_day(5000.0) - 1000.0).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn clamp_seconds_per_day(value: f32) -> f32 {
        value.clamp(0.01, 1000.0)
    }
}

#[allow(unused_imports)]
pub use helpers::*;

impl Args {
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
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Float Default Check Tests
    // ========================================================================

    #[test]
    fn test_is_at_default_f32_exact_match() {
        assert!(is_at_default_f32(10.0, 10.0, 0.01));
        assert!(is_at_default_f32(0.0, 0.0, 0.01));
        assert!(is_at_default_f32(12.0, 12.0, 0.01));
    }

    #[test]
    fn test_is_at_default_f32_within_epsilon() {
        // Just under epsilon
        assert!(is_at_default_f32(10.005, 10.0, 0.01));
        assert!(is_at_default_f32(9.995, 10.0, 0.01));
    }

    #[test]
    fn test_is_at_default_f32_outside_epsilon() {
        // Just over epsilon
        assert!(!is_at_default_f32(10.02, 10.0, 0.01));
        assert!(!is_at_default_f32(9.98, 10.0, 0.01));
        assert!(!is_at_default_f32(15.0, 10.0, 0.01));
    }

    #[test]
    fn test_is_at_default_f32_custom_epsilon() {
        // Large epsilon
        assert!(is_at_default_f32(10.5, 10.0, 1.0));
        assert!(!is_at_default_f32(11.5, 10.0, 1.0));

        // Tiny epsilon
        assert!(is_at_default_f32(10.0001, 10.0, 0.001));
        assert!(!is_at_default_f32(10.002, 10.0, 0.001));
    }

    #[test]
    fn test_is_at_default_f32_negative_values() {
        assert!(is_at_default_f32(-5.0, -5.0, 0.01));
        assert!(!is_at_default_f32(-5.0, 5.0, 0.01));
    }

    // ========================================================================
    // String Default Check Tests
    // ========================================================================

    #[test]
    fn test_is_at_default_string_match() {
        assert!(is_at_default_string("000000", "000000"));
        assert!(is_at_default_string("overview", "overview"));
        assert!(is_at_default_string("", ""));
    }

    #[test]
    fn test_is_at_default_string_no_match() {
        assert!(!is_at_default_string("FFFFFF", "000000"));
        assert!(!is_at_default_string("follow", "overview"));
        assert!(!is_at_default_string("abc", "ABC")); // Case sensitive
    }

    #[test]
    fn test_is_at_default_string_empty_vs_non_empty() {
        assert!(!is_at_default_string("", "something"));
        assert!(!is_at_default_string("something", ""));
    }

    // ========================================================================
    // Integer Default Check Tests
    // ========================================================================

    #[test]
    fn test_is_at_default_u32_match() {
        assert!(is_at_default_u32(1280, 1280));
        assert!(is_at_default_u32(720, 720));
        assert!(is_at_default_u32(0, 0));
    }

    #[test]
    fn test_is_at_default_u32_no_match() {
        assert!(!is_at_default_u32(1920, 1280));
        assert!(!is_at_default_u32(1080, 720));
        assert!(!is_at_default_u32(1, 0));
    }

    // ========================================================================
    // Color to Hex Tests
    // ========================================================================

    #[test]
    fn test_color_to_hex_string_black() {
        let black = Color::new(0.0, 0.0, 0.0, 1.0);
        assert_eq!(color_to_hex_string(&black), "000000");
    }

    #[test]
    fn test_color_to_hex_string_white() {
        let white = Color::new(1.0, 1.0, 1.0, 1.0);
        assert_eq!(color_to_hex_string(&white), "FFFFFF");
    }

    #[test]
    fn test_color_to_hex_string_primary_colors() {
        let red = Color::new(1.0, 0.0, 0.0, 1.0);
        assert_eq!(color_to_hex_string(&red), "FF0000");

        let green = Color::new(0.0, 1.0, 0.0, 1.0);
        assert_eq!(color_to_hex_string(&green), "00FF00");

        let blue = Color::new(0.0, 0.0, 1.0, 1.0);
        assert_eq!(color_to_hex_string(&blue), "0000FF");
    }

    #[test]
    fn test_color_to_hex_string_mid_values() {
        // 0.5 * 255 = 127.5 -> 127 -> 0x7F
        let mid = Color::new(0.5, 0.5, 0.5, 1.0);
        assert_eq!(color_to_hex_string(&mid), "7F7F7F");
    }

    #[test]
    fn test_color_to_hex_string_ignores_alpha() {
        let with_alpha = Color::new(1.0, 0.0, 0.0, 0.5);
        assert_eq!(color_to_hex_string(&with_alpha), "FF0000");

        let transparent = Color::new(0.0, 1.0, 0.0, 0.0);
        assert_eq!(color_to_hex_string(&transparent), "00FF00");
    }

    // ========================================================================
    // Non-Black Color Check Tests
    // ========================================================================

    #[test]
    fn test_is_non_black_color_black() {
        let black = Color::new(0.0, 0.0, 0.0, 1.0);
        assert!(!is_non_black_color(&black));
    }

    #[test]
    fn test_is_non_black_color_white() {
        let white = Color::new(1.0, 1.0, 1.0, 1.0);
        assert!(is_non_black_color(&white));
    }

    #[test]
    fn test_is_non_black_color_single_channel() {
        let red = Color::new(0.5, 0.0, 0.0, 1.0);
        assert!(is_non_black_color(&red));

        let green = Color::new(0.0, 0.5, 0.0, 1.0);
        assert!(is_non_black_color(&green));

        let blue = Color::new(0.0, 0.0, 0.5, 1.0);
        assert!(is_non_black_color(&blue));
    }

    #[test]
    fn test_is_non_black_color_ignores_alpha() {
        // Black with non-zero alpha is still black
        let black_with_alpha = Color::new(0.0, 0.0, 0.0, 0.5);
        assert!(!is_non_black_color(&black_with_alpha));
    }

    // ========================================================================
    // Dimension Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_dimension_normal_values() {
        assert_eq!(clamp_dimension(1280), 1280);
        assert_eq!(clamp_dimension(1920), 1920);
        assert_eq!(clamp_dimension(4096), 4096);
    }

    #[test]
    fn test_clamp_dimension_minimum() {
        assert_eq!(clamp_dimension(0), 1);
        assert_eq!(clamp_dimension(1), 1);
    }

    #[test]
    fn test_clamp_dimension_maximum() {
        assert_eq!(clamp_dimension(16384), 16384);
        assert_eq!(clamp_dimension(16385), 16384);
        assert_eq!(clamp_dimension(100_000), 16384);
    }

    // ========================================================================
    // Framerate Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_framerate_normal_values() {
        assert_eq!(clamp_framerate(30), 30);
        assert_eq!(clamp_framerate(60), 60);
        assert_eq!(clamp_framerate(144), 144);
    }

    #[test]
    fn test_clamp_framerate_minimum() {
        assert_eq!(clamp_framerate(0), 1);
        assert_eq!(clamp_framerate(1), 1);
    }

    #[test]
    fn test_clamp_framerate_maximum() {
        assert_eq!(clamp_framerate(240), 240);
        assert_eq!(clamp_framerate(241), 240);
        assert_eq!(clamp_framerate(1000), 240);
    }

    // ========================================================================
    // Font Size Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_font_size_normal_values() {
        assert!((clamp_font_size(12.0) - 12.0).abs() < 0.001);
        assert!((clamp_font_size(16.0) - 16.0).abs() < 0.001);
        assert!((clamp_font_size(24.0) - 24.0).abs() < 0.001);
    }

    #[test]
    fn test_clamp_font_size_minimum() {
        assert!((clamp_font_size(1.0) - 4.0).abs() < 0.001);
        assert!((clamp_font_size(4.0) - 4.0).abs() < 0.001);
        assert!((clamp_font_size(0.0) - 4.0).abs() < 0.001);
    }

    #[test]
    fn test_clamp_font_size_maximum() {
        assert!((clamp_font_size(72.0) - 72.0).abs() < 0.001);
        assert!((clamp_font_size(73.0) - 72.0).abs() < 0.001);
        assert!((clamp_font_size(200.0) - 72.0).abs() < 0.001);
    }

    // ========================================================================
    // Seconds Per Day Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_seconds_per_day_normal_values() {
        assert!((clamp_seconds_per_day(10.0) - 10.0).abs() < 0.001);
        assert!((clamp_seconds_per_day(1.0) - 1.0).abs() < 0.001);
        assert!((clamp_seconds_per_day(100.0) - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_clamp_seconds_per_day_minimum() {
        assert!((clamp_seconds_per_day(0.001) - 0.01).abs() < 0.001);
        assert!((clamp_seconds_per_day(0.01) - 0.01).abs() < 0.001);
        assert!((clamp_seconds_per_day(0.0) - 0.01).abs() < 0.001);
    }

    #[test]
    fn test_clamp_seconds_per_day_maximum() {
        assert!((clamp_seconds_per_day(1000.0) - 1000.0).abs() < 0.001);
        assert!((clamp_seconds_per_day(1001.0) - 1000.0).abs() < 0.001);
        assert!((clamp_seconds_per_day(5000.0) - 1000.0).abs() < 0.001);
    }
}
