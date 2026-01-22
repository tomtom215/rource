//! Configuration loading methods for Args.
//!
//! This module contains methods for loading settings from config files
//! and environment variables.

use std::path::PathBuf;

use super::Args;

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
