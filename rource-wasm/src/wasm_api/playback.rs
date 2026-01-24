// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Playback control for timeline navigation.
//!
//! This module provides methods to control the visualization timeline:
//! - Play/pause/toggle
//! - Seek to specific commits
//! - Speed control
//! - Step forward/backward
//! - Commit metadata access

use wasm_bindgen::prelude::*;

use crate::playback::{apply_vcs_commit, get_date_range, prewarm_scene};
use crate::Rource;

// ============================================================================
// Helper Functions (testable without Rource instance)
// ============================================================================

#[allow(dead_code)]
mod helpers {
    /// Validates and clamps a playback speed value.
    ///
    /// Returns a valid speed in the range [0.01, 1000.0], or the default (10.0)
    /// for invalid inputs like NaN, infinity, or non-positive values.
    ///
    /// # Arguments
    /// * `seconds_per_day` - The requested playback speed
    ///
    /// # Returns
    /// A valid, clamped speed value.
    #[inline]
    #[must_use]
    pub fn validate_speed(seconds_per_day: f32) -> f32 {
        let speed = if seconds_per_day.is_finite() && seconds_per_day > 0.0 {
            seconds_per_day
        } else {
            10.0
        };
        speed.clamp(0.01, 1000.0)
    }

    /// Formats a date range as a JSON string.
    ///
    /// # Arguments
    /// * `start` - Start timestamp in seconds since Unix epoch
    /// * `end` - End timestamp in seconds since Unix epoch
    ///
    /// # Returns
    /// JSON string with `startTimestamp` and `endTimestamp` fields.
    #[inline]
    #[must_use]
    pub fn format_date_range(start: i64, end: i64) -> String {
        format!(r#"{{"startTimestamp":{start},"endTimestamp":{end}}}"#)
    }
}

#[allow(unused_imports)]
pub use helpers::*;

// ============================================================================
// Playback Control
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Starts playback.
    pub fn play(&mut self) {
        self.playback.play();
    }

    /// Pauses playback.
    pub fn pause(&mut self) {
        self.playback.pause();
    }

    /// Returns whether playback is active.
    #[wasm_bindgen(js_name = isPlaying)]
    pub fn is_playing(&self) -> bool {
        self.playback.is_playing()
    }

    /// Toggles play/pause state.
    #[wasm_bindgen(js_name = togglePlay)]
    pub fn toggle_play(&mut self) {
        self.playback.toggle_play();
    }

    /// Seeks to a specific commit index.
    ///
    /// This rebuilds the scene state by replaying all commits up to the
    /// specified index, then pre-warms the physics simulation.
    ///
    /// # Performance Warning
    ///
    /// For large repositories, seeking to a distant commit (e.g., commit 50,000
    /// in a 100K commit repo) will apply all previous commits synchronously,
    /// which may cause brief UI freezing. Consider using incremental playback
    /// for very large repositories.
    pub fn seek(&mut self, commit_index: usize) {
        if commit_index < self.commits.len() {
            // Log warning for large seeks
            #[cfg(target_arch = "wasm32")]
            if commit_index > 10000 {
                web_sys::console::warn_1(
                    &format!(
                        "Seeking to commit {} may take a moment (replaying {} commits)",
                        commit_index, commit_index
                    )
                    .into(),
                );
            }

            // Reset scene and replay commits up to the target
            self.scene = rource_core::scene::Scene::new();
            self.playback.set_current_commit(0);
            self.playback.set_last_applied_commit(0);

            for i in 0..=commit_index {
                if i < self.commits.len() {
                    apply_vcs_commit(&mut self.scene, &self.commits[i]);
                }
            }

            self.playback.set_current_commit(commit_index);
            self.playback.set_last_applied_commit(commit_index);
            self.playback.reset_accumulated_time();

            // Pre-warm the scene physics
            prewarm_scene(&mut self.scene, 30, 1.0 / 60.0);

            // Position camera to show content
            self.fit_camera_to_content();
        }
    }

    /// Returns the current commit index.
    #[wasm_bindgen(js_name = currentCommit)]
    pub fn current_commit(&self) -> usize {
        self.playback.current_commit()
    }

    /// Returns the timestamp for a commit at the given index.
    #[wasm_bindgen(js_name = getCommitTimestamp)]
    pub fn get_commit_timestamp(&self, index: usize) -> f64 {
        self.commits.get(index).map_or(0.0, |c| c.timestamp as f64)
    }

    /// Returns the author name for a commit at the given index.
    #[wasm_bindgen(js_name = getCommitAuthor)]
    pub fn get_commit_author(&self, index: usize) -> String {
        self.commits
            .get(index)
            .map_or_else(String::new, |c| c.author.clone())
    }

    /// Returns the number of files changed in a commit at the given index.
    #[wasm_bindgen(js_name = getCommitFileCount)]
    pub fn get_commit_file_count(&self, index: usize) -> usize {
        self.commits.get(index).map_or(0, |c| c.files.len())
    }

    /// Returns the date range of all commits as a JSON object.
    ///
    /// Returns `{"startTimestamp": <unix_ts>, "endTimestamp": <unix_ts>}` or null
    /// if no commits are loaded.
    #[wasm_bindgen(js_name = getDateRange)]
    pub fn get_date_range(&self) -> Option<String> {
        get_date_range(&self.commits)
            .map(|(start, end)| format!(r#"{{"startTimestamp":{start},"endTimestamp":{end}}}"#))
    }

    /// Sets playback speed (seconds per day of repository history).
    ///
    /// Lower values = faster playback. Default is 10.0.
    /// Range: [0.01, 1000.0]
    #[wasm_bindgen(js_name = setSpeed)]
    pub fn set_speed(&mut self, seconds_per_day: f32) {
        let speed = if seconds_per_day.is_finite() && seconds_per_day > 0.0 {
            seconds_per_day
        } else {
            10.0
        };
        self.settings.playback.seconds_per_day = speed.clamp(0.01, 1000.0);
    }

    /// Gets the current playback speed.
    #[wasm_bindgen(js_name = getSpeed)]
    pub fn get_speed(&self) -> f32 {
        self.settings.playback.seconds_per_day
    }

    /// Steps forward to the next commit.
    #[wasm_bindgen(js_name = stepForward)]
    pub fn step_forward(&mut self) {
        let current = self.playback.current_commit();
        if current < self.commits.len().saturating_sub(1) {
            self.seek(current + 1);
        }
    }

    /// Steps backward to the previous commit.
    #[wasm_bindgen(js_name = stepBackward)]
    pub fn step_backward(&mut self) {
        let current = self.playback.current_commit();
        if current > 0 {
            self.seek(current - 1);
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
    // Speed Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_speed_normal_values() {
        assert!((validate_speed(10.0) - 10.0).abs() < 0.001);
        assert!((validate_speed(1.0) - 1.0).abs() < 0.001);
        assert!((validate_speed(100.0) - 100.0).abs() < 0.001);
        assert!((validate_speed(0.5) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_validate_speed_clamp_minimum() {
        assert!((validate_speed(0.005) - 0.01).abs() < 0.001);
        assert!((validate_speed(0.001) - 0.01).abs() < 0.001);
    }

    #[test]
    fn test_validate_speed_clamp_maximum() {
        assert!((validate_speed(1001.0) - 1000.0).abs() < 0.001);
        assert!((validate_speed(5000.0) - 1000.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_speed_invalid_nan() {
        // NaN should return default (10.0)
        let result = validate_speed(f32::NAN);
        assert!((result - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_speed_invalid_infinity() {
        // Positive infinity should return default
        let result = validate_speed(f32::INFINITY);
        assert!((result - 10.0).abs() < 0.001);

        // Negative infinity should return default
        let result = validate_speed(f32::NEG_INFINITY);
        assert!((result - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_speed_invalid_negative() {
        // Negative values should return default
        assert!((validate_speed(-1.0) - 10.0).abs() < 0.001);
        assert!((validate_speed(-100.0) - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_speed_invalid_zero() {
        // Zero should return default
        assert!((validate_speed(0.0) - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_speed_edge_values() {
        // Exactly at minimum
        assert!((validate_speed(0.01) - 0.01).abs() < 0.001);

        // Exactly at maximum
        assert!((validate_speed(1000.0) - 1000.0).abs() < 0.001);
    }

    // ========================================================================
    // Date Range Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_date_range_basic() {
        let result = format_date_range(1000, 2000);
        assert_eq!(result, r#"{"startTimestamp":1000,"endTimestamp":2000}"#);
    }

    #[test]
    fn test_format_date_range_same_values() {
        let result = format_date_range(1500, 1500);
        assert_eq!(result, r#"{"startTimestamp":1500,"endTimestamp":1500}"#);
    }

    #[test]
    fn test_format_date_range_large_timestamps() {
        // Unix timestamp for 2026-01-23
        let result = format_date_range(1_769_212_800, 1_769_299_200);
        assert_eq!(
            result,
            r#"{"startTimestamp":1769212800,"endTimestamp":1769299200}"#
        );
    }

    #[test]
    fn test_format_date_range_zero_values() {
        let result = format_date_range(0, 0);
        assert_eq!(result, r#"{"startTimestamp":0,"endTimestamp":0}"#);
    }

    #[test]
    fn test_format_date_range_negative_values() {
        // Timestamps before Unix epoch
        let result = format_date_range(-86400, 0);
        assert_eq!(result, r#"{"startTimestamp":-86400,"endTimestamp":0}"#);
    }
}
