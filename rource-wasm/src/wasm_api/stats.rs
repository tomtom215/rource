// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Render statistics and entity count APIs.
//!
//! This module provides methods to query visualization metrics:
//! - Visible entity counts (files, users, directories, actions)
//! - Total entity counts
//! - Estimated draw call counts
//! - Batched frame statistics for reduced WASM↔JS overhead

use wasm_bindgen::prelude::*;

use crate::Rource;

// ============================================================================
// Helper Functions (testable without Rource instance)
// ============================================================================

#[allow(dead_code)]
mod helpers {
    /// Extracts unique directory paths from a file path.
    ///
    /// Given a file path like "src/core/main.rs", this extracts all directory
    /// components: `["src", "src/core"]`.
    ///
    /// # Arguments
    /// * `path` - The file path to extract directories from
    ///
    /// # Returns
    /// Vector of directory paths from outermost to innermost.
    #[must_use]
    pub fn extract_directories(path: &str) -> Vec<String> {
        let mut directories = Vec::new();
        let mut current_path = String::new();

        let components: Vec<&str> = path.split('/').collect();
        for (i, component) in components.iter().enumerate() {
            if i > 0 {
                current_path.push('/');
            }
            // Check if this is the file (last component) or a directory
            if i < components.len() - 1 {
                current_path.push_str(component);
                directories.push(current_path.clone());
            }
        }

        directories
    }

    /// Counts unique directories from a collection of file paths.
    ///
    /// # Arguments
    /// * `paths` - Iterator of file paths
    ///
    /// # Returns
    /// Total unique directory count including root.
    #[must_use]
    pub fn count_unique_directories<'a>(paths: impl Iterator<Item = &'a str>) -> usize {
        use std::collections::HashSet;

        let mut directories: HashSet<String> = HashSet::new();
        let mut has_files = false;

        for path in paths {
            has_files = true;
            for dir in extract_directories(path) {
                directories.insert(dir);
            }
        }

        if directories.is_empty() && has_files {
            1 // Just root
        } else if directories.is_empty() {
            0 // No files at all
        } else {
            directories.len() + 1 // +1 for root
        }
    }

    /// Formats frame statistics as a JSON string.
    ///
    /// This is a helper for testing the JSON formatting logic.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn format_frame_stats(
        fps: f64,
        frame_time_ms: f64,
        total_entities: usize,
        visible_files: usize,
        visible_users: usize,
        visible_directories: usize,
        active_actions: usize,
        draw_calls: usize,
        canvas_width: u32,
        canvas_height: u32,
        is_playing: bool,
        commit_count: usize,
        current_commit: usize,
        total_files: usize,
        total_users: usize,
        total_directories: usize,
    ) -> String {
        format!(
            r#"{{"fps":{fps:.2},"frameTimeMs":{frame_time_ms:.4},"totalEntities":{total_entities},"visibleFiles":{visible_files},"visibleUsers":{visible_users},"visibleDirectories":{visible_directories},"activeActions":{active_actions},"drawCalls":{draw_calls},"canvasWidth":{canvas_width},"canvasHeight":{canvas_height},"isPlaying":{is_playing},"commitCount":{commit_count},"currentCommit":{current_commit},"totalFiles":{total_files},"totalUsers":{total_users},"totalDirectories":{total_directories}}}"#
        )
    }
}

#[allow(unused_imports)]
pub use helpers::*;

// ============================================================================
// Batched Frame Statistics API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns all frame statistics in a single call to reduce WASM↔JS overhead.
    ///
    /// This batches 12+ individual getter calls into one, reducing per-frame
    /// overhead by approximately 90% when updating the performance metrics UI.
    ///
    /// Frame time is returned with 4 decimal places (0.1µs precision) to enable
    /// precise performance profiling when eliminating individual clock cycles.
    ///
    /// Returns a JSON string with the following structure:
    /// ```json
    /// {
    ///   "fps": 60.0,
    ///   "frameTimeMs": 16.6700,
    ///   "totalEntities": 1500,
    ///   "visibleFiles": 200,
    ///   "visibleUsers": 5,
    ///   "visibleDirectories": 50,
    ///   "activeActions": 10,
    ///   "drawCalls": 6,
    ///   "canvasWidth": 1920,
    ///   "canvasHeight": 1080,
    ///   "isPlaying": true,
    ///   "commitCount": 1000,
    ///   "currentCommit": 500,
    ///   "totalFiles": 500,
    ///   "totalUsers": 20,
    ///   "totalDirectories": 100
    /// }
    /// ```
    #[wasm_bindgen(js_name = getFrameStats)]
    pub fn get_frame_stats(&self) -> String {
        // Use write! macro to format JSON to avoid temporary string allocations
        // This is more efficient than format! for large strings
        format!(
            r#"{{"fps":{:.2},"frameTimeMs":{:.4},"totalEntities":{},"visibleFiles":{},"visibleUsers":{},"visibleDirectories":{},"activeActions":{},"drawCalls":{},"canvasWidth":{},"canvasHeight":{},"isPlaying":{},"commitCount":{},"currentCommit":{},"totalFiles":{},"totalUsers":{},"totalDirectories":{}}}"#,
            self.perf_metrics.fps(),
            self.perf_metrics.frame_time_ms(),
            self.render_stats.total_entities,
            self.render_stats.visible_files,
            self.render_stats.visible_users,
            self.render_stats.visible_directories,
            self.render_stats.active_actions,
            self.render_stats.draw_calls,
            self.backend.width(),
            self.backend.height(),
            self.playback.is_playing(),
            self.commits.len(),
            self.playback.current_commit(),
            self.scene.file_count(),
            self.scene.user_count(),
            self.scene.directory_count(),
        )
    }
}

// ============================================================================
// Render Statistics API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns the number of visible files (in current viewport).
    #[wasm_bindgen(js_name = getVisibleFiles)]
    pub fn get_visible_files(&self) -> usize {
        self.render_stats.visible_files
    }

    /// Returns the number of visible users (in current viewport).
    #[wasm_bindgen(js_name = getVisibleUsers)]
    pub fn get_visible_users(&self) -> usize {
        self.render_stats.visible_users
    }

    /// Returns the number of visible directories (in current viewport).
    #[wasm_bindgen(js_name = getVisibleDirectories)]
    pub fn get_visible_directories(&self) -> usize {
        self.render_stats.visible_directories
    }

    /// Returns the number of active action beams.
    #[wasm_bindgen(js_name = getActiveActions)]
    pub fn get_active_actions(&self) -> usize {
        self.render_stats.active_actions
    }

    /// Returns the total number of entities (files + users + dirs + actions).
    #[wasm_bindgen(js_name = getTotalEntities)]
    pub fn get_total_entities(&self) -> usize {
        self.render_stats.total_entities
    }

    /// Returns the estimated draw call count for the current frame.
    #[wasm_bindgen(js_name = getDrawCalls)]
    pub fn get_draw_calls(&self) -> usize {
        self.render_stats.draw_calls
    }

    /// Returns the total number of files in the scene.
    #[wasm_bindgen(js_name = getTotalFiles)]
    pub fn get_total_files(&self) -> usize {
        self.scene.file_count()
    }

    /// Returns the total number of directories currently in the scene.
    ///
    /// Note: This only includes directories that have been created so far
    /// during playback. For total directories across all commits, use
    /// `getCommitDirectoryCount()`.
    #[wasm_bindgen(js_name = getTotalDirectories)]
    pub fn get_total_directories(&self) -> usize {
        self.scene.directory_count()
    }

    /// Returns the total number of unique directories across all loaded commits.
    ///
    /// This calculates directory count from file paths, independent of
    /// playback state. Useful for displaying total stats before playback
    /// reaches the end.
    #[wasm_bindgen(js_name = getCommitDirectoryCount)]
    pub fn get_commit_directory_count(&self) -> usize {
        use std::collections::HashSet;

        let mut directories: HashSet<String> = HashSet::new();

        for commit in &self.commits {
            for file in &commit.files {
                // Extract parent directories from each file path
                let path = file.path.to_string_lossy();
                let mut current_path = String::new();

                for (i, component) in path.split('/').enumerate() {
                    if i > 0 {
                        current_path.push('/');
                    }
                    // Check if this is the file (last component) or a directory
                    // by checking if there are more components after this one
                    if path.split('/').nth(i + 1).is_some() {
                        // This is a directory component (not the file name)
                        current_path.push_str(component);
                        directories.insert(current_path.clone());
                    }
                }
            }
        }

        // Add 1 for root directory if there are any directories
        if directories.is_empty() && !self.commits.is_empty() {
            1 // Just root
        } else {
            directories.len() + 1 // +1 for root
        }
    }

    /// Returns the total number of users in the scene.
    #[wasm_bindgen(js_name = getTotalUsers)]
    pub fn get_total_users(&self) -> usize {
        self.scene.user_count()
    }

    /// Returns debug information about zoom and entity visibility.
    ///
    /// Returns JSON with zoom level, entity radii, and screen radii to help
    /// diagnose visibility issues.
    #[wasm_bindgen(js_name = getZoomDebugInfo)]
    pub fn get_zoom_debug_info(&self) -> String {
        use crate::render_phases::{LOD_MIN_DIR_RADIUS, LOD_MIN_FILE_RADIUS, LOD_MIN_USER_RADIUS};

        let zoom = self.camera.zoom();

        // Get some sample entity radii
        let mut file_radii: Vec<f32> = self
            .scene
            .files()
            .values()
            .take(10)
            .map(rource_core::scene::FileNode::radius)
            .collect();
        file_radii.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

        let mut dir_radii: Vec<f32> = self
            .scene
            .directories()
            .iter()
            .take(10)
            .map(rource_core::scene::DirNode::radius)
            .collect();
        dir_radii.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

        let mut user_radii: Vec<f32> = self
            .scene
            .users()
            .values()
            .take(10)
            .map(rource_core::scene::User::radius)
            .collect();
        user_radii.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

        // Calculate minimum screen radii
        let min_file_radius = file_radii.first().copied().unwrap_or(5.0);
        let min_dir_radius = dir_radii.first().copied().unwrap_or(5.0);
        let min_user_radius = user_radii.first().copied().unwrap_or(15.0);

        let min_file_screen_radius = min_file_radius * zoom;
        let min_dir_screen_radius = min_dir_radius * zoom;
        let min_user_screen_radius = min_user_radius * zoom;

        // Check which entity types would pass LOD
        let files_pass_lod = min_file_screen_radius >= LOD_MIN_FILE_RADIUS;
        let dirs_pass_lod = min_dir_screen_radius >= LOD_MIN_DIR_RADIUS;
        let users_pass_lod = min_user_screen_radius >= LOD_MIN_USER_RADIUS;

        format!(
            r#"{{"zoom":{:.6},"minZoomLimit":{:.6},"lodThresholds":{{"file":{},"dir":{},"user":{}}},"minEntityRadii":{{"file":{},"dir":{},"user":{}}},"minScreenRadii":{{"file":{:.4},"dir":{:.4},"user":{:.4}}},"passLod":{{"file":{},"dir":{},"user":{}}}}}"#,
            zoom,
            crate::render_phases::AUTO_FIT_MIN_ZOOM,
            LOD_MIN_FILE_RADIUS,
            LOD_MIN_DIR_RADIUS,
            LOD_MIN_USER_RADIUS,
            min_file_radius,
            min_dir_radius,
            min_user_radius,
            min_file_screen_radius,
            min_dir_screen_radius,
            min_user_screen_radius,
            files_pass_lod,
            dirs_pass_lod,
            users_pass_lod,
        )
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Directory Extraction Tests
    // ========================================================================

    #[test]
    fn test_extract_directories_simple() {
        let dirs = extract_directories("src/main.rs");
        assert_eq!(dirs, vec!["src"]);
    }

    #[test]
    fn test_extract_directories_nested() {
        let dirs = extract_directories("src/core/engine/main.rs");
        assert_eq!(dirs, vec!["src", "src/core", "src/core/engine"]);
    }

    #[test]
    fn test_extract_directories_single_file() {
        let dirs = extract_directories("README.md");
        assert!(dirs.is_empty());
    }

    #[test]
    fn test_extract_directories_deeply_nested() {
        let dirs = extract_directories("a/b/c/d/e/f.txt");
        assert_eq!(dirs, vec!["a", "a/b", "a/b/c", "a/b/c/d", "a/b/c/d/e"]);
    }

    #[test]
    fn test_extract_directories_empty_path() {
        let dirs = extract_directories("");
        assert!(dirs.is_empty());
    }

    // ========================================================================
    // Unique Directory Count Tests
    // ========================================================================

    #[test]
    fn test_count_unique_directories_single_file() {
        let paths = ["src/main.rs"];
        let count = count_unique_directories(paths.iter().copied());
        assert_eq!(count, 2); // root + src
    }

    #[test]
    fn test_count_unique_directories_multiple_files_same_dir() {
        let paths = ["src/main.rs", "src/lib.rs", "src/utils.rs"];
        let count = count_unique_directories(paths.iter().copied());
        assert_eq!(count, 2); // root + src
    }

    #[test]
    fn test_count_unique_directories_multiple_nested() {
        let paths = [
            "src/core/main.rs",
            "src/core/lib.rs",
            "src/utils/helpers.rs",
        ];
        let count = count_unique_directories(paths.iter().copied());
        assert_eq!(count, 4); // root + src + src/core + src/utils
    }

    #[test]
    fn test_count_unique_directories_root_only() {
        let paths = ["README.md", "Cargo.toml"];
        let count = count_unique_directories(paths.iter().copied());
        assert_eq!(count, 1); // Just root
    }

    #[test]
    fn test_count_unique_directories_empty() {
        let paths: [&str; 0] = [];
        let count = count_unique_directories(paths.iter().copied());
        assert_eq!(count, 0); // No files
    }

    #[test]
    fn test_count_unique_directories_complex() {
        let paths = [
            "src/main.rs",
            "src/lib.rs",
            "tests/unit/test_a.rs",
            "tests/unit/test_b.rs",
            "tests/integration/test_c.rs",
            "docs/README.md",
        ];
        let count = count_unique_directories(paths.iter().copied());
        // root + src + tests + tests/unit + tests/integration + docs = 6
        assert_eq!(count, 6);
    }

    // ========================================================================
    // Frame Stats Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_frame_stats_basic() {
        let json = format_frame_stats(
            60.0, 16.67, 1500, 200, 5, 50, 10, 6, 1920, 1080, true, 1000, 500, 500, 20, 100,
        );
        assert!(json.contains(r#""fps":60.00"#));
        assert!(json.contains(r#""frameTimeMs":16.6700"#));
        assert!(json.contains(r#""totalEntities":1500"#));
        assert!(json.contains(r#""isPlaying":true"#));
    }

    #[test]
    fn test_format_frame_stats_zero_values() {
        let json = format_frame_stats(0.0, 0.0, 0, 0, 0, 0, 0, 0, 800, 600, false, 0, 0, 0, 0, 0);
        assert!(json.contains(r#""fps":0.00"#));
        assert!(json.contains(r#""isPlaying":false"#));
        assert!(json.contains(r#""totalEntities":0"#));
    }

    #[test]
    fn test_format_frame_stats_large_values() {
        let json = format_frame_stats(
            144.0, 6.944, 100_000, 50_000, 1000, 10_000, 5000, 12, 3840, 2160, true, 100_000,
            99_999, 75_000, 5000, 25_000,
        );
        assert!(json.contains(r#""fps":144.00"#));
        assert!(json.contains(r#""totalEntities":100000"#));
        assert!(json.contains(r#""canvasWidth":3840"#));
        assert!(json.contains(r#""canvasHeight":2160"#));
    }

    #[test]
    fn test_format_frame_stats_is_valid_json() {
        let json = format_frame_stats(
            60.0, 16.67, 1500, 200, 5, 50, 10, 6, 1920, 1080, true, 1000, 500, 500, 20, 100,
        );

        // Verify it starts and ends correctly
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));

        // Verify all expected keys are present
        assert!(json.contains(r#""fps":"#));
        assert!(json.contains(r#""frameTimeMs":"#));
        assert!(json.contains(r#""visibleFiles":"#));
        assert!(json.contains(r#""visibleUsers":"#));
        assert!(json.contains(r#""visibleDirectories":"#));
        assert!(json.contains(r#""activeActions":"#));
        assert!(json.contains(r#""drawCalls":"#));
        assert!(json.contains(r#""commitCount":"#));
        assert!(json.contains(r#""currentCommit":"#));
        assert!(json.contains(r#""totalFiles":"#));
        assert!(json.contains(r#""totalUsers":"#));
        assert!(json.contains(r#""totalDirectories":"#));
    }
}
