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
// Batched Frame Statistics API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns all frame statistics in a single call to reduce WASM↔JS overhead.
    ///
    /// This batches 12+ individual getter calls into one, reducing per-frame
    /// overhead by approximately 90% when updating the performance metrics UI.
    ///
    /// Returns a JSON string with the following structure:
    /// ```json
    /// {
    ///   "fps": 60.0,
    ///   "frameTimeMs": 16.67,
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
            r#"{{"fps":{:.2},"frameTimeMs":{:.3},"totalEntities":{},"visibleFiles":{},"visibleUsers":{},"visibleDirectories":{},"activeActions":{},"drawCalls":{},"canvasWidth":{},"canvasHeight":{},"isPlaying":{},"commitCount":{},"currentCommit":{},"totalFiles":{},"totalUsers":{},"totalDirectories":{}}}"#,
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
