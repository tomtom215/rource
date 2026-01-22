//! Render statistics and entity count APIs.
//!
//! This module provides methods to query visualization metrics:
//! - Visible entity counts (files, users, directories, actions)
//! - Total entity counts
//! - Estimated draw call counts

use wasm_bindgen::prelude::*;

use crate::Rource;

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
}
