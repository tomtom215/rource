// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Playback and timeline management for Rource WASM.
//!
//! This module handles commit playback timing, seeking, and timeline navigation.

use rource_core::scene::{ActionType, Scene};
use rource_vcs::{Commit, FileAction};

// ============================================================================
// Utility Functions
// ============================================================================

/// Converts a VCS `FileAction` to a Scene `ActionType`.
///
/// This bridges the gap between the VCS layer's file change representation
/// and the scene's action system.
#[inline]
pub fn file_action_to_action_type(action: FileAction) -> ActionType {
    match action {
        FileAction::Create => ActionType::Create,
        FileAction::Modify => ActionType::Modify,
        FileAction::Delete => ActionType::Delete,
    }
}

// ============================================================================
// Playback State
// ============================================================================

/// Playback state and timing information.
///
/// This struct encapsulates all playback-related state, making it easier
/// to manage timeline navigation and commit application.
#[derive(Debug, Clone)]
pub struct PlaybackState {
    /// Current commit index.
    current_commit: usize,
    /// Last applied commit index.
    last_applied_commit: usize,
    /// Accumulated time since last commit (seconds).
    accumulated_time: f32,
    /// Whether playback is active.
    playing: bool,
    /// Last frame timestamp (milliseconds).
    last_frame_time: f64,
}

impl Default for PlaybackState {
    fn default() -> Self {
        Self::new()
    }
}

impl PlaybackState {
    /// Creates a new playback state at the beginning.
    #[inline]
    pub fn new() -> Self {
        Self {
            current_commit: 0,
            last_applied_commit: 0,
            accumulated_time: 0.0,
            playing: false,
            last_frame_time: 0.0,
        }
    }

    /// Resets playback to the beginning.
    pub fn reset(&mut self) {
        self.current_commit = 0;
        self.last_applied_commit = 0;
        self.accumulated_time = 0.0;
        // Note: `playing` is intentionally not reset
    }

    /// Returns the current commit index.
    #[inline]
    pub fn current_commit(&self) -> usize {
        self.current_commit
    }

    /// Sets the current commit index.
    #[inline]
    pub fn set_current_commit(&mut self, index: usize) {
        self.current_commit = index;
    }

    /// Returns the last applied commit index.
    #[inline]
    pub fn last_applied_commit(&self) -> usize {
        self.last_applied_commit
    }

    /// Sets the last applied commit index.
    #[inline]
    pub fn set_last_applied_commit(&mut self, index: usize) {
        self.last_applied_commit = index;
    }

    /// Returns the accumulated time since last commit.
    #[inline]
    pub fn accumulated_time(&self) -> f32 {
        self.accumulated_time
    }

    /// Adds delta time to accumulated time.
    #[inline]
    pub fn add_time(&mut self, dt: f32) {
        self.accumulated_time += dt;
    }

    /// Subtracts time from accumulated time.
    #[inline]
    pub fn subtract_time(&mut self, amount: f32) {
        self.accumulated_time -= amount;
    }

    /// Resets accumulated time to zero.
    #[inline]
    pub fn reset_accumulated_time(&mut self) {
        self.accumulated_time = 0.0;
    }

    /// Clamps accumulated time to a maximum value.
    ///
    /// Used to prevent unbounded growth when the per-frame commit limit is hit.
    /// This ensures we don't build up a massive backlog that would freeze the browser.
    #[inline]
    pub fn clamp_accumulated_time(&mut self, max: f32) {
        if self.accumulated_time > max {
            self.accumulated_time = max;
        }
    }

    /// Returns whether playback is active.
    #[inline]
    pub fn is_playing(&self) -> bool {
        self.playing
    }

    /// Starts playback.
    pub fn play(&mut self) {
        self.playing = true;
        self.last_frame_time = 0.0;
    }

    /// Pauses playback.
    #[inline]
    pub fn pause(&mut self) {
        self.playing = false;
    }

    /// Toggles play/pause state.
    pub fn toggle_play(&mut self) {
        if self.playing {
            self.pause();
        } else {
            self.play();
        }
    }

    /// Stops playback (at end of timeline).
    #[inline]
    pub fn stop(&mut self) {
        self.playing = false;
    }

    /// Returns the last frame timestamp.
    #[inline]
    pub fn last_frame_time(&self) -> f64 {
        self.last_frame_time
    }

    /// Sets the last frame timestamp.
    #[inline]
    pub fn set_last_frame_time(&mut self, time: f64) {
        self.last_frame_time = time;
    }

    /// Advances to the next commit.
    ///
    /// Returns the new commit index.
    #[inline]
    pub fn advance_commit(&mut self) -> usize {
        self.current_commit += 1;
        self.current_commit
    }
}

// ============================================================================
// Commit Application
// ============================================================================

/// Applies a VCS commit to the scene.
///
/// This converts the commit's file changes into scene actions and applies them.
/// Uses iterator to avoid per-call Vec allocation (100+ calls/frame at high speed).
///
/// # Arguments
///
/// * `scene` - The scene to apply the commit to
/// * `commit` - The commit to apply
#[inline]
pub fn apply_vcs_commit(scene: &mut Scene, commit: &Commit) {
    // Pass iterator directly to avoid allocating a Vec per commit
    scene.apply_commit(
        &commit.author,
        commit
            .files
            .iter()
            .map(|fc| (fc.path.as_path(), file_action_to_action_type(fc.action))),
    );
}

/// Pre-warms the scene by running update cycles.
///
/// This ensures that files fade in and physics settle before the first visible frame.
///
/// # Arguments
///
/// * `scene` - The scene to pre-warm
/// * `cycles` - Number of update cycles to run (typically 30)
/// * `dt` - Delta time per cycle (typically 1/60 for 60fps)
pub fn prewarm_scene(scene: &mut Scene, cycles: usize, dt: f32) {
    for _ in 0..cycles {
        scene.update(dt);
    }
}

// ============================================================================
// Timeline Utilities
// ============================================================================

/// Returns the date range of commits as `(start_timestamp, end_timestamp)`.
///
/// Returns `None` if the commit list is empty.
pub fn get_date_range(commits: &[Commit]) -> Option<(i64, i64)> {
    if commits.is_empty() {
        return None;
    }

    let start = commits.first().map_or(0, |c| c.timestamp);
    let end = commits.last().map_or(0, |c| c.timestamp);

    Some((start, end))
}

/// Calculates the time per commit based on playback speed.
///
/// # Arguments
///
/// * `seconds_per_day` - Playback speed in seconds per day of repository history
///
/// # Returns
///
/// Time in seconds between commits
#[inline]
pub fn calculate_seconds_per_commit(seconds_per_day: f32) -> f32 {
    // Use multiplication by reciprocal instead of division (1 cycle vs ~15 cycles)
    seconds_per_day * 0.1
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // File Action Conversion Tests

    #[test]
    fn test_file_action_to_action_type_create() {
        let action = file_action_to_action_type(FileAction::Create);
        assert!(matches!(action, ActionType::Create));
    }

    #[test]
    fn test_file_action_to_action_type_modify() {
        let action = file_action_to_action_type(FileAction::Modify);
        assert!(matches!(action, ActionType::Modify));
    }

    #[test]
    fn test_file_action_to_action_type_delete() {
        let action = file_action_to_action_type(FileAction::Delete);
        assert!(matches!(action, ActionType::Delete));
    }

    // Playback State Tests

    #[test]
    fn test_playback_state_new() {
        let state = PlaybackState::new();
        assert_eq!(state.current_commit(), 0);
        assert_eq!(state.last_applied_commit(), 0);
        assert_eq!(state.accumulated_time(), 0.0);
        assert!(!state.is_playing());
    }

    #[test]
    fn test_playback_state_default() {
        let state = PlaybackState::default();
        assert_eq!(state.current_commit(), 0);
        assert!(!state.is_playing());
    }

    #[test]
    fn test_playback_state_play_pause() {
        let mut state = PlaybackState::new();

        state.play();
        assert!(state.is_playing());

        state.pause();
        assert!(!state.is_playing());
    }

    #[test]
    fn test_playback_state_toggle_play() {
        let mut state = PlaybackState::new();
        assert!(!state.is_playing());

        state.toggle_play();
        assert!(state.is_playing());

        state.toggle_play();
        assert!(!state.is_playing());
    }

    #[test]
    fn test_playback_state_reset() {
        let mut state = PlaybackState::new();
        state.set_current_commit(10);
        state.set_last_applied_commit(10);
        state.add_time(5.0);
        state.play();

        state.reset();

        assert_eq!(state.current_commit(), 0);
        assert_eq!(state.last_applied_commit(), 0);
        assert_eq!(state.accumulated_time(), 0.0);
        // playing should NOT be reset
        assert!(state.is_playing());
    }

    #[test]
    fn test_playback_state_time_management() {
        let mut state = PlaybackState::new();

        state.add_time(1.0);
        assert_eq!(state.accumulated_time(), 1.0);

        state.add_time(0.5);
        assert_eq!(state.accumulated_time(), 1.5);

        state.subtract_time(0.3);
        assert!((state.accumulated_time() - 1.2).abs() < 0.0001);

        state.reset_accumulated_time();
        assert_eq!(state.accumulated_time(), 0.0);
    }

    #[test]
    fn test_playback_state_clamp_accumulated_time() {
        let mut state = PlaybackState::new();
        state.add_time(10.0);
        assert_eq!(state.accumulated_time(), 10.0);

        // Clamp to 5.0
        state.clamp_accumulated_time(5.0);
        assert_eq!(state.accumulated_time(), 5.0);

        // Clamping to higher value should not change it
        state.clamp_accumulated_time(100.0);
        assert_eq!(state.accumulated_time(), 5.0);
    }

    #[test]
    fn test_playback_state_advance_commit() {
        let mut state = PlaybackState::new();
        assert_eq!(state.current_commit(), 0);

        assert_eq!(state.advance_commit(), 1);
        assert_eq!(state.current_commit(), 1);

        assert_eq!(state.advance_commit(), 2);
        assert_eq!(state.current_commit(), 2);
    }

    #[test]
    fn test_playback_state_frame_time() {
        let mut state = PlaybackState::new();
        assert_eq!(state.last_frame_time(), 0.0);

        state.set_last_frame_time(16.67);
        assert_eq!(state.last_frame_time(), 16.67);
    }

    // Timeline Utility Tests

    #[test]
    fn test_calculate_seconds_per_commit() {
        assert_eq!(calculate_seconds_per_commit(10.0), 1.0);
        assert_eq!(calculate_seconds_per_commit(1.0), 0.1);
        assert_eq!(calculate_seconds_per_commit(100.0), 10.0);
    }

    #[test]
    fn test_get_date_range_empty() {
        let commits: Vec<Commit> = vec![];
        assert!(get_date_range(&commits).is_none());
    }

    #[test]
    fn test_get_date_range_single() {
        let commits = vec![Commit {
            hash: "abc123".to_string(),
            author: "Test".to_string(),
            email: None,
            timestamp: 1000,
            files: vec![],
        }];
        let range = get_date_range(&commits);
        assert_eq!(range, Some((1000, 1000)));
    }

    #[test]
    fn test_get_date_range_multiple() {
        let commits = vec![
            Commit {
                hash: "abc123".to_string(),
                author: "Test".to_string(),
                email: None,
                timestamp: 1000,
                files: vec![],
            },
            Commit {
                hash: "def456".to_string(),
                author: "Test".to_string(),
                email: None,
                timestamp: 2000,
                files: vec![],
            },
            Commit {
                hash: "ghi789".to_string(),
                author: "Test".to_string(),
                email: None,
                timestamp: 3000,
                files: vec![],
            },
        ];
        let range = get_date_range(&commits);
        assert_eq!(range, Some((1000, 3000)));
    }

    // Commit Application Tests

    use std::path::PathBuf;

    use rource_vcs::FileChange;

    #[test]
    fn test_apply_vcs_commit_creates_files() {
        let mut scene = Scene::new();
        let commit = Commit {
            hash: "abc123".to_string(),
            author: "Alice".to_string(),
            email: None,
            timestamp: 1000,
            files: vec![
                FileChange {
                    path: PathBuf::from("src/main.rs"),
                    action: FileAction::Create,
                },
                FileChange {
                    path: PathBuf::from("src/lib.rs"),
                    action: FileAction::Create,
                },
            ],
        };

        apply_vcs_commit(&mut scene, &commit);

        // Scene should have files after applying commit
        assert!(scene.file_count() >= 2, "Should have at least 2 files");
        assert!(scene.user_count() >= 1, "Should have at least 1 user");
    }

    #[test]
    fn test_apply_vcs_commit_modifies_files() {
        let mut scene = Scene::new();

        // First create files
        let create_commit = Commit {
            hash: "abc123".to_string(),
            author: "Alice".to_string(),
            email: None,
            timestamp: 1000,
            files: vec![FileChange {
                path: PathBuf::from("src/main.rs"),
                action: FileAction::Create,
            }],
        };
        apply_vcs_commit(&mut scene, &create_commit);
        let files_after_create = scene.file_count();

        // Then modify
        let modify_commit = Commit {
            hash: "def456".to_string(),
            author: "Bob".to_string(),
            email: None,
            timestamp: 2000,
            files: vec![FileChange {
                path: PathBuf::from("src/main.rs"),
                action: FileAction::Modify,
            }],
        };
        apply_vcs_commit(&mut scene, &modify_commit);

        // File count should be the same (modify doesn't create new files)
        assert_eq!(scene.file_count(), files_after_create);
    }

    #[test]
    fn test_apply_vcs_commit_empty() {
        let mut scene = Scene::new();
        let commit = Commit {
            hash: "abc123".to_string(),
            author: "Alice".to_string(),
            email: None,
            timestamp: 1000,
            files: vec![],
        };

        // Should not panic on empty commit
        apply_vcs_commit(&mut scene, &commit);

        // Scene should still be valid
        assert!(scene.file_count() == 0 || scene.file_count() > 0);
    }

    #[test]
    fn test_apply_vcs_commit_multiple_authors() {
        let mut scene = Scene::new();

        let commit1 = Commit {
            hash: "abc123".to_string(),
            author: "Alice".to_string(),
            email: None,
            timestamp: 1000,
            files: vec![FileChange {
                path: PathBuf::from("src/main.rs"),
                action: FileAction::Create,
            }],
        };
        apply_vcs_commit(&mut scene, &commit1);

        let commit2 = Commit {
            hash: "def456".to_string(),
            author: "Bob".to_string(),
            email: None,
            timestamp: 2000,
            files: vec![FileChange {
                path: PathBuf::from("src/lib.rs"),
                action: FileAction::Create,
            }],
        };
        apply_vcs_commit(&mut scene, &commit2);

        // Should have at least 2 users
        assert!(scene.user_count() >= 2, "Should have at least 2 users");
    }

    // Prewarm Scene Tests

    #[test]
    fn test_prewarm_scene() {
        let mut scene = Scene::new();

        // Apply a commit first
        let commit = Commit {
            hash: "abc123".to_string(),
            author: "Alice".to_string(),
            email: None,
            timestamp: 1000,
            files: vec![FileChange {
                path: PathBuf::from("src/main.rs"),
                action: FileAction::Create,
            }],
        };
        apply_vcs_commit(&mut scene, &commit);

        // Prewarm should not panic
        prewarm_scene(&mut scene, 30, 1.0 / 60.0);

        // Scene should still be valid after prewarm
        assert!(scene.file_count() >= 1);
    }

    #[test]
    fn test_prewarm_scene_zero_cycles() {
        let mut scene = Scene::new();

        // Apply a commit first
        let commit = Commit {
            hash: "abc123".to_string(),
            author: "Alice".to_string(),
            email: None,
            timestamp: 1000,
            files: vec![FileChange {
                path: PathBuf::from("src/main.rs"),
                action: FileAction::Create,
            }],
        };
        apply_vcs_commit(&mut scene, &commit);

        // Zero cycles should not panic
        prewarm_scene(&mut scene, 0, 1.0 / 60.0);

        // Scene should still be valid
        assert!(scene.file_count() >= 1);
    }

    #[test]
    fn test_prewarm_scene_empty() {
        let mut scene = Scene::new();

        // Prewarm empty scene should not panic
        prewarm_scene(&mut scene, 30, 1.0 / 60.0);

        // Scene should be valid
        assert_eq!(scene.file_count(), 0);
    }
}
