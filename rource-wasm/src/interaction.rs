// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Mouse and touch interaction handling for Rource WASM.
//!
//! This module contains entity hit testing, drag handling, and connected entity movement.

use rource_core::entity::{DirId, FileId, UserId};
use rource_core::scene::{EntityType, Scene};
use rource_math::Vec2;

/// Hit radius for entity picking (in world units).
pub const ENTITY_HIT_RADIUS: f32 = 15.0;

/// Drag coupling strength for connected entities (0.0 = no coupling, 1.0 = full coupling).
/// Lower values create a more elastic, spring-like effect.
pub const DRAG_COUPLING_STRENGTH: f32 = 0.6;

/// Distance threshold beyond which coupling decreases (in world units).
pub const DRAG_COUPLING_DISTANCE_THRESHOLD: f32 = 150.0;

/// Minimum delta magnitude to consider significant (in world units).
pub const MIN_SIGNIFICANT_DELTA: f32 = 0.1;

/// Minimum coupling value to apply movement (below this, skip the update).
pub const MIN_COUPLING_THRESHOLD: f32 = 0.01;

// =============================================================================
// Pure Helper Functions (testable without Scene)
// =============================================================================

// These pure functions are extracted for unit testing. They are not called directly
// from the main interaction code, which uses optimized inline versions.
#[allow(dead_code)]
#[allow(clippy::wildcard_imports)]
mod helpers {
    use super::*;

    /// Computes the distance-based coupling factor (0.0 to 1.0).
    ///
    /// Returns 1.0 when distance is 0, decreasing linearly to 0.0 at the threshold.
    #[inline]
    #[must_use]
    pub fn compute_distance_factor(distance: f32, threshold: f32) -> f32 {
        (1.0 - distance / threshold).clamp(0.0, 1.0)
    }

    /// Computes the coupling strength from base coupling and distance factor.
    #[inline]
    #[must_use]
    pub fn compute_coupling(base_coupling: f32, distance_factor: f32) -> f32 {
        base_coupling * distance_factor
    }

    /// Computes coupling for sibling files (uses default coupling strength).
    #[inline]
    #[must_use]
    pub fn compute_sibling_file_coupling(distance: f32) -> f32 {
        let distance_factor = compute_distance_factor(distance, DRAG_COUPLING_DISTANCE_THRESHOLD);
        compute_coupling(DRAG_COUPLING_STRENGTH, distance_factor)
    }

    /// Computes coupling for parent directory (half the default coupling).
    #[inline]
    #[must_use]
    pub fn compute_parent_dir_coupling(distance: f32) -> f32 {
        let distance_factor = compute_distance_factor(distance, DRAG_COUPLING_DISTANCE_THRESHOLD);
        compute_coupling(DRAG_COUPLING_STRENGTH * 0.5, distance_factor)
    }

    /// Computes coupling for sibling directories (30% of default coupling).
    #[inline]
    #[must_use]
    pub fn compute_sibling_dir_coupling(distance: f32) -> f32 {
        let distance_factor = compute_distance_factor(distance, DRAG_COUPLING_DISTANCE_THRESHOLD);
        compute_coupling(DRAG_COUPLING_STRENGTH * 0.3, distance_factor)
    }

    /// Computes coupling for connected files from user drag.
    #[inline]
    #[must_use]
    pub fn compute_connected_file_coupling(distance: f32) -> f32 {
        let distance_factor = compute_distance_factor(distance, DRAG_COUPLING_DISTANCE_THRESHOLD);
        compute_coupling(DRAG_COUPLING_STRENGTH, distance_factor)
    }

    /// Computes the effective hit radius for entity picking.
    ///
    /// Adds half the hit radius as tolerance.
    #[inline]
    #[must_use]
    pub fn compute_effective_hit_radius(entity_radius: f32, hit_radius: f32) -> f32 {
        entity_radius + hit_radius * 0.5
    }

    /// Determines if a delta movement is significant enough to process.
    #[inline]
    #[must_use]
    pub fn is_significant_delta(delta: Vec2) -> bool {
        delta.length() >= MIN_SIGNIFICANT_DELTA
    }

    /// Determines if a coupling value is significant enough to apply.
    #[inline]
    #[must_use]
    pub fn is_significant_coupling(coupling: f32) -> bool {
        coupling > MIN_COUPLING_THRESHOLD
    }

    /// Computes the new position after applying a coupled delta.
    #[inline]
    #[must_use]
    pub fn compute_coupled_position(current: Vec2, delta: Vec2, coupling: f32) -> Vec2 {
        current + delta * coupling
    }

    /// Determines if a point is within an entity's effective hit area.
    #[inline]
    #[must_use]
    pub fn is_within_hit_area(
        entity_pos: Vec2,
        entity_radius: f32,
        point: Vec2,
        hit_radius: f32,
    ) -> bool {
        let distance = (entity_pos - point).length();
        let effective_radius = compute_effective_hit_radius(entity_radius, hit_radius);
        distance <= effective_radius
    }

    /// Computes the distance between two points.
    #[inline]
    #[must_use]
    pub fn compute_distance(a: Vec2, b: Vec2) -> f32 {
        (a - b).length()
    }

    /// Determines which entity is closer (returns true if `dist_a` < `dist_b`).
    #[inline]
    #[must_use]
    pub fn is_closer(dist_a: f32, dist_b: Option<f32>) -> bool {
        dist_b.is_none_or(|b| dist_a < b)
    }
}

// Re-export helpers for tests
#[allow(unused_imports)]
pub use helpers::*;

// =============================================================================
// Types
// =============================================================================

/// Draggable entity type.
#[derive(Debug, Clone, Copy)]
pub enum DragTarget {
    /// Dragging a file entity.
    File(FileId),
    /// Dragging a user entity.
    User(UserId),
    /// Dragging a directory entity.
    Directory(DirId),
}

/// Tests if a user is within the hit radius of the given world position.
///
/// Returns the drag target if a user is found.
pub fn hit_test_user(scene: &Scene, world_pos: Vec2, hit_radius: f32) -> Option<DragTarget> {
    // Query entities in the hit area
    let entities = scene.query_entities_circle(world_pos, hit_radius);

    // Find the closest user
    let mut closest_user: Option<(UserId, f32)> = None;

    for entity in entities {
        if let EntityType::User(user_id) = entity {
            if let Some(user) = scene.get_user(user_id) {
                let dist = (user.position() - world_pos).length();
                // Check if within the user's radius (with some tolerance)
                let effective_radius = user.radius() + hit_radius * 0.5;
                if dist <= effective_radius
                    && (closest_user.is_none() || dist < closest_user.unwrap().1)
                {
                    closest_user = Some((user_id, dist));
                }
            }
        }
    }

    closest_user.map(|(id, _)| DragTarget::User(id))
}

/// Tests if a file is within the hit radius of the given world position.
///
/// Returns the drag target if a file is found.
pub fn hit_test_file(scene: &Scene, world_pos: Vec2, hit_radius: f32) -> Option<DragTarget> {
    // Query entities in the hit area
    let entities = scene.query_entities_circle(world_pos, hit_radius);

    // Find the closest file
    let mut closest_file: Option<(FileId, f32)> = None;

    for entity in entities {
        if let EntityType::File(file_id) = entity {
            if let Some(file) = scene.get_file(file_id) {
                // Skip files that are faded out
                if file.alpha() < 0.1 {
                    continue;
                }
                let dist = (file.position() - world_pos).length();
                // Check if within the file's radius (with some tolerance)
                let effective_radius = file.radius() + hit_radius * 0.5;
                if dist <= effective_radius
                    && (closest_file.is_none() || dist < closest_file.unwrap().1)
                {
                    closest_file = Some((file_id, dist));
                }
            }
        }
    }

    closest_file.map(|(id, _)| DragTarget::File(id))
}

/// Tests if a directory is within the hit radius of the given world position.
///
/// Returns the drag target if a directory is found.
/// Skips the root directory (cannot be dragged).
pub fn hit_test_directory(scene: &Scene, world_pos: Vec2, hit_radius: f32) -> Option<DragTarget> {
    // Query entities in the hit area
    let entities = scene.query_entities_circle(world_pos, hit_radius);

    // Find the closest directory (excluding root)
    let mut closest_dir: Option<(DirId, f32)> = None;

    for entity in entities {
        if let EntityType::Directory(dir_id) = entity {
            if let Some(dir) = scene.directories().get(dir_id) {
                // Skip root directory - it's anchored and shouldn't be dragged
                if dir.is_root() {
                    continue;
                }
                let dist = (dir.position() - world_pos).length();
                // Check if within the directory's radius (with some tolerance)
                let effective_radius = dir.radius() + hit_radius * 0.5;
                if dist <= effective_radius
                    && (closest_dir.is_none() || dist < closest_dir.unwrap().1)
                {
                    closest_dir = Some((dir_id, dist));
                }
            }
        }
    }

    closest_dir.map(|(id, _)| DragTarget::Directory(id))
}

/// Moves entities connected to a dragged file.
///
/// Connected entities include:
/// - Sibling files in the same directory
/// - The parent directory
/// - Child directories (if dragging a directory)
pub fn move_connected_entities_for_file(
    scene: &mut Scene,
    dragged_file_id: FileId,
    dir_id: DirId,
    delta: Vec2,
) {
    // Skip if delta is negligible
    if delta.length() < 0.1 {
        return;
    }

    // Get the dragged file's position for distance-based coupling
    let dragged_pos = scene
        .get_file(dragged_file_id)
        .map_or(Vec2::ZERO, rource_core::scene::FileNode::position);

    // Move sibling files in the same directory
    let sibling_ids: Vec<FileId> = scene
        .directories()
        .get(dir_id)
        .map(|dir| dir.files().to_vec())
        .unwrap_or_default();

    for sibling_id in sibling_ids {
        if sibling_id == dragged_file_id {
            continue; // Skip the dragged file itself
        }

        if let Some(sibling) = scene.get_file_mut(sibling_id) {
            // Calculate distance-based coupling (closer = stronger)
            let distance = (sibling.position() - dragged_pos).length();
            let distance_factor =
                (1.0 - distance / DRAG_COUPLING_DISTANCE_THRESHOLD).clamp(0.0, 1.0);
            let coupling = DRAG_COUPLING_STRENGTH * distance_factor;

            if coupling > 0.01 {
                let new_pos = sibling.position() + delta * coupling;
                sibling.set_position(new_pos);
                sibling.set_target(new_pos);
            }
        }
    }

    // Move the parent directory (with reduced coupling)
    // Also zero velocity so physics doesn't fight the drag
    if let Some(dir) = scene.directories_mut().get_mut(dir_id) {
        let distance = (dir.position() - dragged_pos).length();
        let distance_factor = (1.0 - distance / DRAG_COUPLING_DISTANCE_THRESHOLD).clamp(0.0, 1.0);
        let coupling = DRAG_COUPLING_STRENGTH * 0.5 * distance_factor;

        if coupling > 0.01 {
            let new_pos = dir.position() + delta * coupling;
            dir.set_position(new_pos);
            dir.set_velocity(Vec2::ZERO);
        }
    }
}

/// Moves entities connected to a dragged user.
///
/// Connected entities include files that have active action beams from this user.
pub fn move_connected_entities_for_user(scene: &mut Scene, user_id: UserId, delta: Vec2) {
    // Skip if delta is negligible
    if delta.length() < 0.1 {
        return;
    }

    // Get the dragged user's position for distance-based coupling
    let dragged_pos = scene
        .get_user(user_id)
        .map_or(Vec2::ZERO, rource_core::scene::User::position);

    // Collect file IDs that have active actions from this user
    let connected_file_ids: Vec<FileId> = scene
        .actions()
        .iter()
        .filter(|action| action.user() == user_id && !action.is_complete())
        .map(rource_core::scene::Action::file)
        .collect();

    // Move connected files and update their targets so they don't snap back
    for file_id in connected_file_ids {
        if let Some(file) = scene.get_file_mut(file_id) {
            // Calculate distance-based coupling
            let distance = (file.position() - dragged_pos).length();
            let distance_factor =
                (1.0 - distance / DRAG_COUPLING_DISTANCE_THRESHOLD).clamp(0.0, 1.0);
            let coupling = DRAG_COUPLING_STRENGTH * distance_factor;

            if coupling > 0.01 {
                let new_pos = file.position() + delta * coupling;
                file.set_position(new_pos);
                file.set_target(new_pos);
            }
        }
    }
}

/// Moves entities connected to a dragged directory.
///
/// Connected entities include:
/// - Child directories
/// - Files in this directory
/// - Sibling directories (with reduced coupling)
pub fn move_connected_entities_for_directory(scene: &mut Scene, dir_id: DirId, delta: Vec2) {
    // Skip if delta is negligible
    if delta.length() < 0.1 {
        return;
    }

    // Get the dragged directory's position for distance-based coupling
    let dragged_pos = scene
        .directories()
        .get(dir_id)
        .map_or(Vec2::ZERO, rource_core::scene::DirNode::position);

    // Collect child directory IDs
    let child_dir_ids: Vec<DirId> = scene
        .directories()
        .get(dir_id)
        .map(|d| d.children().to_vec())
        .unwrap_or_default();

    // Move child directories with full coupling (they move with parent)
    for child_id in child_dir_ids {
        if let Some(child) = scene.directories_mut().get_mut(child_id) {
            let new_pos = child.position() + delta;
            child.set_position(new_pos);
            child.set_velocity(Vec2::ZERO);
        }
    }

    // Collect file IDs in this directory
    let file_ids: Vec<FileId> = scene
        .directories()
        .get(dir_id)
        .map(|d| d.files().to_vec())
        .unwrap_or_default();

    // Move files in this directory with full coupling
    for file_id in file_ids {
        if let Some(file) = scene.get_file_mut(file_id) {
            let new_pos = file.position() + delta;
            file.set_position(new_pos);
            file.set_target(new_pos);
        }
    }

    // Move sibling directories with distance-based reduced coupling
    let parent_id = scene
        .directories()
        .get(dir_id)
        .and_then(rource_core::scene::DirNode::parent);
    if let Some(parent_id) = parent_id {
        let sibling_ids: Vec<DirId> = scene
            .directories()
            .get(parent_id)
            .map(|d| d.children().to_vec())
            .unwrap_or_default();

        for sibling_id in sibling_ids {
            if sibling_id == dir_id {
                continue; // Skip the dragged directory itself
            }

            if let Some(sibling) = scene.directories_mut().get_mut(sibling_id) {
                let distance = (sibling.position() - dragged_pos).length();
                let distance_factor =
                    (1.0 - distance / DRAG_COUPLING_DISTANCE_THRESHOLD).clamp(0.0, 1.0);
                let coupling = DRAG_COUPLING_STRENGTH * 0.3 * distance_factor;

                if coupling > 0.01 {
                    let new_pos = sibling.position() + delta * coupling;
                    sibling.set_position(new_pos);
                    sibling.set_velocity(Vec2::ZERO);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // DragTarget Tests
    // ========================================================================

    #[test]
    fn test_drag_target_user() {
        let user_id = UserId::from_index(42);
        let target = DragTarget::User(user_id);
        assert!(matches!(target, DragTarget::User(_)));
    }

    #[test]
    fn test_drag_target_file() {
        let file_id = FileId::from_index(123);
        let target = DragTarget::File(file_id);
        assert!(matches!(target, DragTarget::File(_)));
    }

    #[test]
    fn test_drag_target_directory() {
        let dir_id = DirId::from_index(7);
        let target = DragTarget::Directory(dir_id);
        assert!(matches!(target, DragTarget::Directory(_)));
    }

    #[test]
    fn test_drag_target_copy() {
        let file_id = FileId::from_index(5);
        let target1 = DragTarget::File(file_id);
        let target2 = target1;
        assert!(matches!(target2, DragTarget::File(_)));
    }

    // ========================================================================
    // Distance Factor Tests
    // ========================================================================

    #[test]
    fn test_compute_distance_factor_at_origin() {
        // At distance 0, factor should be 1.0
        let factor = compute_distance_factor(0.0, 150.0);
        assert!((factor - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_distance_factor_at_threshold() {
        // At threshold distance, factor should be 0.0
        let factor = compute_distance_factor(150.0, 150.0);
        assert!((factor - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_distance_factor_at_half() {
        // At half threshold, factor should be 0.5
        let factor = compute_distance_factor(75.0, 150.0);
        assert!((factor - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_distance_factor_beyond_threshold() {
        // Beyond threshold, factor should be clamped to 0.0
        let factor = compute_distance_factor(200.0, 150.0);
        assert!((factor - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_distance_factor_negative_clamped() {
        // Negative distance clamped to max 1.0
        let factor = compute_distance_factor(-10.0, 150.0);
        assert!(factor <= 1.0);
    }

    // ========================================================================
    // Coupling Computation Tests
    // ========================================================================

    #[test]
    fn test_compute_coupling() {
        // Base coupling * distance factor
        assert!((compute_coupling(0.6, 1.0) - 0.6).abs() < 0.001);
        assert!((compute_coupling(0.6, 0.5) - 0.3).abs() < 0.001);
        assert!((compute_coupling(0.6, 0.0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_sibling_file_coupling_close() {
        // Close siblings should have strong coupling
        let coupling = compute_sibling_file_coupling(0.0);
        assert!((coupling - DRAG_COUPLING_STRENGTH).abs() < 0.001);
    }

    #[test]
    fn test_compute_sibling_file_coupling_far() {
        // Far siblings should have no coupling
        let coupling = compute_sibling_file_coupling(200.0);
        assert!((coupling - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_parent_dir_coupling_close() {
        // Parent gets half the coupling
        let coupling = compute_parent_dir_coupling(0.0);
        assert!((coupling - DRAG_COUPLING_STRENGTH * 0.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_sibling_dir_coupling_close() {
        // Sibling directories get 30% coupling
        let coupling = compute_sibling_dir_coupling(0.0);
        assert!((coupling - DRAG_COUPLING_STRENGTH * 0.3).abs() < 0.001);
    }

    #[test]
    fn test_compute_connected_file_coupling() {
        // Connected files use full coupling strength
        let coupling = compute_connected_file_coupling(0.0);
        assert!((coupling - DRAG_COUPLING_STRENGTH).abs() < 0.001);
    }

    // ========================================================================
    // Hit Radius Tests
    // ========================================================================

    #[test]
    fn test_compute_effective_hit_radius() {
        // entity_radius + hit_radius * 0.5
        let effective = compute_effective_hit_radius(10.0, 15.0);
        assert!((effective - 17.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_effective_hit_radius_zero_hit() {
        let effective = compute_effective_hit_radius(10.0, 0.0);
        assert!((effective - 10.0).abs() < 0.001);
    }

    // ========================================================================
    // Delta Significance Tests
    // ========================================================================

    #[test]
    fn test_is_significant_delta_small() {
        // Small delta is not significant
        assert!(!is_significant_delta(Vec2::new(0.05, 0.05)));
    }

    #[test]
    fn test_is_significant_delta_large() {
        // Large delta is significant
        assert!(is_significant_delta(Vec2::new(1.0, 0.0)));
    }

    #[test]
    fn test_is_significant_delta_boundary() {
        // At boundary (0.1)
        assert!(is_significant_delta(Vec2::new(0.1, 0.0)));
    }

    #[test]
    fn test_is_significant_delta_zero() {
        assert!(!is_significant_delta(Vec2::ZERO));
    }

    // ========================================================================
    // Coupling Significance Tests
    // ========================================================================

    #[test]
    fn test_is_significant_coupling_small() {
        assert!(!is_significant_coupling(0.005));
    }

    #[test]
    fn test_is_significant_coupling_large() {
        assert!(is_significant_coupling(0.5));
    }

    #[test]
    fn test_is_significant_coupling_boundary() {
        // Just above threshold
        assert!(is_significant_coupling(0.011));
        // At threshold (not significant)
        assert!(!is_significant_coupling(0.01));
    }

    // ========================================================================
    // Position Computation Tests
    // ========================================================================

    #[test]
    fn test_compute_coupled_position_full_coupling() {
        let current = Vec2::new(100.0, 100.0);
        let delta = Vec2::new(10.0, 5.0);
        let result = compute_coupled_position(current, delta, 1.0);
        assert!((result.x - 110.0).abs() < 0.001);
        assert!((result.y - 105.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_coupled_position_half_coupling() {
        let current = Vec2::new(100.0, 100.0);
        let delta = Vec2::new(10.0, 10.0);
        let result = compute_coupled_position(current, delta, 0.5);
        assert!((result.x - 105.0).abs() < 0.001);
        assert!((result.y - 105.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_coupled_position_zero_coupling() {
        let current = Vec2::new(100.0, 100.0);
        let delta = Vec2::new(10.0, 10.0);
        let result = compute_coupled_position(current, delta, 0.0);
        assert!((result.x - 100.0).abs() < 0.001);
        assert!((result.y - 100.0).abs() < 0.001);
    }

    // ========================================================================
    // Hit Area Tests
    // ========================================================================

    #[test]
    fn test_is_within_hit_area_inside() {
        let entity_pos = Vec2::new(100.0, 100.0);
        let point = Vec2::new(105.0, 100.0);
        assert!(is_within_hit_area(entity_pos, 10.0, point, 15.0));
    }

    #[test]
    fn test_is_within_hit_area_outside() {
        let entity_pos = Vec2::new(100.0, 100.0);
        let point = Vec2::new(150.0, 100.0);
        assert!(!is_within_hit_area(entity_pos, 10.0, point, 15.0));
    }

    #[test]
    fn test_is_within_hit_area_on_boundary() {
        let entity_pos = Vec2::new(100.0, 100.0);
        // effective radius = 10 + 15*0.5 = 17.5
        let point = Vec2::new(117.5, 100.0);
        assert!(is_within_hit_area(entity_pos, 10.0, point, 15.0));
    }

    // ========================================================================
    // Distance Computation Tests
    // ========================================================================

    #[test]
    fn test_compute_distance_same_point() {
        let a = Vec2::new(100.0, 100.0);
        let b = Vec2::new(100.0, 100.0);
        assert!((compute_distance(a, b) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_distance_horizontal() {
        let a = Vec2::new(0.0, 0.0);
        let b = Vec2::new(10.0, 0.0);
        assert!((compute_distance(a, b) - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_distance_diagonal() {
        let a = Vec2::new(0.0, 0.0);
        let b = Vec2::new(3.0, 4.0);
        assert!((compute_distance(a, b) - 5.0).abs() < 0.001);
    }

    // ========================================================================
    // Closer Comparison Tests
    // ========================================================================

    #[test]
    fn test_is_closer_none() {
        // Always closer when no previous best
        assert!(is_closer(10.0, None));
    }

    #[test]
    fn test_is_closer_true() {
        assert!(is_closer(5.0, Some(10.0)));
    }

    #[test]
    fn test_is_closer_false() {
        assert!(!is_closer(15.0, Some(10.0)));
    }

    #[test]
    fn test_is_closer_equal() {
        // Equal distance is not closer
        assert!(!is_closer(10.0, Some(10.0)));
    }

    // ========================================================================
    // Constants Tests
    // ========================================================================

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_entity_hit_radius_reasonable() {
        // Hit radius should be reasonable for picking
        assert!(ENTITY_HIT_RADIUS > 5.0);
        assert!(ENTITY_HIT_RADIUS < 50.0);
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_drag_coupling_strength_reasonable() {
        // Coupling should be between 0 and 1
        assert!(DRAG_COUPLING_STRENGTH > 0.0);
        assert!(DRAG_COUPLING_STRENGTH <= 1.0);
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_drag_coupling_distance_threshold_reasonable() {
        // Threshold should be large enough for natural dragging
        assert!(DRAG_COUPLING_DISTANCE_THRESHOLD > 50.0);
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_min_significant_delta_reasonable() {
        // Very small threshold to avoid jitter
        assert!(MIN_SIGNIFICANT_DELTA > 0.0);
        assert!(MIN_SIGNIFICANT_DELTA < 1.0);
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_min_coupling_threshold_reasonable() {
        // Small threshold to avoid unnecessary computations
        assert!(MIN_COUPLING_THRESHOLD > 0.0);
        assert!(MIN_COUPLING_THRESHOLD < 0.1);
    }
}
