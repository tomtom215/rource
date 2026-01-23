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
}
