// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Spatial index and visibility query methods for the scene.
//!
//! This module contains methods for managing the spatial index (quadtree)
//! and querying visible entities for frustum culling.

use rource_math::{Bounds, Vec2};

use super::{EntityType, Scene};
use crate::entity::{DirId, FileId, UserId};

impl Scene {
    /// Rebuilds the spatial index with current entity positions.
    pub fn rebuild_spatial_index(&mut self) {
        self.spatial.clear();

        // Add directories
        for dir in self.directories.iter() {
            self.spatial
                .insert(dir.position(), EntityType::Directory(dir.id()));
        }

        // Add files
        for (id, file) in &self.files {
            self.spatial.insert(file.position(), EntityType::File(*id));
        }

        // Add users
        for (id, user) in &self.users {
            self.spatial.insert(user.position(), EntityType::User(*id));
        }
    }

    /// Queries entities within the given bounds.
    #[must_use]
    pub fn query_entities(&self, bounds: &Bounds) -> Vec<EntityType> {
        self.spatial.query(bounds).into_iter().copied().collect()
    }

    /// Queries entities within a circular region.
    #[must_use]
    pub fn query_entities_circle(&self, center: Vec2, radius: f32) -> Vec<EntityType> {
        self.spatial
            .query_circle_with_pos(center, radius)
            .into_iter()
            .map(|(_, &entity)| entity)
            .collect()
    }

    /// Finds the nearest entity to the given position.
    #[must_use]
    pub fn nearest_entity(&self, position: Vec2) -> Option<EntityType> {
        self.spatial.nearest(position).map(|(_, &entity)| entity)
    }

    /// Returns IDs of files visible within the given bounds.
    ///
    /// This is useful for frustum culling - only render files that are
    /// within the camera's visible bounds. The bounds should typically
    /// include some margin for entity radii.
    #[must_use]
    pub fn visible_file_ids(&self, bounds: &Bounds) -> Vec<FileId> {
        self.spatial
            .query(bounds)
            .into_iter()
            .filter_map(|entity| match entity {
                EntityType::File(id) => Some(*id),
                _ => None,
            })
            .collect()
    }

    /// Returns IDs of users visible within the given bounds.
    ///
    /// This is useful for frustum culling - only render users that are
    /// within the camera's visible bounds.
    #[must_use]
    pub fn visible_user_ids(&self, bounds: &Bounds) -> Vec<UserId> {
        self.spatial
            .query(bounds)
            .into_iter()
            .filter_map(|entity| match entity {
                EntityType::User(id) => Some(*id),
                _ => None,
            })
            .collect()
    }

    /// Returns IDs of directories visible within the given bounds.
    ///
    /// This is useful for frustum culling - only render directories that are
    /// within the camera's visible bounds.
    #[must_use]
    pub fn visible_directory_ids(&self, bounds: &Bounds) -> Vec<DirId> {
        self.spatial
            .query(bounds)
            .into_iter()
            .filter_map(|entity| match entity {
                EntityType::Directory(id) => Some(*id),
                _ => None,
            })
            .collect()
    }

    /// Returns all entity types visible within the given bounds, grouped by type.
    ///
    /// This provides efficient frustum culling by using the spatial index
    /// to query only entities within the visible area.
    #[must_use]
    pub fn visible_entities(&self, bounds: &Bounds) -> (Vec<DirId>, Vec<FileId>, Vec<UserId>) {
        let mut dirs = Vec::new();
        let mut files = Vec::new();
        let mut users = Vec::new();

        for entity in self.spatial.query(bounds) {
            match entity {
                EntityType::Directory(id) => dirs.push(*id),
                EntityType::File(id) => files.push(*id),
                EntityType::User(id) => users.push(*id),
            }
        }

        (dirs, files, users)
    }

    /// Zero-allocation version of `visible_entities` that reuses existing buffers.
    ///
    /// This is the preferred method for hot paths (e.g., render loops) where
    /// avoiding per-frame allocations is critical for performance.
    ///
    /// # Arguments
    ///
    /// * `bounds` - The visible area to query
    /// * `dirs` - Buffer to fill with visible directory IDs (cleared first)
    /// * `files` - Buffer to fill with visible file IDs (cleared first)
    /// * `users` - Buffer to fill with visible user IDs (cleared first)
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Reusable buffers (stored in renderer state)
    /// let mut dirs_buf = Vec::new();
    /// let mut files_buf = Vec::new();
    /// let mut users_buf = Vec::new();
    ///
    /// // Each frame - zero allocations after initial capacity
    /// scene.visible_entities_into(&visible_bounds, &mut dirs_buf, &mut files_buf, &mut users_buf);
    /// ```
    #[inline]
    pub fn visible_entities_into(
        &self,
        bounds: &Bounds,
        dirs: &mut Vec<DirId>,
        files: &mut Vec<FileId>,
        users: &mut Vec<UserId>,
    ) {
        dirs.clear();
        files.clear();
        users.clear();

        // Use zero-allocation visitor pattern - no intermediate Vec allocation
        self.spatial.query_for_each(bounds, |entity| match entity {
            EntityType::Directory(id) => dirs.push(*id),
            EntityType::File(id) => files.push(*id),
            EntityType::User(id) => users.push(*id),
        });
    }

    /// Zero-allocation version of `query_entities` that reuses an existing buffer.
    ///
    /// Preferred for hot paths where allocations should be avoided.
    #[inline]
    pub fn query_entities_into(&self, bounds: &Bounds, output: &mut Vec<EntityType>) {
        output.clear();
        self.spatial
            .query_for_each(bounds, |entity| output.push(*entity));
    }

    /// Zero-allocation version of `query_entities_circle` that reuses an existing buffer.
    ///
    /// Preferred for hot paths where allocations should be avoided.
    #[inline]
    pub fn query_entities_circle_into(
        &self,
        center: Vec2,
        radius: f32,
        output: &mut Vec<EntityType>,
    ) {
        output.clear();
        self.spatial
            .query_circle_for_each(center, radius, |_, entity| output.push(*entity));
    }

    /// Zero-allocation version of `visible_file_ids` that reuses an existing buffer.
    ///
    /// Preferred for hot paths where allocations should be avoided.
    #[inline]
    pub fn visible_file_ids_into(&self, bounds: &Bounds, output: &mut Vec<FileId>) {
        output.clear();
        self.spatial.query_for_each(bounds, |entity| {
            if let EntityType::File(id) = entity {
                output.push(*id);
            }
        });
    }

    /// Zero-allocation version of `visible_user_ids` that reuses an existing buffer.
    ///
    /// Preferred for hot paths where allocations should be avoided.
    #[inline]
    pub fn visible_user_ids_into(&self, bounds: &Bounds, output: &mut Vec<UserId>) {
        output.clear();
        self.spatial.query_for_each(bounds, |entity| {
            if let EntityType::User(id) = entity {
                output.push(*id);
            }
        });
    }

    /// Zero-allocation version of `visible_directory_ids` that reuses an existing buffer.
    ///
    /// Preferred for hot paths where allocations should be avoided.
    #[inline]
    pub fn visible_directory_ids_into(&self, bounds: &Bounds, output: &mut Vec<DirId>) {
        output.clear();
        self.spatial.query_for_each(bounds, |entity| {
            if let EntityType::Directory(id) = entity {
                output.push(*id);
            }
        });
    }

    /// Returns the expanded bounds for visibility queries.
    ///
    /// This adds a margin to account for entity radii and ensures
    /// entities at the edge of the screen are included.
    #[must_use]
    pub fn expand_bounds_for_visibility(bounds: &Bounds, margin: f32) -> Bounds {
        Bounds::new(
            bounds.min - Vec2::splat(margin),
            bounds.max + Vec2::splat(margin),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn test_expand_bounds_for_visibility() {
        let bounds = Bounds::new(Vec2::new(0.0, 0.0), Vec2::new(100.0, 100.0));
        let expanded = Scene::expand_bounds_for_visibility(&bounds, 10.0);

        assert_eq!(expanded.min, Vec2::new(-10.0, -10.0));
        assert_eq!(expanded.max, Vec2::new(110.0, 110.0));
    }

    #[test]
    fn test_visible_entities_into_clears_buffers() {
        let mut scene = Scene::new();

        // Create some entities
        scene.create_file(Path::new("test.rs"));
        scene.get_or_create_user("Alice");
        scene.rebuild_spatial_index();

        // Pre-fill buffers with some values
        let mut dirs = Vec::with_capacity(10);
        let mut files = Vec::with_capacity(10);
        let mut users = Vec::with_capacity(10);

        // First query that should populate buffers
        let full_bounds = *scene.bounds();
        scene.visible_entities_into(&full_bounds, &mut dirs, &mut files, &mut users);
        assert!(!dirs.is_empty() || !files.is_empty() || !users.is_empty());

        // Query with empty bounds (should clear and leave empty)
        let empty_bounds = Bounds::new(Vec2::new(10000.0, 10000.0), Vec2::new(10001.0, 10001.0));
        scene.visible_entities_into(&empty_bounds, &mut dirs, &mut files, &mut users);

        // Buffers should be cleared
        assert!(dirs.is_empty());
        assert!(files.is_empty());
        assert!(users.is_empty());
    }
}
