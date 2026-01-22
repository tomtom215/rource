//! Entity bounds computation methods for the scene.
//!
//! This module contains methods for computing the actual bounding box
//! of all entities in the scene, with caching for performance.

use rource_math::{Bounds, Vec2};

use super::Scene;

impl Scene {
    /// Computes the actual bounding box of all entities in the scene.
    ///
    /// Returns `None` if there are no entities with positions.
    /// This is useful for camera fitting to actual content.
    ///
    /// Uses caching to avoid recomputing bounds every frame. The cache is
    /// invalidated when entities are added or removed, or when
    /// [`Self::invalidate_bounds_cache`] is called.
    #[must_use]
    pub fn compute_entity_bounds(&mut self) -> Option<Bounds> {
        // Return cached bounds if still valid
        if !self.bounds_dirty {
            if let Some(cached) = self.cached_entity_bounds {
                return Some(cached);
            }
        }

        // Recompute bounds
        let bounds = self.compute_entity_bounds_uncached();
        self.cached_entity_bounds = bounds;
        self.bounds_dirty = false;
        bounds
    }

    /// Computes entity bounds without using cache.
    ///
    /// This is useful when you need fresh bounds and don't want to update the cache.
    #[must_use]
    pub fn compute_entity_bounds_uncached(&self) -> Option<Bounds> {
        let mut bounds = Bounds::INVERTED;

        // Include file positions
        for file in self.files.values() {
            let pos = file.position();
            let radius = file.radius();
            bounds = bounds
                .include_point(pos - Vec2::splat(radius))
                .include_point(pos + Vec2::splat(radius));
        }

        // Include user positions
        for user in self.users.values() {
            let pos = user.position();
            let radius = user.radius();
            bounds = bounds
                .include_point(pos - Vec2::splat(radius))
                .include_point(pos + Vec2::splat(radius));
        }

        // Include directory positions
        for dir in self.directories.iter() {
            let pos = dir.position();
            let radius = dir.radius();
            bounds = bounds
                .include_point(pos - Vec2::splat(radius))
                .include_point(pos + Vec2::splat(radius));
        }

        // Return None if bounds are still inverted (no entities)
        if bounds.min.x > bounds.max.x || bounds.min.y > bounds.max.y {
            None
        } else {
            Some(bounds)
        }
    }

    /// Invalidates the cached entity bounds, forcing a recomputation on next access.
    #[inline]
    pub fn invalidate_bounds_cache(&mut self) {
        self.bounds_dirty = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn test_compute_entity_bounds_empty_scene() {
        let mut scene = Scene::new();
        // Empty scene has at least root directory, so bounds should exist
        let bounds = scene.compute_entity_bounds();
        assert!(bounds.is_some());
    }

    #[test]
    fn test_bounds_cache_invalidation() {
        let mut scene = Scene::new();

        // Initial computation
        let bounds1 = scene.compute_entity_bounds();
        assert!(bounds1.is_some());
        assert!(!scene.bounds_dirty);

        // Invalidate
        scene.invalidate_bounds_cache();
        assert!(scene.bounds_dirty);

        // Recompute
        let bounds2 = scene.compute_entity_bounds();
        assert!(bounds2.is_some());
        assert!(!scene.bounds_dirty);
    }

    #[test]
    fn test_compute_entity_bounds_with_files() {
        let mut scene = Scene::new();

        scene.create_file(Path::new("test.rs"));

        let bounds = scene.compute_entity_bounds();
        assert!(bounds.is_some());

        let b = bounds.unwrap();
        // Bounds should have positive width and height
        assert!(b.max.x > b.min.x);
        assert!(b.max.y > b.min.y);
    }
}
