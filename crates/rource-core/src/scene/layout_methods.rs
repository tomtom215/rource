// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Force-directed layout methods for the scene.
//!
//! This module contains the force-directed layout algorithm for positioning
//! directory nodes in a natural, organic-looking tree layout.
//!
//! ## Algorithm Selection
//!
//! The layout algorithm automatically selects between two modes:
//!
//! - **O(n²) Pairwise**: Used for small scenes (< 100 directories by default).
//!   Simple and exact, with low overhead for small n.
//!
//! - **O(n log n) Barnes-Hut**: Used for large scenes. Approximates distant
//!   clusters as single bodies, dramatically reducing computation time.
//!
//! The threshold can be configured via `Scene::set_barnes_hut_threshold()`.

use rource_math::Vec2;

use super::Scene;
use crate::entity::DirId;
use crate::physics::{calculate_adaptive_theta, random_push_direction, Body};

// ============================================================================
// Force-directed layout constants
// ============================================================================

/// Repulsion constant between directory nodes.
/// Higher values push sibling directories further apart.
pub(super) const FORCE_REPULSION: f32 = 800.0;

/// Attraction constant to parent directory.
/// Higher values pull children closer to their parents.
pub(super) const FORCE_ATTRACTION: f32 = 0.03;

/// Velocity damping factor (0.0-1.0).
/// Applied each frame to prevent oscillation.
pub(super) const FORCE_DAMPING: f32 = 0.85;

/// Maximum velocity to prevent instability.
pub(super) const FORCE_MAX_VELOCITY: f32 = 300.0;

/// Squared maximum velocity for optimized comparisons (avoids sqrt).
pub(super) const FORCE_MAX_VELOCITY_SQ: f32 = FORCE_MAX_VELOCITY * FORCE_MAX_VELOCITY;

/// Minimum distance for force calculation to prevent extreme forces.
pub(super) const FORCE_MIN_DISTANCE: f32 = 5.0;

/// Squared minimum distance for optimized comparisons (avoids sqrt).
pub(super) const FORCE_MIN_DISTANCE_SQ: f32 = FORCE_MIN_DISTANCE * FORCE_MIN_DISTANCE;

/// Maximum distance beyond which repulsion forces are negligible.
/// At d=100, force = `FORCE_REPULSION` / d² = 800 / 10000 = 0.08 (negligible).
pub(super) const FORCE_MAX_DISTANCE_SQ: f32 = 10000.0;

/// Directory data for force-directed layout calculation.
pub(super) type DirForceData = (DirId, Vec2, u32, Option<DirId>, Option<Vec2>, f32);

impl Scene {
    /// Returns whether Barnes-Hut algorithm is enabled.
    #[inline]
    #[must_use]
    pub fn is_barnes_hut_enabled(&self) -> bool {
        self.use_barnes_hut
    }

    /// Enables or disables Barnes-Hut algorithm for force calculations.
    ///
    /// When enabled and directory count exceeds the threshold, uses O(n log n)
    /// Barnes-Hut approximation instead of O(n²) pairwise calculation.
    pub fn set_barnes_hut_enabled(&mut self, enabled: bool) {
        self.use_barnes_hut = enabled;
    }

    /// Returns the current Barnes-Hut threshold.
    #[inline]
    #[must_use]
    pub fn barnes_hut_threshold(&self) -> usize {
        self.barnes_hut_threshold
    }

    /// Sets the threshold for Barnes-Hut algorithm activation.
    ///
    /// When directory count exceeds this threshold and Barnes-Hut is enabled,
    /// the algorithm switches from O(n²) to O(n log n).
    ///
    /// Default is 100 directories. Set to 0 to always use Barnes-Hut.
    pub fn set_barnes_hut_threshold(&mut self, threshold: usize) {
        self.barnes_hut_threshold = threshold;
    }

    /// Sets the theta parameter for Barnes-Hut approximation.
    ///
    /// - θ = 0.0: Exact calculation (no approximation)
    /// - θ = 0.5: Typical value for accurate simulations
    /// - θ = 0.8: Good balance of speed and accuracy (default)
    /// - θ = 1.0+: Faster but less accurate
    pub fn set_barnes_hut_theta(&mut self, theta: f32) {
        self.barnes_hut_tree.set_theta(theta);
    }

    /// Returns the current Barnes-Hut theta parameter.
    #[inline]
    #[must_use]
    pub fn barnes_hut_theta(&self) -> f32 {
        self.barnes_hut_tree.theta()
    }

    /// Returns whether Barnes-Hut is currently being used for layout calculations.
    ///
    /// True if Barnes-Hut is enabled AND directory count exceeds threshold.
    #[inline]
    #[must_use]
    pub fn is_using_barnes_hut(&self) -> bool {
        self.use_barnes_hut && self.directories.len() >= self.barnes_hut_threshold
    }

    /// Applies force-directed layout to directory nodes.
    ///
    /// This simulates physical forces between directories to create a natural,
    /// organic-looking tree layout:
    /// - **Repulsion**: Sibling directories and nearby nodes push each other apart
    /// - **Attraction**: Child directories are pulled toward their parents
    /// - **Damping**: Friction-like force that stabilizes the system
    ///
    /// Automatically selects between O(n²) pairwise and O(n log n) Barnes-Hut
    /// based on directory count and configuration.
    pub(super) fn apply_force_directed_layout(&mut self, dt: f32) {
        // Collect directory data for force calculation (reusing buffer)
        self.dir_data_buffer.clear();
        for d in self.directories.iter() {
            self.dir_data_buffer.push((
                d.id(),
                d.position(),
                d.depth(),
                d.parent(),
                d.parent_position(),
                d.target_distance(),
            ));
        }

        // Calculate forces for each directory (reusing buffer)
        // Use Vec indexing for O(1) cache-efficient access instead of HashMap
        let dir_count = self.dir_data_buffer.len();
        self.forces_buffer.clear();
        self.forces_buffer.resize(dir_count, Vec2::ZERO);

        // Select algorithm based on directory count and configuration
        if self.use_barnes_hut && dir_count >= self.barnes_hut_threshold {
            self.calculate_repulsion_barnes_hut(dir_count);
        } else {
            self.calculate_repulsion_pairwise(dir_count);
        }

        // Calculate attraction forces to parents (always O(n))
        self.calculate_attraction_forces(dir_count);

        // Apply forces to directories
        self.apply_forces_to_directories(dt);
    }

    /// Calculates repulsion forces using O(n²) pairwise algorithm.
    ///
    /// Best for small scenes (< 100 directories) where overhead is low.
    /// Uses Vec indexing for cache-efficient O(1) force accumulation.
    fn calculate_repulsion_pairwise(&mut self, dir_count: usize) {
        for i in 0..dir_count {
            let (_, pos_i, depth_i, parent_i, _, _) = self.dir_data_buffer[i];
            for j in (i + 1)..dir_count {
                let (_, pos_j, depth_j, parent_j, _, _) = self.dir_data_buffer[j];

                // Repel if:
                // 1. Siblings (same parent)
                // 2. Close in depth (within 1 level)
                let are_siblings = parent_i == parent_j && parent_i.is_some();
                let close_depth = depth_i.abs_diff(depth_j) <= 1;

                if !are_siblings && !close_depth {
                    continue;
                }

                let delta = pos_j - pos_i;
                let distance_sq = delta.length_squared();

                // Distance culling: skip pairs too far apart (force is negligible)
                if distance_sq > FORCE_MAX_DISTANCE_SQ {
                    continue;
                }

                // Guard against zero-length delta (check squared distance)
                if distance_sq < 0.001 {
                    // Push apart using precomputed direction LUT (13.9× faster than sin/cos)
                    let offset = random_push_direction(i, j);
                    self.forces_buffer[i] -= offset;
                    self.forces_buffer[j] += offset;
                    continue;
                }

                // Use squared distance for inverse-square repulsion: F = k / d²
                // Clamp to minimum squared distance to prevent extreme forces
                let clamped_dist_sq = distance_sq.max(FORCE_MIN_DISTANCE_SQ);

                // Optimized force calculation: combine direction and magnitude
                // Force = (delta/d) * (k/d²) = delta * k / d³
                // Using one division instead of three: saves ~20 cycles per pair
                let distance = clamped_dist_sq.sqrt();
                let force_scale = FORCE_REPULSION / (distance * clamped_dist_sq);
                let force = delta * force_scale;

                // Apply equal and opposite forces using Vec indexing (O(1) vs HashMap O(1) amortized)
                self.forces_buffer[i] -= force;
                self.forces_buffer[j] += force;
            }
        }
    }

    /// Calculates repulsion forces using O(n log n) Barnes-Hut algorithm.
    ///
    /// Uses a quadtree to approximate distant clusters as single bodies,
    /// dramatically reducing computation for large scenes.
    /// Uses Vec indexing for cache-efficient O(1) force accumulation.
    ///
    /// Automatically adjusts theta based on directory count (adaptive theta):
    /// - ≤200 dirs: θ=0.8 (accurate)
    /// - 1000 dirs: θ≈1.0 (30% faster)
    /// - 5000+ dirs: θ=1.5 (62% faster)
    fn calculate_repulsion_barnes_hut(&mut self, dir_count: usize) {
        // Use adaptive theta for optimal speed/accuracy tradeoff
        let adaptive_theta = calculate_adaptive_theta(dir_count);
        self.barnes_hut_tree.set_theta(adaptive_theta);

        // Build Barnes-Hut tree from current directory positions
        self.barnes_hut_tree.clear();

        for i in 0..dir_count {
            let (_, pos, _, _, _, _) = self.dir_data_buffer[i];
            self.barnes_hut_tree.insert(Body::new(pos));
        }

        // Calculate forces for each directory using Barnes-Hut approximation
        for i in 0..dir_count {
            let (_, pos, _, _, _, _) = self.dir_data_buffer[i];
            let body = Body::new(pos);

            // Get repulsive force from all other bodies (approximated by tree)
            let force =
                self.barnes_hut_tree
                    .calculate_force(&body, FORCE_REPULSION, FORCE_MIN_DISTANCE_SQ);

            if force.length_squared() > 0.001 {
                self.forces_buffer[i] += force;
            }
        }
    }

    /// Calculates attraction forces to parent directories (always O(n)).
    /// Uses Vec indexing for cache-efficient O(1) force accumulation.
    fn calculate_attraction_forces(&mut self, dir_count: usize) {
        for i in 0..dir_count {
            let (_, pos, _depth, _parent_id, parent_pos, target_dist) = self.dir_data_buffer[i];
            if let Some(parent_pos) = parent_pos {
                let delta = parent_pos - pos;
                let distance_sq = delta.length_squared();
                let target_dist_sq = target_dist * target_dist;

                // Only attract if beyond target distance (compare squared to avoid sqrt)
                if distance_sq > target_dist_sq && distance_sq > 0.001 {
                    // Optimized: compute distance and combine direction with magnitude
                    // Force = (delta/d) * (d - target) * k = delta * (1 - target/d) * k
                    let distance = distance_sq.sqrt();
                    let inv_distance = 1.0 / distance;
                    let excess = distance - target_dist;
                    // Combine: direction * excess * k = (delta * inv_distance) * excess * k
                    let force = delta * (inv_distance * excess * FORCE_ATTRACTION);
                    self.forces_buffer[i] += force;
                }
            }
        }
    }

    /// Applies computed forces to directories and integrates physics.
    /// Uses enumerate to correlate with `forces_buffer` Vec indices.
    fn apply_forces_to_directories(&mut self, dt: f32) {
        for (i, dir) in self.directories.iter_mut().enumerate() {
            // Skip root (anchor it in place)
            if dir.is_root() {
                continue;
            }

            // Access force by index (O(1) Vec access vs O(1) amortized HashMap)
            // Note: forces_buffer is guaranteed to have same length as dir_data_buffer
            // which matches the iteration order of directories
            let force = self.forces_buffer[i];
            if force.length_squared() > 0.001 {
                // Apply force as acceleration (assuming unit mass)
                dir.add_velocity(force * dt);

                // Clamp velocity to prevent instability (use squared comparison)
                let mut vel = dir.velocity();
                let speed_sq = vel.length_squared();
                if speed_sq > FORCE_MAX_VELOCITY_SQ {
                    // Only compute sqrt when actually needed for clamping
                    let speed = speed_sq.sqrt();
                    vel *= FORCE_MAX_VELOCITY / speed;
                }

                // Apply damping and cache final velocity (saves one velocity() call)
                let damped_vel = vel * FORCE_DAMPING;
                dir.set_velocity(damped_vel);

                // Integrate position using cached velocity
                let new_pos = dir.position() + damped_vel * dt;
                dir.set_position(new_pos);
            } else {
                // No force but still apply damping and integration for existing velocity
                dir.update_physics(dt, FORCE_DAMPING);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_force_constants() {
        // Verify constants are reasonable
        assert!(FORCE_REPULSION > 0.0);
        assert!(FORCE_ATTRACTION > 0.0);
        assert!(FORCE_DAMPING > 0.0 && FORCE_DAMPING < 1.0);
        assert!(FORCE_MAX_VELOCITY > 0.0);
        assert!(FORCE_MIN_DISTANCE > 0.0);
    }

    #[test]
    fn test_squared_constants() {
        // Verify squared constants are correct
        let expected_vel_sq = FORCE_MAX_VELOCITY * FORCE_MAX_VELOCITY;
        assert!((FORCE_MAX_VELOCITY_SQ - expected_vel_sq).abs() < 0.001);

        let expected_dist_sq = FORCE_MIN_DISTANCE * FORCE_MIN_DISTANCE;
        assert!((FORCE_MIN_DISTANCE_SQ - expected_dist_sq).abs() < 0.001);
    }

    #[test]
    fn test_barnes_hut_threshold_default() {
        let scene = Scene::new();
        assert_eq!(scene.barnes_hut_threshold(), 100);
    }

    #[test]
    fn test_barnes_hut_enabled_default() {
        let scene = Scene::new();
        assert!(scene.is_barnes_hut_enabled());
    }

    #[test]
    fn test_set_barnes_hut_threshold() {
        let mut scene = Scene::new();
        scene.set_barnes_hut_threshold(500);
        assert_eq!(scene.barnes_hut_threshold(), 500);
    }

    #[test]
    fn test_set_barnes_hut_enabled() {
        let mut scene = Scene::new();
        scene.set_barnes_hut_enabled(false);
        assert!(!scene.is_barnes_hut_enabled());
    }

    #[test]
    fn test_is_using_barnes_hut() {
        let scene = Scene::new();
        // Empty scene should not use Barnes-Hut (0 < 100 threshold)
        assert!(!scene.is_using_barnes_hut());
    }

    #[test]
    fn test_barnes_hut_theta() {
        let mut scene = Scene::new();
        scene.set_barnes_hut_theta(0.5);
        assert!((scene.barnes_hut_theta() - 0.5).abs() < 0.001);
    }
}
