//! Force-directed layout methods for the scene.
//!
//! This module contains the force-directed layout algorithm for positioning
//! directory nodes in a natural, organic-looking tree layout.

use rource_math::Vec2;

use super::Scene;
use crate::entity::DirId;

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

/// Directory data for force-directed layout calculation.
pub(super) type DirForceData = (DirId, Vec2, u32, Option<DirId>, Option<Vec2>, f32);

impl Scene {
    /// Applies force-directed layout to directory nodes.
    ///
    /// This simulates physical forces between directories to create a natural,
    /// organic-looking tree layout:
    /// - **Repulsion**: Sibling directories and nearby nodes push each other apart
    /// - **Attraction**: Child directories are pulled toward their parents
    /// - **Damping**: Friction-like force that stabilizes the system
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
        self.forces_buffer.clear();

        // Calculate repulsion forces between related directories (O(n²) but n is typically small)
        let dir_count = self.dir_data_buffer.len();
        for i in 0..dir_count {
            let (id_i, pos_i, depth_i, parent_i, _, _) = self.dir_data_buffer[i];
            for j in (i + 1)..dir_count {
                let (id_j, pos_j, depth_j, parent_j, _, _) = self.dir_data_buffer[j];

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

                // Guard against zero-length delta (check squared distance)
                if distance_sq < 0.001 {
                    // Push apart randomly based on indices
                    let offset = Vec2::new((i as f32).sin() * 5.0, (j as f32).cos() * 5.0);
                    *self.forces_buffer.entry(id_i).or_insert(Vec2::ZERO) -= offset;
                    *self.forces_buffer.entry(id_j).or_insert(Vec2::ZERO) += offset;
                    continue;
                }

                // Use squared distance for inverse-square repulsion: F = k / d²
                // Clamp to minimum squared distance to prevent extreme forces
                let clamped_dist_sq = distance_sq.max(FORCE_MIN_DISTANCE_SQ);
                let force_magnitude = FORCE_REPULSION / clamped_dist_sq;

                // Compute direction only when needed (requires sqrt via length)
                let distance = distance_sq.sqrt();
                let direction = delta / distance; // Equivalent to delta.normalized()
                let force = direction * force_magnitude;

                // Apply equal and opposite forces
                *self.forces_buffer.entry(id_i).or_insert(Vec2::ZERO) -= force;
                *self.forces_buffer.entry(id_j).or_insert(Vec2::ZERO) += force;
            }
        }

        // Calculate attraction forces to parents
        for i in 0..dir_count {
            let (id, pos, _depth, _parent_id, parent_pos, target_dist) = self.dir_data_buffer[i];
            if let Some(parent_pos) = parent_pos {
                let delta = parent_pos - pos;
                let distance_sq = delta.length_squared();
                let target_dist_sq = target_dist * target_dist;

                // Only attract if beyond target distance (compare squared to avoid sqrt)
                if distance_sq > target_dist_sq && distance_sq > 0.001 {
                    // Now compute actual distance since we need it for the force
                    let distance = distance_sq.sqrt();
                    let excess = distance - target_dist;
                    let direction = delta / distance; // Equivalent to delta.normalized()
                    let force = direction * excess * FORCE_ATTRACTION;
                    *self.forces_buffer.entry(id).or_insert(Vec2::ZERO) += force;
                }
            }
        }

        // Apply forces to directories
        for dir in self.directories.iter_mut() {
            // Skip root (anchor it in place)
            if dir.is_root() {
                continue;
            }

            if let Some(&force) = self.forces_buffer.get(&dir.id()) {
                // Apply force as acceleration (assuming unit mass)
                dir.add_velocity(force * dt);

                // Clamp velocity to prevent instability (use squared comparison)
                let vel = dir.velocity();
                let speed_sq = vel.length_squared();
                if speed_sq > FORCE_MAX_VELOCITY_SQ {
                    // Only compute sqrt when actually needed for clamping
                    let speed = speed_sq.sqrt();
                    dir.set_velocity(vel * (FORCE_MAX_VELOCITY / speed));
                }

                // Apply damping
                dir.set_velocity(dir.velocity() * FORCE_DAMPING);

                // Integrate position
                let new_pos = dir.position() + dir.velocity() * dt;
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
    fn test_force_constants() {
        assert!(FORCE_REPULSION > 0.0);
        assert!(FORCE_ATTRACTION > 0.0);
        assert!(FORCE_DAMPING > 0.0 && FORCE_DAMPING < 1.0);
        assert!(FORCE_MAX_VELOCITY > 0.0);
        assert!((FORCE_MAX_VELOCITY_SQ - FORCE_MAX_VELOCITY * FORCE_MAX_VELOCITY).abs() < 0.001);
        assert!(FORCE_MIN_DISTANCE > 0.0);
        assert!((FORCE_MIN_DISTANCE_SQ - FORCE_MIN_DISTANCE * FORCE_MIN_DISTANCE).abs() < 0.001);
    }
}
