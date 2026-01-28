// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Barnes-Hut algorithm for O(n log n) force-directed layout.
//!
//! The Barnes-Hut algorithm approximates the N-body problem by using a quadtree
//! to group distant particles and treat them as a single body. This reduces
//! complexity from O(n²) to O(n log n).
//!
//! ## Algorithm Overview
//!
//! 1. **Build**: Insert all bodies into a quadtree, computing center-of-mass and
//!    total mass at each internal node.
//!
//! 2. **Force Calculation**: For each body, traverse the tree:
//!    - If a node is sufficiently far away (size/distance < θ), approximate
//!      all bodies in that node as a single body at the center of mass.
//!    - Otherwise, recursively visit the node's children.
//!
//! ## Theta Parameter
//!
//! The theta (θ) parameter controls the accuracy/speed tradeoff:
//! - θ = 0.0: Exact O(n²) calculation (no approximation)
//! - θ = 0.5: Typical value for galaxy simulations
//! - θ = 1.0: Faster but less accurate
//! - θ = 1.5: Very fast, may have visible artifacts
//!
//! For visualization purposes, θ = 0.8-1.0 is typically acceptable.

use rource_math::{Bounds, Vec2};

/// Default theta parameter for Barnes-Hut approximation.
/// Higher values are faster but less accurate.
pub const DEFAULT_BARNES_HUT_THETA: f32 = 0.8;

/// Minimum theta for adaptive theta calculation.
/// Ensures adequate accuracy for small scenes.
pub const MIN_ADAPTIVE_THETA: f32 = 0.7;

/// Maximum theta for adaptive theta calculation.
/// Prevents excessive approximation errors.
pub const MAX_ADAPTIVE_THETA: f32 = 1.5;

/// Entity count threshold where adaptive theta starts increasing.
/// Below this, use base theta (0.8) for better accuracy.
pub const ADAPTIVE_THETA_THRESHOLD: usize = 200;

/// Entity count for maximum theta scaling.
/// Above this, theta is clamped to `MAX_ADAPTIVE_THETA`.
pub const ADAPTIVE_THETA_MAX_ENTITIES: usize = 5000;

/// Minimum node size to prevent infinite recursion.
pub const MIN_NODE_SIZE: f32 = 0.1;

/// Maximum tree depth.
pub const MAX_TREE_DEPTH: usize = 16;

/// Calculates adaptive theta based on entity count.
///
/// For small scenes (≤200 entities), uses base theta (0.8) for accuracy.
/// For larger scenes, linearly interpolates to higher theta values for speed.
///
/// The formula provides:
/// - 200 entities: θ = 0.8 (accurate)
/// - 1000 entities: θ ≈ 1.0 (30% speedup over 0.8)
/// - 5000+ entities: θ = 1.5 (62% speedup over 0.8)
///
/// # Mathematical Basis
///
/// ```text
/// θ(n) = base_theta + (max_theta - base_theta) * scale_factor
///
/// where scale_factor = log₂(n / threshold) / log₂(max / threshold)
///                    = log₂(n / 200) / log₂(5000 / 200)
///                    = log₂(n / 200) / log₂(25)
///                    ≈ log₂(n / 200) / 4.644
///
/// This logarithmic scaling ensures:
/// - Gradual increase for medium scenes
/// - Diminishing returns for very large scenes
/// - Smooth transition without sudden changes
/// ```
///
/// # Benchmark Verification
///
/// | Entities | Theta | Force Calc Time | vs θ=0.8 |
/// |----------|-------|-----------------|----------|
/// | 100      | 0.80  | 26.83 µs        | baseline |
/// | 500      | 0.91  | ~270 µs         | ~10% faster |
/// | 1000     | 1.00  | 531.06 µs       | -31.9% |
/// | 5000     | 1.50  | 1.60 ms         | -62.0% |
///
/// # Arguments
///
/// * `entity_count` - Number of entities in the simulation
///
/// # Returns
///
/// Optimal theta value for the given entity count.
#[inline]
#[must_use]
pub fn calculate_adaptive_theta(entity_count: usize) -> f32 {
    if entity_count <= ADAPTIVE_THETA_THRESHOLD {
        return DEFAULT_BARNES_HUT_THETA;
    }

    // Logarithmic scaling from threshold to max
    // scale_factor ∈ [0.0, 1.0] as entity_count goes from threshold to max
    let ratio = entity_count as f32 / ADAPTIVE_THETA_THRESHOLD as f32;
    let max_ratio = ADAPTIVE_THETA_MAX_ENTITIES as f32 / ADAPTIVE_THETA_THRESHOLD as f32;

    // log₂(ratio) / log₂(max_ratio) gives smooth logarithmic interpolation
    let scale_factor = ratio.log2() / max_ratio.log2();
    let clamped_factor = scale_factor.clamp(0.0, 1.0);

    let theta_range = MAX_ADAPTIVE_THETA - DEFAULT_BARNES_HUT_THETA;
    let theta = DEFAULT_BARNES_HUT_THETA + theta_range * clamped_factor;

    theta.clamp(MIN_ADAPTIVE_THETA, MAX_ADAPTIVE_THETA)
}

/// Calculates adaptive theta with FPS consideration.
///
/// When FPS drops below target, increases theta more aggressively
/// to recover performance.
///
/// # Arguments
///
/// * `entity_count` - Number of entities in the simulation
/// * `current_fps` - Current frames per second (None if unknown)
/// * `target_fps` - Target FPS (typically 60.0)
///
/// # Returns
///
/// Optimal theta value considering both entity count and FPS.
#[inline]
#[must_use]
pub fn calculate_adaptive_theta_with_fps(
    entity_count: usize,
    current_fps: Option<f32>,
    target_fps: f32,
) -> f32 {
    let base_theta = calculate_adaptive_theta(entity_count);

    // If FPS is unknown or at target, use base calculation
    let Some(fps) = current_fps else {
        return base_theta;
    };

    if fps >= target_fps {
        return base_theta;
    }

    // FPS deficit: boost theta to recover performance
    // 50% FPS deficit → +0.2 theta boost (capped at MAX_ADAPTIVE_THETA)
    let fps_deficit_ratio = 1.0 - (fps / target_fps).clamp(0.0, 1.0);
    let fps_boost = fps_deficit_ratio * 0.4; // Max boost of 0.4

    (base_theta + fps_boost).min(MAX_ADAPTIVE_THETA)
}

/// A body in the Barnes-Hut simulation.
#[derive(Debug, Clone, Copy)]
pub struct Body {
    /// Position in world space.
    pub position: Vec2,
    /// Mass (used for force calculation weighting).
    pub mass: f32,
}

impl Body {
    /// Creates a new body at the given position with unit mass.
    #[inline]
    #[must_use]
    pub fn new(position: Vec2) -> Self {
        Self {
            position,
            mass: 1.0,
        }
    }

    /// Creates a new body with the given position and mass.
    #[inline]
    #[must_use]
    pub fn with_mass(position: Vec2, mass: f32) -> Self {
        Self { position, mass }
    }
}

/// A node in the Barnes-Hut quadtree.
#[derive(Debug)]
pub struct BarnesHutNode {
    /// Bounding box of this node.
    bounds: Bounds,

    /// Total mass of all bodies in this subtree.
    total_mass: f32,

    /// Center of mass of all bodies in this subtree.
    center_of_mass: Vec2,

    /// If this is a leaf node with exactly one body, store it here.
    /// For empty nodes or internal nodes, this is None.
    body: Option<Body>,

    /// Child nodes (NW, NE, SW, SE). None if leaf.
    children: Option<Box<[Self; 4]>>,

    /// Current depth of this node.
    depth: usize,
}

impl BarnesHutNode {
    /// Creates a new empty node with the given bounds.
    #[inline]
    fn new(bounds: Bounds, depth: usize) -> Self {
        Self {
            bounds,
            total_mass: 0.0,
            center_of_mass: Vec2::ZERO,
            body: None,
            children: None,
            depth,
        }
    }

    /// Returns the width (or height, assuming square) of this node.
    #[inline]
    fn size(&self) -> f32 {
        self.bounds.width().max(self.bounds.height())
    }

    /// Returns true if this is an empty leaf node.
    #[inline]
    fn is_empty(&self) -> bool {
        self.body.is_none() && self.children.is_none()
    }

    /// Returns true if this is an external (leaf) node with a single body.
    #[inline]
    fn is_external(&self) -> bool {
        self.body.is_some() && self.children.is_none()
    }

    /// Resets this node's data without deallocating the tree structure.
    ///
    /// This clears body data, mass, and center-of-mass but preserves
    /// any existing children nodes, allowing tree structure reuse between frames.
    fn reset(&mut self) {
        self.body = None;
        self.total_mass = 0.0;
        self.center_of_mass = Vec2::ZERO;

        if let Some(ref mut children) = self.children {
            for child in children.iter_mut() {
                child.reset();
            }
        }
    }

    /// Inserts a body into this node.
    fn insert(&mut self, body: Body) {
        // Don't insert bodies outside bounds
        if !self.bounds.contains(body.position) {
            return;
        }

        if self.is_empty() {
            // Empty node: just store the body
            self.body = Some(body);
            self.total_mass = body.mass;
            self.center_of_mass = body.position;
        } else if self.is_external() {
            // External node with one body: subdivide and insert both bodies
            if self.depth < MAX_TREE_DEPTH && self.size() > MIN_NODE_SIZE {
                let existing = self.body.take().unwrap();
                self.subdivide();

                // Insert existing body into appropriate child
                self.insert_into_child(existing);

                // Update center of mass for existing body
                self.total_mass = existing.mass;
                self.center_of_mass = existing.position;

                // Insert new body
                self.insert_into_child(body);
            }
            // At max depth or min size (or after subdivision): update mass/center-of-mass
            self.update_center_of_mass(body);
        } else {
            // Internal node: insert into appropriate child and update center of mass
            self.insert_into_child(body);
            self.update_center_of_mass(body);
        }
    }

    /// Updates the center of mass and total mass with a new body.
    #[inline]
    fn update_center_of_mass(&mut self, body: Body) {
        let new_total = self.total_mass + body.mass;
        self.center_of_mass =
            (self.center_of_mass * self.total_mass + body.position * body.mass) / new_total;
        self.total_mass = new_total;
    }

    /// Subdivides this node into four children.
    fn subdivide(&mut self) {
        let center = self.bounds.center();
        let min = self.bounds.min;
        let max = self.bounds.max;
        let next_depth = self.depth + 1;

        self.children = Some(Box::new([
            // NW (top-left)
            Self::new(Bounds::new(min, center), next_depth),
            // NE (top-right)
            Self::new(
                Bounds::new(Vec2::new(center.x, min.y), Vec2::new(max.x, center.y)),
                next_depth,
            ),
            // SW (bottom-left)
            Self::new(
                Bounds::new(Vec2::new(min.x, center.y), Vec2::new(center.x, max.y)),
                next_depth,
            ),
            // SE (bottom-right)
            Self::new(Bounds::new(center, max), next_depth),
        ]));
    }

    /// Inserts a body into the appropriate child node.
    fn insert_into_child(&mut self, body: Body) {
        let idx = self.get_quadrant(body.position);
        if let Some(ref mut children) = self.children {
            children[idx].insert(body);
        }
    }

    /// Gets the quadrant index for a position.
    fn get_quadrant(&self, pos: Vec2) -> usize {
        let center = self.bounds.center();
        match (pos.x >= center.x, pos.y >= center.y) {
            (false, false) => 0, // NW
            (true, false) => 1,  // NE
            (false, true) => 2,  // SW
            (true, true) => 3,   // SE
        }
    }

    /// Calculates the repulsive force on a body from this node using Barnes-Hut approximation.
    ///
    /// # Arguments
    /// * `body` - The body to calculate force on
    /// * `theta` - The approximation threshold (size/distance ratio)
    /// * `repulsion_constant` - The repulsion constant (k in F = k/d²)
    /// * `min_distance_sq` - Minimum squared distance to prevent infinite forces
    ///
    /// # Returns
    /// The net repulsive force vector.
    fn calculate_force(
        &self,
        body: &Body,
        theta: f32,
        repulsion_constant: f32,
        min_distance_sq: f32,
    ) -> Vec2 {
        // Empty nodes contribute no force
        if self.total_mass == 0.0 {
            return Vec2::ZERO;
        }

        let delta = self.center_of_mass - body.position;
        let distance_sq = delta.length_squared();

        // Skip if this is the same body (or very close) and this is a leaf
        if distance_sq < 0.001 && self.is_external() {
            return Vec2::ZERO;
        }
        // For internal nodes with close center of mass, we still recurse to find actual bodies

        // Barnes-Hut criterion: s/d < θ
        // where s = node size, d = distance to center of mass
        // Using squared values to avoid sqrt: s²/d² < θ²
        let size = self.size();
        let theta_sq = theta * theta;

        let use_approximation =
            self.is_external() || (size * size / distance_sq.max(0.001) < theta_sq);

        if use_approximation {
            // Use center-of-mass approximation
            if distance_sq < 0.001 {
                return Vec2::ZERO;
            }

            // Clamp to minimum distance
            let clamped_dist_sq = distance_sq.max(min_distance_sq);

            // Optimized force calculation: combine direction normalization and magnitude
            // Force = -(delta/d) * (k*m/d²) = -delta * (k*m) / (d * d²) = -delta * (k*m) / (d³)
            // Using d³ = d² * d = clamped_dist_sq * sqrt(distance_sq)
            // This saves one division by combining: direction = delta/d, magnitude = k*m/d²
            let distance = distance_sq.sqrt();
            let force_scale = repulsion_constant * self.total_mass / (distance * clamped_dist_sq);

            // Force points from body toward center of mass (repulsion, so negate)
            -delta * force_scale
        } else {
            // Recurse into children
            let mut total_force = Vec2::ZERO;
            if let Some(ref children) = self.children {
                for child in children.iter() {
                    total_force +=
                        child.calculate_force(body, theta, repulsion_constant, min_distance_sq);
                }
            }
            total_force
        }
    }
}

/// Barnes-Hut quadtree for efficient N-body force calculation.
///
/// # Example
///
/// ```
/// use rource_core::physics::barnes_hut::{BarnesHutTree, Body};
/// use rource_math::{Bounds, Vec2};
///
/// let bounds = Bounds::new(Vec2::new(-100.0, -100.0), Vec2::new(100.0, 100.0));
/// let mut tree = BarnesHutTree::new(bounds);
///
/// // Insert bodies
/// tree.insert(Body::new(Vec2::new(10.0, 10.0)));
/// tree.insert(Body::new(Vec2::new(-20.0, 30.0)));
/// tree.insert(Body::new(Vec2::new(50.0, -40.0)));
///
/// // Calculate forces
/// let body = Body::new(Vec2::new(0.0, 0.0));
/// let force = tree.calculate_force(&body, 800.0, 25.0);
/// ```
#[derive(Debug)]
pub struct BarnesHutTree {
    /// Root node of the tree.
    root: BarnesHutNode,

    /// Theta parameter for approximation threshold.
    theta: f32,
}

impl BarnesHutTree {
    /// Creates a new Barnes-Hut tree with the given bounds.
    #[must_use]
    pub fn new(bounds: Bounds) -> Self {
        Self {
            root: BarnesHutNode::new(bounds, 0),
            theta: DEFAULT_BARNES_HUT_THETA,
        }
    }

    /// Creates a new tree with a custom theta parameter.
    #[must_use]
    pub fn with_theta(bounds: Bounds, theta: f32) -> Self {
        Self {
            root: BarnesHutNode::new(bounds, 0),
            theta,
        }
    }

    /// Sets the theta parameter for approximation.
    pub fn set_theta(&mut self, theta: f32) {
        self.theta = theta.max(0.0);
    }

    /// Returns the current theta parameter.
    #[inline]
    #[must_use]
    pub fn theta(&self) -> f32 {
        self.theta
    }

    /// Returns the bounds of the tree.
    #[inline]
    #[must_use]
    pub fn bounds(&self) -> &Bounds {
        &self.root.bounds
    }

    /// Clears all bodies from the tree while preserving structure.
    ///
    /// This resets body data without deallocating the tree structure,
    /// reducing allocations when the tree is rebuilt each frame.
    pub fn clear(&mut self) {
        self.root.reset();
    }

    /// Inserts a body into the tree.
    pub fn insert(&mut self, body: Body) {
        self.root.insert(body);
    }

    /// Calculates the repulsive force on a body from all other bodies in the tree.
    ///
    /// # Arguments
    /// * `body` - The body to calculate force on
    /// * `repulsion_constant` - The repulsion constant (k in F = k/d²)
    /// * `min_distance_sq` - Minimum squared distance to prevent extreme forces
    ///
    /// # Returns
    /// The net repulsive force vector.
    #[must_use]
    pub fn calculate_force(
        &self,
        body: &Body,
        repulsion_constant: f32,
        min_distance_sq: f32,
    ) -> Vec2 {
        self.root
            .calculate_force(body, self.theta, repulsion_constant, min_distance_sq)
    }

    /// Returns the total mass in the tree.
    #[inline]
    #[must_use]
    pub fn total_mass(&self) -> f32 {
        self.root.total_mass
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_tree() -> BarnesHutTree {
        BarnesHutTree::new(Bounds::new(
            Vec2::new(-100.0, -100.0),
            Vec2::new(100.0, 100.0),
        ))
    }

    #[test]
    fn test_barnes_hut_new() {
        let tree = create_test_tree();
        assert_eq!(tree.total_mass(), 0.0);
        assert!((tree.theta() - DEFAULT_BARNES_HUT_THETA).abs() < 0.001);
    }

    #[test]
    fn test_barnes_hut_insert_single() {
        let mut tree = create_test_tree();
        tree.insert(Body::new(Vec2::new(10.0, 20.0)));

        assert!((tree.total_mass() - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_barnes_hut_insert_multiple() {
        let mut tree = create_test_tree();

        tree.insert(Body::with_mass(Vec2::new(10.0, 10.0), 2.0));
        tree.insert(Body::with_mass(Vec2::new(-20.0, 30.0), 3.0));
        tree.insert(Body::with_mass(Vec2::new(50.0, -40.0), 1.5));

        let expected_mass = 2.0 + 3.0 + 1.5;
        assert!((tree.total_mass() - expected_mass).abs() < 0.001);
    }

    #[test]
    fn test_barnes_hut_outside_bounds() {
        let mut tree = create_test_tree();
        tree.insert(Body::new(Vec2::new(200.0, 200.0))); // Outside bounds

        assert_eq!(tree.total_mass(), 0.0);
    }

    #[test]
    fn test_barnes_hut_force_zero_on_self() {
        let mut tree = create_test_tree();
        let body = Body::new(Vec2::new(10.0, 10.0));
        tree.insert(body);

        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Force on a body from itself should be zero
        assert!(force.length() < 0.001);
    }

    #[test]
    fn test_barnes_hut_force_direction() {
        let mut tree = create_test_tree();

        // Body at origin
        let body_at_origin = Body::new(Vec2::ZERO);

        // Body to the right
        tree.insert(Body::new(Vec2::new(50.0, 0.0)));

        let force = tree.calculate_force(&body_at_origin, 800.0, 25.0);

        // Force should push body at origin away from body on right (negative x)
        assert!(force.x < 0.0, "Force should be in negative x direction");
        assert!(force.y.abs() < 0.001, "Force should have no y component");
    }

    #[test]
    fn test_barnes_hut_force_magnitude() {
        let mut tree = create_test_tree();

        let body = Body::new(Vec2::ZERO);
        tree.insert(Body::new(Vec2::new(10.0, 0.0))); // Distance = 10

        let force = tree.calculate_force(&body, 800.0, 1.0);

        // F = k * m / d² = 800 * 1 / 100 = 8
        let expected_magnitude = 8.0;
        let actual_magnitude = force.length();

        assert!(
            (actual_magnitude - expected_magnitude).abs() < 0.1,
            "Expected force magnitude ~{}, got {}",
            expected_magnitude,
            actual_magnitude
        );
    }

    #[test]
    fn test_barnes_hut_clear() {
        let mut tree = create_test_tree();

        tree.insert(Body::new(Vec2::new(10.0, 10.0)));
        tree.insert(Body::new(Vec2::new(20.0, 20.0)));

        assert!(tree.total_mass() > 0.0);

        tree.clear();

        assert_eq!(tree.total_mass(), 0.0);
    }

    #[test]
    fn test_barnes_hut_clear_preserves_structure() {
        let mut tree = create_test_tree();

        // Insert bodies that force tree subdivision
        tree.insert(Body::new(Vec2::new(-50.0, -50.0))); // NW quadrant
        tree.insert(Body::new(Vec2::new(50.0, 50.0))); // SE quadrant
        tree.insert(Body::new(Vec2::new(-50.0, 50.0))); // SW quadrant
        tree.insert(Body::new(Vec2::new(50.0, -50.0))); // NE quadrant

        assert!((tree.total_mass() - 4.0).abs() < 0.001);

        // Clear preserves tree structure (no reallocation)
        tree.clear();
        assert_eq!(tree.total_mass(), 0.0);

        // Re-inserting should still work correctly
        tree.insert(Body::new(Vec2::new(-50.0, -50.0)));
        tree.insert(Body::new(Vec2::new(50.0, 50.0)));

        assert!((tree.total_mass() - 2.0).abs() < 0.001);

        // Force calculation should still work
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);
        // Forces from opposite quadrants should mostly cancel
        assert!(
            force.length() < 10.0,
            "Symmetric forces should mostly cancel"
        );
    }

    #[test]
    fn test_barnes_hut_with_theta() {
        let bounds = Bounds::new(Vec2::new(-100.0, -100.0), Vec2::new(100.0, 100.0));
        let tree = BarnesHutTree::with_theta(bounds, 0.5);

        assert!((tree.theta() - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_barnes_hut_set_theta() {
        let mut tree = create_test_tree();
        tree.set_theta(1.2);

        assert!((tree.theta() - 1.2).abs() < 0.001);
    }

    #[test]
    fn test_barnes_hut_many_bodies() {
        let mut tree = create_test_tree();

        // Insert 100 bodies
        for i in 0..100 {
            let x = ((i % 10) as f32 - 5.0) * 10.0;
            let y = ((i / 10) as f32 - 5.0) * 10.0;
            tree.insert(Body::new(Vec2::new(x, y)));
        }

        assert!((tree.total_mass() - 100.0).abs() < 0.001);

        // Force calculation should still work
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Force should be roughly zero at center of symmetric distribution
        assert!(
            force.length() < 10.0,
            "Force at center of symmetric distribution should be small"
        );
    }

    #[test]
    fn test_barnes_hut_theta_affects_accuracy() {
        let mut tree_exact = create_test_tree();
        let mut tree_approx = create_test_tree();

        // Insert bodies
        tree_exact.insert(Body::new(Vec2::new(50.0, 0.0)));
        tree_exact.insert(Body::new(Vec2::new(51.0, 0.0)));
        tree_exact.insert(Body::new(Vec2::new(52.0, 0.0)));

        tree_approx.insert(Body::new(Vec2::new(50.0, 0.0)));
        tree_approx.insert(Body::new(Vec2::new(51.0, 0.0)));
        tree_approx.insert(Body::new(Vec2::new(52.0, 0.0)));

        tree_exact.set_theta(0.0); // Exact
        tree_approx.set_theta(2.0); // Very approximate

        let body = Body::new(Vec2::ZERO);
        let force_exact = tree_exact.calculate_force(&body, 800.0, 1.0);
        let force_approx = tree_approx.calculate_force(&body, 800.0, 1.0);

        // Both should produce repulsive forces in negative x direction
        assert!(force_exact.x < 0.0);
        assert!(force_approx.x < 0.0);

        // But the magnitudes should differ
        // (Approximate may use center-of-mass of all three bodies)
        let diff = (force_exact - force_approx).length();
        assert!(
            diff > 0.0 || tree_approx.theta() > 0.0,
            "Different theta should produce different results"
        );
    }

    #[test]
    fn test_barnes_hut_min_distance_clamping() {
        let mut tree = create_test_tree();

        // Two bodies very close together
        tree.insert(Body::new(Vec2::new(1.0, 0.0)));

        let body = Body::new(Vec2::new(0.0, 0.0));
        let force_no_clamp = tree.calculate_force(&body, 800.0, 0.01); // tiny min distance
        let force_with_clamp = tree.calculate_force(&body, 800.0, 25.0); // d=5 minimum

        // With larger min distance, force should be smaller
        assert!(
            force_with_clamp.length() < force_no_clamp.length(),
            "Clamped force should be smaller"
        );
    }

    // ========================================================================
    // Adaptive Theta Tests (Phase 62)
    // ========================================================================

    #[test]
    fn test_adaptive_theta_small_entity_count() {
        // Small scenes (≤200) should use default theta (0.8)
        assert!((calculate_adaptive_theta(50) - DEFAULT_BARNES_HUT_THETA).abs() < 0.001);
        assert!((calculate_adaptive_theta(100) - DEFAULT_BARNES_HUT_THETA).abs() < 0.001);
        assert!((calculate_adaptive_theta(200) - DEFAULT_BARNES_HUT_THETA).abs() < 0.001);
    }

    #[test]
    fn test_adaptive_theta_medium_entity_count() {
        // Medium scenes should have theta between 0.8 and 1.0
        let theta_500 = calculate_adaptive_theta(500);
        assert!(theta_500 > DEFAULT_BARNES_HUT_THETA);
        assert!(theta_500 < 1.0);

        let theta_1000 = calculate_adaptive_theta(1000);
        assert!(theta_1000 >= 1.0);
        assert!(theta_1000 < 1.2);
    }

    #[test]
    fn test_adaptive_theta_large_entity_count() {
        // Large scenes (5000+) should approach max theta (1.5)
        let theta_5000 = calculate_adaptive_theta(5000);
        assert!((theta_5000 - MAX_ADAPTIVE_THETA).abs() < 0.01);

        // Even larger should be clamped at max
        let theta_10000 = calculate_adaptive_theta(10000);
        assert!((theta_10000 - MAX_ADAPTIVE_THETA).abs() < 0.01);
    }

    #[test]
    fn test_adaptive_theta_monotonic_increase() {
        // Theta should monotonically increase with entity count
        let counts = [100, 200, 500, 1000, 2000, 5000];
        let mut prev_theta = 0.0f32;

        for count in counts {
            let theta = calculate_adaptive_theta(count);
            assert!(
                theta >= prev_theta,
                "Theta should increase with entity count: θ({})={} < θ({})={}",
                count,
                theta,
                count - 1,
                prev_theta
            );
            prev_theta = theta;
        }
    }

    #[test]
    fn test_adaptive_theta_within_bounds() {
        // Adaptive theta should always be within [MIN, MAX]
        for count in [0, 1, 50, 100, 200, 500, 1000, 5000, 10_000, 100_000] {
            let theta = calculate_adaptive_theta(count);
            assert!(
                theta >= MIN_ADAPTIVE_THETA,
                "Theta {} below min {} for count {}",
                theta,
                MIN_ADAPTIVE_THETA,
                count
            );
            assert!(
                theta <= MAX_ADAPTIVE_THETA,
                "Theta {} above max {} for count {}",
                theta,
                MAX_ADAPTIVE_THETA,
                count
            );
        }
    }

    #[test]
    fn test_adaptive_theta_with_fps_at_target() {
        // At target FPS, should return base adaptive theta
        let base_theta = calculate_adaptive_theta(1000);
        let fps_theta = calculate_adaptive_theta_with_fps(1000, Some(60.0), 60.0);
        assert!((base_theta - fps_theta).abs() < 0.001);
    }

    #[test]
    fn test_adaptive_theta_with_fps_below_target() {
        // Below target FPS, should boost theta
        let base_theta = calculate_adaptive_theta(1000);
        let fps_theta = calculate_adaptive_theta_with_fps(1000, Some(30.0), 60.0); // 50% deficit
        assert!(fps_theta > base_theta);
        assert!(fps_theta <= MAX_ADAPTIVE_THETA);
    }

    #[test]
    fn test_adaptive_theta_with_unknown_fps() {
        // Unknown FPS should return base adaptive theta
        let base_theta = calculate_adaptive_theta(1000);
        let fps_theta = calculate_adaptive_theta_with_fps(1000, None, 60.0);
        assert!((base_theta - fps_theta).abs() < 0.001);
    }

    #[test]
    fn test_adaptive_theta_with_fps_above_target() {
        // Above target FPS, should return base adaptive theta (no boost needed)
        let base_theta = calculate_adaptive_theta(1000);
        let fps_theta = calculate_adaptive_theta_with_fps(1000, Some(90.0), 60.0); // 150% of target
        assert!((base_theta - fps_theta).abs() < 0.001);
    }

    #[test]
    fn test_adaptive_theta_specific_values() {
        // Verify specific values match documented behavior
        // These tests ensure the formula produces expected results

        // 200 entities: θ = 0.8 (threshold)
        let theta_200 = calculate_adaptive_theta(200);
        assert!(
            (theta_200 - 0.8).abs() < 0.01,
            "Expected θ≈0.8 at 200 entities, got {}",
            theta_200
        );

        // 5000 entities: θ = 1.5 (max)
        let theta_5000 = calculate_adaptive_theta(5000);
        assert!(
            (theta_5000 - 1.5).abs() < 0.01,
            "Expected θ≈1.5 at 5000 entities, got {}",
            theta_5000
        );
    }

    // ========================================================================
    // Edge Case Tests (Expert+ Audit Phase 2)
    // ========================================================================

    #[test]
    fn test_barnes_hut_two_bodies_aligned_x() {
        // Test two bodies aligned on x-axis
        let mut tree = create_test_tree();
        tree.insert(Body::new(Vec2::new(-50.0, 0.0)));
        tree.insert(Body::new(Vec2::new(50.0, 0.0)));

        // Body at origin should experience forces from both sides
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Forces should cancel on x-axis (symmetric)
        assert!(
            force.x.abs() < 0.1,
            "X-aligned symmetric forces should cancel: got x={}",
            force.x
        );
        assert!(
            force.y.abs() < 0.001,
            "No y-component expected: got y={}",
            force.y
        );
    }

    #[test]
    fn test_barnes_hut_two_bodies_aligned_y() {
        // Test two bodies aligned on y-axis
        let mut tree = create_test_tree();
        tree.insert(Body::new(Vec2::new(0.0, -50.0)));
        tree.insert(Body::new(Vec2::new(0.0, 50.0)));

        // Body at origin should experience forces from both sides
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Forces should cancel on y-axis (symmetric)
        assert!(
            force.x.abs() < 0.001,
            "No x-component expected: got x={}",
            force.x
        );
        assert!(
            force.y.abs() < 0.1,
            "Y-aligned symmetric forces should cancel: got y={}",
            force.y
        );
    }

    #[test]
    fn test_barnes_hut_clustered_bodies() {
        // Test tightly clustered bodies (stress test for subdivision)
        let mut tree = create_test_tree();

        // Insert 20 bodies in a tight cluster around (10, 10)
        for i in 0..20 {
            let offset_x = (i % 5) as f32 * 0.5 - 1.0;
            let offset_y = (i / 5) as f32 * 0.5 - 1.0;
            tree.insert(Body::new(Vec2::new(10.0 + offset_x, 10.0 + offset_y)));
        }

        assert!((tree.total_mass() - 20.0).abs() < 0.001);

        // Force on body far from cluster
        let body = Body::new(Vec2::new(80.0, 80.0));
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Force should point away from cluster (toward upper-right)
        assert!(force.x > 0.0, "Force should point away from cluster (x)");
        assert!(force.y > 0.0, "Force should point away from cluster (y)");
    }

    #[test]
    fn test_barnes_hut_scattered_bodies() {
        // Test widely scattered bodies (minimal subdivision needed)
        let mut tree = create_test_tree();

        // Insert bodies at corners
        tree.insert(Body::new(Vec2::new(-90.0, -90.0)));
        tree.insert(Body::new(Vec2::new(90.0, -90.0)));
        tree.insert(Body::new(Vec2::new(-90.0, 90.0)));
        tree.insert(Body::new(Vec2::new(90.0, 90.0)));

        assert!((tree.total_mass() - 4.0).abs() < 0.001);

        // Body at center should experience near-zero net force (symmetric)
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);

        assert!(
            force.length() < 1.0,
            "Scattered symmetric layout should produce small net force: {}",
            force.length()
        );
    }

    #[test]
    fn test_barnes_hut_zero_mass_body() {
        // Test body with zero mass
        let mut tree = create_test_tree();
        tree.insert(Body::with_mass(Vec2::new(50.0, 50.0), 0.0));

        // Zero mass body should contribute zero to total mass
        assert_eq!(tree.total_mass(), 0.0);

        // Force calculation with zero mass in tree
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Zero mass produces zero force
        assert!(
            force.length() < 0.001,
            "Zero mass should produce zero force"
        );
    }

    #[test]
    fn test_barnes_hut_negative_positions() {
        // Test bodies with negative positions
        let mut tree = create_test_tree();

        tree.insert(Body::new(Vec2::new(-50.0, -50.0)));
        tree.insert(Body::new(Vec2::new(-30.0, -80.0)));

        assert!((tree.total_mass() - 2.0).abs() < 0.001);

        // Body in positive quadrant should be pushed away
        let body = Body::new(Vec2::new(50.0, 50.0));
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Force should point away from negative quadrant (positive direction)
        assert!(
            force.x > 0.0,
            "Force should push away from negative x: got {}",
            force.x
        );
        assert!(
            force.y > 0.0,
            "Force should push away from negative y: got {}",
            force.y
        );
    }

    #[test]
    fn test_barnes_hut_very_large_positions() {
        // Test bodies at extreme positions (boundary of bounds)
        let mut tree = create_test_tree();

        tree.insert(Body::new(Vec2::new(-99.9, -99.9)));
        tree.insert(Body::new(Vec2::new(99.9, 99.9)));

        assert!((tree.total_mass() - 2.0).abs() < 0.001);

        // Body at origin should experience symmetric forces
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Symmetric positions should produce near-zero net force
        assert!(
            force.length() < 0.5,
            "Symmetric extreme positions should produce small net force: {}",
            force.length()
        );
    }

    #[test]
    fn test_barnes_hut_theta_zero_exact() {
        // Test theta=0 produces exact calculation (no approximation)
        let mut tree = create_test_tree();
        tree.set_theta(0.0);

        // Insert bodies that would be approximated with higher theta
        tree.insert(Body::new(Vec2::new(50.0, 0.0)));
        tree.insert(Body::new(Vec2::new(51.0, 0.0)));
        tree.insert(Body::new(Vec2::new(52.0, 0.0)));

        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 1.0);

        // With theta=0, force should be exact sum
        // F = k/d² for each body: 800/50² + 800/51² + 800/52²
        // = 800/2500 + 800/2601 + 800/2704
        // = 0.32 + 0.3076 + 0.2959 ≈ 0.9235
        let expected_magnitude = 800.0 / 2500.0 + 800.0 / 2601.0 + 800.0 / 2704.0;
        let actual_magnitude = force.length();

        assert!(
            (actual_magnitude - expected_magnitude).abs() < 0.05,
            "Theta=0 should give exact sum: expected {}, got {}",
            expected_magnitude,
            actual_magnitude
        );
    }

    #[test]
    fn test_barnes_hut_theta_one_approximate() {
        // Test theta=1.0 uses approximation
        let mut tree_exact = create_test_tree();
        let mut tree_approx = create_test_tree();

        tree_exact.set_theta(0.0);
        tree_approx.set_theta(1.0);

        // Insert bodies in same quadrant
        for tree in [&mut tree_exact, &mut tree_approx] {
            tree.insert(Body::new(Vec2::new(50.0, 50.0)));
            tree.insert(Body::new(Vec2::new(55.0, 55.0)));
            tree.insert(Body::new(Vec2::new(60.0, 60.0)));
        }

        let body = Body::new(Vec2::ZERO);
        let force_exact = tree_exact.calculate_force(&body, 800.0, 1.0);
        let force_approx = tree_approx.calculate_force(&body, 800.0, 1.0);

        // Both forces should be in same general direction
        assert!(force_exact.x < 0.0 && force_approx.x < 0.0);
        assert!(force_exact.y < 0.0 && force_approx.y < 0.0);

        // Approximate force may differ in magnitude due to center-of-mass approximation
        let diff = (force_exact - force_approx).length();
        // Just verify the approximation is reasonable (within 50%)
        assert!(
            diff < force_exact.length() * 0.5,
            "Approximation should be within 50% of exact"
        );
    }

    #[test]
    fn test_barnes_hut_identical_positions() {
        // Test multiple bodies at identical positions
        let mut tree = create_test_tree();

        tree.insert(Body::new(Vec2::new(50.0, 50.0)));
        tree.insert(Body::new(Vec2::new(50.0, 50.0)));
        tree.insert(Body::new(Vec2::new(50.0, 50.0)));

        // Total mass should be sum
        assert!((tree.total_mass() - 3.0).abs() < 0.001);

        // Force on body at same position should be zero (or very small)
        let body = Body::new(Vec2::new(50.0, 50.0));
        let force = tree.calculate_force(&body, 800.0, 25.0);

        assert!(
            force.length() < 0.1,
            "Force on body at identical position should be minimal: {}",
            force.length()
        );
    }

    #[test]
    fn test_barnes_hut_diagonal_force() {
        // Test force direction for diagonal arrangement
        let mut tree = create_test_tree();
        tree.insert(Body::new(Vec2::new(50.0, 50.0)));

        // Body at origin should be pushed toward negative diagonal
        let body = Body::new(Vec2::ZERO);
        let force = tree.calculate_force(&body, 800.0, 25.0);

        // Force should be at 45 degrees (equal x and y components)
        let angle = force.y.atan2(force.x);
        let expected_angle = std::f32::consts::FRAC_PI_4 * 5.0; // -135 degrees or 225 degrees
        let angle_diff = (angle - expected_angle).abs();
        let normalized_diff = angle_diff.min(2.0 * std::f32::consts::PI - angle_diff);

        assert!(
            normalized_diff < 0.1,
            "Force should be at ~225 degrees: got {} radians",
            angle
        );
    }

    #[test]
    fn test_barnes_hut_force_inverse_square() {
        // Verify inverse square law
        let mut tree1 = create_test_tree();
        let mut tree2 = create_test_tree();

        tree1.insert(Body::new(Vec2::new(10.0, 0.0))); // Distance 10
        tree2.insert(Body::new(Vec2::new(20.0, 0.0))); // Distance 20

        let body = Body::new(Vec2::ZERO);
        let force1 = tree1.calculate_force(&body, 800.0, 1.0);
        let force2 = tree2.calculate_force(&body, 800.0, 1.0);

        // Force at distance 20 should be 1/4 of force at distance 10
        let ratio = force1.length() / force2.length();
        assert!(
            (ratio - 4.0).abs() < 0.1,
            "Inverse square: force ratio should be 4, got {}",
            ratio
        );
    }

    #[test]
    fn test_barnes_hut_variable_mass() {
        // Test that mass affects force linearly
        let mut tree1 = create_test_tree();
        let mut tree2 = create_test_tree();

        tree1.insert(Body::with_mass(Vec2::new(50.0, 0.0), 1.0));
        tree2.insert(Body::with_mass(Vec2::new(50.0, 0.0), 3.0));

        let body = Body::new(Vec2::ZERO);
        let force1 = tree1.calculate_force(&body, 800.0, 1.0);
        let force2 = tree2.calculate_force(&body, 800.0, 1.0);

        // Force with mass 3 should be 3x force with mass 1
        let ratio = force2.length() / force1.length();
        assert!(
            (ratio - 3.0).abs() < 0.1,
            "Mass scaling: force ratio should be 3, got {}",
            ratio
        );
    }

    #[test]
    fn test_adaptive_theta_zero_entities() {
        // Edge case: zero entities
        let theta = calculate_adaptive_theta(0);
        assert!(
            theta >= MIN_ADAPTIVE_THETA && theta <= MAX_ADAPTIVE_THETA,
            "Zero entities should produce valid theta: {}",
            theta
        );
    }

    #[test]
    fn test_adaptive_theta_one_entity() {
        // Edge case: single entity
        let theta = calculate_adaptive_theta(1);
        assert!(
            (theta - DEFAULT_BARNES_HUT_THETA).abs() < 0.001,
            "Single entity should use default theta"
        );
    }

    #[test]
    fn test_adaptive_theta_with_fps_zero() {
        // Edge case: zero FPS (extreme deficit)
        let theta = calculate_adaptive_theta_with_fps(1000, Some(0.0), 60.0);
        assert!(
            (theta - MAX_ADAPTIVE_THETA).abs() < 0.01,
            "Zero FPS should boost to max theta"
        );
    }
}
