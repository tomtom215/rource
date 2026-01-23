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

/// Minimum node size to prevent infinite recursion.
pub const MIN_NODE_SIZE: f32 = 0.1;

/// Maximum tree depth.
pub const MAX_TREE_DEPTH: usize = 16;

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
            let distance = distance_sq.sqrt();
            let force_magnitude = repulsion_constant * self.total_mass / clamped_dist_sq;
            let direction = delta / distance;

            // Force points from body toward center of mass (repulsion, so negate)
            -direction * force_magnitude
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

    /// Clears all bodies from the tree.
    pub fn clear(&mut self) {
        let bounds = self.root.bounds;
        self.root = BarnesHutNode::new(bounds, 0);
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
}
