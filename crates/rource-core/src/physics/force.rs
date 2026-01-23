// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Force-directed layout simulation.
//!
//! This module provides a physics simulation for laying out the directory
//! tree using force-directed algorithms. Nodes repel each other to avoid
//! overlap while being attracted to their parent nodes.

use rource_math::Vec2;

use crate::scene::tree::DirNode;

/// Minimum distance between nodes to prevent division by zero.
pub const MIN_DISTANCE: f32 = 1.0;

/// Default repulsion constant between nodes.
pub const DEFAULT_REPULSION: f32 = 1000.0;

/// Default attraction constant to parent.
pub const DEFAULT_ATTRACTION: f32 = 0.05;

/// Default damping factor.
pub const DEFAULT_DAMPING: f32 = 0.9;

/// Default maximum velocity to prevent instability.
pub const MAX_VELOCITY: f32 = 500.0;

/// Configuration for the force-directed layout simulation.
#[derive(Debug, Clone, Copy)]
pub struct ForceConfig {
    /// Repulsion constant between nodes. Higher values push nodes apart more.
    pub repulsion: f32,

    /// Attraction constant to parent. Higher values pull children closer.
    pub attraction: f32,

    /// Damping factor (0.0-1.0). Applied to velocity each frame for stability.
    pub damping: f32,

    /// Minimum distance for force calculation to prevent extreme forces.
    pub min_distance: f32,

    /// Maximum velocity to prevent instability.
    pub max_velocity: f32,

    /// Whether to apply forces to the root node.
    pub anchor_root: bool,
}

impl Default for ForceConfig {
    fn default() -> Self {
        Self {
            repulsion: DEFAULT_REPULSION,
            attraction: DEFAULT_ATTRACTION,
            damping: DEFAULT_DAMPING,
            min_distance: MIN_DISTANCE,
            max_velocity: MAX_VELOCITY,
            anchor_root: true,
        }
    }
}

impl ForceConfig {
    /// Creates a new configuration with custom values.
    #[must_use]
    pub const fn new(repulsion: f32, attraction: f32, damping: f32) -> Self {
        Self {
            repulsion,
            attraction,
            damping,
            min_distance: MIN_DISTANCE,
            max_velocity: MAX_VELOCITY,
            anchor_root: true,
        }
    }

    /// Creates a configuration for a dense layout (stronger repulsion).
    #[must_use]
    pub fn dense() -> Self {
        Self {
            repulsion: 2000.0,
            attraction: 0.1,
            damping: 0.85,
            ..Self::default()
        }
    }

    /// Creates a configuration for a sparse layout (weaker repulsion).
    #[must_use]
    pub fn sparse() -> Self {
        Self {
            repulsion: 500.0,
            attraction: 0.02,
            damping: 0.95,
            ..Self::default()
        }
    }
}

/// Force-directed layout simulation.
///
/// This simulates physical forces between nodes to create a natural
/// tree layout:
/// - **Repulsion**: All nodes push each other away to prevent overlap
/// - **Attraction**: Children are pulled toward their parents
/// - **Damping**: Friction-like force that stabilizes the system
///
/// # Example
///
/// ```ignore
/// use rource_core::physics::ForceSimulation;
///
/// let mut simulation = ForceSimulation::new();
///
/// // Each frame:
/// simulation.apply(&mut dir_tree, dt);
/// ```
#[derive(Debug, Clone)]
pub struct ForceSimulation {
    /// Configuration for the simulation.
    config: ForceConfig,

    /// Whether the simulation is paused.
    paused: bool,

    /// Accumulated kinetic energy (for convergence detection).
    kinetic_energy: f32,

    /// Number of iterations performed.
    iterations: u64,
}

impl Default for ForceSimulation {
    fn default() -> Self {
        Self::new()
    }
}

impl ForceSimulation {
    /// Creates a new force simulation with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self {
            config: ForceConfig::default(),
            paused: false,
            kinetic_energy: 0.0,
            iterations: 0,
        }
    }

    /// Creates a new simulation with custom configuration.
    #[must_use]
    pub fn with_config(config: ForceConfig) -> Self {
        Self {
            config,
            paused: false,
            kinetic_energy: 0.0,
            iterations: 0,
        }
    }

    /// Returns the configuration.
    #[inline]
    #[must_use]
    pub const fn config(&self) -> &ForceConfig {
        &self.config
    }

    /// Returns a mutable reference to the configuration.
    #[inline]
    pub fn config_mut(&mut self) -> &mut ForceConfig {
        &mut self.config
    }

    /// Returns whether the simulation is paused.
    #[inline]
    #[must_use]
    pub const fn is_paused(&self) -> bool {
        self.paused
    }

    /// Pauses or resumes the simulation.
    #[inline]
    pub fn set_paused(&mut self, paused: bool) {
        self.paused = paused;
    }

    /// Returns the current kinetic energy of the system.
    ///
    /// This can be used to detect when the layout has stabilized
    /// (low kinetic energy means little movement).
    #[inline]
    #[must_use]
    pub const fn kinetic_energy(&self) -> f32 {
        self.kinetic_energy
    }

    /// Returns the number of iterations performed.
    #[inline]
    #[must_use]
    pub const fn iterations(&self) -> u64 {
        self.iterations
    }

    /// Returns true if the simulation has likely converged.
    ///
    /// This is a heuristic based on low kinetic energy.
    #[must_use]
    pub fn has_converged(&self) -> bool {
        self.kinetic_energy < 0.1
    }

    /// Resets the simulation state.
    pub fn reset(&mut self) {
        self.kinetic_energy = 0.0;
        self.iterations = 0;
    }

    /// Calculates the repulsion force between two nodes.
    ///
    /// Uses inverse square law: F = k / d²
    ///
    /// # Safety
    ///
    /// Returns `Vec2::ZERO` if `delta` has near-zero length to prevent
    /// invalid normalized vectors. Callers should check `distance > 0.001`
    /// before calling for meaningful results.
    #[must_use]
    fn repulsion_force(&self, delta: Vec2, distance: f32) -> Vec2 {
        // Guard against zero-length delta which would produce zero normalized vector
        if delta.length_squared() < 0.000_001 {
            return Vec2::ZERO;
        }
        let safe_distance = distance.max(self.config.min_distance);
        let magnitude = self.config.repulsion / (safe_distance * safe_distance);
        delta.normalized() * magnitude
    }

    /// Calculates the attraction force toward a parent.
    ///
    /// Uses linear spring: `F = k * (d - rest_length)`
    ///
    /// # Safety
    ///
    /// Returns `Vec2::ZERO` if `delta` has near-zero length or if
    /// distance is within target distance.
    #[must_use]
    fn attraction_force(&self, delta: Vec2, distance: f32, target_distance: f32) -> Vec2 {
        if distance > target_distance {
            // Guard against zero-length delta which would produce zero normalized vector
            if delta.length_squared() < 0.000_001 {
                return Vec2::ZERO;
            }
            let excess = distance - target_distance;
            delta.normalized() * excess * self.config.attraction
        } else {
            Vec2::ZERO
        }
    }

    /// Determines if two nodes should repel each other.
    ///
    /// Nodes repel if they:
    /// - Share the same parent (siblings)
    /// - Are close in tree depth
    fn should_repel(a: &DirNode, b: &DirNode) -> bool {
        // Siblings always repel
        if a.parent() == b.parent() && a.parent().is_some() {
            return true;
        }

        // Nodes close in depth repel
        let depth_diff = a.depth().abs_diff(b.depth());
        depth_diff <= 1
    }

    /// Applies forces to a slice of directory nodes.
    ///
    /// This is the main simulation step. Call this once per frame
    /// with the current delta time.
    ///
    /// # Arguments
    ///
    /// * `nodes` - Mutable slice of all directory nodes
    /// * `dt` - Delta time in seconds
    pub fn apply_to_slice(&mut self, nodes: &mut [DirNode], dt: f32) {
        if self.paused || nodes.is_empty() {
            return;
        }

        self.iterations += 1;
        let len = nodes.len();

        // Collect forces to apply (to avoid borrow issues)
        let mut forces: Vec<Vec2> = vec![Vec2::ZERO; len];

        // Calculate repulsion forces between all pairs
        for i in 0..len {
            for j in (i + 1)..len {
                if !Self::should_repel(&nodes[i], &nodes[j]) {
                    continue;
                }

                let delta = nodes[j].position() - nodes[i].position();
                let distance = delta.length();

                if distance < 0.001 {
                    // Nodes at same position, push apart randomly
                    let offset = Vec2::new((i as f32).sin() * 10.0, (j as f32).cos() * 10.0);
                    forces[i] -= offset;
                    forces[j] += offset;
                    continue;
                }

                let force = self.repulsion_force(delta, distance);

                // Apply equal and opposite forces
                forces[i] -= force;
                forces[j] += force;
            }
        }

        // Calculate attraction forces to parents
        for (i, node) in nodes.iter().enumerate() {
            if let Some(parent_pos) = node.parent_position() {
                let delta = parent_pos - node.position();
                let distance = delta.length();
                let target = node.target_distance();

                let force = self.attraction_force(delta, distance, target);
                forces[i] += force;
            }
        }

        // Apply forces and integrate
        let mut total_kinetic_energy = 0.0;

        for (i, node) in nodes.iter_mut().enumerate() {
            // Skip root if anchored
            if self.config.anchor_root && node.is_root() {
                continue;
            }

            // Apply force as acceleration (assuming unit mass)
            node.add_velocity(forces[i] * dt);

            // Clamp velocity
            let vel = node.velocity();
            let speed = vel.length();
            if speed > self.config.max_velocity {
                node.set_velocity(vel.normalized() * self.config.max_velocity);
            }

            // Track kinetic energy (for convergence)
            let speed = node.velocity().length();
            total_kinetic_energy += 0.5 * speed * speed;

            // Apply damping
            node.set_velocity(node.velocity() * self.config.damping);

            // Integrate position
            let new_pos = node.position() + node.velocity() * dt;
            node.set_position(new_pos);
        }

        self.kinetic_energy = total_kinetic_energy;
    }

    /// Applies a single force between two specific nodes.
    ///
    /// This can be used for interactive manipulation.
    #[must_use]
    pub fn calculate_force_between(&self, a: &DirNode, b: &DirNode) -> Vec2 {
        if !Self::should_repel(a, b) {
            return Vec2::ZERO;
        }

        let delta = b.position() - a.position();
        let distance = delta.length();

        if distance < 0.001 {
            return Vec2::ZERO;
        }

        self.repulsion_force(delta, distance)
    }

    /// Calculates the total force on a node from all other nodes.
    #[must_use]
    pub fn calculate_total_force(&self, node: &DirNode, all_nodes: &[DirNode]) -> Vec2 {
        let mut total_force = Vec2::ZERO;

        // Repulsion from other nodes
        for other in all_nodes {
            if other.id() == node.id() {
                continue;
            }

            let delta = other.position() - node.position();
            let distance = delta.length();

            if distance > 0.001 && Self::should_repel(node, other) {
                total_force -= self.repulsion_force(delta, distance);
            }
        }

        // Attraction to parent
        if let Some(parent_pos) = node.parent_position() {
            let delta = parent_pos - node.position();
            let distance = delta.length();
            total_force += self.attraction_force(delta, distance, node.target_distance());
        }

        total_force
    }
}

/// Result of a single simulation step for analysis.
#[derive(Debug, Clone)]
pub struct SimulationStats {
    /// Total kinetic energy in the system.
    pub kinetic_energy: f32,

    /// Maximum velocity of any node.
    pub max_velocity: f32,

    /// Average velocity across all nodes.
    pub avg_velocity: f32,

    /// Number of nodes processed.
    pub node_count: usize,
}

impl ForceSimulation {
    /// Performs a simulation step and returns statistics.
    ///
    /// This is useful for debugging and tuning the simulation.
    pub fn apply_with_stats(&mut self, nodes: &mut [DirNode], dt: f32) -> SimulationStats {
        self.apply_to_slice(nodes, dt);

        let mut max_vel = 0.0f32;
        let mut total_vel = 0.0f32;

        for node in nodes.iter() {
            let speed = node.velocity().length();
            max_vel = max_vel.max(speed);
            total_vel += speed;
        }

        let node_count = nodes.len();
        let avg_vel = if node_count > 0 {
            total_vel / node_count as f32
        } else {
            0.0
        };

        SimulationStats {
            kinetic_energy: self.kinetic_energy,
            max_velocity: max_vel,
            avg_velocity: avg_vel,
            node_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::entity::{DirId, Generation};

    fn create_test_node(index: u32, name: &str, parent: Option<DirId>) -> DirNode {
        use std::path::Path;
        let id = DirId::new(index, Generation::first());
        parent.map_or_else(
            || DirNode::new_root(id),
            |parent_id| DirNode::new(id, name, parent_id, Path::new("")),
        )
    }

    #[test]
    fn test_force_config_default() {
        let config = ForceConfig::default();

        assert_eq!(config.repulsion, DEFAULT_REPULSION);
        assert_eq!(config.attraction, DEFAULT_ATTRACTION);
        assert_eq!(config.damping, DEFAULT_DAMPING);
        assert!(config.anchor_root);
    }

    #[test]
    fn test_force_config_presets() {
        let dense = ForceConfig::dense();
        let sparse = ForceConfig::sparse();

        // Dense should have stronger repulsion
        assert!(dense.repulsion > sparse.repulsion);

        // Dense should have stronger attraction
        assert!(dense.attraction > sparse.attraction);
    }

    #[test]
    fn test_force_simulation_new() {
        let sim = ForceSimulation::new();

        assert!(!sim.is_paused());
        assert_eq!(sim.kinetic_energy(), 0.0);
        assert_eq!(sim.iterations(), 0);
    }

    #[test]
    fn test_force_simulation_pause() {
        let mut sim = ForceSimulation::new();

        sim.set_paused(true);
        assert!(sim.is_paused());

        sim.set_paused(false);
        assert!(!sim.is_paused());
    }

    #[test]
    fn test_force_simulation_reset() {
        let mut sim = ForceSimulation::new();
        sim.kinetic_energy = 100.0;
        sim.iterations = 1000;

        sim.reset();

        assert_eq!(sim.kinetic_energy(), 0.0);
        assert_eq!(sim.iterations(), 0);
    }

    #[test]
    fn test_repulsion_force() {
        let sim = ForceSimulation::new();

        // Force should be in opposite direction of delta
        let delta = Vec2::new(10.0, 0.0);
        let force = sim.repulsion_force(delta, 10.0);

        // Should push in positive x direction (away from origin)
        assert!(force.x > 0.0);
        assert!((force.y).abs() < 0.001);
    }

    #[test]
    fn test_repulsion_force_inverse_square() {
        let sim = ForceSimulation::new();

        let delta = Vec2::new(1.0, 0.0);
        let force_near = sim.repulsion_force(delta, 10.0);
        let force_far = sim.repulsion_force(delta, 20.0);

        // Force at twice the distance should be 1/4 the magnitude
        let ratio = force_near.length() / force_far.length();
        assert!((ratio - 4.0).abs() < 0.1);
    }

    #[test]
    fn test_attraction_force() {
        let sim = ForceSimulation::new();

        // Node beyond target distance should be attracted
        let delta = Vec2::new(100.0, 0.0);
        let force = sim.attraction_force(delta, 100.0, 50.0);

        // Should pull toward parent (positive x)
        assert!(force.x > 0.0);
        assert!((force.y).abs() < 0.001);
    }

    #[test]
    fn test_attraction_force_within_target() {
        let sim = ForceSimulation::new();

        // Node within target distance should not be attracted
        let delta = Vec2::new(30.0, 0.0);
        let force = sim.attraction_force(delta, 30.0, 50.0);

        assert_eq!(force, Vec2::ZERO);
    }

    #[test]
    fn test_should_repel_siblings() {
        let root_id = DirId::new(0, Generation::first());
        let mut node1 = create_test_node(1, "a", Some(root_id));
        let mut node2 = create_test_node(2, "b", Some(root_id));

        node1.set_depth(1);
        node2.set_depth(1);

        assert!(ForceSimulation::should_repel(&node1, &node2));
    }

    #[test]
    fn test_should_repel_close_depth() {
        let root_id = DirId::new(0, Generation::first());
        let parent_id = DirId::new(1, Generation::first());

        let mut node1 = create_test_node(1, "a", Some(root_id));
        let mut node2 = create_test_node(2, "b", Some(parent_id));

        node1.set_depth(1);
        node2.set_depth(2);

        // Different parents but close in depth
        assert!(ForceSimulation::should_repel(&node1, &node2));
    }

    #[test]
    fn test_apply_to_slice_empty() {
        let mut sim = ForceSimulation::new();
        let mut nodes: Vec<DirNode> = vec![];

        sim.apply_to_slice(&mut nodes, 0.016);

        assert_eq!(sim.kinetic_energy(), 0.0);
    }

    #[test]
    fn test_apply_to_slice_single() {
        let mut sim = ForceSimulation::new();
        let mut nodes = vec![create_test_node(0, "", None)];

        sim.apply_to_slice(&mut nodes, 0.016);

        // Root should not move when anchored
        assert_eq!(nodes[0].position(), Vec2::ZERO);
    }

    #[test]
    fn test_apply_to_slice_repulsion() {
        let mut sim = ForceSimulation::new();
        sim.config_mut().anchor_root = false;

        let root_id = DirId::new(0, Generation::first());

        let root = create_test_node(0, "", None);
        let mut child1 = create_test_node(1, "a", Some(root_id));
        let mut child2 = create_test_node(2, "b", Some(root_id));

        // Position children at same spot
        child1.set_position(Vec2::new(10.0, 0.0));
        child2.set_position(Vec2::new(10.0, 0.0));
        child1.set_depth(1);
        child2.set_depth(1);

        let mut nodes = vec![root, child1, child2];

        // Run simulation
        sim.apply_to_slice(&mut nodes, 0.1);

        // Children should have moved apart
        let dist = (nodes[1].position() - nodes[2].position()).length();
        assert!(dist > 0.0);
    }

    #[test]
    fn test_simulation_convergence() {
        let mut sim = ForceSimulation::new();
        sim.config_mut().anchor_root = false;

        let root_id = DirId::new(0, Generation::first());

        let mut nodes = vec![
            create_test_node(0, "", None),
            create_test_node(1, "a", Some(root_id)),
            create_test_node(2, "b", Some(root_id)),
        ];

        nodes[1].set_position(Vec2::new(100.0, 0.0));
        nodes[1].set_depth(1);
        nodes[2].set_position(Vec2::new(-100.0, 0.0));
        nodes[2].set_depth(1);

        // Run many iterations
        for _ in 0..1000 {
            sim.apply_to_slice(&mut nodes, 0.016);
        }

        // Should eventually converge (low kinetic energy)
        assert!(sim.kinetic_energy() < 100.0);
    }

    #[test]
    fn test_paused_simulation() {
        let mut sim = ForceSimulation::new();
        sim.set_paused(true);

        let mut nodes = vec![create_test_node(0, "", None)];
        nodes[0].set_velocity(Vec2::new(100.0, 0.0));
        let initial_pos = nodes[0].position();

        sim.apply_to_slice(&mut nodes, 1.0);

        // Nothing should change when paused
        assert_eq!(nodes[0].position(), initial_pos);
    }

    #[test]
    fn test_simulation_stats() {
        let mut sim = ForceSimulation::new();
        sim.config_mut().anchor_root = false;

        let root_id = DirId::new(0, Generation::first());

        let mut nodes = vec![
            create_test_node(0, "", None),
            create_test_node(1, "a", Some(root_id)),
        ];
        nodes[1].set_position(Vec2::new(10.0, 0.0));
        nodes[1].set_velocity(Vec2::new(50.0, 0.0));
        nodes[1].set_depth(1);

        let stats = sim.apply_with_stats(&mut nodes, 0.016);

        assert_eq!(stats.node_count, 2);
        assert!(stats.max_velocity >= 0.0);
        assert!(stats.avg_velocity >= 0.0);
    }

    #[test]
    fn test_calculate_total_force() {
        let sim = ForceSimulation::new();

        let root_id = DirId::new(0, Generation::first());

        let mut nodes = vec![
            create_test_node(0, "", None),
            create_test_node(1, "a", Some(root_id)),
            create_test_node(2, "b", Some(root_id)),
        ];

        // Set positions close enough to cause repulsion
        nodes[0].set_position(Vec2::ZERO);
        nodes[0].set_depth(0);
        nodes[1].set_position(Vec2::new(50.0, 0.0));
        nodes[1].set_depth(1);
        nodes[2].set_position(Vec2::new(52.0, 0.0)); // Very close to node 1
        nodes[2].set_depth(1);

        let force = sim.calculate_total_force(&nodes[1], &nodes);

        // Should have some force due to repulsion from nearby sibling
        // Force magnitude depends on distance - closer nodes have stronger repulsion
        assert!(
            force.length() > 0.0,
            "Expected non-zero force, got {force:?}"
        );
    }
}
