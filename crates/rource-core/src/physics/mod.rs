//! Physics simulation for the visualization.
//!
//! This module provides force-directed layout and spatial indexing
//! for the scene graph entities.
//!
//! # Modules
//!
//! - [`spatial`]: Quadtree for spatial partitioning and efficient queries
//! - [`force`]: Force-directed layout simulation
//! - [`barnes_hut`]: Barnes-Hut algorithm for O(n log n) force calculations

pub mod barnes_hut;
pub mod force;
pub mod spatial;

pub use barnes_hut::{BarnesHutTree, Body, DEFAULT_BARNES_HUT_THETA};
pub use force::{ForceConfig, ForceSimulation, SimulationStats};
pub use spatial::QuadTree;
