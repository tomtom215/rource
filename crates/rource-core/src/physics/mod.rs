//! Physics simulation for the visualization.
//!
//! This module provides force-directed layout and spatial indexing
//! for the scene graph entities.
//!
//! # Modules
//!
//! - [`spatial`]: Quadtree for spatial partitioning and efficient queries
//! - [`force`]: Force-directed layout simulation

pub mod force;
pub mod spatial;

pub use force::{ForceConfig, ForceSimulation, SimulationStats};
pub use spatial::QuadTree;
