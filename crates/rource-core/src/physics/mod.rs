// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

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
//! - [`optimized`]: Micro-optimized primitives using compile-time lookup tables

pub mod barnes_hut;
pub mod force;
pub mod optimized;
pub mod spatial;

pub use barnes_hut::{
    calculate_adaptive_theta, calculate_adaptive_theta_with_fps, BarnesHutTree, Body,
    DEFAULT_BARNES_HUT_THETA, MAX_ADAPTIVE_THETA, MIN_ADAPTIVE_THETA,
};
pub use force::{ForceConfig, ForceSimulation, SimulationStats};
pub use optimized::random_push_direction;
pub use spatial::QuadTree;
