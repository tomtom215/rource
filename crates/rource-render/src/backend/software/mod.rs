// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Software rendering backend with optimized CPU primitives.
//!
//! This module provides the main `SoftwareRenderer` along with optimized
//! rendering primitives for production-quality CPU rendering.
//!
//! # Module Structure
//!
//! - `renderer`: Main [`SoftwareRenderer`] implementation
//! - [`optimized`]: Fixed-point arithmetic and lookup table optimizations
//!
//! # Production Quality
//!
//! The optimized module provides:
//! - 100% deterministic rendering (fixed-point math)
//! - Auditable lookup tables (compile-time generated)
//! - Observable metrics for profiling
//! - Comprehensive test coverage

pub mod optimized;
mod renderer;

// Re-export the main renderer
pub use renderer::SoftwareRenderer;

// Re-export optimized primitives for direct use
pub use optimized::{
    blend_pixel_fixed, blend_scanline_uniform, color_to_rgb, draw_disc_optimized,
    draw_disc_precomputed, draw_disc_simd, draw_ring_optimized, fast_sqrt_fixed, RenderMetrics,
    ScanlineBuffer, SQRT_LUT,
};
