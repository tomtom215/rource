//! Rendering backends.
//!
//! This module contains different rendering backend implementations:
//! - [`software`]: CPU-based software rasterizer for maximum portability
//!
//! Future backends (feature-gated):
//! - WebGL2: GPU-accelerated browser rendering
//! - `Canvas2D`: Simple browser fallback

pub mod software;
