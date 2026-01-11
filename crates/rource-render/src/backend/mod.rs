//! Rendering backends.
//!
//! This module contains different rendering backend implementations:
//! - [`software`]: CPU-based software rasterizer for maximum portability
//! - [`webgl2`]: GPU-accelerated WebGL2 renderer for browser (feature-gated)
//!
//! ## Backend Selection
//!
//! For native builds, use the [`SoftwareRenderer`](software::SoftwareRenderer).
//!
//! For WASM builds, you can choose:
//! - [`SoftwareRenderer`](software::SoftwareRenderer) + `Canvas2D`: Maximum compatibility
//! - [`WebGl2Renderer`](webgl2::WebGl2Renderer): Better performance with GPU acceleration
//!
//! The WebGL2 backend requires the `webgl2` feature to be enabled.

pub mod software;

#[cfg(feature = "webgl2")]
pub mod webgl2;
