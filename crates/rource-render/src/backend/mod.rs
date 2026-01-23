//! Rendering backends.
//!
//! This module contains different rendering backend implementations:
//! - [`software`]: CPU-based software rasterizer for maximum portability
//! - `webgl2`: GPU-accelerated WebGL2 renderer for browser (feature-gated)
//! - [`wgpu`]: Cross-platform GPU-accelerated renderer using wgpu (feature-gated)
//!
//! ## Backend Selection
//!
//! Backend priority for maximum performance (recommended):
//! 1. **wgpu** (WebGPU/Vulkan/Metal/DX12) - Best performance, cross-platform
//! 2. **webgl2** (WebGL2) - Good performance, browser fallback
//! 3. **software** (CPU) - Maximum compatibility, slowest
//!
//! ### Native Builds
//!
//! For native builds, the recommended hierarchy is:
//! - [`WgpuRenderer`](wgpu::WgpuRenderer): Best performance with native GPU APIs
//! - [`SoftwareRenderer`](software::SoftwareRenderer): Fallback for compatibility
//!
//! ### WASM Builds
//!
//! For WASM builds, the recommended hierarchy is:
//! - [`WgpuRenderer`](wgpu::WgpuRenderer): WebGPU for modern browsers
//! - `WebGl2Renderer`: WebGL2 fallback for older browsers (feature-gated)
//! - [`SoftwareRenderer`](software::SoftwareRenderer): `Canvas2D` for maximum compatibility
//!
//! ## Feature Flags
//!
//! - `wgpu`: Enables the wgpu-based renderer (recommended)
//! - `webgl2`: Enables the WebGL2-based renderer (browser fallback)
//!
//! ## Example: Backend Selection
//!
//! ```ignore
//! #[cfg(feature = "wgpu")]
//! type PreferredRenderer = rource_render::backend::wgpu::WgpuRenderer;
//!
//! #[cfg(all(feature = "webgl2", not(feature = "wgpu")))]
//! type PreferredRenderer = rource_render::backend::webgl2::WebGl2Renderer;
//!
//! #[cfg(not(any(feature = "wgpu", feature = "webgl2")))]
//! type PreferredRenderer = rource_render::backend::software::SoftwareRenderer;
//! ```

pub mod icons;
pub mod software;

#[cfg(feature = "webgl2")]
pub mod webgl2;

#[cfg(feature = "wgpu")]
pub mod wgpu;
