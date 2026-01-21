//! Renderer backend abstraction for Rource WASM.
//!
//! This module provides a unified interface for rendering that can use either
//! WebGL2 (GPU-accelerated) or Software (CPU-based) rendering backends.
//!
//! The backend is selected automatically at construction time, with WebGL2
//! being preferred and Software as a fallback for maximum compatibility.

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement, ImageData, OffscreenCanvas};

use rource_render::{FontId, Renderer, SoftwareRenderer, WebGl2Renderer};

/// Checks if WebGL2 is available by testing on an offscreen canvas.
///
/// This is important because once you call `getContext()` on a canvas with one
/// context type, you cannot get a different context type from that canvas.
/// By testing on an offscreen canvas first, we don't "taint" the main canvas.
fn is_webgl2_available() -> bool {
    // First check if WebGL2RenderingContext exists in the global scope
    let window = match web_sys::window() {
        Some(w) => w,
        None => return false,
    };

    // Check if WebGL2RenderingContext is defined
    let has_webgl2_class = js_sys::Reflect::has(&window, &JsValue::from_str("WebGL2RenderingContext"))
        .unwrap_or(false);
    if !has_webgl2_class {
        return false;
    }

    // Try to actually get a WebGL2 context on an offscreen canvas
    // This catches cases where the class exists but context creation fails
    // (e.g., software rendering fallback in some browsers, or GPU blocklisted)
    let offscreen = match OffscreenCanvas::new(1, 1) {
        Ok(canvas) => canvas,
        Err(_) => return false,
    };

    offscreen
        .get_context("webgl2")
        .ok()
        .flatten()
        .is_some()
}

// ============================================================================
// Renderer Type
// ============================================================================

/// The type of renderer being used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RendererType {
    /// WebGL2 GPU-accelerated renderer.
    WebGl2,
    /// Software CPU renderer with `Canvas2D` output.
    Software,
}

impl RendererType {
    /// Returns the renderer type as a string identifier.
    ///
    /// Returns `"webgl2"` for WebGL2 renderer or `"software"` for software renderer.
    #[inline]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::WebGl2 => "webgl2",
            Self::Software => "software",
        }
    }
}

// ============================================================================
// Renderer Backend
// ============================================================================

/// Unified renderer backend that can be either WebGL2 or Software.
///
/// This enum abstracts over the two rendering backends, providing a unified
/// interface for all rendering operations. The backend is selected at
/// construction time based on browser capabilities.
///
/// # Backend Selection
///
/// When created via [`RendererBackend::new`], the backend will:
/// 1. First attempt to create a WebGL2 context
/// 2. Fall back to Software rendering with `Canvas2D` if WebGL2 is unavailable
///
/// # Performance Characteristics
///
/// - **WebGL2**: Best performance, GPU-accelerated, uses instanced rendering
/// - **Software**: Maximum compatibility, CPU-based, may be slower on complex scenes
#[allow(clippy::large_enum_variant)] // WebGl2Renderer is larger, but boxing adds complexity for little gain
pub enum RendererBackend {
    /// WebGL2 GPU-accelerated renderer.
    WebGl2(WebGl2Renderer),
    /// Software CPU renderer with `Canvas2D` output context.
    Software {
        /// The software renderer instance.
        renderer: SoftwareRenderer,
        /// Canvas 2D context for presenting frames.
        context: CanvasRenderingContext2d,
    },
}

impl RendererBackend {
    /// Creates a new renderer backend, trying WebGL2 first then falling back to Software.
    ///
    /// # Arguments
    ///
    /// * `canvas` - The HTML canvas element to render to
    ///
    /// # Returns
    ///
    /// A tuple of `(backend, renderer_type)` on success, or a `JsValue` error on failure.
    ///
    /// # Errors
    ///
    /// Returns an error if neither WebGL2 nor `Canvas2D` contexts can be obtained.
    ///
    /// # Context Selection
    ///
    /// This function first checks if WebGL2 is available using an offscreen canvas
    /// test. This is crucial because HTML5 Canvas only allows one context type per
    /// canvas - once you call `getContext("webgl2")`, you cannot later get a 2D
    /// context from that same canvas, even if the WebGL2 call failed.
    ///
    /// By testing on an offscreen canvas first, we avoid "tainting" the main canvas
    /// with a failed WebGL context attempt.
    pub fn new(canvas: &HtmlCanvasElement) -> Result<(Self, RendererType), JsValue> {
        let width = canvas.width();
        let height = canvas.height();

        // IMPORTANT: Check WebGL2 availability BEFORE touching the main canvas.
        // Once you call getContext() with one type, you cannot get a different type.
        if is_webgl2_available() {
            // WebGL2 is available, try to create the renderer on the main canvas
            if let Ok(webgl2) = WebGl2Renderer::new(canvas) {
                web_sys::console::log_1(&"Rource: Using WebGL2 renderer".into());
                return Ok((Self::WebGl2(webgl2), RendererType::WebGl2));
            }
            // WebGL2 was available but renderer creation failed (shader compilation, etc.)
            // This is rare but can happen. We can still try 2D since we haven't touched
            // the canvas yet (WebGl2Renderer::new only calls getContext if we get here).
            // Actually, WebGl2Renderer::new DOES call getContext, so if it failed,
            // the canvas is tainted. Log a warning.
            web_sys::console::warn_1(
                &"Rource: WebGL2 available but renderer init failed, canvas may be tainted".into(),
            );
        } else {
            // WebGL2 not available - go straight to software renderer without
            // ever trying WebGL on the main canvas
            web_sys::console::log_1(
                &"Rource: WebGL2 not available, using software renderer".into(),
            );
        }

        // Fall back to software rendering with 2D context
        let context = canvas
            .get_context("2d")
            .map_err(|e| JsValue::from_str(&format!("Failed to get 2D context: {e:?}")))?
            .ok_or_else(|| JsValue::from_str("Canvas 2D context not available"))?
            .dyn_into::<CanvasRenderingContext2d>()?;

        let renderer = SoftwareRenderer::new(width, height);

        Ok((Self::Software { renderer, context }, RendererType::Software))
    }

    /// Returns the width of the renderer in pixels.
    #[inline]
    pub fn width(&self) -> u32 {
        match self {
            Self::WebGl2(r) => r.width(),
            Self::Software { renderer, .. } => renderer.width(),
        }
    }

    /// Returns the height of the renderer in pixels.
    #[inline]
    pub fn height(&self) -> u32 {
        match self {
            Self::WebGl2(r) => r.height(),
            Self::Software { renderer, .. } => renderer.height(),
        }
    }

    /// Resizes the renderer to the specified dimensions.
    ///
    /// # Arguments
    ///
    /// * `width` - New width in pixels
    /// * `height` - New height in pixels
    pub fn resize(&mut self, width: u32, height: u32) {
        match self {
            Self::WebGl2(r) => r.resize(width, height),
            Self::Software { renderer, .. } => renderer.resize(width, height),
        }
    }

    /// Gets a mutable reference to the underlying [`Renderer`] trait object.
    ///
    /// This allows calling generic renderer methods without knowing the
    /// concrete backend type.
    #[inline]
    pub fn as_renderer_mut(&mut self) -> &mut dyn Renderer {
        match self {
            Self::WebGl2(r) => r,
            Self::Software { renderer, .. } => renderer,
        }
    }

    /// Presents the rendered frame to the canvas.
    ///
    /// For Software renderer, this copies the pixel buffer to the canvas via `ImageData`.
    /// For WebGL2, this is a no-op since WebGL renders directly to the canvas.
    ///
    /// Call this after `end_frame()` to display the rendered content.
    pub fn present(&self) {
        if let Self::Software { renderer, context } = self {
            let width = renderer.width();
            let height = renderer.height();
            let pixels = renderer.pixels();

            // Convert ARGB to RGBA for ImageData
            let mut rgba = vec![0u8; (width * height * 4) as usize];
            for (i, &pixel) in pixels.iter().enumerate() {
                let offset = i * 4;
                rgba[offset] = ((pixel >> 16) & 0xFF) as u8; // R
                rgba[offset + 1] = ((pixel >> 8) & 0xFF) as u8; // G
                rgba[offset + 2] = (pixel & 0xFF) as u8; // B
                rgba[offset + 3] = ((pixel >> 24) & 0xFF) as u8; // A
            }

            // Create ImageData and put it on the canvas
            if let Ok(image_data) = ImageData::new_with_u8_clamped_array_and_sh(
                wasm_bindgen::Clamped(&rgba),
                width,
                height,
            ) {
                let _ = context.put_image_data(&image_data, 0.0, 0.0);
            }
        }
        // WebGL2 renders directly to canvas, no copy needed
    }

    /// Returns true if the WebGL context is lost.
    ///
    /// This can happen when the GPU is reset, the browser tab is backgrounded
    /// for a long time, or system resources are exhausted.
    ///
    /// Software renderer always returns `false` (it never loses context).
    #[inline]
    pub fn is_context_lost(&self) -> bool {
        match self {
            Self::WebGl2(r) => r.is_context_lost(),
            Self::Software { .. } => false,
        }
    }

    /// Attempts to recover from a lost WebGL context.
    ///
    /// # Returns
    ///
    /// - `Ok(())` if recovery was successful or if context was not lost
    /// - `Err` if recovery failed
    ///
    /// For Software renderer, this always succeeds.
    pub fn recover_context(&mut self) -> Result<(), JsValue> {
        if let Self::WebGl2(ref mut renderer) = self {
            renderer
                .recover_context()
                .map_err(|e| JsValue::from_str(&format!("{e:?}")))
        } else {
            // Software renderer never loses context
            Ok(())
        }
    }

    /// Returns pixel data for screenshot (software renderer only).
    ///
    /// # Returns
    ///
    /// - `Some(&[u32])` - ARGB pixel buffer for software renderer
    /// - `None` - For WebGL2 renderer (use `canvas.toBlob()` instead)
    #[inline]
    pub fn pixels(&self) -> Option<&[u32]> {
        if let Self::Software { renderer, .. } = self {
            Some(renderer.pixels())
        } else {
            None
        }
    }

    /// Loads a font and returns its ID.
    ///
    /// # Arguments
    ///
    /// * `data` - Font file data (TTF/OTF format)
    ///
    /// # Returns
    ///
    /// The font ID if loading succeeded, `None` otherwise.
    pub fn load_font(&mut self, data: &[u8]) -> Option<FontId> {
        match self {
            Self::WebGl2(r) => r.load_font(data),
            Self::Software { renderer, .. } => renderer.load_font(data),
        }
    }

    /// Synchronizes CPU with GPU by waiting for all pending commands to complete.
    ///
    /// For WebGL2: calls `gl.finish()` to block until GPU is done.
    /// For Software: no-op (CPU rendering is inherently synchronous).
    ///
    /// **Important**: Call this ONLY when you need to read from the canvas
    /// (screenshots, exports). Do NOT call every frame as it hurts performance.
    #[inline]
    pub fn sync(&self) {
        if let Self::WebGl2(r) = self {
            r.sync();
        }
        // Software renderer is synchronous - no sync needed
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_renderer_type_as_str() {
        assert_eq!(RendererType::WebGl2.as_str(), "webgl2");
        assert_eq!(RendererType::Software.as_str(), "software");
    }

    #[test]
    fn test_renderer_type_equality() {
        assert_eq!(RendererType::WebGl2, RendererType::WebGl2);
        assert_eq!(RendererType::Software, RendererType::Software);
        assert_ne!(RendererType::WebGl2, RendererType::Software);
    }

    #[test]
    fn test_renderer_type_copy() {
        let t1 = RendererType::WebGl2;
        let t2 = t1;
        assert_eq!(t1, t2);
    }

    #[test]
    fn test_renderer_type_debug() {
        let debug_str = format!("{:?}", RendererType::WebGl2);
        assert!(debug_str.contains("WebGl2"));
    }
}
