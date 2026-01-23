//! Renderer backend abstraction for Rource WASM.
//!
//! This module provides a unified interface for rendering that can use
//! wgpu (WebGPU), WebGL2, or Software (CPU-based) rendering backends.
//!
//! The backend is selected automatically at construction time, with wgpu
//! being preferred (when WebGPU is available), then WebGL2, and finally
//! Software as a fallback for maximum compatibility.
//!
//! ## Backend Selection Priority
//!
//! 1. **wgpu (WebGPU)** - Best performance with modern GPU APIs
//! 2. **WebGL2** - Good performance, widely supported
//! 3. **Software** - Maximum compatibility, CPU-based

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen_futures::JsFuture;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement, ImageData, OffscreenCanvas};

use rource_render::{FontId, Renderer, SoftwareRenderer, WebGl2Renderer};

#[cfg(target_arch = "wasm32")]
use rource_render::WgpuRenderer;

/// Checks if WebGPU is available in the browser.
///
/// WebGPU is a modern graphics API that provides lower overhead and better
/// performance than WebGL. It's supported in Chrome 113+, Edge 113+, and
/// Firefox 128+ (behind flag).
///
/// Returns `true` if `navigator.gpu` exists and is available.
#[cfg(target_arch = "wasm32")]
fn is_webgpu_available() -> bool {
    let Some(window) = web_sys::window() else {
        return false;
    };

    let Some(navigator) = window.navigator().dyn_into::<web_sys::Navigator>().ok() else {
        return false;
    };

    // Check if navigator.gpu exists
    js_sys::Reflect::has(&navigator, &JsValue::from_str("gpu")).unwrap_or(false)
}

/// Asynchronously checks if WebGPU can actually be used (adapter available).
///
/// This goes beyond `is_webgpu_available()` by actually requesting an adapter,
/// which may fail even if `navigator.gpu` exists (e.g., no compatible GPU).
///
/// # Note on Send
///
/// This future is not `Send` because JavaScript/browser APIs are single-threaded.
/// This is expected and safe for WASM usage.
#[cfg(target_arch = "wasm32")]
#[allow(clippy::future_not_send)]
async fn can_use_webgpu() -> bool {
    let Some(window) = web_sys::window() else {
        return false;
    };

    let Some(navigator) = window.navigator().dyn_into::<web_sys::Navigator>().ok() else {
        return false;
    };

    // Get navigator.gpu
    let Ok(gpu_value) = js_sys::Reflect::get(&navigator, &JsValue::from_str("gpu")) else {
        return false;
    };

    if gpu_value.is_undefined() || gpu_value.is_null() {
        return false;
    }

    // Try to request an adapter
    let Ok(request_adapter) =
        js_sys::Reflect::get(&gpu_value, &JsValue::from_str("requestAdapter"))
    else {
        return false;
    };

    if !request_adapter.is_function() {
        return false;
    }

    let request_adapter_fn = request_adapter.unchecked_into::<js_sys::Function>();
    let Ok(promise) = request_adapter_fn.call0(&gpu_value) else {
        return false;
    };

    let Ok(promise) = promise.dyn_into::<js_sys::Promise>() else {
        return false;
    };

    // Await the adapter request
    JsFuture::from(promise)
        .await
        .is_ok_and(|adapter| !adapter.is_null() && !adapter.is_undefined())
}

/// Checks if WebGL2 is available by testing on an offscreen canvas.
///
/// This is important because once you call `getContext()` on a canvas with one
/// context type, you cannot get a different context type from that canvas.
/// By testing on an offscreen canvas first, we don't "taint" the main canvas.
fn is_webgl2_available() -> bool {
    // First check if WebGL2RenderingContext exists in the global scope
    let Some(window) = web_sys::window() else {
        return false;
    };

    // Check if WebGL2RenderingContext is defined
    let has_webgl2_class =
        js_sys::Reflect::has(&window, &JsValue::from_str("WebGL2RenderingContext"))
            .unwrap_or(false);
    if !has_webgl2_class {
        return false;
    }

    // Try to actually get a WebGL2 context on an offscreen canvas
    // This catches cases where the class exists but context creation fails
    // (e.g., software rendering fallback in some browsers, or GPU blocklisted)
    let Ok(offscreen) = OffscreenCanvas::new(1, 1) else {
        return false;
    };

    offscreen.get_context("webgl2").ok().flatten().is_some()
}

// ============================================================================
// Renderer Type
// ============================================================================

/// The type of renderer being used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RendererType {
    /// wgpu renderer using WebGPU API.
    Wgpu,
    /// WebGL2 GPU-accelerated renderer.
    WebGl2,
    /// Software CPU renderer with `Canvas2D` output.
    Software,
}

impl RendererType {
    /// Returns the renderer type as a string identifier.
    ///
    /// Returns `"wgpu"`, `"webgl2"`, or `"software"`.
    #[inline]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Wgpu => "wgpu",
            Self::WebGl2 => "webgl2",
            Self::Software => "software",
        }
    }

    /// Returns `true` if this is a GPU-accelerated renderer (wgpu or WebGL2).
    #[inline]
    pub fn is_gpu_accelerated(self) -> bool {
        matches!(self, Self::Wgpu | Self::WebGl2)
    }
}

// ============================================================================
// Renderer Backend
// ============================================================================

/// Unified renderer backend that can be wgpu, WebGL2, or Software.
///
/// This enum abstracts over the three rendering backends, providing a unified
/// interface for all rendering operations. The backend is selected at
/// construction time based on browser capabilities.
///
/// # Backend Selection
///
/// When created via [`RendererBackend::new_async`], the backend will:
/// 1. First attempt to create a wgpu (WebGPU) context (best performance)
/// 2. Fall back to WebGL2 if WebGPU is unavailable
/// 3. Fall back to Software rendering with `Canvas2D` if WebGL2 is unavailable
///
/// # Performance Characteristics
///
/// - **wgpu (WebGPU)**: Best performance, modern GPU API, lower overhead
/// - **WebGL2**: Good performance, GPU-accelerated, uses instanced rendering
/// - **Software**: Maximum compatibility, CPU-based, may be slower on complex scenes
#[allow(clippy::large_enum_variant)] // GPU renderers are larger, but boxing adds complexity for little gain
pub enum RendererBackend {
    /// wgpu renderer using WebGPU API.
    #[cfg(target_arch = "wasm32")]
    Wgpu(WgpuRenderer),
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
    /// Creates a new renderer backend asynchronously, trying wgpu first, then WebGL2,
    /// then falling back to Software.
    ///
    /// # Arguments
    ///
    /// * `canvas` - The HTML canvas element to render to
    ///
    /// # Returns
    ///
    /// A tuple of `(backend, renderer_type)` on success, or a `JsValue` error on failure.
    ///
    /// # Backend Selection Priority
    ///
    /// 1. **wgpu (WebGPU)**: Best performance, modern GPU API
    /// 2. **WebGL2**: Good performance, widely supported
    /// 3. **Software**: Maximum compatibility, CPU-based
    ///
    /// # Context Selection
    ///
    /// This function checks capabilities on offscreen canvases before touching the main
    /// canvas. This is crucial because HTML5 Canvas only allows one context type per
    /// canvas - once you call `getContext()` with one type, you cannot get another.
    ///
    /// # Note on Send
    ///
    /// This future is not `Send` because JavaScript/browser APIs are single-threaded.
    /// This is expected and safe for WASM usage.
    #[allow(clippy::future_not_send)]
    #[allow(clippy::unused_async)] // On non-wasm targets, no await is used (wgpu block is cfg'd out)
    pub async fn new_async(canvas: &HtmlCanvasElement) -> Result<(Self, RendererType), JsValue> {
        let width = canvas.width();
        let height = canvas.height();

        // Try wgpu (WebGPU) first - best performance (only available on wasm32)
        #[cfg(target_arch = "wasm32")]
        {
            if is_webgpu_available() {
                web_sys::console::log_1(&"Rource: WebGPU API detected, checking adapter...".into());

                if can_use_webgpu().await {
                    web_sys::console::log_1(&"Rource: Attempting wgpu (WebGPU) renderer...".into());

                    match WgpuRenderer::new_from_canvas(canvas).await {
                        Ok(wgpu) => {
                            web_sys::console::log_1(&"Rource: Using wgpu (WebGPU) renderer".into());
                            return Ok((Self::Wgpu(wgpu), RendererType::Wgpu));
                        }
                        Err(e) => {
                            web_sys::console::warn_1(
                                &format!("Rource: wgpu init failed: {e}, trying WebGL2...").into(),
                            );
                            // wgpu failed, but canvas might not be tainted since wgpu
                            // uses WebGPU API, not getContext. Fall through to WebGL2.
                        }
                    }
                } else {
                    web_sys::console::log_1(
                        &"Rource: WebGPU adapter not available, trying WebGL2...".into(),
                    );
                }
            }
        }

        // Suppress unused variable warning on non-wasm targets
        let _ = (width, height);

        // Try WebGL2 next
        if is_webgl2_available() {
            if let Ok(webgl2) = WebGl2Renderer::new(canvas) {
                web_sys::console::log_1(&"Rource: Using WebGL2 renderer".into());
                return Ok((Self::WebGl2(webgl2), RendererType::WebGl2));
            }
            web_sys::console::warn_1(
                &"Rource: WebGL2 available but renderer init failed, canvas may be tainted".into(),
            );
        } else {
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
        web_sys::console::log_1(&"Rource: Using software renderer".into());

        Ok((Self::Software { renderer, context }, RendererType::Software))
    }

    /// Creates a new renderer backend synchronously (WebGL2 or Software only).
    ///
    /// This is a convenience method for cases where async is not available.
    /// **Note**: This method cannot use wgpu since wgpu initialization is async.
    /// Use [`new_async`](Self::new_async) to get the best available renderer.
    ///
    /// # Arguments
    ///
    /// * `canvas` - The HTML canvas element to render to
    ///
    /// # Returns
    ///
    /// A tuple of `(backend, renderer_type)` on success, or a `JsValue` error on failure.
    #[allow(dead_code)] // Keep for potential future use where async is not available
    pub fn new(canvas: &HtmlCanvasElement) -> Result<(Self, RendererType), JsValue> {
        let width = canvas.width();
        let height = canvas.height();

        // Try WebGL2 first (can't use wgpu synchronously)
        if is_webgl2_available() {
            if let Ok(webgl2) = WebGl2Renderer::new(canvas) {
                web_sys::console::log_1(&"Rource: Using WebGL2 renderer".into());
                return Ok((Self::WebGl2(webgl2), RendererType::WebGl2));
            }
            web_sys::console::warn_1(
                &"Rource: WebGL2 available but renderer init failed, canvas may be tainted".into(),
            );
        } else {
            web_sys::console::log_1(
                &"Rource: WebGL2 not available, using software renderer".into(),
            );
        }

        // Fall back to software rendering
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
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(r) => r.width(),
            Self::WebGl2(r) => r.width(),
            Self::Software { renderer, .. } => renderer.width(),
        }
    }

    /// Returns the height of the renderer in pixels.
    #[inline]
    pub fn height(&self) -> u32 {
        match self {
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(r) => r.height(),
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
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(r) => r.resize(width, height),
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
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(r) => r,
            Self::WebGl2(r) => r,
            Self::Software { renderer, .. } => renderer,
        }
    }

    /// Presents the rendered frame to the canvas.
    ///
    /// For Software renderer, this copies the pixel buffer to the canvas via `ImageData`.
    /// For wgpu/WebGL2, this is a no-op since they render directly to the canvas.
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
        // wgpu and WebGL2 render directly to canvas, no copy needed
    }

    /// Returns true if the GPU context is lost.
    ///
    /// This can happen when the GPU is reset, the browser tab is backgrounded
    /// for a long time, or system resources are exhausted.
    ///
    /// Software renderer always returns `false` (it never loses context).
    #[inline]
    pub fn is_context_lost(&self) -> bool {
        match self {
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(_) => false, // wgpu handles this internally via surface errors
            Self::WebGl2(r) => r.is_context_lost(),
            Self::Software { .. } => false,
        }
    }

    /// Attempts to recover from a lost GPU context.
    ///
    /// # Returns
    ///
    /// - `Ok(())` if recovery was successful or if context was not lost
    /// - `Err` if recovery failed
    ///
    /// For Software renderer, this always succeeds.
    pub fn recover_context(&mut self) -> Result<(), JsValue> {
        match self {
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(_) => {
                // wgpu handles context loss via surface reconfiguration
                // which happens automatically in resize/begin_frame
                Ok(())
            }
            Self::WebGl2(ref mut renderer) => renderer
                .recover_context()
                .map_err(|e| JsValue::from_str(&format!("{e:?}"))),
            Self::Software { .. } => Ok(()),
        }
    }

    /// Returns pixel data for screenshot (software renderer only).
    ///
    /// # Returns
    ///
    /// - `Some(&[u32])` - ARGB pixel buffer for software renderer
    /// - `None` - For GPU renderers (use `canvas.toBlob()` instead)
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
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(r) => r.load_font(data),
            Self::WebGl2(r) => r.load_font(data),
            Self::Software { renderer, .. } => renderer.load_font(data),
        }
    }

    /// Synchronizes CPU with GPU by waiting for all pending commands to complete.
    ///
    /// For GPU renderers: blocks until GPU is done with pending work.
    /// For Software: no-op (CPU rendering is inherently synchronous).
    ///
    /// **Important**: Call this ONLY when you need to read from the canvas
    /// (screenshots, exports). Do NOT call every frame as it hurts performance.
    #[inline]
    pub fn sync(&self) {
        match self {
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(_) => {
                // wgpu doesn't have a direct sync equivalent in WASM
                // The submit/present model handles this
            }
            Self::WebGl2(r) => r.sync(),
            Self::Software { .. } => {}
        }
    }

    /// Returns a mutable reference to the wgpu renderer if available.
    ///
    /// This is used for GPU-specific operations like compute shaders for
    /// physics simulation.
    ///
    /// # Returns
    ///
    /// - `Some(&mut WgpuRenderer)` if using wgpu backend
    /// - `None` for WebGL2 or Software backends
    #[cfg(target_arch = "wasm32")]
    #[inline]
    pub fn as_wgpu_mut(&mut self) -> Option<&mut WgpuRenderer> {
        match self {
            Self::Wgpu(r) => Some(r),
            _ => None,
        }
    }

    /// Returns an immutable reference to the wgpu renderer if available.
    ///
    /// This is used for querying GPU-specific state like file icon counts.
    ///
    /// # Returns
    ///
    /// - `Some(&WgpuRenderer)` if using wgpu backend
    /// - `None` for WebGL2 or Software backends
    #[cfg(target_arch = "wasm32")]
    #[inline]
    pub fn as_wgpu(&self) -> Option<&WgpuRenderer> {
        match self {
            Self::Wgpu(r) => Some(r),
            _ => None,
        }
    }

    /// Returns a mutable reference to the WebGL2 renderer if available.
    ///
    /// # Returns
    ///
    /// - `Some(&mut WebGl2Renderer)` if using WebGL2 backend
    /// - `None` for wgpu or Software backends
    #[inline]
    pub fn as_webgl2_mut(&mut self) -> Option<&mut WebGl2Renderer> {
        match self {
            Self::WebGl2(r) => Some(r),
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(_) => None,
            Self::Software { .. } => None,
        }
    }

    /// Returns an immutable reference to the WebGL2 renderer if available.
    #[inline]
    pub fn as_webgl2(&self) -> Option<&WebGl2Renderer> {
        match self {
            Self::WebGl2(r) => Some(r),
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(_) => None,
            Self::Software { .. } => None,
        }
    }

    /// Returns a mutable reference to the Software renderer if available.
    ///
    /// # Returns
    ///
    /// - `Some(&mut SoftwareRenderer)` if using Software backend
    /// - `None` for wgpu or WebGL2 backends
    #[inline]
    pub fn as_software_mut(&mut self) -> Option<&mut SoftwareRenderer> {
        match self {
            Self::Software { renderer, .. } => Some(renderer),
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(_) => None,
            Self::WebGl2(_) => None,
        }
    }

    /// Returns an immutable reference to the Software renderer if available.
    #[inline]
    pub fn as_software(&self) -> Option<&SoftwareRenderer> {
        match self {
            Self::Software { renderer, .. } => Some(renderer),
            #[cfg(target_arch = "wasm32")]
            Self::Wgpu(_) => None,
            Self::WebGl2(_) => None,
        }
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
        assert_eq!(RendererType::Wgpu.as_str(), "wgpu");
        assert_eq!(RendererType::WebGl2.as_str(), "webgl2");
        assert_eq!(RendererType::Software.as_str(), "software");
    }

    #[test]
    fn test_renderer_type_equality() {
        assert_eq!(RendererType::Wgpu, RendererType::Wgpu);
        assert_eq!(RendererType::WebGl2, RendererType::WebGl2);
        assert_eq!(RendererType::Software, RendererType::Software);
        assert_ne!(RendererType::Wgpu, RendererType::WebGl2);
        assert_ne!(RendererType::WebGl2, RendererType::Software);
    }

    #[test]
    fn test_renderer_type_copy() {
        let t1 = RendererType::Wgpu;
        let t2 = t1;
        assert_eq!(t1, t2);
    }

    #[test]
    fn test_renderer_type_debug() {
        let debug_str = format!("{:?}", RendererType::Wgpu);
        assert!(debug_str.contains("Wgpu"));

        let debug_str = format!("{:?}", RendererType::WebGl2);
        assert!(debug_str.contains("WebGl2"));
    }

    #[test]
    fn test_renderer_type_is_gpu_accelerated() {
        assert!(RendererType::Wgpu.is_gpu_accelerated());
        assert!(RendererType::WebGl2.is_gpu_accelerated());
        assert!(!RendererType::Software.is_gpu_accelerated());
    }
}
