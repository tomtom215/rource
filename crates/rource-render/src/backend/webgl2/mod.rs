//! WebGL2 rendering backend for GPU-accelerated browser rendering.
//!
//! This module provides a WebGL2-based renderer that implements the [`Renderer`] trait,
//! enabling GPU-accelerated rendering in web browsers via WebAssembly.
//!
//! ## Features
//!
//! - Instanced rendering for efficient draw call batching
//! - Anti-aliased primitives (circles, lines) via fragment shaders
//! - Font atlas for efficient text rendering
//! - Context loss detection and recovery
//!
//! ## Usage
//!
//! This backend is enabled via the `webgl2` feature flag and is designed for WASM builds.
//!
//! ```ignore
//! use rource_render::backend::webgl2::WebGl2Renderer;
//!
//! let canvas: web_sys::HtmlCanvasElement = ...;
//! let renderer = WebGl2Renderer::new(&canvas)?;
//! ```

// WebGL APIs use i32 for sizes which may involve u32 casts
#![allow(clippy::cast_possible_wrap)]

pub mod bloom;
pub mod buffers;
pub mod shaders;
pub mod textures;

use std::collections::HashMap;

use wasm_bindgen::JsCast;
use wasm_bindgen::JsValue;
use web_sys::{HtmlCanvasElement, WebGl2RenderingContext, WebGlProgram, WebGlUniformLocation};

use rource_math::{Bounds, Color, Mat4, Vec2};

use crate::{FontCache, FontId, Renderer, TextureId};

use bloom::BloomPipeline;
use buffers::{InstanceBuffer, VertexArrayManager};
use shaders::{
    CIRCLE_FRAGMENT_SHADER, CIRCLE_VERTEX_SHADER, LINE_FRAGMENT_SHADER, LINE_VERTEX_SHADER,
    QUAD_FRAGMENT_SHADER, QUAD_VERTEX_SHADER, RING_FRAGMENT_SHADER, RING_VERTEX_SHADER,
    TEXTURED_QUAD_FRAGMENT_SHADER, TEXTURED_QUAD_VERTEX_SHADER, TEXT_FRAGMENT_SHADER,
    TEXT_VERTEX_SHADER,
};
use textures::{FontAtlas, GlyphKey, TextureManager};

// Re-export bloom configuration for external use
pub use bloom::{BloomConfig, BloomPipeline as BloomEffect};

/// Error type for WebGL2 renderer initialization.
#[derive(Debug, Clone)]
pub enum WebGl2Error {
    /// WebGL2 context not available.
    ContextNotAvailable,
    /// Shader compilation failed.
    ShaderCompilation(String),
    /// Program linking failed.
    ProgramLinking(String),
}

impl std::fmt::Display for WebGl2Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ContextNotAvailable => write!(f, "WebGL2 context not available"),
            Self::ShaderCompilation(msg) => write!(f, "Shader compilation failed: {msg}"),
            Self::ProgramLinking(msg) => write!(f, "Program linking failed: {msg}"),
        }
    }
}

impl std::error::Error for WebGl2Error {}

/// Compiled shader program with uniform locations.
struct ShaderProgram {
    program: WebGlProgram,
    resolution_loc: Option<WebGlUniformLocation>,
    texture_loc: Option<WebGlUniformLocation>,
}

/// WebGL2 renderer implementing the Renderer trait.
///
/// This renderer uses WebGL2 for GPU-accelerated rendering in web browsers.
/// It batches draw calls using instanced rendering for optimal performance.
pub struct WebGl2Renderer {
    /// WebGL2 rendering context.
    gl: WebGl2RenderingContext,

    /// Viewport width.
    width: u32,

    /// Viewport height.
    height: u32,

    /// Current transformation matrix.
    transform: Mat4,

    /// Clip rectangle stack.
    clips: Vec<Bounds>,

    /// Font cache (shared with software renderer for rasterization).
    font_cache: FontCache,

    /// Font atlas for GPU text rendering.
    font_atlas: FontAtlas,

    /// Texture manager for user textures.
    texture_manager: TextureManager,

    /// Circle shader program.
    circle_program: Option<ShaderProgram>,

    /// Ring (circle outline) shader program.
    ring_program: Option<ShaderProgram>,

    /// Line shader program.
    line_program: Option<ShaderProgram>,

    /// Solid quad shader program.
    quad_program: Option<ShaderProgram>,

    /// Textured quad shader program.
    textured_quad_program: Option<ShaderProgram>,

    /// Text shader program.
    text_program: Option<ShaderProgram>,

    /// VAO manager.
    vao_manager: VertexArrayManager,

    /// Instance buffer for circles.
    circle_instances: InstanceBuffer,

    /// Instance buffer for rings.
    ring_instances: InstanceBuffer,

    /// Instance buffer for lines.
    line_instances: InstanceBuffer,

    /// Instance buffer for solid quads.
    quad_instances: InstanceBuffer,

    /// Instance buffer for textured quads (grouped by texture).
    textured_quad_instances: HashMap<TextureId, InstanceBuffer>,

    /// Instance buffer for text glyphs.
    text_instances: InstanceBuffer,

    /// GPU bloom post-processing pipeline.
    bloom_pipeline: BloomPipeline,

    /// Whether context was lost.
    context_lost: bool,
}

impl WebGl2Renderer {
    /// Creates a new WebGL2 renderer attached to a canvas.
    pub fn new(canvas: &HtmlCanvasElement) -> Result<Self, WebGl2Error> {
        // Create context options with preserveDrawingBuffer: true
        // This is required for screenshots (canvas.toBlob/toDataURL) to work correctly
        let context_options = js_sys::Object::new();
        js_sys::Reflect::set(
            &context_options,
            &JsValue::from_str("preserveDrawingBuffer"),
            &JsValue::from(true),
        )
        .ok();
        // Also set alpha to true for proper transparency blending
        js_sys::Reflect::set(
            &context_options,
            &JsValue::from_str("alpha"),
            &JsValue::from(true),
        )
        .ok();

        let gl = canvas
            .get_context_with_context_options("webgl2", &context_options)
            .ok()
            .flatten()
            .and_then(|ctx| ctx.dyn_into::<WebGl2RenderingContext>().ok())
            .ok_or(WebGl2Error::ContextNotAvailable)?;

        let width = canvas.width();
        let height = canvas.height();

        let mut renderer = Self {
            gl,
            width,
            height,
            transform: Mat4::IDENTITY,
            clips: Vec::new(),
            font_cache: FontCache::new(),
            font_atlas: FontAtlas::new(),
            texture_manager: TextureManager::new(),
            circle_program: None,
            ring_program: None,
            line_program: None,
            quad_program: None,
            textured_quad_program: None,
            text_program: None,
            vao_manager: VertexArrayManager::new(),
            circle_instances: InstanceBuffer::new(7, 1000), // center(2) + radius(1) + color(4)
            ring_instances: InstanceBuffer::new(8, 500), // center(2) + radius(1) + width(1) + color(4)
            line_instances: InstanceBuffer::new(9, 1000), // start(2) + end(2) + width(1) + color(4)
            quad_instances: InstanceBuffer::new(8, 500), // bounds(4) + color(4)
            textured_quad_instances: HashMap::new(),
            text_instances: InstanceBuffer::new(12, 2000), // bounds(4) + uv_bounds(4) + color(4)
            bloom_pipeline: BloomPipeline::new(),
            context_lost: false,
        };

        renderer.init_gl()?;

        // Initialize bloom pipeline (non-fatal if it fails)
        if !renderer.bloom_pipeline.initialize(&renderer.gl) {
            web_sys::console::warn_1(&"Rource: Bloom pipeline initialization failed".into());
        }

        Ok(renderer)
    }

    /// Initializes WebGL state and compiles shaders.
    fn init_gl(&mut self) -> Result<(), WebGl2Error> {
        let gl = &self.gl;

        // Enable blending
        gl.enable(WebGl2RenderingContext::BLEND);
        gl.blend_func(
            WebGl2RenderingContext::SRC_ALPHA,
            WebGl2RenderingContext::ONE_MINUS_SRC_ALPHA,
        );

        // Compile shader programs
        self.circle_program =
            Some(self.compile_program(CIRCLE_VERTEX_SHADER, CIRCLE_FRAGMENT_SHADER)?);
        self.ring_program = Some(self.compile_program(RING_VERTEX_SHADER, RING_FRAGMENT_SHADER)?);
        self.line_program = Some(self.compile_program(LINE_VERTEX_SHADER, LINE_FRAGMENT_SHADER)?);
        self.quad_program = Some(self.compile_program(QUAD_VERTEX_SHADER, QUAD_FRAGMENT_SHADER)?);
        self.textured_quad_program =
            Some(self.compile_program(TEXTURED_QUAD_VERTEX_SHADER, TEXTURED_QUAD_FRAGMENT_SHADER)?);
        self.text_program = Some(self.compile_program(TEXT_VERTEX_SHADER, TEXT_FRAGMENT_SHADER)?);

        // Create VAO manager vertex buffer
        self.vao_manager.create_vertex_buffer(gl);

        Ok(())
    }

    /// Compiles a shader program from vertex and fragment shader sources.
    fn compile_program(
        &self,
        vertex_src: &str,
        fragment_src: &str,
    ) -> Result<ShaderProgram, WebGl2Error> {
        let gl = &self.gl;

        // Compile vertex shader
        let vertex_shader = gl
            .create_shader(WebGl2RenderingContext::VERTEX_SHADER)
            .ok_or_else(|| {
                WebGl2Error::ShaderCompilation("Failed to create vertex shader".into())
            })?;

        gl.shader_source(&vertex_shader, vertex_src);
        gl.compile_shader(&vertex_shader);

        if !gl
            .get_shader_parameter(&vertex_shader, WebGl2RenderingContext::COMPILE_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_shader_info_log(&vertex_shader).unwrap_or_default();
            gl.delete_shader(Some(&vertex_shader));
            return Err(WebGl2Error::ShaderCompilation(format!(
                "Vertex shader: {log}"
            )));
        }

        // Compile fragment shader
        let fragment_shader = gl
            .create_shader(WebGl2RenderingContext::FRAGMENT_SHADER)
            .ok_or_else(|| {
                WebGl2Error::ShaderCompilation("Failed to create fragment shader".into())
            })?;

        gl.shader_source(&fragment_shader, fragment_src);
        gl.compile_shader(&fragment_shader);

        if !gl
            .get_shader_parameter(&fragment_shader, WebGl2RenderingContext::COMPILE_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_shader_info_log(&fragment_shader).unwrap_or_default();
            gl.delete_shader(Some(&vertex_shader));
            gl.delete_shader(Some(&fragment_shader));
            return Err(WebGl2Error::ShaderCompilation(format!(
                "Fragment shader: {log}"
            )));
        }

        // Link program
        let program = gl
            .create_program()
            .ok_or_else(|| WebGl2Error::ProgramLinking("Failed to create program".into()))?;

        gl.attach_shader(&program, &vertex_shader);
        gl.attach_shader(&program, &fragment_shader);
        gl.link_program(&program);

        // Shaders can be deleted after linking
        gl.delete_shader(Some(&vertex_shader));
        gl.delete_shader(Some(&fragment_shader));

        if !gl
            .get_program_parameter(&program, WebGl2RenderingContext::LINK_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_program_info_log(&program).unwrap_or_default();
            gl.delete_program(Some(&program));
            return Err(WebGl2Error::ProgramLinking(log));
        }

        // Get uniform locations
        let resolution_loc = gl.get_uniform_location(&program, "u_resolution");
        let texture_loc = gl
            .get_uniform_location(&program, "u_texture")
            .or_else(|| gl.get_uniform_location(&program, "u_font_atlas"));

        Ok(ShaderProgram {
            program,
            resolution_loc,
            texture_loc,
        })
    }

    /// Transforms a point from world to screen coordinates.
    #[inline]
    fn transform_point(&self, point: Vec2) -> Vec2 {
        let p = self
            .transform
            .transform_point(rource_math::Vec3::from_vec2(point, 0.0));
        Vec2::new(p.x, p.y)
    }

    /// Flushes all batched draw calls.
    fn flush(&mut self) {
        self.flush_circles();
        self.flush_rings();
        self.flush_lines();
        self.flush_quads();
        self.flush_textured_quads();
        self.flush_text();
    }

    /// Flushes circle draw calls.
    fn flush_circles(&mut self) {
        if self.circle_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.circle_program else {
            return;
        };

        let gl = &self.gl;

        // Upload instance data
        self.circle_instances.upload(gl);

        // Setup VAO if needed
        if self.vao_manager.circle_vao.is_none() {
            self.vao_manager
                .setup_circle_vao(gl, &self.circle_instances);
        }

        // Use program and bind VAO
        gl.use_program(Some(&program.program));
        gl.bind_vertex_array(self.vao_manager.circle_vao.as_ref());

        // Set uniforms
        if let Some(loc) = &program.resolution_loc {
            gl.uniform2f(Some(loc), self.width as f32, self.height as f32);
        }

        // Draw instanced
        let instance_count = self.circle_instances.instance_count() as i32;
        gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, instance_count);

        gl.bind_vertex_array(None);

        self.circle_instances.clear();
    }

    /// Flushes ring (circle outline) draw calls.
    fn flush_rings(&mut self) {
        if self.ring_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.ring_program else {
            return;
        };

        let gl = &self.gl;

        self.ring_instances.upload(gl);

        if self.vao_manager.ring_vao.is_none() {
            self.vao_manager.setup_ring_vao(gl, &self.ring_instances);
        }

        gl.use_program(Some(&program.program));
        gl.bind_vertex_array(self.vao_manager.ring_vao.as_ref());

        if let Some(loc) = &program.resolution_loc {
            gl.uniform2f(Some(loc), self.width as f32, self.height as f32);
        }

        let instance_count = self.ring_instances.instance_count() as i32;
        gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, instance_count);

        gl.bind_vertex_array(None);

        self.ring_instances.clear();
    }

    /// Flushes line draw calls.
    fn flush_lines(&mut self) {
        if self.line_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.line_program else {
            return;
        };

        let gl = &self.gl;

        self.line_instances.upload(gl);

        if self.vao_manager.line_vao.is_none() {
            self.vao_manager.setup_line_vao(gl, &self.line_instances);
        }

        gl.use_program(Some(&program.program));
        gl.bind_vertex_array(self.vao_manager.line_vao.as_ref());

        if let Some(loc) = &program.resolution_loc {
            gl.uniform2f(Some(loc), self.width as f32, self.height as f32);
        }

        let instance_count = self.line_instances.instance_count() as i32;
        gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, instance_count);

        gl.bind_vertex_array(None);

        self.line_instances.clear();
    }

    /// Flushes solid quad draw calls.
    fn flush_quads(&mut self) {
        if self.quad_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.quad_program else {
            return;
        };

        let gl = &self.gl;

        self.quad_instances.upload(gl);

        if self.vao_manager.quad_vao.is_none() {
            self.vao_manager.setup_quad_vao(gl, &self.quad_instances);
        }

        gl.use_program(Some(&program.program));
        gl.bind_vertex_array(self.vao_manager.quad_vao.as_ref());

        if let Some(loc) = &program.resolution_loc {
            gl.uniform2f(Some(loc), self.width as f32, self.height as f32);
        }

        let instance_count = self.quad_instances.instance_count() as i32;
        gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, instance_count);

        gl.bind_vertex_array(None);

        self.quad_instances.clear();
    }

    /// Flushes textured quad draw calls.
    fn flush_textured_quads(&mut self) {
        if self.textured_quad_instances.is_empty() {
            return;
        }

        let Some(program) = &self.textured_quad_program else {
            return;
        };

        let gl = &self.gl;

        gl.use_program(Some(&program.program));

        if let Some(loc) = &program.resolution_loc {
            gl.uniform2f(Some(loc), self.width as f32, self.height as f32);
        }

        if let Some(loc) = &program.texture_loc {
            gl.uniform1i(Some(loc), 0); // Texture unit 0
        }

        // Draw each texture's instances
        let texture_ids: Vec<TextureId> = self.textured_quad_instances.keys().copied().collect();

        for tex_id in texture_ids {
            if let Some(instances) = self.textured_quad_instances.get_mut(&tex_id) {
                if instances.instance_count() == 0 {
                    continue;
                }

                instances.upload(gl);

                // Bind texture
                self.texture_manager.bind(gl, tex_id, 0);

                // Setup VAO if needed
                if self.vao_manager.textured_quad_vao.is_none() {
                    self.vao_manager.setup_textured_vao(gl, instances);
                }

                gl.bind_vertex_array(self.vao_manager.textured_quad_vao.as_ref());

                let instance_count = instances.instance_count() as i32;
                gl.draw_arrays_instanced(
                    WebGl2RenderingContext::TRIANGLE_STRIP,
                    0,
                    4,
                    instance_count,
                );

                instances.clear();
            }
        }

        gl.bind_vertex_array(None);
    }

    /// Flushes text draw calls.
    fn flush_text(&mut self) {
        if self.text_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.text_program else {
            return;
        };

        let gl = &self.gl;

        // Upload font atlas
        self.font_atlas.upload(gl);
        self.text_instances.upload(gl);

        // Setup VAO if needed (reusing textured quad VAO layout)
        if self.vao_manager.text_vao.is_none() {
            // Text uses same layout as textured quads
            self.vao_manager
                .setup_textured_vao(gl, &self.text_instances);
            self.vao_manager.text_vao = self.vao_manager.textured_quad_vao.take();
        }

        gl.use_program(Some(&program.program));
        gl.bind_vertex_array(self.vao_manager.text_vao.as_ref());

        if let Some(loc) = &program.resolution_loc {
            gl.uniform2f(Some(loc), self.width as f32, self.height as f32);
        }

        if let Some(loc) = &program.texture_loc {
            gl.uniform1i(Some(loc), 0);
        }

        // Bind font atlas
        self.font_atlas.bind(gl, 0);

        let instance_count = self.text_instances.instance_count() as i32;
        gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, instance_count);

        gl.bind_vertex_array(None);

        self.text_instances.clear();
    }

    /// Checks if WebGL context was lost.
    pub fn is_context_lost(&self) -> bool {
        self.context_lost || self.gl.is_context_lost()
    }

    /// Attempts to recover from context loss.
    pub fn recover_context(&mut self) -> Result<(), WebGl2Error> {
        if self.gl.is_context_lost() {
            return Err(WebGl2Error::ContextNotAvailable);
        }

        self.context_lost = false;

        // Reinitialize GL state
        self.init_gl()?;

        // Clear font atlas (glyphs need to be re-cached)
        self.font_atlas.clear();

        // Recreate VAOs
        self.vao_manager = VertexArrayManager::new();
        self.vao_manager.create_vertex_buffer(&self.gl);

        // Reinitialize bloom pipeline
        // Preserve config but recreate GPU resources
        let bloom_config = self.bloom_pipeline.config;
        self.bloom_pipeline.destroy(&self.gl);
        self.bloom_pipeline = BloomPipeline::new();
        self.bloom_pipeline.config = bloom_config;
        if !self.bloom_pipeline.initialize(&self.gl) {
            web_sys::console::warn_1(
                &"Rource: Bloom pipeline re-initialization failed after context recovery".into(),
            );
        }

        Ok(())
    }

    /// Returns access to the font cache.
    pub fn font_cache(&self) -> &FontCache {
        &self.font_cache
    }

    /// Returns mutable access to the font cache.
    pub fn font_cache_mut(&mut self) -> &mut FontCache {
        &mut self.font_cache
    }

    // =========================================================================
    // Bloom Effect API
    // =========================================================================

    /// Returns whether the bloom effect is enabled.
    #[inline]
    pub fn is_bloom_enabled(&self) -> bool {
        self.bloom_pipeline.config.enabled
    }

    /// Enables or disables the bloom effect.
    ///
    /// When enabled, bright areas of the scene will have a soft glow effect.
    /// Bloom is processed entirely on the GPU for maximum performance.
    #[inline]
    pub fn set_bloom_enabled(&mut self, enabled: bool) {
        self.bloom_pipeline.config.enabled = enabled;
    }

    /// Returns the current bloom brightness threshold.
    #[inline]
    pub fn bloom_threshold(&self) -> f32 {
        self.bloom_pipeline.config.threshold
    }

    /// Sets the bloom brightness threshold (0.0 - 1.0).
    ///
    /// Pixels brighter than this value will contribute to the bloom effect.
    /// Lower values = more bloom, higher values = bloom only on very bright areas.
    ///
    /// Default: 0.7
    #[inline]
    pub fn set_bloom_threshold(&mut self, threshold: f32) {
        self.bloom_pipeline.config.threshold = threshold.clamp(0.0, 1.0);
    }

    /// Returns the current bloom intensity multiplier.
    #[inline]
    pub fn bloom_intensity(&self) -> f32 {
        self.bloom_pipeline.config.intensity
    }

    /// Sets the bloom intensity multiplier.
    ///
    /// Higher values create a brighter, more pronounced glow effect.
    ///
    /// Default: 1.0
    #[inline]
    pub fn set_bloom_intensity(&mut self, intensity: f32) {
        self.bloom_pipeline.config.intensity = intensity.max(0.0);
    }

    /// Returns the current bloom downscale factor.
    #[inline]
    pub fn bloom_downscale(&self) -> u32 {
        self.bloom_pipeline.config.downscale
    }

    /// Sets the bloom downscale factor.
    ///
    /// The bloom effect is rendered at `width/downscale` x `height/downscale`
    /// resolution for performance. Higher values = faster but blockier bloom.
    ///
    /// Default: 4
    #[inline]
    pub fn set_bloom_downscale(&mut self, downscale: u32) {
        self.bloom_pipeline.config.downscale = downscale.max(1);
    }

    /// Returns the current number of bloom blur passes.
    #[inline]
    pub fn bloom_passes(&self) -> u32 {
        self.bloom_pipeline.config.passes
    }

    /// Sets the number of bloom blur passes.
    ///
    /// More passes create a softer, more spread-out glow.
    /// Each pass adds a horizontal and vertical blur.
    ///
    /// Default: 2
    #[inline]
    pub fn set_bloom_passes(&mut self, passes: u32) {
        self.bloom_pipeline.config.passes = passes.max(1);
    }

    /// Returns the full bloom configuration.
    #[inline]
    pub fn bloom_config(&self) -> BloomConfig {
        self.bloom_pipeline.config
    }

    /// Sets the full bloom configuration.
    #[inline]
    pub fn set_bloom_config(&mut self, config: BloomConfig) {
        self.bloom_pipeline.config = config;
    }

    // =========================================================================
    // Synchronization
    // =========================================================================

    /// Synchronizes CPU with GPU by waiting for all pending commands to complete.
    ///
    /// This is a blocking call that should only be used when GPU synchronization
    /// is required, such as before reading from the canvas (screenshots, exports).
    /// Do NOT call this every frame as it defeats the purpose of double-buffering
    /// and can significantly reduce performance.
    ///
    /// # Performance Note
    ///
    /// `gl.finish()` blocks the CPU until all GPU commands complete. For normal
    /// rendering, this is unnecessary because:
    /// - The browser's compositor handles frame presentation timing
    /// - `requestAnimationFrame` ensures frames are ready before paint
    /// - Double-buffering naturally hides GPU latency
    ///
    /// Only call this when you need to read from the canvas (e.g., `canvas.toBlob()`).
    pub fn sync(&self) {
        if !self.context_lost {
            self.gl.finish();
        }
    }
}

impl Renderer for WebGl2Renderer {
    fn begin_frame(&mut self) {
        // Check for context loss
        if self.gl.is_context_lost() {
            self.context_lost = true;
            return;
        }

        // Clear instance buffers
        self.circle_instances.clear();
        self.ring_instances.clear();
        self.line_instances.clear();
        self.quad_instances.clear();
        for instances in self.textured_quad_instances.values_mut() {
            instances.clear();
        }
        self.text_instances.clear();

        // If bloom is active, render to scene FBO instead of canvas
        if self.bloom_pipeline.config.enabled {
            // Ensure FBOs are sized correctly
            if self
                .bloom_pipeline
                .ensure_size(&self.gl, self.width, self.height)
            {
                self.bloom_pipeline.bind_scene_fbo(&self.gl);
                self.gl
                    .viewport(0, 0, self.width as i32, self.height as i32);
            }
        }
    }

    fn end_frame(&mut self) {
        if self.context_lost {
            return;
        }

        // Flush all batched draw calls to the GPU
        self.flush();

        // Apply bloom post-processing if active
        if self.bloom_pipeline.is_active() {
            self.bloom_pipeline.apply(&self.gl, &mut self.vao_manager);

            // Re-enable blending after bloom (bloom disables it)
            self.gl.enable(WebGl2RenderingContext::BLEND);
            self.gl.blend_func(
                WebGl2RenderingContext::SRC_ALPHA,
                WebGl2RenderingContext::ONE_MINUS_SRC_ALPHA,
            );
        }

        // Note: gl.finish() is NOT called here for performance.
        // Normal rendering relies on the browser's compositor for frame timing.
        // For operations that require GPU synchronization (screenshots, exports),
        // call sync() explicitly after render.
    }

    fn clear(&mut self, color: Color) {
        if self.context_lost {
            return;
        }

        self.gl.clear_color(color.r, color.g, color.b, color.a);
        self.gl.clear(WebGl2RenderingContext::COLOR_BUFFER_BIT);
    }

    fn draw_circle(&mut self, center: Vec2, radius: f32, width: f32, color: Color) {
        if self.context_lost || color.a < 0.001 {
            return;
        }

        let center = self.transform_point(center);

        // Add to ring instances
        self.ring_instances.push_raw(&[
            center.x, center.y, radius, width, color.r, color.g, color.b, color.a,
        ]);
    }

    fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color) {
        if self.context_lost || color.a < 0.001 || radius < 0.1 {
            return;
        }

        let center = self.transform_point(center);

        // Add to circle instances
        self.circle_instances.push_raw(&[
            center.x, center.y, radius, color.r, color.g, color.b, color.a,
        ]);
    }

    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color) {
        if self.context_lost || color.a < 0.001 {
            return;
        }

        let start = self.transform_point(start);
        let end = self.transform_point(end);

        // Add to line instances
        self.line_instances.push_raw(&[
            start.x, start.y, end.x, end.y, width, color.r, color.g, color.b, color.a,
        ]);
    }

    fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color) {
        if points.len() < 2 {
            return;
        }

        // Draw as line segments
        for window in points.windows(2) {
            self.draw_line(window[0], window[1], width, color);
        }
    }

    fn draw_quad(&mut self, bounds: Bounds, texture: Option<TextureId>, color: Color) {
        if self.context_lost || color.a < 0.001 {
            return;
        }

        let min = self.transform_point(bounds.min);
        let max = self.transform_point(bounds.max);

        if let Some(tex_id) = texture {
            // Textured quad
            let instances = self
                .textured_quad_instances
                .entry(tex_id)
                .or_insert_with(|| InstanceBuffer::new(12, 100));

            instances.push_raw(&[
                min.x, min.y, max.x, max.y, // bounds
                0.0, 0.0, 1.0, 1.0, // uv bounds (full texture)
                color.r, color.g, color.b, color.a,
            ]);
        } else {
            // Solid colored quad
            self.quad_instances.push_raw(&[
                min.x, min.y, max.x, max.y, color.r, color.g, color.b, color.a,
            ]);
        }
    }

    fn draw_text(&mut self, text: &str, position: Vec2, font: FontId, size: f32, color: Color) {
        if self.context_lost || text.is_empty() || color.a < 0.001 {
            return;
        }

        let position = self.transform_point(position);
        let mut x = position.x;
        let y = position.y;

        let size_tenths = (size * 10.0) as u32;

        for ch in text.chars() {
            let key = GlyphKey { ch, size_tenths };

            // Get or rasterize glyph
            let region = if let Some(region) = self.font_atlas.get_glyph(key) {
                *region
            } else {
                // Rasterize glyph using font cache
                if let Some(glyph) = self.font_cache.rasterize(font, ch, size) {
                    let width = glyph.metrics.width as u32;
                    let height = glyph.metrics.height as u32;

                    if width > 0 && height > 0 {
                        if let Some(region) =
                            self.font_atlas.add_glyph(key, width, height, &glyph.bitmap)
                        {
                            // Calculate glyph position
                            let gx = x + glyph.metrics.xmin as f32;
                            let gy = y - glyph.metrics.ymin as f32 - height as f32 + (size * 0.8);

                            let (u_min, v_min, u_max, v_max) = region.uv_bounds();

                            self.text_instances.push_raw(&[
                                gx,
                                gy,
                                gx + width as f32,
                                gy + height as f32,
                                u_min,
                                v_min,
                                u_max,
                                v_max,
                                color.r,
                                color.g,
                                color.b,
                                color.a,
                            ]);
                        }
                    }

                    x += glyph.metrics.advance_width;
                }
                continue;
            };

            // Use cached glyph
            if let Some(glyph) = self.font_cache.rasterize(font, ch, size) {
                let width = region.width as f32;
                let height = region.height as f32;

                let gx = x + glyph.metrics.xmin as f32;
                let gy = y - glyph.metrics.ymin as f32 - height + (size * 0.8);

                let (u_min, v_min, u_max, v_max) = region.uv_bounds();

                self.text_instances.push_raw(&[
                    gx,
                    gy,
                    gx + width,
                    gy + height,
                    u_min,
                    v_min,
                    u_max,
                    v_max,
                    color.r,
                    color.g,
                    color.b,
                    color.a,
                ]);

                x += glyph.metrics.advance_width;
            }
        }
    }

    fn set_transform(&mut self, transform: Mat4) {
        // Flush before changing transform
        if self.circle_instances.instance_count() > 0
            || self.ring_instances.instance_count() > 0
            || self.line_instances.instance_count() > 0
            || self.quad_instances.instance_count() > 0
            || self.text_instances.instance_count() > 0
        {
            self.flush();
        }
        self.transform = transform;
    }

    fn transform(&self) -> Mat4 {
        self.transform
    }

    fn push_clip(&mut self, bounds: Bounds) {
        if self.context_lost {
            return;
        }

        // Flush before enabling scissor
        self.flush();

        let min = self.transform_point(bounds.min);
        let max = self.transform_point(bounds.max);
        self.clips.push(Bounds::new(min, max));

        // Enable scissor test
        self.gl.enable(WebGl2RenderingContext::SCISSOR_TEST);

        // Set scissor rect (WebGL has Y-up from bottom)
        let scissor_y = self.height as i32 - max.y as i32;
        self.gl.scissor(
            min.x as i32,
            scissor_y,
            (max.x - min.x) as i32,
            (max.y - min.y) as i32,
        );
    }

    fn pop_clip(&mut self) {
        if self.context_lost {
            return;
        }

        // Flush before changing scissor
        self.flush();

        self.clips.pop();

        if self.clips.is_empty() {
            self.gl.disable(WebGl2RenderingContext::SCISSOR_TEST);
        } else if let Some(clip) = self.clips.last() {
            let scissor_y = self.height as i32 - clip.max.y as i32;
            self.gl.scissor(
                clip.min.x as i32,
                scissor_y,
                (clip.max.x - clip.min.x) as i32,
                (clip.max.y - clip.min.y) as i32,
            );
        }
    }

    fn width(&self) -> u32 {
        self.width
    }

    fn height(&self) -> u32 {
        self.height
    }

    fn resize(&mut self, width: u32, height: u32) {
        self.width = width;
        self.height = height;
        self.gl.viewport(0, 0, width as i32, height as i32);
    }

    fn load_texture(&mut self, width: u32, height: u32, data: &[u8]) -> TextureId {
        self.texture_manager.load(&self.gl, width, height, data)
    }

    fn unload_texture(&mut self, texture: TextureId) {
        self.texture_manager.unload(&self.gl, texture);
        self.textured_quad_instances.remove(&texture);
    }

    fn load_font(&mut self, data: &[u8]) -> Option<FontId> {
        self.font_cache.load(data)
    }
}

impl Drop for WebGl2Renderer {
    fn drop(&mut self) {
        // Clean up WebGL resources
        self.vao_manager.destroy(&self.gl);
        self.font_atlas.destroy(&self.gl);
        self.texture_manager.destroy(&self.gl);
        self.circle_instances.destroy(&self.gl);
        self.ring_instances.destroy(&self.gl);
        self.line_instances.destroy(&self.gl);
        self.quad_instances.destroy(&self.gl);
        for instances in self.textured_quad_instances.values_mut() {
            instances.destroy(&self.gl);
        }
        self.text_instances.destroy(&self.gl);

        // Clean up bloom pipeline (FBOs, textures, shader programs)
        self.bloom_pipeline.destroy(&self.gl);

        // Delete shader programs
        if let Some(prog) = &self.circle_program {
            self.gl.delete_program(Some(&prog.program));
        }
        if let Some(prog) = &self.ring_program {
            self.gl.delete_program(Some(&prog.program));
        }
        if let Some(prog) = &self.line_program {
            self.gl.delete_program(Some(&prog.program));
        }
        if let Some(prog) = &self.quad_program {
            self.gl.delete_program(Some(&prog.program));
        }
        if let Some(prog) = &self.textured_quad_program {
            self.gl.delete_program(Some(&prog.program));
        }
        if let Some(prog) = &self.text_program {
            self.gl.delete_program(Some(&prog.program));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_webgl2_error_display() {
        let err = WebGl2Error::ContextNotAvailable;
        assert_eq!(format!("{err}"), "WebGL2 context not available");

        let err = WebGl2Error::ShaderCompilation("test error".into());
        assert!(format!("{err}").contains("test error"));

        let err = WebGl2Error::ProgramLinking("link error".into());
        assert!(format!("{err}").contains("link error"));
    }

    #[test]
    fn test_instance_buffer_floats() {
        // Verify instance buffer float counts match shader expectations
        let circle_buf = InstanceBuffer::new(7, 10); // center(2) + radius(1) + color(4)
        assert_eq!(circle_buf.floats_per_instance(), 7);

        let ring_buf = InstanceBuffer::new(8, 10); // center(2) + radius(1) + width(1) + color(4)
        assert_eq!(ring_buf.floats_per_instance(), 8);

        let line_buf = InstanceBuffer::new(9, 10); // start(2) + end(2) + width(1) + color(4)
        assert_eq!(line_buf.floats_per_instance(), 9);

        let quad_buf = InstanceBuffer::new(8, 10); // bounds(4) + color(4)
        assert_eq!(quad_buf.floats_per_instance(), 8);

        let text_buf = InstanceBuffer::new(12, 10); // bounds(4) + uv_bounds(4) + color(4)
        assert_eq!(text_buf.floats_per_instance(), 12);
    }
}
