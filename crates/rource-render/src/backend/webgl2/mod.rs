// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

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
//!
//! ## Module Organization
//!
//! | Module | Description |
//! |--------|-------------|
//! | `adaptive` | Adaptive quality controller |
//! | `bloom` | GPU bloom post-processing |
//! | `buffers` | VBO/VAO management |
//! | `error` | Error types |
//! | `shaders` | GLSL ES 3.0 shaders |
//! | `shadow` | GPU shadow post-processing |
//! | `state` | WebGL state caching |
//! | `stats` | Frame statistics |
//! | `textures` | Texture and font atlas management |
//! | `ubo` | Uniform Buffer Objects |

// WebGL APIs use i32 for sizes which may involve u32 casts
#![allow(clippy::cast_possible_wrap)]

pub mod adaptive;
pub mod bloom;
pub mod buffers;
pub mod error;
pub mod shaders;
pub mod shadow;
pub mod state;
pub mod stats;
pub mod texture_array;
pub mod textures;
pub mod ubo;

// Internal implementation modules (methods on WebGl2Renderer)
mod effects_methods;
mod flush_passes;
mod icons_methods;

use std::collections::HashMap;

use wasm_bindgen::JsCast;
use wasm_bindgen::JsValue;
use web_sys::{HtmlCanvasElement, WebGl2RenderingContext, WebGlProgram, WebGlUniformLocation};

use rource_math::{Bounds, Color, Mat4, Vec2};

use crate::{FontCache, FontId, Renderer, TextureId};

use bloom::BloomPipeline;
use buffers::{InstanceBuffer, VertexArrayManager};
use shaders::{
    CIRCLE_FRAGMENT_SHADER, CIRCLE_VERTEX_SHADER, CIRCLE_VERTEX_SHADER_UBO, CURVE_FRAGMENT_SHADER,
    CURVE_VERTEX_SHADER, CURVE_VERTEX_SHADER_UBO, LINE_FRAGMENT_SHADER, LINE_VERTEX_SHADER,
    LINE_VERTEX_SHADER_UBO, QUAD_FRAGMENT_SHADER, QUAD_VERTEX_SHADER, QUAD_VERTEX_SHADER_UBO,
    RING_FRAGMENT_SHADER, RING_VERTEX_SHADER, RING_VERTEX_SHADER_UBO,
    TEXTURED_QUAD_FRAGMENT_SHADER, TEXTURED_QUAD_VERTEX_SHADER, TEXTURED_QUAD_VERTEX_SHADER_UBO,
    TEXTURE_ARRAY_FRAGMENT_SHADER, TEXTURE_ARRAY_VERTEX_SHADER, TEXTURE_ARRAY_VERTEX_SHADER_UBO,
    TEXT_FRAGMENT_SHADER, TEXT_VERTEX_SHADER, TEXT_VERTEX_SHADER_UBO,
};
use shadow::ShadowPipeline;
use state::GlStateCache;
use texture_array::TextureArray;
use textures::{FontAtlas, GlyphKey, TextureManager};
use ubo::UniformBufferManager;

// Re-export post-processing configuration for external use
pub use adaptive::{AdaptiveQuality, QualityAdjustment, QualityLevel};
pub use bloom::{BloomConfig, BloomPipeline as BloomEffect};
pub use error::WebGl2Error;
pub use shadow::{ShadowConfig, ShadowPipeline as ShadowEffect};
pub use stats::FrameStats;

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

    /// Texture array shader program (for file icons).
    texture_array_program: Option<ShaderProgram>,

    /// Curve shader program (GPU-tessellated splines).
    curve_program: Option<ShaderProgram>,

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

    /// Instance buffer for file icons (texture array rendering).
    file_icon_instances: InstanceBuffer,

    /// Instance buffer for curves (GPU-tessellated splines).
    curve_instances: InstanceBuffer,

    /// GPU bloom post-processing pipeline.
    bloom_pipeline: BloomPipeline,

    /// GPU shadow post-processing pipeline.
    shadow_pipeline: ShadowPipeline,

    /// Adaptive quality controller for auto-adjusting effect parameters.
    adaptive_quality: AdaptiveQuality,

    /// GPU state cache for avoiding redundant API calls.
    state_cache: GlStateCache,

    /// Uniform Buffer Object manager for shared uniforms.
    ubo_manager: UniformBufferManager,

    /// Whether UBO mode is active (uses UBO shaders instead of legacy).
    ubo_enabled: bool,

    /// Frame statistics for debugging and profiling.
    frame_stats: FrameStats,

    /// Whether context was lost.
    context_lost: bool,

    /// Reusable buffer for texture IDs (avoids per-frame allocation in `flush_textured_quads`).
    cached_texture_ids: Vec<TextureId>,

    /// Reusable buffer for transformed spline points (avoids per-draw_spline allocation).
    spline_points_buf: Vec<Vec2>,

    /// File icon texture array (optional, initialized via `init_file_icons`).
    file_icon_array: Option<TextureArray>,
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
            texture_array_program: None,
            curve_program: None,
            vao_manager: VertexArrayManager::new(),
            circle_instances: InstanceBuffer::new(7, 1000), // center(2) + radius(1) + color(4)
            ring_instances: InstanceBuffer::new(8, 500), // center(2) + radius(1) + width(1) + color(4)
            line_instances: InstanceBuffer::new(9, 1000), // start(2) + end(2) + width(1) + color(4)
            quad_instances: InstanceBuffer::new(8, 500), // bounds(4) + color(4)
            textured_quad_instances: HashMap::new(),
            text_instances: InstanceBuffer::new(12, 2000), // bounds(4) + uv_bounds(4) + color(4)
            file_icon_instances: InstanceBuffer::new(13, 1000), // bounds(4) + uv_bounds(4) + color(4) + layer(1)
            curve_instances: InstanceBuffer::new(13, 500), // p0(2) + p1(2) + p2(2) + p3(2) + width(1) + color(4)
            bloom_pipeline: BloomPipeline::new(),
            shadow_pipeline: ShadowPipeline::new(),
            adaptive_quality: AdaptiveQuality::new(),
            state_cache: GlStateCache::new(),
            ubo_manager: UniformBufferManager::new(),
            ubo_enabled: false,
            frame_stats: FrameStats::new(),
            context_lost: false,
            cached_texture_ids: Vec::with_capacity(16),
            // Pre-allocate spline buffer for typical curve complexity (16 control points)
            spline_points_buf: Vec::with_capacity(16),
            file_icon_array: None,
        };

        renderer.init_gl()?;

        // Initialize bloom pipeline (non-fatal if it fails)
        if !renderer.bloom_pipeline.initialize(&renderer.gl) {
            web_sys::console::warn_1(&"Rource: Bloom pipeline initialization failed".into());
        }

        // Initialize shadow pipeline (non-fatal if it fails)
        if !renderer.shadow_pipeline.initialize(&renderer.gl) {
            web_sys::console::warn_1(&"Rource: Shadow pipeline initialization failed".into());
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

        // Try to initialize UBO system
        // UBO mode reduces uniform API calls from ~12/frame to 1/frame
        self.ubo_enabled = self.ubo_manager.initialize(gl);

        if self.ubo_enabled {
            // Use UBO-enabled shaders
            self.circle_program =
                Some(self.compile_program(CIRCLE_VERTEX_SHADER_UBO, CIRCLE_FRAGMENT_SHADER)?);
            self.ring_program =
                Some(self.compile_program(RING_VERTEX_SHADER_UBO, RING_FRAGMENT_SHADER)?);
            self.line_program =
                Some(self.compile_program(LINE_VERTEX_SHADER_UBO, LINE_FRAGMENT_SHADER)?);
            self.quad_program =
                Some(self.compile_program(QUAD_VERTEX_SHADER_UBO, QUAD_FRAGMENT_SHADER)?);
            self.textured_quad_program = Some(self.compile_program(
                TEXTURED_QUAD_VERTEX_SHADER_UBO,
                TEXTURED_QUAD_FRAGMENT_SHADER,
            )?);
            self.text_program =
                Some(self.compile_program(TEXT_VERTEX_SHADER_UBO, TEXT_FRAGMENT_SHADER)?);
            self.texture_array_program = Some(self.compile_program(
                TEXTURE_ARRAY_VERTEX_SHADER_UBO,
                TEXTURE_ARRAY_FRAGMENT_SHADER,
            )?);
            self.curve_program =
                Some(self.compile_program(CURVE_VERTEX_SHADER_UBO, CURVE_FRAGMENT_SHADER)?);

            // Bind each shader's uniform block to the UBO binding point
            // This is required in WebGL2/GLSL ES 3.0 since layout(binding = N) is not supported
            if let Some(prog) = &self.circle_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
            if let Some(prog) = &self.ring_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
            if let Some(prog) = &self.line_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
            if let Some(prog) = &self.quad_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
            if let Some(prog) = &self.textured_quad_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
            if let Some(prog) = &self.text_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
            if let Some(prog) = &self.texture_array_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
            if let Some(prog) = &self.curve_program {
                self.ubo_manager.bind_program(gl, &prog.program);
            }
        } else {
            // Fallback to legacy shaders with individual uniforms
            self.circle_program =
                Some(self.compile_program(CIRCLE_VERTEX_SHADER, CIRCLE_FRAGMENT_SHADER)?);
            self.ring_program =
                Some(self.compile_program(RING_VERTEX_SHADER, RING_FRAGMENT_SHADER)?);
            self.line_program =
                Some(self.compile_program(LINE_VERTEX_SHADER, LINE_FRAGMENT_SHADER)?);
            self.quad_program =
                Some(self.compile_program(QUAD_VERTEX_SHADER, QUAD_FRAGMENT_SHADER)?);
            self.textured_quad_program = Some(
                self.compile_program(TEXTURED_QUAD_VERTEX_SHADER, TEXTURED_QUAD_FRAGMENT_SHADER)?,
            );
            self.text_program =
                Some(self.compile_program(TEXT_VERTEX_SHADER, TEXT_FRAGMENT_SHADER)?);
            self.texture_array_program = Some(
                self.compile_program(TEXTURE_ARRAY_VERTEX_SHADER, TEXTURE_ARRAY_FRAGMENT_SHADER)?,
            );
            self.curve_program =
                Some(self.compile_program(CURVE_VERTEX_SHADER, CURVE_FRAGMENT_SHADER)?);
        }

        // Create VAO manager vertex buffer
        self.vao_manager.create_vertex_buffer(gl);

        // Warmup all shaders to eliminate first-frame stutters
        self.warmup_shaders();

        Ok(())
    }

    /// Warms up all shader programs by performing zero-instance draws.
    ///
    /// GPU shader compilation often happens lazily when a program is first used
    /// with actual draw calls. This can cause visible stutters on the first frame
    /// where each primitive type is drawn. By performing warmup draws during
    /// initialization, we move this compilation cost to the startup phase.
    ///
    /// The warmup consists of:
    /// 1. Using each shader program
    /// 2. Setting all uniforms with valid values
    /// 3. Binding the appropriate VAO
    /// 4. Issuing a zero-instance draw call to trigger GPU compilation
    ///
    /// This technique is especially important for WebGL where shader compilation
    /// can be deferred until the first draw call, and GPU drivers may perform
    /// additional optimizations on first use.
    #[allow(clippy::too_many_lines)]
    fn warmup_shaders(&mut self) {
        let gl = &self.gl;

        // Use a default resolution for warmup
        let warmup_width = self.width.max(1) as f32;
        let warmup_height = self.height.max(1) as f32;

        // Ensure VAOs are created for warmup draws
        // We need to create minimal instance buffers and upload dummy data
        // to set up the VAO attribute pointers correctly

        // Create temporary instance buffers with minimal data for VAO setup
        self.circle_instances
            .push_raw(&[0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0]);
        self.circle_instances.upload(gl);
        self.vao_manager
            .setup_circle_vao(gl, &self.circle_instances);
        self.circle_instances.clear();

        self.ring_instances
            .push_raw(&[0.0, 0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0]);
        self.ring_instances.upload(gl);
        self.vao_manager.setup_ring_vao(gl, &self.ring_instances);
        self.ring_instances.clear();

        self.line_instances
            .push_raw(&[0.0, 0.0, 1.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0]);
        self.line_instances.upload(gl);
        self.vao_manager.setup_line_vao(gl, &self.line_instances);
        self.line_instances.clear();

        self.quad_instances
            .push_raw(&[0.0, 0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0]);
        self.quad_instances.upload(gl);
        self.vao_manager.setup_quad_vao(gl, &self.quad_instances);
        self.quad_instances.clear();

        self.text_instances
            .push_raw(&[0.0, 0.0, 1.0, 1.0, 0.0, 0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0]);
        self.text_instances.upload(gl);
        self.vao_manager
            .setup_textured_vao(gl, &self.text_instances);
        // Move textured VAO to text VAO and recreate textured
        self.vao_manager.text_vao = self.vao_manager.textured_quad_vao.take();
        self.text_instances.clear();

        // Setup file icon instance buffer (13 floats: bounds(4) + uv_bounds(4) + color(4) + layer(1))
        self.file_icon_instances.push_raw(&[
            0.0, 0.0, 1.0, 1.0, // bounds
            0.0, 0.0, 1.0, 1.0, // uv_bounds
            0.0, 0.0, 0.0, 0.0, // color
            0.0, // layer
        ]);
        self.file_icon_instances.upload(gl);
        self.vao_manager
            .setup_texture_array_vao(gl, &self.file_icon_instances);
        self.file_icon_instances.clear();

        // Setup curve instance buffer (13 floats: p0(2) + p1(2) + p2(2) + p3(2) + width(1) + color(4))
        self.curve_instances.push_raw(&[
            0.0, 0.0, // p0
            0.0, 0.0, // p1
            1.0, 1.0, // p2
            1.0, 1.0, // p3
            1.0, // width
            0.0, 0.0, 0.0, 0.0, // color
        ]);
        self.curve_instances.upload(gl);
        self.vao_manager.setup_curve_vao(gl, &self.curve_instances);
        self.curve_instances.clear();

        // Setup fullscreen VAO for bloom/shadow warmup
        self.vao_manager.setup_fullscreen_vao(gl);

        // Warmup circle shader
        if let Some(program) = &self.circle_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            gl.bind_vertex_array(self.vao_manager.circle_vao.as_ref());
            // Zero-instance draw triggers GPU shader compilation without rendering anything
            gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, 0);
        }

        // Warmup ring shader
        if let Some(program) = &self.ring_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            gl.bind_vertex_array(self.vao_manager.ring_vao.as_ref());
            gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, 0);
        }

        // Warmup line shader
        if let Some(program) = &self.line_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            gl.bind_vertex_array(self.vao_manager.line_vao.as_ref());
            gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, 0);
        }

        // Warmup quad shader
        if let Some(program) = &self.quad_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            gl.bind_vertex_array(self.vao_manager.quad_vao.as_ref());
            gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, 0);
        }

        // Warmup textured quad shader (creates its own VAO on demand, but we can warmup the program)
        if let Some(program) = &self.textured_quad_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0);
            }
            // No draw call since we don't have a textured VAO yet (created on demand)
        }

        // Warmup text shader
        if let Some(program) = &self.text_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0);
            }
            gl.bind_vertex_array(self.vao_manager.text_vao.as_ref());
            gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, 0);
        }

        // Warmup texture array shader (for file icons)
        if let Some(program) = &self.texture_array_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0);
            }
            gl.bind_vertex_array(self.vao_manager.texture_array_vao.as_ref());
            gl.draw_arrays_instanced(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4, 0);
        }

        // Warmup curve shader (GPU-tessellated splines)
        if let Some(program) = &self.curve_program {
            gl.use_program(Some(&program.program));
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), warmup_width, warmup_height);
            }
            gl.bind_vertex_array(self.vao_manager.curve_vao.as_ref());
            gl.draw_arrays_instanced(
                WebGl2RenderingContext::TRIANGLE_STRIP,
                0,
                buffers::CURVE_STRIP_VERTEX_COUNT as i32,
                0,
            );
        }

        // Cleanup warmup state
        gl.bind_vertex_array(None);
        gl.use_program(None);
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

        // Invalidate UBO state (must be re-initialized)
        self.ubo_manager.invalidate();

        // Reinitialize GL state (will re-initialize UBO)
        self.init_gl()?;

        // Clear font atlas (glyphs need to be re-cached)
        self.font_atlas.clear();

        // Invalidate state cache (all GPU state is stale after context loss)
        self.state_cache.invalidate();

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

        // Reinitialize shadow pipeline
        let shadow_config = self.shadow_pipeline.config;
        self.shadow_pipeline.destroy(&self.gl);
        self.shadow_pipeline = ShadowPipeline::new();
        self.shadow_pipeline.config = shadow_config;
        if !self.shadow_pipeline.initialize(&self.gl) {
            web_sys::console::warn_1(
                &"Rource: Shadow pipeline re-initialization failed after context recovery".into(),
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

    /// Returns whether UBO mode is enabled.
    ///
    /// When enabled, shaders use Uniform Buffer Objects for the `u_resolution`
    /// uniform instead of individual uniform calls. This reduces API overhead
    /// by ~90% for uniform-related calls.
    ///
    /// UBO mode is enabled by default on all WebGL2-capable browsers.
    #[inline]
    pub fn is_ubo_enabled(&self) -> bool {
        self.ubo_enabled
    }

    /// Returns statistics from the last rendered frame.
    ///
    /// These statistics are useful for debugging and performance profiling.
    /// Call this after `end_frame()` to get accurate metrics for the
    /// most recently completed frame.
    #[inline]
    pub fn frame_stats(&self) -> &FrameStats {
        &self.frame_stats
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

        // Reset frame statistics
        self.frame_stats.reset();
        self.frame_stats.ubo_enabled = self.ubo_enabled;

        // Initialize state cache for this frame
        self.state_cache.begin_frame(self.width, self.height);

        // Update and bind UBO if enabled
        if self.ubo_enabled {
            self.ubo_manager
                .set_resolution(self.width as f32, self.height as f32);
            self.ubo_manager.upload(&self.gl);
            self.ubo_manager.bind(&self.gl);
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

        // If bloom or shadow is active, render to scene FBO instead of canvas
        // Both effects use the bloom pipeline's scene FBO for the source
        let needs_scene_fbo =
            self.bloom_pipeline.config.enabled || self.shadow_pipeline.config.enabled;

        if needs_scene_fbo {
            // Ensure bloom FBOs are sized correctly (even if only shadow is enabled)
            // Shadow uses bloom's scene FBO as input
            if self
                .bloom_pipeline
                .ensure_size(&self.gl, self.width, self.height)
            {
                self.bloom_pipeline.bind_scene_fbo(&self.gl);
                self.gl
                    .viewport(0, 0, self.width as i32, self.height as i32);
            }

            // Also ensure shadow FBOs are sized if shadow is enabled
            if self.shadow_pipeline.config.enabled {
                self.shadow_pipeline
                    .ensure_size(&self.gl, self.width, self.height);
            }
        }
    }

    fn end_frame(&mut self) {
        if self.context_lost {
            return;
        }

        // Flush all batched draw calls to the GPU
        self.flush();

        // Post-processing effects use their own programs, so invalidate cache
        let bloom_active = self.bloom_pipeline.is_active();
        let shadow_active = self.shadow_pipeline.is_active();
        let needs_post_processing = bloom_active || shadow_active;

        if needs_post_processing {
            self.state_cache.invalidate_program();
        }

        // Combined bloom+shadow or standalone effects
        if bloom_active && shadow_active {
            // Combined pipeline: shadow is applied first, then bloom on top
            // The bloom pipeline's scene FBO contains the rendered scene.
            // We apply shadow effect first (renders shadow behind scene),
            // then apply bloom on the combined result.
            //
            // Implementation approach:
            // 1. Shadow renders to its own FBO using bloom's scene texture
            // 2. Bloom composites everything together
            //
            // For now, bloom takes precedence as shadow+bloom combined
            // requires rendering shadow to an intermediate FBO that bloom
            // can then use. This is a future enhancement.
            self.bloom_pipeline.apply(&self.gl, &mut self.vao_manager);
            self.frame_stats.bloom_applied = true;
            // Note: Shadow is skipped when bloom is active (future: combined pipeline)
        } else if shadow_active {
            // Shadow-only: apply shadow pipeline
            if let Some(scene_texture) = self.bloom_pipeline.scene_texture() {
                let (scene_width, scene_height) = self.bloom_pipeline.scene_size();
                self.shadow_pipeline.apply(
                    &self.gl,
                    scene_texture,
                    scene_width,
                    scene_height,
                    &mut self.vao_manager,
                );
                self.frame_stats.shadow_applied = true;
            }
        } else if bloom_active {
            // Bloom-only: apply bloom pipeline
            self.bloom_pipeline.apply(&self.gl, &mut self.vao_manager);
            self.frame_stats.bloom_applied = true;
        }

        // Re-enable blending after post-processing
        if needs_post_processing {
            self.gl.enable(WebGl2RenderingContext::BLEND);
            self.gl.blend_func(
                WebGl2RenderingContext::SRC_ALPHA,
                WebGl2RenderingContext::ONE_MINUS_SRC_ALPHA,
            );
        }

        // Unbind VAO at end of frame for clean state
        self.state_cache.unbind_vao(&self.gl);

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

    #[inline]
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

    #[inline]
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

    #[inline]
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

    #[inline]
    fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color) {
        if self.context_lost || color.a < 0.001 {
            return;
        }

        if points.len() < 2 {
            return;
        }

        // Transform all points to screen space using reusable buffer (avoids heap allocation)
        self.spline_points_buf.clear();
        for p in points {
            self.spline_points_buf.push(self.transform_point(*p));
        }

        // For each segment, queue a curve instance with 4 control points
        // Using Catmull-Rom spline, the segment between p1 and p2 is interpolated
        // using p0 and p3 as control points
        let transformed = &self.spline_points_buf;
        for i in 0..(transformed.len() - 1) {
            // Get the 4 control points (clamping at edges)
            let p0 = if i == 0 {
                // Mirror first point: p0 = 2*p1 - p2
                Vec2::new(
                    2.0 * transformed[0].x - transformed[1].x,
                    2.0 * transformed[0].y - transformed[1].y,
                )
            } else {
                transformed[i - 1]
            };
            let p1 = transformed[i];
            let p2 = transformed[i + 1];
            let p3 = if i + 2 >= transformed.len() {
                // Mirror last point: p3 = 2*p2 - p1
                Vec2::new(
                    2.0 * transformed[i + 1].x - transformed[i].x,
                    2.0 * transformed[i + 1].y - transformed[i].y,
                )
            } else {
                transformed[i + 2]
            };

            // Queue curve segment instance: p0(2) + p1(2) + p2(2) + p3(2) + width(1) + color(4)
            self.curve_instances.push_raw(&[
                p0.x, p0.y, // p0
                p1.x, p1.y, // p1
                p2.x, p2.y, // p2
                p3.x, p3.y,  // p3
                width, // width
                color.r, color.g, color.b, color.a,
            ]);
        }
    }

    #[inline]
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

    #[inline]
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
        // Flush before changing transform to ensure buffered primitives
        // are rendered with the current transform
        let has_textured_quads = self
            .textured_quad_instances
            .values()
            .any(|buf| buf.instance_count() > 0);

        if self.circle_instances.instance_count() > 0
            || self.ring_instances.instance_count() > 0
            || self.line_instances.instance_count() > 0
            || self.quad_instances.instance_count() > 0
            || self.text_instances.instance_count() > 0
            || has_textured_quads
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

    // =========================================================================
    // File Icon Methods (uses texture array when initialized)
    // =========================================================================

    fn init_file_icons(&mut self) -> bool {
        // Delegate to the implementation in icons_methods.rs
        Self::init_file_icons(self)
    }

    fn has_file_icons(&self) -> bool {
        // Delegate to the implementation in icons_methods.rs
        Self::has_file_icons(self)
    }

    fn draw_file_icon(&mut self, center: Vec2, size: f32, _extension: &str, color: Color) {
        // Use colored disc - cleaner, scales better, more modern look.
        // File icon texture array infrastructure is retained for future use
        // (e.g., high-quality devicons integration) but disabled by default.
        self.draw_disc(center, size * 0.5, color);
    }
}

impl Drop for WebGl2Renderer {
    fn drop(&mut self) {
        // Clean up WebGL resources
        self.vao_manager.destroy(&self.gl);
        self.font_atlas.destroy(&self.gl);
        self.texture_manager.destroy(&self.gl);
        self.ubo_manager.destroy(&self.gl);
        self.circle_instances.destroy(&self.gl);
        self.ring_instances.destroy(&self.gl);
        self.line_instances.destroy(&self.gl);
        self.quad_instances.destroy(&self.gl);
        for instances in self.textured_quad_instances.values_mut() {
            instances.destroy(&self.gl);
        }
        self.text_instances.destroy(&self.gl);
        self.file_icon_instances.destroy(&self.gl);
        self.curve_instances.destroy(&self.gl);

        // Clean up file icon texture array
        if let Some(mut array) = self.file_icon_array.take() {
            array.destroy(&self.gl);
        }

        // Clean up post-processing pipelines (FBOs, textures, shader programs)
        self.bloom_pipeline.destroy(&self.gl);
        self.shadow_pipeline.destroy(&self.gl);

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
        if let Some(prog) = &self.texture_array_program {
            self.gl.delete_program(Some(&prog.program));
        }
        if let Some(prog) = &self.curve_program {
            self.gl.delete_program(Some(&prog.program));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
