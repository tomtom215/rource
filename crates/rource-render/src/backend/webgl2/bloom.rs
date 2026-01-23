// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! GPU bloom effect implementation for WebGL2.
//!
//! This module provides a high-performance GPU-based bloom effect that creates
//! a glow around bright areas of the rendered scene. The implementation uses
//! framebuffer objects (FBOs) for render-to-texture operations.
//!
//! ## Pipeline
//!
//! The bloom effect is implemented as a multi-pass post-processing pipeline:
//!
//! 1. **Scene Render**: Scene is rendered to the scene FBO instead of directly to canvas
//! 2. **Bright Pass**: Extract pixels above brightness threshold to bloom FBO
//! 3. **Blur Pass (H)**: Horizontal Gaussian blur on bloom FBO
//! 4. **Blur Pass (V)**: Vertical Gaussian blur (ping-pong to second FBO)
//! 5. **Composite**: Additively blend bloom with original scene to canvas
//!
//! ## Performance
//!
//! - Bloom is rendered at configurable downscale (default 4x) for efficiency
//! - Separable Gaussian blur (two 1D passes instead of one 2D pass)
//! - Lazy FBO creation - resources allocated only when bloom is enabled
//! - Automatic resize handling when viewport dimensions change
//!
//! ## Usage
//!
//! ```ignore
//! // Enable bloom in the renderer
//! renderer.set_bloom_enabled(true);
//! renderer.set_bloom_threshold(0.7);
//! renderer.set_bloom_intensity(1.0);
//!
//! // Bloom is automatically applied during end_frame()
//! ```

use web_sys::{
    WebGl2RenderingContext, WebGlFramebuffer, WebGlProgram, WebGlTexture, WebGlUniformLocation,
};

use super::buffers::VertexArrayManager;

// ============================================================================
// Constants
// ============================================================================

/// Default brightness threshold for bloom extraction.
/// Pixels brighter than this value will contribute to the bloom effect.
pub const DEFAULT_BLOOM_THRESHOLD: f32 = 0.7;

/// Default bloom intensity multiplier.
pub const DEFAULT_BLOOM_INTENSITY: f32 = 1.0;

/// Default downscale factor for bloom buffers.
/// Higher values = faster but blockier bloom.
pub const DEFAULT_BLOOM_DOWNSCALE: u32 = 4;

/// Number of blur passes (each pass = horizontal + vertical).
/// More passes = softer, more spread bloom.
pub const DEFAULT_BLOOM_PASSES: u32 = 2;

// ============================================================================
// Bloom Configuration
// ============================================================================

/// Configuration for the GPU bloom effect.
#[derive(Debug, Clone, Copy)]
pub struct BloomConfig {
    /// Whether bloom effect is enabled.
    pub enabled: bool,

    /// Brightness threshold (0.0 - 1.0).
    /// Pixels brighter than this will bloom.
    pub threshold: f32,

    /// Bloom intensity multiplier.
    /// Higher values = brighter glow.
    pub intensity: f32,

    /// Downscale factor for bloom buffers.
    /// Higher values = faster but lower quality.
    pub downscale: u32,

    /// Number of blur passes.
    /// More passes = softer bloom.
    pub passes: u32,
}

impl Default for BloomConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            threshold: DEFAULT_BLOOM_THRESHOLD,
            intensity: DEFAULT_BLOOM_INTENSITY,
            downscale: DEFAULT_BLOOM_DOWNSCALE,
            passes: DEFAULT_BLOOM_PASSES,
        }
    }
}

impl BloomConfig {
    /// Creates a new bloom configuration with default values.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a subtle bloom configuration.
    #[must_use]
    pub fn subtle() -> Self {
        Self {
            enabled: true,
            threshold: 0.8,
            intensity: 0.5,
            downscale: 4,
            passes: 1,
        }
    }

    /// Creates an intense bloom configuration.
    #[must_use]
    pub fn intense() -> Self {
        Self {
            enabled: true,
            threshold: 0.5,
            intensity: 2.0,
            downscale: 2,
            passes: 3,
        }
    }
}

// ============================================================================
// Bloom Shader Programs
// ============================================================================

/// Compiled shader program with uniform locations for bloom passes.
pub struct BloomProgram {
    /// The compiled WebGL program.
    pub program: WebGlProgram,

    /// Uniform: input texture sampler.
    pub texture_loc: Option<WebGlUniformLocation>,

    /// Uniform: brightness threshold (bright pass only).
    pub threshold_loc: Option<WebGlUniformLocation>,

    /// Uniform: bloom intensity.
    pub intensity_loc: Option<WebGlUniformLocation>,

    /// Uniform: blur direction vector (blur pass only).
    pub direction_loc: Option<WebGlUniformLocation>,

    /// Uniform: texture resolution for texel size calculation.
    pub resolution_loc: Option<WebGlUniformLocation>,

    /// Uniform: scene texture sampler (composite pass only).
    pub scene_loc: Option<WebGlUniformLocation>,

    /// Uniform: bloom texture sampler (composite pass only).
    pub bloom_loc: Option<WebGlUniformLocation>,
}

// ============================================================================
// Framebuffer Object
// ============================================================================

/// A framebuffer object with an attached color texture.
///
/// Used for render-to-texture operations in the bloom pipeline.
pub struct BloomFbo {
    /// The WebGL framebuffer object.
    framebuffer: Option<WebGlFramebuffer>,

    /// The attached color texture.
    texture: Option<WebGlTexture>,

    /// Texture width in pixels.
    width: u32,

    /// Texture height in pixels.
    height: u32,
}

impl BloomFbo {
    /// Creates a new uninitialized FBO.
    pub fn new() -> Self {
        Self {
            framebuffer: None,
            texture: None,
            width: 0,
            height: 0,
        }
    }

    /// Returns whether the FBO is initialized.
    #[inline]
    pub fn is_initialized(&self) -> bool {
        self.framebuffer.is_some() && self.texture.is_some()
    }

    /// Returns the texture width.
    #[inline]
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Returns the texture height.
    #[inline]
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Initializes or resizes the FBO to the specified dimensions.
    ///
    /// This method is idempotent - calling it with the same dimensions is a no-op.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `width` - Texture width in pixels
    /// * `height` - Texture height in pixels
    ///
    /// # Returns
    ///
    /// `true` if initialization/resize succeeded, `false` otherwise.
    pub fn ensure_size(&mut self, gl: &WebGl2RenderingContext, width: u32, height: u32) -> bool {
        // Skip if already the correct size
        if self.is_initialized() && self.width == width && self.height == height {
            return true;
        }

        // Clean up existing resources
        self.destroy(gl);

        // Create framebuffer
        let Some(framebuffer) = gl.create_framebuffer() else {
            return false;
        };

        // Create texture
        let Some(texture) = gl.create_texture() else {
            gl.delete_framebuffer(Some(&framebuffer));
            return false;
        };

        // Configure texture
        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(&texture));

        // Allocate texture storage (RGBA8 for color)
        gl.tex_image_2d_with_i32_and_i32_and_i32_and_format_and_type_and_opt_u8_array(
            WebGl2RenderingContext::TEXTURE_2D,
            0,                                    // mip level
            WebGl2RenderingContext::RGBA8 as i32, // internal format
            width as i32,
            height as i32,
            0,                                     // border (must be 0)
            WebGl2RenderingContext::RGBA,          // format
            WebGl2RenderingContext::UNSIGNED_BYTE, // type
            None,                                  // no initial data
        )
        .ok();

        // Set texture parameters for FBO usage
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D,
            WebGl2RenderingContext::TEXTURE_MIN_FILTER,
            WebGl2RenderingContext::LINEAR as i32,
        );
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D,
            WebGl2RenderingContext::TEXTURE_MAG_FILTER,
            WebGl2RenderingContext::LINEAR as i32,
        );
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D,
            WebGl2RenderingContext::TEXTURE_WRAP_S,
            WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
        );
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D,
            WebGl2RenderingContext::TEXTURE_WRAP_T,
            WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
        );

        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, None);

        // Attach texture to framebuffer
        gl.bind_framebuffer(WebGl2RenderingContext::FRAMEBUFFER, Some(&framebuffer));
        gl.framebuffer_texture_2d(
            WebGl2RenderingContext::FRAMEBUFFER,
            WebGl2RenderingContext::COLOR_ATTACHMENT0,
            WebGl2RenderingContext::TEXTURE_2D,
            Some(&texture),
            0,
        );

        // Check framebuffer completeness
        let status = gl.check_framebuffer_status(WebGl2RenderingContext::FRAMEBUFFER);
        gl.bind_framebuffer(WebGl2RenderingContext::FRAMEBUFFER, None);

        if status != WebGl2RenderingContext::FRAMEBUFFER_COMPLETE {
            gl.delete_framebuffer(Some(&framebuffer));
            gl.delete_texture(Some(&texture));
            return false;
        }

        self.framebuffer = Some(framebuffer);
        self.texture = Some(texture);
        self.width = width;
        self.height = height;

        true
    }

    /// Binds this FBO as the render target.
    #[inline]
    pub fn bind(&self, gl: &WebGl2RenderingContext) {
        gl.bind_framebuffer(
            WebGl2RenderingContext::FRAMEBUFFER,
            self.framebuffer.as_ref(),
        );
    }

    /// Binds the FBO's texture to a texture unit.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `unit` - Texture unit (0-15)
    #[inline]
    pub fn bind_texture(&self, gl: &WebGl2RenderingContext, unit: u32) {
        gl.active_texture(WebGl2RenderingContext::TEXTURE0 + unit);
        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, self.texture.as_ref());
    }

    /// Releases all WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        if let Some(fb) = self.framebuffer.take() {
            gl.delete_framebuffer(Some(&fb));
        }
        if let Some(tex) = self.texture.take() {
            gl.delete_texture(Some(&tex));
        }
        self.width = 0;
        self.height = 0;
    }
}

impl Default for BloomFbo {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Bloom Pipeline
// ============================================================================

/// GPU bloom effect pipeline.
///
/// Manages all resources needed for the bloom post-processing effect:
/// - Framebuffer objects for render-to-texture
/// - Shader programs for each pass
/// - Configuration state
pub struct BloomPipeline {
    /// Bloom configuration.
    pub config: BloomConfig,

    /// FBO for the scene render (full resolution).
    scene_fbo: BloomFbo,

    /// FBO for bloom pass A (downscaled).
    bloom_fbo_a: BloomFbo,

    /// FBO for bloom pass B (downscaled, ping-pong target).
    bloom_fbo_b: BloomFbo,

    /// Bright pass shader program.
    bright_program: Option<BloomProgram>,

    /// Blur pass shader program.
    blur_program: Option<BloomProgram>,

    /// Composite pass shader program.
    composite_program: Option<BloomProgram>,

    /// Cached full resolution (width, height).
    cached_size: (u32, u32),

    /// Whether the pipeline is initialized.
    initialized: bool,
}

impl BloomPipeline {
    /// Creates a new bloom pipeline with default configuration.
    pub fn new() -> Self {
        Self {
            config: BloomConfig::default(),
            scene_fbo: BloomFbo::new(),
            bloom_fbo_a: BloomFbo::new(),
            bloom_fbo_b: BloomFbo::new(),
            bright_program: None,
            blur_program: None,
            composite_program: None,
            cached_size: (0, 0),
            initialized: false,
        }
    }

    /// Returns whether bloom is enabled and the pipeline is ready.
    #[inline]
    pub fn is_active(&self) -> bool {
        self.config.enabled && self.initialized
    }

    /// Initializes the bloom pipeline.
    ///
    /// This compiles shaders and prepares the pipeline for rendering.
    /// FBOs are created lazily when `ensure_size` is called.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    ///
    /// # Returns
    ///
    /// `true` if initialization succeeded, `false` otherwise.
    pub fn initialize(&mut self, gl: &WebGl2RenderingContext) -> bool {
        use super::shaders::{
            BLOOM_BLUR_FRAGMENT_SHADER, BLOOM_BRIGHT_FRAGMENT_SHADER,
            BLOOM_COMPOSITE_FRAGMENT_SHADER, BLOOM_VERTEX_SHADER,
        };

        // Compile bright pass program
        self.bright_program =
            Self::compile_program(gl, BLOOM_VERTEX_SHADER, BLOOM_BRIGHT_FRAGMENT_SHADER).map(
                |program| BloomProgram {
                    texture_loc: gl.get_uniform_location(&program, "u_texture"),
                    threshold_loc: gl.get_uniform_location(&program, "u_threshold"),
                    intensity_loc: gl.get_uniform_location(&program, "u_intensity"),
                    direction_loc: None,
                    resolution_loc: None,
                    scene_loc: None,
                    bloom_loc: None,
                    program,
                },
            );

        if self.bright_program.is_none() {
            return false;
        }

        // Compile blur pass program
        self.blur_program =
            Self::compile_program(gl, BLOOM_VERTEX_SHADER, BLOOM_BLUR_FRAGMENT_SHADER).map(
                |program| BloomProgram {
                    texture_loc: gl.get_uniform_location(&program, "u_texture"),
                    threshold_loc: None,
                    intensity_loc: None,
                    direction_loc: gl.get_uniform_location(&program, "u_direction"),
                    // Use u_texel_size instead of u_resolution to avoid per-fragment division
                    resolution_loc: gl.get_uniform_location(&program, "u_texel_size"),
                    scene_loc: None,
                    bloom_loc: None,
                    program,
                },
            );

        if self.blur_program.is_none() {
            return false;
        }

        // Compile composite pass program
        self.composite_program =
            Self::compile_program(gl, BLOOM_VERTEX_SHADER, BLOOM_COMPOSITE_FRAGMENT_SHADER).map(
                |program| BloomProgram {
                    texture_loc: None,
                    threshold_loc: None,
                    intensity_loc: gl.get_uniform_location(&program, "u_intensity"),
                    direction_loc: None,
                    resolution_loc: None,
                    scene_loc: gl.get_uniform_location(&program, "u_scene"),
                    bloom_loc: gl.get_uniform_location(&program, "u_bloom"),
                    program,
                },
            );

        if self.composite_program.is_none() {
            return false;
        }

        self.initialized = true;
        true
    }

    /// Ensures FBOs are sized correctly for the viewport.
    ///
    /// Call this when the viewport size changes or before rendering.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `width` - Viewport width in pixels
    /// * `height` - Viewport height in pixels
    ///
    /// # Returns
    ///
    /// `true` if all FBOs are ready, `false` otherwise.
    pub fn ensure_size(&mut self, gl: &WebGl2RenderingContext, width: u32, height: u32) -> bool {
        if !self.initialized || !self.config.enabled {
            return false;
        }

        // Check if size unchanged
        if self.cached_size == (width, height) && self.scene_fbo.is_initialized() {
            return true;
        }

        self.cached_size = (width, height);

        // Scene FBO at full resolution
        if !self.scene_fbo.ensure_size(gl, width, height) {
            return false;
        }

        // Bloom FBOs at downscaled resolution
        let bloom_width = (width / self.config.downscale).max(1);
        let bloom_height = (height / self.config.downscale).max(1);

        if !self.bloom_fbo_a.ensure_size(gl, bloom_width, bloom_height) {
            return false;
        }

        if !self.bloom_fbo_b.ensure_size(gl, bloom_width, bloom_height) {
            return false;
        }

        true
    }

    /// Binds the scene FBO for rendering.
    ///
    /// Call this at the start of frame rendering to capture the scene.
    #[inline]
    pub fn bind_scene_fbo(&self, gl: &WebGl2RenderingContext) {
        self.scene_fbo.bind(gl);
    }

    /// Returns a reference to the scene FBO texture.
    ///
    /// This is used by other post-processing effects (like shadow) that need
    /// access to the rendered scene.
    #[inline]
    pub fn scene_texture(&self) -> Option<&WebGlTexture> {
        self.scene_fbo.texture.as_ref()
    }

    /// Returns the scene FBO dimensions.
    #[inline]
    pub fn scene_size(&self) -> (u32, u32) {
        (self.scene_fbo.width, self.scene_fbo.height)
    }

    /// Executes the bloom post-processing pipeline.
    ///
    /// This should be called after the scene has been rendered to the scene FBO.
    /// The result is rendered to the default framebuffer (canvas).
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `vao_manager` - VAO manager for fullscreen quad
    pub fn apply(&self, gl: &WebGl2RenderingContext, vao_manager: &mut VertexArrayManager) {
        if !self.is_active() {
            return;
        }

        // Ensure fullscreen VAO is set up
        if vao_manager.fullscreen_vao.is_none() {
            vao_manager.setup_fullscreen_vao(gl);
        }

        let bloom_width = self.bloom_fbo_a.width();
        let bloom_height = self.bloom_fbo_a.height();

        // Disable depth test for post-processing
        gl.disable(WebGl2RenderingContext::DEPTH_TEST);

        // =====================================================================
        // Pass 1: Extract bright pixels
        // =====================================================================
        if let Some(program) = &self.bright_program {
            self.bloom_fbo_a.bind(gl);
            gl.viewport(0, 0, bloom_width as i32, bloom_height as i32);
            gl.clear_color(0.0, 0.0, 0.0, 1.0);
            gl.clear(WebGl2RenderingContext::COLOR_BUFFER_BIT);

            gl.use_program(Some(&program.program));

            // Bind scene texture
            self.scene_fbo.bind_texture(gl, 0);
            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0);
            }

            // Set threshold and intensity
            if let Some(loc) = &program.threshold_loc {
                gl.uniform1f(Some(loc), self.config.threshold);
            }
            if let Some(loc) = &program.intensity_loc {
                gl.uniform1f(Some(loc), self.config.intensity);
            }

            // Draw fullscreen quad
            gl.bind_vertex_array(vao_manager.fullscreen_vao.as_ref());
            gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);
        }

        // =====================================================================
        // Pass 2: Gaussian blur (ping-pong between FBOs)
        // =====================================================================
        if let Some(program) = &self.blur_program {
            gl.use_program(Some(&program.program));

            // Pass pre-computed texel size (1/resolution) to avoid per-fragment division
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(
                    Some(loc),
                    1.0 / bloom_width as f32,
                    1.0 / bloom_height as f32,
                );
            }

            for _ in 0..self.config.passes {
                // Horizontal blur: A -> B
                self.bloom_fbo_b.bind(gl);
                self.bloom_fbo_a.bind_texture(gl, 0);

                if let Some(loc) = &program.texture_loc {
                    gl.uniform1i(Some(loc), 0);
                }
                if let Some(loc) = &program.direction_loc {
                    gl.uniform2f(Some(loc), 1.0, 0.0); // Horizontal
                }

                gl.bind_vertex_array(vao_manager.fullscreen_vao.as_ref());
                gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);

                // Vertical blur: B -> A
                self.bloom_fbo_a.bind(gl);
                self.bloom_fbo_b.bind_texture(gl, 0);

                if let Some(loc) = &program.direction_loc {
                    gl.uniform2f(Some(loc), 0.0, 1.0); // Vertical
                }

                gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);
            }
        }

        // =====================================================================
        // Pass 3: Composite bloom with scene
        // =====================================================================
        if let Some(program) = &self.composite_program {
            // Render to default framebuffer (canvas)
            gl.bind_framebuffer(WebGl2RenderingContext::FRAMEBUFFER, None);
            gl.viewport(0, 0, self.cached_size.0 as i32, self.cached_size.1 as i32);

            gl.use_program(Some(&program.program));

            // Bind scene texture to unit 0
            self.scene_fbo.bind_texture(gl, 0);
            if let Some(loc) = &program.scene_loc {
                gl.uniform1i(Some(loc), 0);
            }

            // Bind bloom texture to unit 1
            self.bloom_fbo_a.bind_texture(gl, 1);
            if let Some(loc) = &program.bloom_loc {
                gl.uniform1i(Some(loc), 1);
            }

            // Set final intensity
            if let Some(loc) = &program.intensity_loc {
                gl.uniform1f(Some(loc), 1.0); // Composite uses full intensity
            }

            // Draw fullscreen quad
            gl.bind_vertex_array(vao_manager.fullscreen_vao.as_ref());
            gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);
        }

        // Cleanup
        gl.bind_vertex_array(None);
        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, None);
    }

    /// Compiles a shader program from vertex and fragment sources.
    fn compile_program(
        gl: &WebGl2RenderingContext,
        vertex_src: &str,
        fragment_src: &str,
    ) -> Option<WebGlProgram> {
        // Compile vertex shader
        let vertex_shader = gl.create_shader(WebGl2RenderingContext::VERTEX_SHADER)?;
        gl.shader_source(&vertex_shader, vertex_src);
        gl.compile_shader(&vertex_shader);

        if !gl
            .get_shader_parameter(&vertex_shader, WebGl2RenderingContext::COMPILE_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_shader_info_log(&vertex_shader).unwrap_or_default();
            web_sys::console::error_1(&format!("Bloom vertex shader error: {log}").into());
            gl.delete_shader(Some(&vertex_shader));
            return None;
        }

        // Compile fragment shader
        let fragment_shader = gl.create_shader(WebGl2RenderingContext::FRAGMENT_SHADER)?;
        gl.shader_source(&fragment_shader, fragment_src);
        gl.compile_shader(&fragment_shader);

        if !gl
            .get_shader_parameter(&fragment_shader, WebGl2RenderingContext::COMPILE_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_shader_info_log(&fragment_shader).unwrap_or_default();
            web_sys::console::error_1(&format!("Bloom fragment shader error: {log}").into());
            gl.delete_shader(Some(&vertex_shader));
            gl.delete_shader(Some(&fragment_shader));
            return None;
        }

        // Link program
        let program = gl.create_program()?;
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
            web_sys::console::error_1(&format!("Bloom program link error: {log}").into());
            gl.delete_program(Some(&program));
            return None;
        }

        Some(program)
    }

    /// Releases all WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        self.scene_fbo.destroy(gl);
        self.bloom_fbo_a.destroy(gl);
        self.bloom_fbo_b.destroy(gl);

        if let Some(program) = self.bright_program.take() {
            gl.delete_program(Some(&program.program));
        }
        if let Some(program) = self.blur_program.take() {
            gl.delete_program(Some(&program.program));
        }
        if let Some(program) = self.composite_program.take() {
            gl.delete_program(Some(&program.program));
        }

        self.initialized = false;
        self.cached_size = (0, 0);
    }
}

impl Default for BloomPipeline {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_config_default() {
        let config = BloomConfig::default();
        assert!(config.enabled);
        assert!((config.threshold - DEFAULT_BLOOM_THRESHOLD).abs() < 0.001);
        assert!((config.intensity - DEFAULT_BLOOM_INTENSITY).abs() < 0.001);
        assert_eq!(config.downscale, DEFAULT_BLOOM_DOWNSCALE);
        assert_eq!(config.passes, DEFAULT_BLOOM_PASSES);
    }

    #[test]
    fn test_bloom_config_subtle() {
        let config = BloomConfig::subtle();
        assert!(config.enabled);
        assert!(config.threshold > DEFAULT_BLOOM_THRESHOLD);
        assert!(config.intensity < DEFAULT_BLOOM_INTENSITY);
    }

    #[test]
    fn test_bloom_config_intense() {
        let config = BloomConfig::intense();
        assert!(config.enabled);
        assert!(config.threshold < DEFAULT_BLOOM_THRESHOLD);
        assert!(config.intensity > DEFAULT_BLOOM_INTENSITY);
    }

    #[test]
    fn test_bloom_fbo_new() {
        let fbo = BloomFbo::new();
        assert!(!fbo.is_initialized());
        assert_eq!(fbo.width(), 0);
        assert_eq!(fbo.height(), 0);
    }

    #[test]
    fn test_bloom_pipeline_new() {
        let pipeline = BloomPipeline::new();
        assert!(!pipeline.is_active());
        assert!(pipeline.config.enabled);
        assert!(!pipeline.initialized);
    }

    #[test]
    fn test_bloom_pipeline_not_active_when_disabled() {
        let mut pipeline = BloomPipeline::new();
        pipeline.config.enabled = false;
        assert!(!pipeline.is_active());
    }

    #[test]
    fn test_bloom_pipeline_not_active_when_not_initialized() {
        let pipeline = BloomPipeline::new();
        assert!(pipeline.config.enabled);
        assert!(!pipeline.initialized);
        assert!(!pipeline.is_active());
    }
}
