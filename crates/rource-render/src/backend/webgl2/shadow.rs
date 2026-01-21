//! GPU shadow effect implementation for WebGL2.
//!
//! This module provides a GPU-based drop shadow effect that creates soft shadows
//! beneath entities in the scene. The implementation uses framebuffer objects (FBOs)
//! for efficient render-to-texture operations.
//!
//! ## Pipeline
//!
//! The shadow effect is implemented as a multi-pass post-processing pipeline:
//!
//! 1. **Scene Render**: Scene is rendered to the scene FBO (shared with bloom)
//! 2. **Silhouette Pass**: Extract alpha channel as shadow shape
//! 3. **Offset Pass**: Shift silhouette in shadow direction
//! 4. **Blur Pass**: Apply Gaussian blur for soft edges
//! 5. **Composite**: Render shadow behind original scene
//!
//! ## Performance
//!
//! - Shadow is rendered at configurable downscale (default 2x) for efficiency
//! - Uses the same blur shader as bloom effect
//! - Lazy FBO creation - resources allocated only when shadow is enabled
//! - Automatic resize handling when viewport dimensions change
//!
//! ## Usage
//!
//! ```ignore
//! // Enable shadow in the renderer
//! renderer.set_shadow_enabled(true);
//! renderer.set_shadow_offset(4.0, 4.0);
//! renderer.set_shadow_opacity(0.5);
//!
//! // Shadow is automatically applied during end_frame()
//! ```

// Allow raw string hashes for GLSL shader consistency
#![allow(clippy::needless_raw_string_hashes)]

use web_sys::{
    WebGl2RenderingContext, WebGlFramebuffer, WebGlProgram, WebGlTexture, WebGlUniformLocation,
};

use super::buffers::VertexArrayManager;

// ============================================================================
// Constants
// ============================================================================

/// Default shadow offset in pixels (X direction).
pub const DEFAULT_SHADOW_OFFSET_X: f32 = 4.0;

/// Default shadow offset in pixels (Y direction).
pub const DEFAULT_SHADOW_OFFSET_Y: f32 = 4.0;

/// Default shadow opacity (0.0 - 1.0).
pub const DEFAULT_SHADOW_OPACITY: f32 = 0.5;

/// Default shadow blur radius.
pub const DEFAULT_SHADOW_BLUR: u32 = 2;

/// Default shadow color (RGBA).
pub const DEFAULT_SHADOW_COLOR: [f32; 4] = [0.0, 0.0, 0.0, 1.0];

/// Default downscale factor for shadow buffers.
pub const DEFAULT_SHADOW_DOWNSCALE: u32 = 2;

// ============================================================================
// Shadow Configuration
// ============================================================================

/// Configuration for the GPU shadow effect.
#[derive(Debug, Clone, Copy)]
pub struct ShadowConfig {
    /// Whether shadow effect is enabled.
    pub enabled: bool,

    /// Shadow offset X in pixels.
    pub offset_x: f32,

    /// Shadow offset Y in pixels.
    pub offset_y: f32,

    /// Shadow opacity (0.0 - 1.0).
    pub opacity: f32,

    /// Number of blur passes for soft edges.
    pub blur_passes: u32,

    /// Shadow color (RGBA).
    pub color: [f32; 4],

    /// Downscale factor for shadow buffers.
    pub downscale: u32,
}

impl Default for ShadowConfig {
    fn default() -> Self {
        Self {
            enabled: false, // Shadow off by default (unlike bloom)
            offset_x: DEFAULT_SHADOW_OFFSET_X,
            offset_y: DEFAULT_SHADOW_OFFSET_Y,
            opacity: DEFAULT_SHADOW_OPACITY,
            blur_passes: DEFAULT_SHADOW_BLUR,
            color: DEFAULT_SHADOW_COLOR,
            downscale: DEFAULT_SHADOW_DOWNSCALE,
        }
    }
}

impl ShadowConfig {
    /// Creates a new shadow configuration with default values.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a subtle shadow configuration.
    #[must_use]
    pub fn subtle() -> Self {
        Self {
            enabled: true,
            offset_x: 2.0,
            offset_y: 2.0,
            opacity: 0.3,
            blur_passes: 1,
            color: DEFAULT_SHADOW_COLOR,
            downscale: 2,
        }
    }

    /// Creates a pronounced shadow configuration.
    #[must_use]
    pub fn pronounced() -> Self {
        Self {
            enabled: true,
            offset_x: 6.0,
            offset_y: 6.0,
            opacity: 0.7,
            blur_passes: 3,
            color: DEFAULT_SHADOW_COLOR,
            downscale: 2,
        }
    }
}

// ============================================================================
// Shadow Shader Sources
// ============================================================================

/// Vertex shader for fullscreen shadow passes.
const SHADOW_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

layout(location = 0) in vec2 a_position;

out vec2 v_uv;

void main() {
    gl_Position = vec4(a_position, 0.0, 1.0);
    v_uv = a_position * 0.5 + 0.5;
}
"#;

/// Fragment shader for extracting silhouette from scene.
///
/// Extracts pixels with non-zero alpha and renders them as solid shadow color.
const SHADOW_SILHOUETTE_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_texture;
uniform vec4 u_shadow_color;
uniform float u_opacity;

in vec2 v_uv;

out vec4 fragColor;

void main() {
    float alpha = texture(u_texture, v_uv).a;

    // Only create shadow where there's content
    if (alpha < 0.01) {
        discard;
    }

    // Output shadow color with combined opacity
    fragColor = vec4(u_shadow_color.rgb, u_shadow_color.a * alpha * u_opacity);
}
"#;

/// Fragment shader for offsetting the silhouette.
///
/// Samples the silhouette texture at an offset position to shift the shadow.
const SHADOW_OFFSET_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_texture;
uniform vec2 u_offset;       // Offset in UV space
uniform vec2 u_resolution;   // Texture resolution

in vec2 v_uv;

out vec4 fragColor;

void main() {
    // Calculate offset in UV space
    vec2 offset_uv = u_offset / u_resolution;
    vec2 sample_uv = v_uv - offset_uv;

    // Clamp to texture bounds
    if (sample_uv.x < 0.0 || sample_uv.x > 1.0 || sample_uv.y < 0.0 || sample_uv.y > 1.0) {
        fragColor = vec4(0.0);
        return;
    }

    fragColor = texture(u_texture, sample_uv);
}
"#;

/// Fragment shader for shadow blur (same Gaussian as bloom).
const SHADOW_BLUR_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_texture;
uniform vec2 u_direction;  // (1,0) for horizontal, (0,1) for vertical
uniform vec2 u_resolution;

in vec2 v_uv;

out vec4 fragColor;

// 9-tap Gaussian blur weights
const float weights[5] = float[](0.227027, 0.1945946, 0.1216216, 0.054054, 0.016216);

void main() {
    vec2 texel_size = 1.0 / u_resolution;
    vec4 result = texture(u_texture, v_uv) * weights[0];

    for (int i = 1; i < 5; i++) {
        vec2 offset = u_direction * texel_size * float(i);
        result += texture(u_texture, v_uv + offset) * weights[i];
        result += texture(u_texture, v_uv - offset) * weights[i];
    }

    fragColor = result;
}
"#;

/// Fragment shader for compositing shadow behind scene.
///
/// Renders the shadow first, then composites the original scene on top.
const SHADOW_COMPOSITE_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_scene;
uniform sampler2D u_shadow;

in vec2 v_uv;

out vec4 fragColor;

void main() {
    vec4 scene = texture(u_scene, v_uv);
    vec4 shadow = texture(u_shadow, v_uv);

    // Composite: shadow is rendered behind scene using standard alpha blending
    // Result = scene + shadow * (1 - scene.a)
    // This ensures shadow shows only where scene is transparent
    vec3 composited = scene.rgb + shadow.rgb * shadow.a * (1.0 - scene.a);
    float alpha = scene.a + shadow.a * (1.0 - scene.a);

    fragColor = vec4(composited, alpha);
}
"#;

// ============================================================================
// Shadow Program
// ============================================================================

/// Compiled shader program with uniform locations for shadow passes.
struct ShadowProgram {
    program: WebGlProgram,
    texture_loc: Option<WebGlUniformLocation>,
    shadow_color_loc: Option<WebGlUniformLocation>,
    opacity_loc: Option<WebGlUniformLocation>,
    offset_loc: Option<WebGlUniformLocation>,
    resolution_loc: Option<WebGlUniformLocation>,
    direction_loc: Option<WebGlUniformLocation>,
    scene_loc: Option<WebGlUniformLocation>,
    shadow_loc: Option<WebGlUniformLocation>,
}

// ============================================================================
// Shadow FBO
// ============================================================================

/// A framebuffer object for shadow rendering.
struct ShadowFbo {
    framebuffer: Option<WebGlFramebuffer>,
    texture: Option<WebGlTexture>,
    width: u32,
    height: u32,
}

impl ShadowFbo {
    fn new() -> Self {
        Self {
            framebuffer: None,
            texture: None,
            width: 0,
            height: 0,
        }
    }

    fn is_initialized(&self) -> bool {
        self.framebuffer.is_some() && self.texture.is_some()
    }

    fn ensure_size(&mut self, gl: &WebGl2RenderingContext, width: u32, height: u32) -> bool {
        if self.is_initialized() && self.width == width && self.height == height {
            return true;
        }

        self.destroy(gl);

        let Some(framebuffer) = gl.create_framebuffer() else {
            return false;
        };

        let Some(texture) = gl.create_texture() else {
            gl.delete_framebuffer(Some(&framebuffer));
            return false;
        };

        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(&texture));

        gl.tex_image_2d_with_i32_and_i32_and_i32_and_format_and_type_and_opt_u8_array(
            WebGl2RenderingContext::TEXTURE_2D,
            0,
            WebGl2RenderingContext::RGBA8 as i32,
            width as i32,
            height as i32,
            0,
            WebGl2RenderingContext::RGBA,
            WebGl2RenderingContext::UNSIGNED_BYTE,
            None,
        )
        .ok();

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

        gl.bind_framebuffer(WebGl2RenderingContext::FRAMEBUFFER, Some(&framebuffer));
        gl.framebuffer_texture_2d(
            WebGl2RenderingContext::FRAMEBUFFER,
            WebGl2RenderingContext::COLOR_ATTACHMENT0,
            WebGl2RenderingContext::TEXTURE_2D,
            Some(&texture),
            0,
        );

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

    fn bind(&self, gl: &WebGl2RenderingContext) {
        gl.bind_framebuffer(
            WebGl2RenderingContext::FRAMEBUFFER,
            self.framebuffer.as_ref(),
        );
    }

    fn bind_texture(&self, gl: &WebGl2RenderingContext, unit: u32) {
        gl.active_texture(WebGl2RenderingContext::TEXTURE0 + unit);
        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, self.texture.as_ref());
    }

    fn destroy(&mut self, gl: &WebGl2RenderingContext) {
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

// ============================================================================
// Shadow Pipeline
// ============================================================================

/// GPU shadow effect pipeline.
///
/// Manages all resources needed for the shadow post-processing effect.
pub struct ShadowPipeline {
    /// Shadow configuration.
    pub config: ShadowConfig,

    /// FBO for silhouette extraction (downscaled).
    silhouette_fbo: ShadowFbo,

    /// FBO for shadow blur A (downscaled).
    shadow_fbo_a: ShadowFbo,

    /// FBO for shadow blur B (ping-pong target).
    shadow_fbo_b: ShadowFbo,

    /// Silhouette extraction shader program.
    silhouette_program: Option<ShadowProgram>,

    /// Offset shader program.
    offset_program: Option<ShadowProgram>,

    /// Blur shader program.
    blur_program: Option<ShadowProgram>,

    /// Composite shader program.
    composite_program: Option<ShadowProgram>,

    /// Cached full resolution (width, height).
    cached_size: (u32, u32),

    /// Whether the pipeline is initialized.
    initialized: bool,
}

impl ShadowPipeline {
    /// Creates a new shadow pipeline with default configuration.
    pub fn new() -> Self {
        Self {
            config: ShadowConfig::default(),
            silhouette_fbo: ShadowFbo::new(),
            shadow_fbo_a: ShadowFbo::new(),
            shadow_fbo_b: ShadowFbo::new(),
            silhouette_program: None,
            offset_program: None,
            blur_program: None,
            composite_program: None,
            cached_size: (0, 0),
            initialized: false,
        }
    }

    /// Returns whether shadow is enabled and the pipeline is ready.
    #[inline]
    pub fn is_active(&self) -> bool {
        self.config.enabled && self.initialized
    }

    /// Initializes the shadow pipeline.
    ///
    /// Compiles shaders and prepares the pipeline for rendering.
    pub fn initialize(&mut self, gl: &WebGl2RenderingContext) -> bool {
        // Compile silhouette program
        self.silhouette_program =
            Self::compile_program(gl, SHADOW_VERTEX_SHADER, SHADOW_SILHOUETTE_FRAGMENT_SHADER).map(
                |program| ShadowProgram {
                    texture_loc: gl.get_uniform_location(&program, "u_texture"),
                    shadow_color_loc: gl.get_uniform_location(&program, "u_shadow_color"),
                    opacity_loc: gl.get_uniform_location(&program, "u_opacity"),
                    offset_loc: None,
                    resolution_loc: None,
                    direction_loc: None,
                    scene_loc: None,
                    shadow_loc: None,
                    program,
                },
            );

        if self.silhouette_program.is_none() {
            return false;
        }

        // Compile offset program
        self.offset_program =
            Self::compile_program(gl, SHADOW_VERTEX_SHADER, SHADOW_OFFSET_FRAGMENT_SHADER).map(
                |program| ShadowProgram {
                    texture_loc: gl.get_uniform_location(&program, "u_texture"),
                    shadow_color_loc: None,
                    opacity_loc: None,
                    offset_loc: gl.get_uniform_location(&program, "u_offset"),
                    resolution_loc: gl.get_uniform_location(&program, "u_resolution"),
                    direction_loc: None,
                    scene_loc: None,
                    shadow_loc: None,
                    program,
                },
            );

        if self.offset_program.is_none() {
            return false;
        }

        // Compile blur program
        self.blur_program =
            Self::compile_program(gl, SHADOW_VERTEX_SHADER, SHADOW_BLUR_FRAGMENT_SHADER).map(
                |program| ShadowProgram {
                    texture_loc: gl.get_uniform_location(&program, "u_texture"),
                    shadow_color_loc: None,
                    opacity_loc: None,
                    offset_loc: None,
                    resolution_loc: gl.get_uniform_location(&program, "u_resolution"),
                    direction_loc: gl.get_uniform_location(&program, "u_direction"),
                    scene_loc: None,
                    shadow_loc: None,
                    program,
                },
            );

        if self.blur_program.is_none() {
            return false;
        }

        // Compile composite program
        self.composite_program =
            Self::compile_program(gl, SHADOW_VERTEX_SHADER, SHADOW_COMPOSITE_FRAGMENT_SHADER).map(
                |program| ShadowProgram {
                    texture_loc: None,
                    shadow_color_loc: None,
                    opacity_loc: None,
                    offset_loc: None,
                    resolution_loc: None,
                    direction_loc: None,
                    scene_loc: gl.get_uniform_location(&program, "u_scene"),
                    shadow_loc: gl.get_uniform_location(&program, "u_shadow"),
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
    pub fn ensure_size(&mut self, gl: &WebGl2RenderingContext, width: u32, height: u32) -> bool {
        if !self.initialized || !self.config.enabled {
            return false;
        }

        if self.cached_size == (width, height) && self.silhouette_fbo.is_initialized() {
            return true;
        }

        self.cached_size = (width, height);

        // Shadow FBOs at downscaled resolution
        let shadow_width = (width / self.config.downscale).max(1);
        let shadow_height = (height / self.config.downscale).max(1);

        if !self
            .silhouette_fbo
            .ensure_size(gl, shadow_width, shadow_height)
        {
            return false;
        }

        if !self
            .shadow_fbo_a
            .ensure_size(gl, shadow_width, shadow_height)
        {
            return false;
        }

        if !self
            .shadow_fbo_b
            .ensure_size(gl, shadow_width, shadow_height)
        {
            return false;
        }

        true
    }

    /// Applies the shadow post-processing pipeline.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 context
    /// * `scene_texture` - The scene texture to apply shadow to (from bloom's scene FBO)
    /// * `scene_width` - Scene texture width
    /// * `scene_height` - Scene texture height
    /// * `vao_manager` - VAO manager for fullscreen quad
    #[allow(clippy::too_many_lines)]
    pub fn apply(
        &self,
        gl: &WebGl2RenderingContext,
        scene_fbo_texture: &web_sys::WebGlTexture,
        scene_width: u32,
        scene_height: u32,
        vao_manager: &mut VertexArrayManager,
    ) {
        if !self.is_active() {
            return;
        }

        // Ensure fullscreen VAO exists
        if vao_manager.fullscreen_vao.is_none() {
            vao_manager.setup_fullscreen_vao(gl);
        }

        let shadow_width = self.silhouette_fbo.width;
        let shadow_height = self.silhouette_fbo.height;

        // Disable depth test for post-processing
        gl.disable(WebGl2RenderingContext::DEPTH_TEST);

        // Enable blending for shadow compositing
        gl.enable(WebGl2RenderingContext::BLEND);
        gl.blend_func(
            WebGl2RenderingContext::SRC_ALPHA,
            WebGl2RenderingContext::ONE_MINUS_SRC_ALPHA,
        );

        // =====================================================================
        // Pass 1: Extract silhouette with offset
        // =====================================================================
        if let Some(program) = &self.silhouette_program {
            self.silhouette_fbo.bind(gl);
            gl.viewport(0, 0, shadow_width as i32, shadow_height as i32);
            gl.clear_color(0.0, 0.0, 0.0, 0.0);
            gl.clear(WebGl2RenderingContext::COLOR_BUFFER_BIT);

            gl.use_program(Some(&program.program));

            // Bind scene texture
            gl.active_texture(WebGl2RenderingContext::TEXTURE0);
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(scene_fbo_texture));
            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0);
            }

            // Set shadow color and opacity
            if let Some(loc) = &program.shadow_color_loc {
                gl.uniform4f(
                    Some(loc),
                    self.config.color[0],
                    self.config.color[1],
                    self.config.color[2],
                    self.config.color[3],
                );
            }
            if let Some(loc) = &program.opacity_loc {
                gl.uniform1f(Some(loc), self.config.opacity);
            }

            gl.bind_vertex_array(vao_manager.fullscreen_vao.as_ref());
            gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);
        }

        // =====================================================================
        // Pass 2: Offset the silhouette
        // =====================================================================
        if let Some(program) = &self.offset_program {
            self.shadow_fbo_a.bind(gl);
            gl.clear_color(0.0, 0.0, 0.0, 0.0);
            gl.clear(WebGl2RenderingContext::COLOR_BUFFER_BIT);

            gl.use_program(Some(&program.program));

            self.silhouette_fbo.bind_texture(gl, 0);
            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0);
            }

            // Offset in screen space, scaled for downsampled resolution
            let scale = self.config.downscale as f32;
            if let Some(loc) = &program.offset_loc {
                gl.uniform2f(
                    Some(loc),
                    self.config.offset_x / scale,
                    self.config.offset_y / scale,
                );
            }
            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), shadow_width as f32, shadow_height as f32);
            }

            gl.bind_vertex_array(vao_manager.fullscreen_vao.as_ref());
            gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);
        }

        // =====================================================================
        // Pass 3: Gaussian blur (ping-pong between FBOs)
        // =====================================================================
        if let Some(program) = &self.blur_program {
            gl.use_program(Some(&program.program));

            if let Some(loc) = &program.resolution_loc {
                gl.uniform2f(Some(loc), shadow_width as f32, shadow_height as f32);
            }

            for _ in 0..self.config.blur_passes {
                // Horizontal blur: A -> B
                self.shadow_fbo_b.bind(gl);
                self.shadow_fbo_a.bind_texture(gl, 0);

                if let Some(loc) = &program.texture_loc {
                    gl.uniform1i(Some(loc), 0);
                }
                if let Some(loc) = &program.direction_loc {
                    gl.uniform2f(Some(loc), 1.0, 0.0);
                }

                gl.bind_vertex_array(vao_manager.fullscreen_vao.as_ref());
                gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);

                // Vertical blur: B -> A
                self.shadow_fbo_a.bind(gl);
                self.shadow_fbo_b.bind_texture(gl, 0);

                if let Some(loc) = &program.direction_loc {
                    gl.uniform2f(Some(loc), 0.0, 1.0);
                }

                gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);
            }
        }

        // =====================================================================
        // Pass 4: Composite shadow with scene
        // =====================================================================
        if let Some(program) = &self.composite_program {
            // Render to default framebuffer (canvas)
            gl.bind_framebuffer(WebGl2RenderingContext::FRAMEBUFFER, None);
            gl.viewport(0, 0, scene_width as i32, scene_height as i32);

            gl.use_program(Some(&program.program));

            // Bind scene texture to unit 0
            gl.active_texture(WebGl2RenderingContext::TEXTURE0);
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(scene_fbo_texture));
            if let Some(loc) = &program.scene_loc {
                gl.uniform1i(Some(loc), 0);
            }

            // Bind shadow texture to unit 1
            self.shadow_fbo_a.bind_texture(gl, 1);
            if let Some(loc) = &program.shadow_loc {
                gl.uniform1i(Some(loc), 1);
            }

            gl.bind_vertex_array(vao_manager.fullscreen_vao.as_ref());
            gl.draw_arrays(WebGl2RenderingContext::TRIANGLE_STRIP, 0, 4);
        }

        // Cleanup
        gl.bind_vertex_array(None);
        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, None);
    }

    /// Compiles a shader program.
    fn compile_program(
        gl: &WebGl2RenderingContext,
        vertex_src: &str,
        fragment_src: &str,
    ) -> Option<WebGlProgram> {
        let vertex_shader = gl.create_shader(WebGl2RenderingContext::VERTEX_SHADER)?;
        gl.shader_source(&vertex_shader, vertex_src);
        gl.compile_shader(&vertex_shader);

        if !gl
            .get_shader_parameter(&vertex_shader, WebGl2RenderingContext::COMPILE_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_shader_info_log(&vertex_shader).unwrap_or_default();
            web_sys::console::error_1(&format!("Shadow vertex shader error: {log}").into());
            gl.delete_shader(Some(&vertex_shader));
            return None;
        }

        let fragment_shader = gl.create_shader(WebGl2RenderingContext::FRAGMENT_SHADER)?;
        gl.shader_source(&fragment_shader, fragment_src);
        gl.compile_shader(&fragment_shader);

        if !gl
            .get_shader_parameter(&fragment_shader, WebGl2RenderingContext::COMPILE_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_shader_info_log(&fragment_shader).unwrap_or_default();
            web_sys::console::error_1(&format!("Shadow fragment shader error: {log}").into());
            gl.delete_shader(Some(&vertex_shader));
            gl.delete_shader(Some(&fragment_shader));
            return None;
        }

        let program = gl.create_program()?;
        gl.attach_shader(&program, &vertex_shader);
        gl.attach_shader(&program, &fragment_shader);
        gl.link_program(&program);

        gl.delete_shader(Some(&vertex_shader));
        gl.delete_shader(Some(&fragment_shader));

        if !gl
            .get_program_parameter(&program, WebGl2RenderingContext::LINK_STATUS)
            .as_bool()
            .unwrap_or(false)
        {
            let log = gl.get_program_info_log(&program).unwrap_or_default();
            web_sys::console::error_1(&format!("Shadow program link error: {log}").into());
            gl.delete_program(Some(&program));
            return None;
        }

        Some(program)
    }

    /// Releases all WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        self.silhouette_fbo.destroy(gl);
        self.shadow_fbo_a.destroy(gl);
        self.shadow_fbo_b.destroy(gl);

        if let Some(program) = self.silhouette_program.take() {
            gl.delete_program(Some(&program.program));
        }
        if let Some(program) = self.offset_program.take() {
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

impl Default for ShadowPipeline {
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
    fn test_shadow_config_default() {
        let config = ShadowConfig::default();
        assert!(!config.enabled); // Shadow is off by default
        assert!((config.offset_x - DEFAULT_SHADOW_OFFSET_X).abs() < 0.001);
        assert!((config.offset_y - DEFAULT_SHADOW_OFFSET_Y).abs() < 0.001);
        assert!((config.opacity - DEFAULT_SHADOW_OPACITY).abs() < 0.001);
        assert_eq!(config.blur_passes, DEFAULT_SHADOW_BLUR);
    }

    #[test]
    fn test_shadow_config_subtle() {
        let config = ShadowConfig::subtle();
        assert!(config.enabled);
        assert!(config.offset_x < DEFAULT_SHADOW_OFFSET_X);
        assert!(config.opacity < DEFAULT_SHADOW_OPACITY);
    }

    #[test]
    fn test_shadow_config_pronounced() {
        let config = ShadowConfig::pronounced();
        assert!(config.enabled);
        assert!(config.offset_x > DEFAULT_SHADOW_OFFSET_X);
        assert!(config.opacity > DEFAULT_SHADOW_OPACITY);
    }

    #[test]
    fn test_shadow_pipeline_new() {
        let pipeline = ShadowPipeline::new();
        assert!(!pipeline.is_active());
        assert!(!pipeline.config.enabled);
        assert!(!pipeline.initialized);
    }

    #[test]
    fn test_shadow_fbo_new() {
        let fbo = ShadowFbo::new();
        assert!(!fbo.is_initialized());
        assert_eq!(fbo.width, 0);
        assert_eq!(fbo.height, 0);
    }
}
