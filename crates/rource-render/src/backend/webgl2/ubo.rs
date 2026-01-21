//! Uniform Buffer Objects (UBOs) for WebGL2 shared uniform management.
//!
//! This module provides efficient uniform data sharing across multiple shader programs.
//! Instead of setting `u_resolution` individually for each shader, we use a UBO that
//! all shaders can read from, reducing the number of `gl.uniform*` calls per frame.
//!
//! ## Performance Impact
//!
//! Without UBOs: ~12 uniform calls per frame (2 per primitive type × 6 types)
//! With UBOs: 1 buffer update per frame
//!
//! Expected improvement: ~90% reduction in uniform-related API calls.
//!
//! ## Memory Layout
//!
//! The `CommonUniforms` uniform block uses std140 layout:
//!
//! | Offset | Size | Field        | Description                    |
//! |--------|------|--------------|--------------------------------|
//! | 0      | 8    | `u_resolution` | vec2, canvas size in pixels    |
//! | 8      | 8    | (padding)    | Alignment to 16 bytes          |
//!
//! Total size: 16 bytes (std140 requires vec4 alignment for uniform blocks)

use web_sys::{WebGl2RenderingContext, WebGlBuffer, WebGlProgram};

/// Binding point for the common uniforms UBO.
/// This is shared across all shader programs.
pub const COMMON_UNIFORMS_BINDING: u32 = 0;

/// Name of the uniform block in GLSL shaders.
pub const COMMON_UNIFORMS_BLOCK_NAME: &str = "CommonUniforms";

/// Size of the common uniforms buffer in bytes.
/// Uses std140 layout: vec2 (8 bytes) + padding (8 bytes) = 16 bytes.
const COMMON_UNIFORMS_SIZE: usize = 16;

/// Manages Uniform Buffer Objects for sharing uniform data across shaders.
///
/// The UBO contains commonly-used uniforms like resolution that would otherwise
/// need to be set separately for each shader program every frame.
#[derive(Debug)]
pub struct UniformBufferManager {
    /// The WebGL buffer for common uniforms.
    buffer: Option<WebGlBuffer>,

    /// CPU-side data for the uniform buffer.
    /// Layout (std140):
    /// - bytes 0-7: `u_resolution` (vec2)
    /// - bytes 8-15: padding
    data: [u8; COMMON_UNIFORMS_SIZE],

    /// Whether the buffer needs to be uploaded to GPU.
    dirty: bool,

    /// Whether the UBO system has been initialized.
    initialized: bool,
}

impl UniformBufferManager {
    /// Creates a new uniform buffer manager.
    #[must_use]
    pub fn new() -> Self {
        Self {
            buffer: None,
            data: [0; COMMON_UNIFORMS_SIZE],
            dirty: true,
            initialized: false,
        }
    }

    /// Initializes the UBO and creates the GPU buffer.
    ///
    /// # Returns
    ///
    /// `true` if initialization succeeded, `false` otherwise.
    pub fn initialize(&mut self, gl: &WebGl2RenderingContext) -> bool {
        if self.initialized {
            return true;
        }

        let Some(buffer) = gl.create_buffer() else {
            return false;
        };

        // Allocate the buffer with initial data
        gl.bind_buffer(WebGl2RenderingContext::UNIFORM_BUFFER, Some(&buffer));
        gl.buffer_data_with_i32(
            WebGl2RenderingContext::UNIFORM_BUFFER,
            COMMON_UNIFORMS_SIZE as i32,
            WebGl2RenderingContext::DYNAMIC_DRAW,
        );
        gl.bind_buffer(WebGl2RenderingContext::UNIFORM_BUFFER, None);

        self.buffer = Some(buffer);
        self.initialized = true;
        self.dirty = true;

        true
    }

    /// Binds a shader program's uniform block to the common uniforms UBO.
    ///
    /// This should be called once per program during initialization or after
    /// program compilation.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 context
    /// * `program` - The shader program to bind
    ///
    /// # Returns
    ///
    /// `true` if the binding succeeded, `false` if the uniform block doesn't exist.
    pub fn bind_program(&self, gl: &WebGl2RenderingContext, program: &WebGlProgram) -> bool {
        let block_index = gl.get_uniform_block_index(program, COMMON_UNIFORMS_BLOCK_NAME);

        // INVALID_INDEX means the block doesn't exist in the shader
        if block_index == WebGl2RenderingContext::INVALID_INDEX {
            return false;
        }

        gl.uniform_block_binding(program, block_index, COMMON_UNIFORMS_BINDING);
        true
    }

    /// Sets the resolution uniform value.
    ///
    /// This doesn't immediately upload to GPU - call `upload()` to sync.
    #[inline]
    pub fn set_resolution(&mut self, width: f32, height: f32) {
        let width_bytes = width.to_ne_bytes();
        let height_bytes = height.to_ne_bytes();

        // Check if values changed to avoid unnecessary uploads
        if self.data[0..4] != width_bytes || self.data[4..8] != height_bytes {
            self.data[0..4].copy_from_slice(&width_bytes);
            self.data[4..8].copy_from_slice(&height_bytes);
            self.dirty = true;
        }
    }

    /// Uploads the uniform data to GPU if dirty.
    ///
    /// Call this once per frame before rendering.
    pub fn upload(&mut self, gl: &WebGl2RenderingContext) {
        if !self.dirty || !self.initialized {
            return;
        }

        if let Some(buffer) = &self.buffer {
            gl.bind_buffer(WebGl2RenderingContext::UNIFORM_BUFFER, Some(buffer));
            gl.buffer_sub_data_with_i32_and_u8_array(
                WebGl2RenderingContext::UNIFORM_BUFFER,
                0,
                &self.data,
            );
            gl.bind_buffer(WebGl2RenderingContext::UNIFORM_BUFFER, None);
        }

        self.dirty = false;
    }

    /// Binds the UBO to its binding point for rendering.
    ///
    /// Call this before draw calls that use the common uniforms.
    pub fn bind(&self, gl: &WebGl2RenderingContext) {
        if let Some(buffer) = &self.buffer {
            gl.bind_buffer_base(
                WebGl2RenderingContext::UNIFORM_BUFFER,
                COMMON_UNIFORMS_BINDING,
                Some(buffer),
            );
        }
    }

    /// Unbinds the UBO from its binding point.
    pub fn unbind(&self, gl: &WebGl2RenderingContext) {
        gl.bind_buffer_base(
            WebGl2RenderingContext::UNIFORM_BUFFER,
            COMMON_UNIFORMS_BINDING,
            None,
        );
    }

    /// Releases GPU resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        if let Some(buffer) = self.buffer.take() {
            gl.delete_buffer(Some(&buffer));
        }
        self.initialized = false;
    }

    /// Returns whether the UBO system is initialized.
    #[inline]
    pub fn is_initialized(&self) -> bool {
        self.initialized
    }

    /// Invalidates the UBO state, forcing a re-upload on next frame.
    ///
    /// Call this after context recovery.
    pub fn invalidate(&mut self) {
        self.initialized = false;
        self.buffer = None;
        self.dirty = true;
    }
}

impl Default for UniformBufferManager {
    fn default() -> Self {
        Self::new()
    }
}

/// GLSL uniform block declaration for shaders that use the common uniforms UBO.
///
/// Add this to your shader source before the main function.
pub const COMMON_UNIFORMS_BLOCK_GLSL: &str = r"
// Common uniforms shared across all shaders via UBO
layout(std140) uniform CommonUniforms {
    vec2 u_resolution;  // Canvas size in pixels
};
";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ubo_manager_new() {
        let manager = UniformBufferManager::new();
        assert!(!manager.initialized);
        assert!(manager.dirty);
        assert!(manager.buffer.is_none());
    }

    #[test]
    fn test_set_resolution() {
        let mut manager = UniformBufferManager::new();

        manager.set_resolution(1920.0, 1080.0);
        assert!(manager.dirty);

        // Verify bytes are set correctly
        let width = f32::from_ne_bytes([
            manager.data[0],
            manager.data[1],
            manager.data[2],
            manager.data[3],
        ]);
        let height = f32::from_ne_bytes([
            manager.data[4],
            manager.data[5],
            manager.data[6],
            manager.data[7],
        ]);

        assert!((width - 1920.0).abs() < 0.001);
        assert!((height - 1080.0).abs() < 0.001);
    }

    #[test]
    fn test_set_resolution_no_change() {
        let mut manager = UniformBufferManager::new();

        manager.set_resolution(1920.0, 1080.0);
        manager.dirty = false;

        // Same values should not mark dirty
        manager.set_resolution(1920.0, 1080.0);
        assert!(!manager.dirty);

        // Different values should mark dirty
        manager.set_resolution(800.0, 600.0);
        assert!(manager.dirty);
    }

    #[test]
    fn test_constants() {
        assert_eq!(COMMON_UNIFORMS_SIZE, 16);
        assert_eq!(COMMON_UNIFORMS_BINDING, 0);
        assert!(!COMMON_UNIFORMS_BLOCK_NAME.is_empty());
        assert!(COMMON_UNIFORMS_BLOCK_GLSL.contains("std140"));
        assert!(COMMON_UNIFORMS_BLOCK_GLSL.contains("u_resolution"));
    }
}
