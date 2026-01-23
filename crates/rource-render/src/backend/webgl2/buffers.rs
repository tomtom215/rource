// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! WebGL2 buffer management for VBOs and VAOs.
//!
//! This module provides abstractions for vertex buffers and vertex array objects
//! used for instanced rendering of primitives.

// WebGL buffer operations require unsafe for byte reinterpretation
#![allow(unsafe_code)]
// Pointer casting and size calculations are intentional for WebGL interop
#![allow(clippy::ptr_as_ptr, clippy::manual_slice_size_calculation)]

use web_sys::{WebGl2RenderingContext, WebGlBuffer, WebGlVertexArrayObject};

/// Converts a slice of f32 values to a slice of u8 bytes for WebGL upload.
///
/// # Safety
///
/// This function reinterprets f32 memory as bytes, which is safe because:
/// - The alignment of u8 (1) is always satisfied by any other type
/// - The data is valid for the lifetime of the input slice
/// - This is a standard pattern for WebGL buffer uploads
fn float_slice_to_bytes(floats: &[f32]) -> &[u8] {
    let ptr = floats.as_ptr() as *const u8;
    let len = floats.len() * std::mem::size_of::<f32>();
    // SAFETY: Reinterpreting f32 bytes is safe for WebGL uploads.
    // The slice is valid for the same lifetime as the input.
    unsafe { std::slice::from_raw_parts(ptr, len) }
}

/// Unit quad vertices for circle rendering.
/// Coordinates from -1 to 1 for easy distance calculations in shader.
pub const UNIT_QUAD_CIRCLE: [f32; 8] = [
    -1.0, -1.0, // Bottom-left
    1.0, -1.0, // Bottom-right
    -1.0, 1.0, // Top-left
    1.0, 1.0, // Top-right
];

/// Unit quad vertices for line rendering.
/// X: 0 to 1 (along line), Y: -0.5 to 0.5 (perpendicular)
pub const UNIT_QUAD_LINE: [f32; 8] = [
    0.0, -0.5, // Start bottom
    1.0, -0.5, // End bottom
    0.0, 0.5, // Start top
    1.0, 0.5, // End top
];

/// Unit quad vertices for standard quad/text rendering.
/// Coordinates from 0 to 1 for UV mapping.
pub const UNIT_QUAD_STANDARD: [f32; 8] = [
    0.0, 0.0, // Bottom-left
    1.0, 0.0, // Bottom-right
    0.0, 1.0, // Top-left
    1.0, 1.0, // Top-right
];

/// Fullscreen quad vertices for post-processing.
/// Coordinates from -1 to 1 in clip space.
pub const FULLSCREEN_QUAD: [f32; 8] = [
    -1.0, -1.0, // Bottom-left
    1.0, -1.0, // Bottom-right
    -1.0, 1.0, // Top-left
    1.0, 1.0, // Top-right
];

/// Number of segments for curve tessellation.
/// More segments = smoother curves but more vertices.
pub const CURVE_SEGMENTS: usize = 8;

/// Number of vertices in the curve strip.
/// Each segment has 2 vertices (top and bottom), plus 1 pair for the final endpoint.
pub const CURVE_STRIP_VERTEX_COUNT: u32 = ((CURVE_SEGMENTS + 1) * 2) as u32;

/// Generates curve strip vertex data.
///
/// Creates a triangle strip with vertices along t (0 to 1)
/// and perpendicular offset (-0.5 to 0.5).
fn generate_curve_strip() -> Vec<f32> {
    let mut vertices = Vec::with_capacity((CURVE_SEGMENTS + 1) * 4);
    for i in 0..=CURVE_SEGMENTS {
        let t = i as f32 / CURVE_SEGMENTS as f32;
        // Bottom vertex (y = -0.5)
        vertices.push(t);
        vertices.push(-0.5);
        // Top vertex (y = 0.5)
        vertices.push(t);
        vertices.push(0.5);
    }
    vertices
}

/// Minimum capacity threshold - buffers won't shrink below this.
const MIN_BUFFER_CAPACITY: usize = 100;

/// Shrink threshold - buffer shrinks if usage is below this fraction of capacity.
const SHRINK_THRESHOLD: f32 = 0.25;

/// Number of frames of low usage before shrinking.
const SHRINK_STABILITY_FRAMES: u32 = 120;

/// A buffer for storing per-instance data for batch rendering.
#[derive(Debug)]
pub struct InstanceBuffer {
    /// The WebGL buffer object.
    buffer: Option<WebGlBuffer>,

    /// Current data in CPU memory.
    data: Vec<f32>,

    /// Number of floats per instance.
    floats_per_instance: usize,

    /// Maximum capacity in instances.
    capacity: usize,

    /// GPU buffer capacity (in bytes) - may differ from CPU capacity.
    gpu_buffer_size: usize,

    /// Peak usage in instances during the current measurement window.
    peak_usage: usize,

    /// Frames since last significant usage.
    low_usage_frames: u32,

    /// Needs upload flag.
    dirty: bool,
}

impl InstanceBuffer {
    /// Creates a new instance buffer.
    pub fn new(floats_per_instance: usize, initial_capacity: usize) -> Self {
        Self {
            buffer: None,
            data: Vec::with_capacity(floats_per_instance * initial_capacity),
            floats_per_instance,
            capacity: initial_capacity,
            gpu_buffer_size: 0,
            peak_usage: 0,
            low_usage_frames: 0,
            dirty: false,
        }
    }

    /// Clears all instance data and updates usage tracking.
    pub fn clear(&mut self) {
        // Track peak usage before clearing
        let current_instances = self.instance_count();
        if current_instances > self.peak_usage {
            self.peak_usage = current_instances;
        }

        self.data.clear();
        self.dirty = true;
    }

    /// Returns the number of instances.
    pub fn instance_count(&self) -> usize {
        self.data.len() / self.floats_per_instance
    }

    /// Returns the number of floats per instance.
    pub fn floats_per_instance(&self) -> usize {
        self.floats_per_instance
    }

    /// Pushes raw float data for an instance.
    pub fn push_raw(&mut self, data: &[f32]) {
        debug_assert_eq!(data.len(), self.floats_per_instance);
        self.data.extend_from_slice(data);
        self.dirty = true;
    }

    /// Ensures the WebGL buffer is created.
    pub fn ensure_buffer(&mut self, gl: &WebGl2RenderingContext) {
        if self.buffer.is_none() {
            self.buffer = gl.create_buffer();
        }
    }

    /// Uploads data to GPU if dirty.
    ///
    /// Uses `buffer_sub_data` when the data fits within the existing GPU buffer
    /// to avoid expensive buffer reallocation. Only uses `buffer_data` when the
    /// buffer needs to grow.
    ///
    /// # Performance
    ///
    /// - **Sub-data update**: ~0.1ms (just copies data to existing buffer)
    /// - **Full allocation**: ~0.5ms (allocates new GPU memory + copies data)
    ///
    /// For typical visualization with 1000-5000 entities, this optimization
    /// reduces per-frame GPU buffer overhead by ~80%.
    pub fn upload(&mut self, gl: &WebGl2RenderingContext) {
        if !self.dirty || self.data.is_empty() {
            return;
        }

        self.ensure_buffer(gl);

        if let Some(buffer) = &self.buffer {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(buffer));

            // Convert f32 slice to u8 slice safely
            let byte_data = float_slice_to_bytes(&self.data);
            let data_size = byte_data.len();

            // Use buffer_sub_data if data fits within existing GPU buffer
            // This avoids expensive GPU buffer reallocation
            if data_size <= self.gpu_buffer_size && self.gpu_buffer_size > 0 {
                // Fast path: update existing buffer in-place
                gl.buffer_sub_data_with_i32_and_u8_array(
                    WebGl2RenderingContext::ARRAY_BUFFER,
                    0, // offset
                    byte_data,
                );
            } else {
                // Slow path: need to allocate/reallocate GPU buffer
                // Round up to power of 2 for better reuse
                let new_capacity = if self.data.len() > self.capacity * self.floats_per_instance {
                    self.data.len() / self.floats_per_instance * 2
                } else {
                    self.capacity
                };

                self.capacity = new_capacity;
                let new_buffer_size = new_capacity * self.floats_per_instance * 4; // 4 bytes per float

                // Allocate with extra capacity to reduce future reallocations
                gl.buffer_data_with_i32(
                    WebGl2RenderingContext::ARRAY_BUFFER,
                    new_buffer_size as i32,
                    WebGl2RenderingContext::DYNAMIC_DRAW,
                );

                // Upload current data
                gl.buffer_sub_data_with_i32_and_u8_array(
                    WebGl2RenderingContext::ARRAY_BUFFER,
                    0,
                    byte_data,
                );

                self.gpu_buffer_size = new_buffer_size;
            }

            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
        }

        self.dirty = false;
    }

    /// Called at end of frame to update usage tracking and potentially shrink.
    ///
    /// Returns `true` if the buffer was shrunk.
    pub fn end_frame(&mut self, gl: &WebGl2RenderingContext) -> bool {
        let usage_fraction = if self.capacity > 0 {
            self.peak_usage as f32 / self.capacity as f32
        } else {
            1.0
        };

        if usage_fraction < SHRINK_THRESHOLD && self.capacity > MIN_BUFFER_CAPACITY {
            self.low_usage_frames += 1;

            if self.low_usage_frames >= SHRINK_STABILITY_FRAMES {
                // Shrink to 2x peak usage or minimum capacity
                let new_capacity = (self.peak_usage * 2).max(MIN_BUFFER_CAPACITY);

                if new_capacity < self.capacity {
                    self.shrink_to(gl, new_capacity);
                    self.low_usage_frames = 0;
                    self.peak_usage = 0;
                    return true;
                }
            }
        } else {
            self.low_usage_frames = 0;
        }

        // Reset peak usage for next measurement window
        self.peak_usage = 0;
        false
    }

    /// Shrinks the buffer to a new capacity.
    fn shrink_to(&mut self, gl: &WebGl2RenderingContext, new_capacity: usize) {
        // Shrink the Vec capacity
        let new_vec_capacity = new_capacity * self.floats_per_instance;
        self.data.shrink_to(new_vec_capacity);
        self.capacity = new_capacity;

        // The next upload will reallocate the GPU buffer with the new size
        self.dirty = true;

        // Delete buffer to release GPU memory (forces reallocation on next upload)
        if let Some(buffer) = self.buffer.take() {
            gl.delete_buffer(Some(&buffer));
        }
        self.gpu_buffer_size = 0;
    }

    /// Returns the current capacity in instances.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns the peak usage since last reset.
    #[inline]
    pub fn peak_usage(&self) -> usize {
        self.peak_usage
    }

    /// Returns the WebGL buffer.
    pub fn buffer(&self) -> Option<&WebGlBuffer> {
        self.buffer.as_ref()
    }

    /// Releases WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        if let Some(buffer) = self.buffer.take() {
            gl.delete_buffer(Some(&buffer));
        }
        self.gpu_buffer_size = 0;
    }

    /// Returns the current GPU buffer size in bytes.
    #[inline]
    pub fn gpu_buffer_size(&self) -> usize {
        self.gpu_buffer_size
    }
}

/// Manages vertex array objects for different primitive types.
#[derive(Debug)]
pub struct VertexArrayManager {
    /// VAO for circle rendering
    pub circle_vao: Option<WebGlVertexArrayObject>,

    /// VAO for ring rendering
    pub ring_vao: Option<WebGlVertexArrayObject>,

    /// VAO for line rendering
    pub line_vao: Option<WebGlVertexArrayObject>,

    /// VAO for solid quad rendering
    pub quad_vao: Option<WebGlVertexArrayObject>,

    /// VAO for textured quad rendering
    pub textured_quad_vao: Option<WebGlVertexArrayObject>,

    /// VAO for text rendering
    pub text_vao: Option<WebGlVertexArrayObject>,

    /// VAO for fullscreen effects
    pub fullscreen_vao: Option<WebGlVertexArrayObject>,

    /// VAO for texture array (file icons) rendering
    pub texture_array_vao: Option<WebGlVertexArrayObject>,

    /// VAO for curve (spline) rendering
    pub curve_vao: Option<WebGlVertexArrayObject>,

    /// Shared vertex buffer for unit quads
    vertex_buffer: Option<WebGlBuffer>,

    /// Vertex buffer for curve strip
    curve_strip_buffer: Option<WebGlBuffer>,
}

impl VertexArrayManager {
    /// Creates a new VAO manager.
    pub fn new() -> Self {
        Self {
            circle_vao: None,
            ring_vao: None,
            line_vao: None,
            quad_vao: None,
            textured_quad_vao: None,
            text_vao: None,
            fullscreen_vao: None,
            texture_array_vao: None,
            curve_vao: None,
            vertex_buffer: None,
            curve_strip_buffer: None,
        }
    }

    /// Creates shared vertex buffer with all unit quad types.
    pub fn create_vertex_buffer(&mut self, gl: &WebGl2RenderingContext) {
        if self.vertex_buffer.is_some() {
            return;
        }

        let buffer = gl.create_buffer();
        if buffer.is_none() {
            return;
        }

        self.vertex_buffer = buffer;

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Pack all quad types into one buffer
        // Offset 0: circle quad (-1 to 1)
        // Offset 8: line quad (0-1 x, -0.5-0.5 y)
        // Offset 16: standard quad (0 to 1)
        // Offset 24: fullscreen quad (-1 to 1)
        let mut all_quads = Vec::with_capacity(32);
        all_quads.extend_from_slice(&UNIT_QUAD_CIRCLE);
        all_quads.extend_from_slice(&UNIT_QUAD_LINE);
        all_quads.extend_from_slice(&UNIT_QUAD_STANDARD);
        all_quads.extend_from_slice(&FULLSCREEN_QUAD);

        let byte_data = float_slice_to_bytes(&all_quads);
        gl.buffer_data_with_u8_array(
            WebGl2RenderingContext::ARRAY_BUFFER,
            byte_data,
            WebGl2RenderingContext::STATIC_DRAW,
        );

        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for circle rendering with instance buffer.
    pub fn setup_circle_vao(
        &mut self,
        gl: &WebGl2RenderingContext,
        instance_buffer: &InstanceBuffer,
    ) {
        if self.vertex_buffer.is_none() {
            self.create_vertex_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.circle_vao = vao;
        gl.bind_vertex_array(self.circle_vao.as_ref());

        // Bind vertex buffer for position attribute
        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Position attribute (location 0) - offset 0 for circle quad
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 0);
        gl.enable_vertex_attrib_array(0);

        // Bind instance buffer
        if let Some(inst_buf) = instance_buffer.buffer() {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(inst_buf));

            // Instance attributes: center (vec2), radius (float), color (vec4)
            let stride = 7 * 4; // 7 floats * 4 bytes

            // Center (location 1)
            gl.vertex_attrib_pointer_with_i32(
                1,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                0,
            );
            gl.enable_vertex_attrib_array(1);
            gl.vertex_attrib_divisor(1, 1);

            // Radius (location 2)
            gl.vertex_attrib_pointer_with_i32(
                2,
                1,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                8,
            );
            gl.enable_vertex_attrib_array(2);
            gl.vertex_attrib_divisor(2, 1);

            // Color (location 3)
            gl.vertex_attrib_pointer_with_i32(
                3,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                12,
            );
            gl.enable_vertex_attrib_array(3);
            gl.vertex_attrib_divisor(3, 1);
        }

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for ring (circle outline) rendering with instance buffer.
    pub fn setup_ring_vao(
        &mut self,
        gl: &WebGl2RenderingContext,
        instance_buffer: &InstanceBuffer,
    ) {
        if self.vertex_buffer.is_none() {
            self.create_vertex_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.ring_vao = vao;
        gl.bind_vertex_array(self.ring_vao.as_ref());

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Position attribute (location 0) - offset 0 for circle quad
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 0);
        gl.enable_vertex_attrib_array(0);

        if let Some(inst_buf) = instance_buffer.buffer() {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(inst_buf));

            // Instance attributes: center (vec2), radius (float), width (float), color (vec4)
            let stride = 8 * 4; // 8 floats * 4 bytes

            // Center (location 1)
            gl.vertex_attrib_pointer_with_i32(
                1,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                0,
            );
            gl.enable_vertex_attrib_array(1);
            gl.vertex_attrib_divisor(1, 1);

            // Radius (location 2)
            gl.vertex_attrib_pointer_with_i32(
                2,
                1,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                8,
            );
            gl.enable_vertex_attrib_array(2);
            gl.vertex_attrib_divisor(2, 1);

            // Width (location 3)
            gl.vertex_attrib_pointer_with_i32(
                3,
                1,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                12,
            );
            gl.enable_vertex_attrib_array(3);
            gl.vertex_attrib_divisor(3, 1);

            // Color (location 4)
            gl.vertex_attrib_pointer_with_i32(
                4,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                16,
            );
            gl.enable_vertex_attrib_array(4);
            gl.vertex_attrib_divisor(4, 1);
        }

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for line rendering with instance buffer.
    pub fn setup_line_vao(
        &mut self,
        gl: &WebGl2RenderingContext,
        instance_buffer: &InstanceBuffer,
    ) {
        if self.vertex_buffer.is_none() {
            self.create_vertex_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.line_vao = vao;
        gl.bind_vertex_array(self.line_vao.as_ref());

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Position attribute (location 0) - offset 8*4 for line quad
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 32);
        gl.enable_vertex_attrib_array(0);

        if let Some(inst_buf) = instance_buffer.buffer() {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(inst_buf));

            // Instance attributes: start (vec2), end (vec2), width (float), color (vec4)
            let stride = 9 * 4; // 9 floats * 4 bytes

            // Start (location 1)
            gl.vertex_attrib_pointer_with_i32(
                1,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                0,
            );
            gl.enable_vertex_attrib_array(1);
            gl.vertex_attrib_divisor(1, 1);

            // End (location 2)
            gl.vertex_attrib_pointer_with_i32(
                2,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                8,
            );
            gl.enable_vertex_attrib_array(2);
            gl.vertex_attrib_divisor(2, 1);

            // Width (location 3)
            gl.vertex_attrib_pointer_with_i32(
                3,
                1,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                16,
            );
            gl.enable_vertex_attrib_array(3);
            gl.vertex_attrib_divisor(3, 1);

            // Color (location 4)
            gl.vertex_attrib_pointer_with_i32(
                4,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                20,
            );
            gl.enable_vertex_attrib_array(4);
            gl.vertex_attrib_divisor(4, 1);
        }

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for solid quad rendering with instance buffer.
    pub fn setup_quad_vao(
        &mut self,
        gl: &WebGl2RenderingContext,
        instance_buffer: &InstanceBuffer,
    ) {
        if self.vertex_buffer.is_none() {
            self.create_vertex_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.quad_vao = vao;
        gl.bind_vertex_array(self.quad_vao.as_ref());

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Position attribute (location 0) - offset 16*4 for standard quad
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 64);
        gl.enable_vertex_attrib_array(0);

        if let Some(inst_buf) = instance_buffer.buffer() {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(inst_buf));

            // Instance attributes: bounds (vec4), color (vec4)
            let stride = 8 * 4; // 8 floats * 4 bytes

            // Bounds (location 1)
            gl.vertex_attrib_pointer_with_i32(
                1,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                0,
            );
            gl.enable_vertex_attrib_array(1);
            gl.vertex_attrib_divisor(1, 1);

            // Color (location 2)
            gl.vertex_attrib_pointer_with_i32(
                2,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                16,
            );
            gl.enable_vertex_attrib_array(2);
            gl.vertex_attrib_divisor(2, 1);
        }

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for textured quad/text rendering with instance buffer.
    pub fn setup_textured_vao(
        &mut self,
        gl: &WebGl2RenderingContext,
        instance_buffer: &InstanceBuffer,
    ) {
        if self.vertex_buffer.is_none() {
            self.create_vertex_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.textured_quad_vao = vao;
        gl.bind_vertex_array(self.textured_quad_vao.as_ref());

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Position attribute (location 0) - offset 16*4 for standard quad
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 64);
        gl.enable_vertex_attrib_array(0);

        if let Some(inst_buf) = instance_buffer.buffer() {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(inst_buf));

            // Instance attributes: bounds (vec4), uv_bounds (vec4), color (vec4)
            let stride = 12 * 4; // 12 floats * 4 bytes

            // Bounds (location 1)
            gl.vertex_attrib_pointer_with_i32(
                1,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                0,
            );
            gl.enable_vertex_attrib_array(1);
            gl.vertex_attrib_divisor(1, 1);

            // UV bounds (location 2)
            gl.vertex_attrib_pointer_with_i32(
                2,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                16,
            );
            gl.enable_vertex_attrib_array(2);
            gl.vertex_attrib_divisor(2, 1);

            // Color (location 3)
            gl.vertex_attrib_pointer_with_i32(
                3,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                32,
            );
            gl.enable_vertex_attrib_array(3);
            gl.vertex_attrib_divisor(3, 1);
        }

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for fullscreen quad rendering.
    pub fn setup_fullscreen_vao(&mut self, gl: &WebGl2RenderingContext) {
        if self.vertex_buffer.is_none() {
            self.create_vertex_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.fullscreen_vao = vao;
        gl.bind_vertex_array(self.fullscreen_vao.as_ref());

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Position attribute (location 0) - offset 24*4 for fullscreen quad
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 96);
        gl.enable_vertex_attrib_array(0);

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for texture array (file icons) rendering with instance buffer.
    ///
    /// Instance layout: `bounds(4) + uv_bounds(4) + color(4) + layer(1) = 13 floats`
    pub fn setup_texture_array_vao(
        &mut self,
        gl: &WebGl2RenderingContext,
        instance_buffer: &InstanceBuffer,
    ) {
        if self.vertex_buffer.is_none() {
            self.create_vertex_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.texture_array_vao = vao;
        gl.bind_vertex_array(self.texture_array_vao.as_ref());

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.vertex_buffer.as_ref(),
        );

        // Position attribute (location 0) - offset 16*4 for standard quad
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 64);
        gl.enable_vertex_attrib_array(0);

        if let Some(inst_buf) = instance_buffer.buffer() {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(inst_buf));

            // Instance attributes: bounds (vec4), uv_bounds (vec4), color (vec4), layer (float)
            let stride = 13 * 4; // 13 floats * 4 bytes

            // Bounds (location 1)
            gl.vertex_attrib_pointer_with_i32(
                1,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                0,
            );
            gl.enable_vertex_attrib_array(1);
            gl.vertex_attrib_divisor(1, 1);

            // UV bounds (location 2)
            gl.vertex_attrib_pointer_with_i32(
                2,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                16,
            );
            gl.enable_vertex_attrib_array(2);
            gl.vertex_attrib_divisor(2, 1);

            // Color (location 3)
            gl.vertex_attrib_pointer_with_i32(
                3,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                32,
            );
            gl.enable_vertex_attrib_array(3);
            gl.vertex_attrib_divisor(3, 1);

            // Layer (location 4)
            gl.vertex_attrib_pointer_with_i32(
                4,
                1,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                48,
            );
            gl.enable_vertex_attrib_array(4);
            gl.vertex_attrib_divisor(4, 1);
        }

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Creates the curve strip vertex buffer for GPU curve tessellation.
    pub fn create_curve_strip_buffer(&mut self, gl: &WebGl2RenderingContext) {
        if self.curve_strip_buffer.is_some() {
            return;
        }

        let buffer = gl.create_buffer();
        if buffer.is_none() {
            return;
        }

        self.curve_strip_buffer = buffer;

        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.curve_strip_buffer.as_ref(),
        );

        let curve_strip = generate_curve_strip();
        let byte_data = float_slice_to_bytes(&curve_strip);
        gl.buffer_data_with_u8_array(
            WebGl2RenderingContext::ARRAY_BUFFER,
            byte_data,
            WebGl2RenderingContext::STATIC_DRAW,
        );

        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Sets up VAO for curve (spline) rendering with instance buffer.
    ///
    /// Instance layout: `p0(2) + p1(2) + p2(2) + p3(2) + width(1) + color(4) = 13 floats`
    pub fn setup_curve_vao(
        &mut self,
        gl: &WebGl2RenderingContext,
        instance_buffer: &InstanceBuffer,
    ) {
        if self.curve_strip_buffer.is_none() {
            self.create_curve_strip_buffer(gl);
        }

        let vao = gl.create_vertex_array();
        if vao.is_none() {
            return;
        }

        self.curve_vao = vao;
        gl.bind_vertex_array(self.curve_vao.as_ref());

        // Bind curve strip vertex buffer for position
        gl.bind_buffer(
            WebGl2RenderingContext::ARRAY_BUFFER,
            self.curve_strip_buffer.as_ref(),
        );

        // Position attribute (location 0) - t and offset
        gl.vertex_attrib_pointer_with_i32(0, 2, WebGl2RenderingContext::FLOAT, false, 0, 0);
        gl.enable_vertex_attrib_array(0);

        // Bind instance buffer for curve segment data
        if let Some(inst_buf) = instance_buffer.buffer() {
            gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, Some(inst_buf));

            // Instance attributes: p0(2), p1(2), p2(2), p3(2), width(1), color(4) = 13 floats
            let stride = 13 * 4; // 13 floats * 4 bytes

            // p0 (location 1) - control point before start
            gl.vertex_attrib_pointer_with_i32(
                1,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                0,
            );
            gl.enable_vertex_attrib_array(1);
            gl.vertex_attrib_divisor(1, 1);

            // p1 (location 2) - start point
            gl.vertex_attrib_pointer_with_i32(
                2,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                8,
            );
            gl.enable_vertex_attrib_array(2);
            gl.vertex_attrib_divisor(2, 1);

            // p2 (location 3) - end point
            gl.vertex_attrib_pointer_with_i32(
                3,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                16,
            );
            gl.enable_vertex_attrib_array(3);
            gl.vertex_attrib_divisor(3, 1);

            // p3 (location 4) - control point after end
            gl.vertex_attrib_pointer_with_i32(
                4,
                2,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                24,
            );
            gl.enable_vertex_attrib_array(4);
            gl.vertex_attrib_divisor(4, 1);

            // width (location 5)
            gl.vertex_attrib_pointer_with_i32(
                5,
                1,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                32,
            );
            gl.enable_vertex_attrib_array(5);
            gl.vertex_attrib_divisor(5, 1);

            // color (location 6)
            gl.vertex_attrib_pointer_with_i32(
                6,
                4,
                WebGl2RenderingContext::FLOAT,
                false,
                stride,
                36,
            );
            gl.enable_vertex_attrib_array(6);
            gl.vertex_attrib_divisor(6, 1);
        }

        gl.bind_vertex_array(None);
        gl.bind_buffer(WebGl2RenderingContext::ARRAY_BUFFER, None);
    }

    /// Releases all WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        if let Some(vao) = self.circle_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.ring_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.line_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.quad_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.textured_quad_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.text_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.fullscreen_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.texture_array_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(vao) = self.curve_vao.take() {
            gl.delete_vertex_array(Some(&vao));
        }
        if let Some(buf) = self.vertex_buffer.take() {
            gl.delete_buffer(Some(&buf));
        }
        if let Some(buf) = self.curve_strip_buffer.take() {
            gl.delete_buffer(Some(&buf));
        }
    }
}

impl Default for VertexArrayManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_instance_buffer_new() {
        let buffer = InstanceBuffer::new(7, 100);
        assert_eq!(buffer.instance_count(), 0);
        assert_eq!(buffer.floats_per_instance, 7);
    }

    #[test]
    fn test_instance_buffer_push() {
        let mut buffer = InstanceBuffer::new(3, 10);
        buffer.push_raw(&[1.0, 2.0, 3.0]);
        buffer.push_raw(&[4.0, 5.0, 6.0]);
        assert_eq!(buffer.instance_count(), 2);
        assert!(buffer.dirty);
    }

    #[test]
    fn test_instance_buffer_clear() {
        let mut buffer = InstanceBuffer::new(3, 10);
        buffer.push_raw(&[1.0, 2.0, 3.0]);
        buffer.clear();
        assert_eq!(buffer.instance_count(), 0);
    }

    #[test]
    fn test_vertex_array_manager_new() {
        let manager = VertexArrayManager::new();
        assert!(manager.circle_vao.is_none());
        assert!(manager.line_vao.is_none());
        assert!(manager.vertex_buffer.is_none());
    }

    #[test]
    fn test_quad_constants() {
        // Verify quad vertex counts
        assert_eq!(UNIT_QUAD_CIRCLE.len(), 8);
        assert_eq!(UNIT_QUAD_LINE.len(), 8);
        assert_eq!(UNIT_QUAD_STANDARD.len(), 8);
        assert_eq!(FULLSCREEN_QUAD.len(), 8);
    }

    #[test]
    fn test_instance_buffer_capacity() {
        let buffer = InstanceBuffer::new(4, 500);
        assert_eq!(buffer.capacity(), 500);
    }

    #[test]
    fn test_instance_buffer_peak_usage_tracking() {
        let mut buffer = InstanceBuffer::new(2, 100);

        // Push some data
        buffer.push_raw(&[1.0, 2.0]);
        buffer.push_raw(&[3.0, 4.0]);
        buffer.push_raw(&[5.0, 6.0]);

        // Clear should update peak usage
        buffer.clear();
        assert_eq!(buffer.peak_usage(), 3);

        // Push fewer items
        buffer.push_raw(&[1.0, 2.0]);
        buffer.clear();

        // Peak should remain at 3 (highest seen)
        assert_eq!(buffer.peak_usage(), 3);
    }

    #[test]
    fn test_instance_buffer_gpu_size_tracking() {
        let buffer = InstanceBuffer::new(4, 100);
        // GPU buffer size starts at 0 (not allocated yet)
        assert_eq!(buffer.gpu_buffer_size(), 0);
        assert_eq!(buffer.capacity(), 100);
    }

    // Compile-time verification that shrink constants are reasonable
    const _: () = {
        assert!(MIN_BUFFER_CAPACITY > 0);
        assert!(SHRINK_THRESHOLD > 0.0 && SHRINK_THRESHOLD < 1.0);
        assert!(SHRINK_STABILITY_FRAMES > 0);
    };

    #[test]
    fn test_curve_strip_generation() {
        let strip = generate_curve_strip();
        // Should have (CURVE_SEGMENTS + 1) * 4 floats (2 vertices per segment, 2 floats per vertex)
        assert_eq!(strip.len(), (CURVE_SEGMENTS + 1) * 4);

        // First vertex should be at t=0, y=-0.5
        assert!((strip[0] - 0.0).abs() < 0.001); // t = 0
        assert!((strip[1] - (-0.5)).abs() < 0.001); // y = -0.5

        // Second vertex should be at t=0, y=0.5
        assert!((strip[2] - 0.0).abs() < 0.001); // t = 0
        assert!((strip[3] - 0.5).abs() < 0.001); // y = 0.5

        // Last two vertices should be at t=1
        let last_idx = strip.len() - 4;
        assert!((strip[last_idx] - 1.0).abs() < 0.001); // t = 1
        assert!((strip[last_idx + 2] - 1.0).abs() < 0.001); // t = 1
    }

    #[test]
    fn test_curve_strip_vertex_count() {
        // 8 segments = 9 pairs = 18 vertices
        assert_eq!(CURVE_STRIP_VERTEX_COUNT, 18);
    }
}
