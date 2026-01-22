//! GPU buffer management for wgpu renderer.
//!
//! This module provides abstractions for vertex buffers, instance buffers,
//! and uniform buffers used in the rendering pipeline. Key features include:
//!
//! - Efficient instance buffer management with automatic resizing
//! - Sub-data updates to minimize GPU memory allocation overhead
//! - Pre-allocated vertex buffers for unit quads
//! - Uniform buffer management for shared shader parameters
//!
//! ## Performance
//!
//! The instance buffer implementation uses several optimizations:
//!
//! - **Capacity over-allocation**: Buffers are allocated with 2x headroom
//!   to reduce reallocation frequency
//! - **Write buffer**: Uses `queue.write_buffer()` for small updates,
//!   avoiding staging buffer overhead
//! - **Lazy shrinking**: Buffers shrink only after sustained low usage
//!   to avoid thrashing
//!
//! ## Usage
//!
//! ```ignore
//! let mut circles = InstanceBuffer::new(device, 7, 1000, "circle_instances");
//!
//! // Add instances each frame
//! circles.push_raw(&[x, y, radius, r, g, b, a]);
//! circles.upload(queue);
//!
//! // Use in render pass
//! render_pass.set_vertex_buffer(1, circles.slice());
//! render_pass.draw(0..4, 0..circles.instance_count() as u32);
//!
//! // Clear for next frame
//! circles.clear();
//! ```

use wgpu::util::DeviceExt;

use super::stats::FrameStats;

/// Unit quad vertices for circle rendering.
/// Coordinates from -1 to 1 for easy distance calculations in shader.
pub const UNIT_QUAD_CIRCLE: [f32; 8] = [
    -1.0, -1.0, // Bottom-left
    1.0, -1.0, // Bottom-right
    -1.0, 1.0, // Top-left
    1.0, 1.0, // Top-right
];

/// Unit quad vertices for line rendering.
/// X: 0 to 1 (along line), Y: -0.5 to 0.5 (perpendicular).
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

/// Minimum capacity threshold - buffers won't shrink below this.
const MIN_BUFFER_CAPACITY: usize = 100;

/// Shrink threshold - buffer shrinks if usage is below this fraction of capacity.
const SHRINK_THRESHOLD: f32 = 0.25;

/// Number of frames of low usage before shrinking.
const SHRINK_STABILITY_FRAMES: u32 = 120;

/// Growth factor when buffer needs to expand.
const GROWTH_FACTOR: usize = 2;

/// A buffer for storing per-instance data for batch rendering.
///
/// Instance buffers hold per-primitive data (position, color, etc.) that
/// varies between instances in a single draw call. They are uploaded to
/// the GPU each frame and used with instanced rendering.
#[derive(Debug)]
pub struct InstanceBuffer {
    /// The wgpu buffer object.
    buffer: wgpu::Buffer,

    /// Current data in CPU memory.
    data: Vec<f32>,

    /// Number of floats per instance.
    floats_per_instance: usize,

    /// Maximum capacity in instances.
    capacity: usize,

    /// GPU buffer capacity (in bytes).
    gpu_buffer_size: usize,

    /// Peak usage in instances during the current measurement window.
    peak_usage: usize,

    /// Frames since last significant usage.
    low_usage_frames: u32,

    /// Debug label for the buffer.
    label: &'static str,
}

impl InstanceBuffer {
    /// Creates a new instance buffer.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for buffer creation
    /// * `floats_per_instance` - Number of f32 values per instance
    /// * `initial_capacity` - Initial capacity in instances
    /// * `label` - Debug label for GPU debugging tools
    ///
    /// # Returns
    ///
    /// A new instance buffer with the specified capacity.
    pub fn new(
        device: &wgpu::Device,
        floats_per_instance: usize,
        initial_capacity: usize,
        label: &'static str,
    ) -> Self {
        let byte_size = initial_capacity * floats_per_instance * std::mem::size_of::<f32>();

        let buffer = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: byte_size as u64,
            usage: wgpu::BufferUsages::VERTEX | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        Self {
            buffer,
            data: Vec::with_capacity(floats_per_instance * initial_capacity),
            floats_per_instance,
            capacity: initial_capacity,
            gpu_buffer_size: byte_size,
            peak_usage: 0,
            low_usage_frames: 0,
            label,
        }
    }

    /// Clears all instance data and updates usage tracking.
    ///
    /// This should be called at the start of each frame before adding
    /// new instances. The buffer capacity is retained for reuse.
    pub fn clear(&mut self) {
        // Track peak usage before clearing
        let current_instances = self.instance_count();
        if current_instances > self.peak_usage {
            self.peak_usage = current_instances;
        }

        self.data.clear();
    }

    /// Returns the number of instances currently stored.
    #[inline]
    pub fn instance_count(&self) -> usize {
        if self.floats_per_instance == 0 {
            0
        } else {
            self.data.len() / self.floats_per_instance
        }
    }

    /// Returns whether the buffer is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns the number of floats per instance.
    #[inline]
    pub fn floats_per_instance(&self) -> usize {
        self.floats_per_instance
    }

    /// Pushes raw float data for an instance.
    ///
    /// # Arguments
    ///
    /// * `data` - Float values for one instance
    ///
    /// # Panics
    ///
    /// Panics in debug builds if `data.len() != floats_per_instance`.
    #[inline]
    pub fn push_raw(&mut self, data: &[f32]) {
        debug_assert_eq!(
            data.len(),
            self.floats_per_instance,
            "Instance data size mismatch: expected {}, got {}",
            self.floats_per_instance,
            data.len()
        );
        self.data.extend_from_slice(data);
    }

    /// Uploads data to GPU.
    ///
    /// This method efficiently handles buffer resizing and data upload:
    /// - If data fits in existing buffer, uses `write_buffer` for fast update
    /// - If buffer needs to grow, creates a new larger buffer
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device (only needed if buffer must grow)
    /// * `queue` - wgpu queue for data upload
    /// * `stats` - Frame statistics to update
    pub fn upload(&mut self, device: &wgpu::Device, queue: &wgpu::Queue, stats: &mut FrameStats) {
        if self.data.is_empty() {
            return;
        }

        let byte_data = bytemuck::cast_slice::<f32, u8>(&self.data);
        let data_size = byte_data.len();

        // Check if we need to grow the buffer
        if data_size > self.gpu_buffer_size {
            // Calculate new capacity (grow by factor)
            let new_instance_capacity = (self.data.len() / self.floats_per_instance
                * GROWTH_FACTOR)
                .max(MIN_BUFFER_CAPACITY);
            let new_byte_size =
                new_instance_capacity * self.floats_per_instance * std::mem::size_of::<f32>();

            // Create new larger buffer
            self.buffer = device.create_buffer(&wgpu::BufferDescriptor {
                label: Some(self.label),
                size: new_byte_size as u64,
                usage: wgpu::BufferUsages::VERTEX | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            });

            self.capacity = new_instance_capacity;
            self.gpu_buffer_size = new_byte_size;
        }

        // Upload data
        queue.write_buffer(&self.buffer, 0, byte_data);
        stats.record_upload(data_size as u64);
    }

    /// Called at end of frame to update usage tracking and potentially shrink.
    ///
    /// Returns `true` if the buffer was shrunk.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for buffer recreation
    pub fn end_frame(&mut self, device: &wgpu::Device) -> bool {
        let usage_fraction = if self.capacity > 0 {
            self.peak_usage as f32 / self.capacity as f32
        } else {
            1.0
        };

        if usage_fraction < SHRINK_THRESHOLD && self.capacity > MIN_BUFFER_CAPACITY {
            self.low_usage_frames += 1;

            if self.low_usage_frames >= SHRINK_STABILITY_FRAMES {
                // Shrink to 2x peak usage or minimum capacity
                let new_capacity = (self.peak_usage * GROWTH_FACTOR).max(MIN_BUFFER_CAPACITY);

                if new_capacity < self.capacity {
                    self.shrink_to(device, new_capacity);
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
    fn shrink_to(&mut self, device: &wgpu::Device, new_capacity: usize) {
        let new_byte_size = new_capacity * self.floats_per_instance * std::mem::size_of::<f32>();

        self.buffer = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(self.label),
            size: new_byte_size as u64,
            usage: wgpu::BufferUsages::VERTEX | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        self.capacity = new_capacity;
        self.gpu_buffer_size = new_byte_size;

        // Shrink the Vec capacity
        let new_vec_capacity = new_capacity * self.floats_per_instance;
        self.data.shrink_to(new_vec_capacity);
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

    /// Returns a reference to the wgpu buffer.
    #[inline]
    pub fn buffer(&self) -> &wgpu::Buffer {
        &self.buffer
    }

    /// Returns a buffer slice for the entire buffer.
    #[inline]
    pub fn slice(&self) -> wgpu::BufferSlice<'_> {
        self.buffer.slice(..)
    }

    /// Returns a buffer slice for the current data.
    #[inline]
    pub fn data_slice(&self) -> wgpu::BufferSlice<'_> {
        let byte_size = self.data.len() * std::mem::size_of::<f32>();
        self.buffer.slice(..byte_size as u64)
    }

    /// Returns the current GPU buffer size in bytes.
    #[inline]
    pub fn gpu_buffer_size(&self) -> usize {
        self.gpu_buffer_size
    }

    /// Returns the debug label.
    #[inline]
    pub fn label(&self) -> &'static str {
        self.label
    }
}

/// Uniform buffer for shared shader parameters.
///
/// Contains global parameters that are shared across all primitives
/// in a frame, such as resolution and time.
#[derive(Debug)]
pub struct UniformBuffer {
    /// The wgpu buffer object.
    buffer: wgpu::Buffer,

    /// Bind group layout for this uniform buffer.
    bind_group_layout: wgpu::BindGroupLayout,

    /// Bind group for shader access.
    bind_group: wgpu::BindGroup,
}

/// Uniform data structure matching shader layout.
///
/// This must match the WGSL uniform struct exactly (including padding).
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
pub struct Uniforms {
    /// Viewport resolution (width, height).
    pub resolution: [f32; 2],
    /// Time in seconds (for animations).
    pub time: f32,
    /// Padding for 16-byte alignment (unused, required for GPU alignment).
    #[doc(hidden)]
    pub padding: f32,
}

impl Default for Uniforms {
    fn default() -> Self {
        Self {
            resolution: [1.0, 1.0],
            time: 0.0,
            padding: 0.0,
        }
    }
}

impl UniformBuffer {
    /// Creates a new uniform buffer.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for buffer and bind group creation
    ///
    /// # Returns
    ///
    /// A new uniform buffer with default values.
    pub fn new(device: &wgpu::Device) -> Self {
        let uniforms = Uniforms::default();

        let buffer = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("uniform_buffer"),
            contents: bytemuck::cast_slice(&[uniforms]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });

        let bind_group_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("uniform_bind_group_layout"),
            entries: &[wgpu::BindGroupLayoutEntry {
                binding: 0,
                visibility: wgpu::ShaderStages::VERTEX | wgpu::ShaderStages::FRAGMENT,
                ty: wgpu::BindingType::Buffer {
                    ty: wgpu::BufferBindingType::Uniform,
                    has_dynamic_offset: false,
                    min_binding_size: None,
                },
                count: None,
            }],
        });

        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("uniform_bind_group"),
            layout: &bind_group_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: buffer.as_entire_binding(),
            }],
        });

        Self {
            buffer,
            bind_group_layout,
            bind_group,
        }
    }

    /// Updates the uniform buffer with new values.
    ///
    /// # Arguments
    ///
    /// * `queue` - wgpu queue for data upload
    /// * `uniforms` - New uniform values
    pub fn update(&self, queue: &wgpu::Queue, uniforms: &Uniforms) {
        queue.write_buffer(&self.buffer, 0, bytemuck::cast_slice(&[*uniforms]));
    }

    /// Returns a reference to the bind group layout.
    #[inline]
    pub fn bind_group_layout(&self) -> &wgpu::BindGroupLayout {
        &self.bind_group_layout
    }

    /// Returns a reference to the bind group.
    #[inline]
    pub fn bind_group(&self) -> &wgpu::BindGroup {
        &self.bind_group
    }

    /// Returns a reference to the buffer.
    #[inline]
    pub fn buffer(&self) -> &wgpu::Buffer {
        &self.buffer
    }
}

/// Manages vertex buffers for unit quads.
///
/// Pre-allocated vertex buffers for the different quad types used in
/// rendering. These are created once and reused across all frames.
#[derive(Debug)]
pub struct VertexBuffers {
    /// Unit quad for circle rendering (-1 to 1).
    pub circle_quad: wgpu::Buffer,

    /// Unit quad for line rendering (0-1 x, -0.5-0.5 y).
    pub line_quad: wgpu::Buffer,

    /// Unit quad for standard quad/text rendering (0 to 1).
    pub standard_quad: wgpu::Buffer,

    /// Fullscreen quad for post-processing (-1 to 1 clip space).
    pub fullscreen_quad: wgpu::Buffer,
}

impl VertexBuffers {
    /// Creates all vertex buffers.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for buffer creation
    pub fn new(device: &wgpu::Device) -> Self {
        Self {
            circle_quad: device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("circle_quad_vertices"),
                contents: bytemuck::cast_slice(&UNIT_QUAD_CIRCLE),
                usage: wgpu::BufferUsages::VERTEX,
            }),
            line_quad: device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("line_quad_vertices"),
                contents: bytemuck::cast_slice(&UNIT_QUAD_LINE),
                usage: wgpu::BufferUsages::VERTEX,
            }),
            standard_quad: device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("standard_quad_vertices"),
                contents: bytemuck::cast_slice(&UNIT_QUAD_STANDARD),
                usage: wgpu::BufferUsages::VERTEX,
            }),
            fullscreen_quad: device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("fullscreen_quad_vertices"),
                contents: bytemuck::cast_slice(&FULLSCREEN_QUAD),
                usage: wgpu::BufferUsages::VERTEX,
            }),
        }
    }

    /// Returns the vertex buffer layout for position-only quads.
    ///
    /// Used for circle, ring, line, quad, and fullscreen quad rendering.
    pub fn position_layout() -> wgpu::VertexBufferLayout<'static> {
        wgpu::VertexBufferLayout {
            array_stride: 2 * std::mem::size_of::<f32>() as u64,
            step_mode: wgpu::VertexStepMode::Vertex,
            attributes: &[wgpu::VertexAttribute {
                format: wgpu::VertexFormat::Float32x2,
                offset: 0,
                shader_location: 0,
            }],
        }
    }
}

/// Storage buffer for compute shaders.
///
/// Used for GPU-side physics simulation data (positions, velocities, forces).
#[derive(Debug)]
pub struct StorageBuffer {
    /// The wgpu buffer object.
    buffer: wgpu::Buffer,

    /// Buffer size in bytes.
    size: usize,

    /// Debug label.
    label: &'static str,
}

impl StorageBuffer {
    /// Creates a new storage buffer.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for buffer creation
    /// * `size` - Buffer size in bytes
    /// * `label` - Debug label
    /// * `read_write` - Whether the buffer can be written by shaders
    pub fn new(device: &wgpu::Device, size: usize, label: &'static str, read_write: bool) -> Self {
        let usage = if read_write {
            wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_DST
                | wgpu::BufferUsages::COPY_SRC
        } else {
            wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST
        };

        let buffer = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: size as u64,
            usage,
            mapped_at_creation: false,
        });

        Self {
            buffer,
            size,
            label,
        }
    }

    /// Creates a new storage buffer initialized with data.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for buffer creation
    /// * `data` - Initial buffer contents
    /// * `label` - Debug label
    /// * `read_write` - Whether the buffer can be written by shaders
    pub fn new_with_data<T: bytemuck::Pod>(
        device: &wgpu::Device,
        data: &[T],
        label: &'static str,
        read_write: bool,
    ) -> Self {
        let usage = if read_write {
            wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_DST
                | wgpu::BufferUsages::COPY_SRC
        } else {
            wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST
        };

        let buffer = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some(label),
            contents: bytemuck::cast_slice(data),
            usage,
        });

        Self {
            buffer,
            size: std::mem::size_of_val(data),
            label,
        }
    }

    /// Updates the buffer with new data.
    ///
    /// # Arguments
    ///
    /// * `queue` - wgpu queue for data upload
    /// * `data` - New buffer contents
    pub fn update<T: bytemuck::Pod>(&self, queue: &wgpu::Queue, data: &[T]) {
        queue.write_buffer(&self.buffer, 0, bytemuck::cast_slice(data));
    }

    /// Returns a reference to the buffer.
    #[inline]
    pub fn buffer(&self) -> &wgpu::Buffer {
        &self.buffer
    }

    /// Returns the buffer size in bytes.
    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the debug label.
    #[inline]
    pub fn label(&self) -> &'static str {
        self.label
    }
}

// Compile-time constant validation
const _: () = {
    assert!(MIN_BUFFER_CAPACITY > 0);
    assert!(SHRINK_THRESHOLD > 0.0);
    assert!(SHRINK_THRESHOLD < 1.0);
    assert!(SHRINK_STABILITY_FRAMES > 0);
    assert!(GROWTH_FACTOR >= 2);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unit_quad_sizes() {
        assert_eq!(UNIT_QUAD_CIRCLE.len(), 8);
        assert_eq!(UNIT_QUAD_LINE.len(), 8);
        assert_eq!(UNIT_QUAD_STANDARD.len(), 8);
        assert_eq!(FULLSCREEN_QUAD.len(), 8);
    }

    #[test]
    fn test_circle_quad_range() {
        for &v in &UNIT_QUAD_CIRCLE {
            assert!((-1.0..=1.0).contains(&v));
        }
    }

    #[test]
    fn test_line_quad_range() {
        // X values should be 0 to 1
        assert!((UNIT_QUAD_LINE[0] - 0.0).abs() < 0.001);
        assert!((UNIT_QUAD_LINE[2] - 1.0).abs() < 0.001);
        // Y values should be -0.5 to 0.5
        assert!((UNIT_QUAD_LINE[1] - (-0.5)).abs() < 0.001);
        assert!((UNIT_QUAD_LINE[5] - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_standard_quad_range() {
        for &v in &UNIT_QUAD_STANDARD {
            assert!((0.0..=1.0).contains(&v));
        }
    }

    #[test]
    fn test_fullscreen_quad_range() {
        for &v in &FULLSCREEN_QUAD {
            assert!((-1.0..=1.0).contains(&v));
        }
    }

    #[test]
    fn test_uniforms_default() {
        let uniforms = Uniforms::default();
        assert!((uniforms.resolution[0] - 1.0).abs() < 0.001);
        assert!((uniforms.resolution[1] - 1.0).abs() < 0.001);
        assert!((uniforms.time - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_uniforms_size() {
        // Uniforms must be 16 bytes (4 floats) for proper GPU alignment
        assert_eq!(std::mem::size_of::<Uniforms>(), 16);
    }

    #[test]
    fn test_uniforms_alignment() {
        // Uniforms must have 4-byte alignment (f32)
        assert_eq!(std::mem::align_of::<Uniforms>(), 4);
    }

    #[test]
    fn test_constants() {
        // Verify constants are accessible (actual validation is at compile time)
        let _ = MIN_BUFFER_CAPACITY;
        let _ = SHRINK_THRESHOLD;
        let _ = SHRINK_STABILITY_FRAMES;
        let _ = GROWTH_FACTOR;
    }

    // Note: Tests requiring wgpu::Device are integration tests that need
    // actual GPU access. They should be run with the full test harness.
}
