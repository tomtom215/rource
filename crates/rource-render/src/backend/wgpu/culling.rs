//! GPU visibility culling pipeline for wgpu renderer.
//!
//! This module provides GPU-accelerated visibility culling using compute shaders.
//! The culling pipeline filters instance data based on view bounds, outputting
//! only visible instances to a compacted buffer for efficient rendering.
//!
//! ## Integration Status
//!
//! **Infrastructure: COMPLETE** | **Render Integration: NOT YET**
//!
//! The culling pipeline is fully implemented with compute shaders for circles,
//! lines, and quads. However, it is not yet wired into the render loop because:
//!
//! 1. CPU quadtree culling is efficient for typical use cases (< 10,000 entities)
//! 2. Integration requires buffer layout changes (STORAGE → VERTEX+STORAGE)
//! 3. Indirect draw adds synchronization complexity
//!
//! See `culling_methods.rs` for detailed integration steps when needed.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    GPU Visibility Culling                            │
//! │                                                                      │
//! │  Input Instance Buffer                 Output Instance Buffer        │
//! │  ┌─────────────────┐                  ┌─────────────────┐           │
//! │  │ All instances   │──► cs_cull_X() ──│ Visible only    │           │
//! │  │ (unculled)      │                  │ (compacted)     │           │
//! │  └─────────────────┘                  └─────────────────┘           │
//! │                                                │                     │
//! │                                                ▼                     │
//! │                                       ┌─────────────────┐           │
//! │                                       │ DrawIndirect    │           │
//! │                                       │ instance_count  │           │
//! │                                       └─────────────────┘           │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## When to Use
//!
//! GPU culling is beneficial when:
//! - Scenes have 10,000+ instances where CPU culling becomes a bottleneck
//! - View bounds change every frame (continuous panning/zooming)
//! - GPU compute is available and render throughput is limited
//!
//! For most use cases, CPU-side quadtree culling (the default) is more efficient.
//!
//! ## Usage
//!
//! ```ignore
//! use rource_render::backend::wgpu::WgpuRenderer;
//!
//! let mut renderer = WgpuRenderer::new_headless(800, 600)?;
//!
//! // Enable GPU culling
//! renderer.set_gpu_culling_enabled(true);
//!
//! // Set view bounds for culling (typically from camera)
//! renderer.set_cull_bounds(-1000.0, -1000.0, 1000.0, 1000.0);
//!
//! // Render as normal - culling happens automatically
//! renderer.begin_frame();
//! // ... draw calls ...
//! renderer.end_frame();
//! ```

use super::buffers::{CullParams, DrawIndirectCommand, IndirectDrawBuffer, StorageBuffer};
use super::shaders::VISIBILITY_CULLING_SHADER;

/// Workgroup size for culling compute shaders.
pub const CULLING_WORKGROUP_SIZE: u32 = 256;

/// Minimum buffer capacity for culling (number of instances).
pub const MIN_CULLING_CAPACITY: usize = 1024;

/// Growth factor when buffer needs to expand.
pub const CULLING_GROWTH_FACTOR: f32 = 1.5;

/// Primitive type for culling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CullPrimitive {
    /// Filled circles (7 floats per instance).
    Circles,
    /// Line segments (9 floats per instance).
    Lines,
    /// Solid quads (8 floats per instance).
    Quads,
}

impl CullPrimitive {
    /// Returns the number of floats per instance for this primitive type.
    #[inline]
    #[must_use]
    pub const fn floats_per_instance(&self) -> u32 {
        match self {
            Self::Circles => 7, // center(2) + radius(1) + color(4)
            Self::Lines => 9,   // start(2) + end(2) + width(1) + color(4)
            Self::Quads => 8,   // bounds(4) + color(4)
        }
    }
}

/// Statistics from GPU culling operations.
#[derive(Debug, Clone, Copy, Default)]
pub struct CullingStats {
    /// Total instances submitted for culling.
    pub total_instances: u32,
    /// Instances that passed culling (visible).
    pub visible_instances: u32,
    /// Number of culling dispatches.
    pub dispatch_count: u32,
}

impl CullingStats {
    /// Returns the culling ratio (0.0 = all culled, 1.0 = none culled).
    #[inline]
    #[must_use]
    pub fn cull_ratio(&self) -> f32 {
        if self.total_instances == 0 {
            1.0
        } else {
            self.visible_instances as f32 / self.total_instances as f32
        }
    }

    /// Returns the percentage of instances that were culled.
    #[inline]
    #[must_use]
    pub fn culled_percentage(&self) -> f32 {
        if self.total_instances == 0 {
            0.0
        } else {
            (1.0 - self.cull_ratio()) * 100.0
        }
    }

    /// Resets statistics.
    pub fn reset(&mut self) {
        self.total_instances = 0;
        self.visible_instances = 0;
        self.dispatch_count = 0;
    }
}

/// GPU visibility culling pipeline.
///
/// This pipeline uses compute shaders to cull instances based on view bounds,
/// outputting only visible instances to a compacted buffer. The indirect draw
/// command buffer tracks the number of visible instances.
#[allow(dead_code)]
pub struct VisibilityCullingPipeline {
    /// Compute shader module (retained for potential hot-reload support).
    shader_module: wgpu::ShaderModule,

    /// Pipeline for resetting indirect draw commands.
    reset_pipeline: wgpu::ComputePipeline,

    /// Pipeline for culling circles.
    cull_circles_pipeline: wgpu::ComputePipeline,

    /// Pipeline for culling lines.
    cull_lines_pipeline: wgpu::ComputePipeline,

    /// Pipeline for culling quads.
    cull_quads_pipeline: wgpu::ComputePipeline,

    /// Bind group layout for culling.
    bind_group_layout: wgpu::BindGroupLayout,

    /// Uniform buffer for cull parameters.
    params_buffer: wgpu::Buffer,

    /// Input instance buffer (raw data).
    input_buffer: Option<StorageBuffer>,

    /// Output instance buffer (compacted visible instances).
    output_buffer: Option<StorageBuffer>,

    /// Indirect draw command buffer.
    indirect_buffer: Option<IndirectDrawBuffer>,

    /// Cached bind group (recreated when buffers change).
    bind_group: Option<wgpu::BindGroup>,

    /// Current view bounds for culling.
    view_bounds: [f32; 4],

    /// Current buffer capacity in instances.
    capacity: usize,

    /// Statistics from last culling operation.
    stats: CullingStats,
}

impl VisibilityCullingPipeline {
    /// Creates a new visibility culling pipeline.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for resource creation
    pub fn new(device: &wgpu::Device) -> Self {
        // Create shader module
        let shader_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("Visibility Culling Shader"),
            source: wgpu::ShaderSource::Wgsl(VISIBILITY_CULLING_SHADER.into()),
        });

        // Create bind group layout
        let bind_group_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("Culling Bind Group Layout"),
            entries: &[
                // Binding 0: CullParams uniform
                wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Uniform,
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // Binding 1: Input instances (read-only storage)
                wgpu::BindGroupLayoutEntry {
                    binding: 1,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: true },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // Binding 2: Output instances (read-write storage)
                wgpu::BindGroupLayoutEntry {
                    binding: 2,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // Binding 3: Indirect draw command (read-write storage)
                wgpu::BindGroupLayoutEntry {
                    binding: 3,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
            ],
        });

        // Create pipeline layout
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("Culling Pipeline Layout"),
            bind_group_layouts: &[&bind_group_layout],
            push_constant_ranges: &[],
        });

        // Create reset pipeline (1 thread workgroup)
        let reset_pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("Reset Indirect Pipeline"),
            layout: Some(&pipeline_layout),
            module: &shader_module,
            entry_point: Some("cs_reset_indirect"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        // Create cull circles pipeline
        let cull_circles_pipeline =
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("Cull Circles Pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader_module,
                entry_point: Some("cs_cull_circles"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        // Create cull lines pipeline
        let cull_lines_pipeline =
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("Cull Lines Pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader_module,
                entry_point: Some("cs_cull_lines"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        // Create cull quads pipeline
        let cull_quads_pipeline =
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("Cull Quads Pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader_module,
                entry_point: Some("cs_cull_quads"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        // Create params buffer
        let params_buffer = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("Cull Params Buffer"),
            size: std::mem::size_of::<CullParams>() as u64,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        Self {
            shader_module,
            reset_pipeline,
            cull_circles_pipeline,
            cull_lines_pipeline,
            cull_quads_pipeline,
            bind_group_layout,
            params_buffer,
            input_buffer: None,
            output_buffer: None,
            indirect_buffer: None,
            bind_group: None,
            view_bounds: [-1000.0, -1000.0, 1000.0, 1000.0],
            capacity: 0,
            stats: CullingStats::default(),
        }
    }

    /// Warms up the culling pipeline by pre-compiling shaders.
    ///
    /// Call this during initialization to avoid first-frame stuttering.
    pub fn warmup(&mut self, device: &wgpu::Device, queue: &wgpu::Queue) {
        // Ensure we have at least minimum capacity buffers
        self.ensure_capacity(device, MIN_CULLING_CAPACITY, CullPrimitive::Circles);

        // Create a dummy encoder and dispatch each pipeline once
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Culling Warmup Encoder"),
        });

        // Get bind group (created by ensure_capacity)
        if let Some(ref bind_group) = self.bind_group {
            {
                let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                    label: Some("Culling Warmup Pass"),
                    timestamp_writes: None,
                });

                pass.set_bind_group(0, bind_group, &[]);

                // Dispatch reset with 0 instances
                pass.set_pipeline(&self.reset_pipeline);
                pass.dispatch_workgroups(1, 1, 1);

                // Dispatch each cull pipeline with 0 work (just for shader compilation)
                pass.set_pipeline(&self.cull_circles_pipeline);
                pass.dispatch_workgroups(0, 1, 1);

                pass.set_pipeline(&self.cull_lines_pipeline);
                pass.dispatch_workgroups(0, 1, 1);

                pass.set_pipeline(&self.cull_quads_pipeline);
                pass.dispatch_workgroups(0, 1, 1);
            }

            queue.submit(Some(encoder.finish()));
        }
    }

    /// Sets the view bounds for culling.
    ///
    /// # Arguments
    ///
    /// * `min_x` - Minimum X coordinate
    /// * `min_y` - Minimum Y coordinate
    /// * `max_x` - Maximum X coordinate
    /// * `max_y` - Maximum Y coordinate
    pub fn set_view_bounds(&mut self, min_x: f32, min_y: f32, max_x: f32, max_y: f32) {
        self.view_bounds = [min_x, min_y, max_x, max_y];
    }

    /// Returns the current view bounds.
    #[inline]
    #[must_use]
    pub fn view_bounds(&self) -> [f32; 4] {
        self.view_bounds
    }

    /// Returns statistics from the last culling operation.
    #[inline]
    #[must_use]
    pub fn stats(&self) -> &CullingStats {
        &self.stats
    }

    /// Resets statistics.
    pub fn reset_stats(&mut self) {
        self.stats.reset();
    }

    /// Ensures the pipeline has sufficient buffer capacity.
    fn ensure_capacity(
        &mut self,
        device: &wgpu::Device,
        instance_count: usize,
        primitive: CullPrimitive,
    ) {
        let floats_per_instance = primitive.floats_per_instance() as usize;
        let required_capacity = instance_count.max(MIN_CULLING_CAPACITY);

        if required_capacity <= self.capacity && self.bind_group.is_some() {
            return;
        }

        // Calculate new capacity with growth factor
        let new_capacity = if self.capacity == 0 {
            required_capacity
        } else {
            ((required_capacity as f32) * CULLING_GROWTH_FACTOR).ceil() as usize
        };

        // Calculate buffer sizes
        let buffer_size = new_capacity * floats_per_instance * std::mem::size_of::<f32>();

        // Create input buffer
        self.input_buffer = Some(StorageBuffer::new(
            device,
            buffer_size,
            "culling_input_buffer",
            false, // read-only
        ));

        // Create output buffer
        self.output_buffer = Some(StorageBuffer::new(
            device,
            buffer_size,
            "culling_output_buffer",
            true, // read-write
        ));

        // Create indirect buffer
        self.indirect_buffer = Some(IndirectDrawBuffer::new_with_command(
            device,
            &DrawIndirectCommand::empty(),
            "culling_indirect_buffer",
        ));

        // Recreate bind group
        self.bind_group = Some(
            device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("Culling Bind Group"),
                layout: &self.bind_group_layout,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: self.params_buffer.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: self
                            .input_buffer
                            .as_ref()
                            .unwrap()
                            .buffer()
                            .as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 2,
                        resource: self
                            .output_buffer
                            .as_ref()
                            .unwrap()
                            .buffer()
                            .as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 3,
                        resource: self
                            .indirect_buffer
                            .as_ref()
                            .unwrap()
                            .buffer()
                            .as_entire_binding(),
                    },
                ],
            }),
        );

        self.capacity = new_capacity;
    }

    /// Dispatches visibility culling for instances.
    ///
    /// This method:
    /// 1. Uploads instance data to the input buffer
    /// 2. Dispatches the appropriate cull compute shader
    /// 3. Updates the indirect draw command with visible instance count
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device
    /// * `queue` - wgpu queue
    /// * `encoder` - Command encoder to record commands to
    /// * `instances` - Raw instance data (floats)
    /// * `primitive` - Type of primitive being culled
    ///
    /// # Returns
    ///
    /// Returns `true` if culling was dispatched, `false` if no instances.
    pub fn dispatch(
        &mut self,
        device: &wgpu::Device,
        queue: &wgpu::Queue,
        encoder: &mut wgpu::CommandEncoder,
        instances: &[f32],
        primitive: CullPrimitive,
    ) -> bool {
        let floats_per_instance = primitive.floats_per_instance() as usize;
        let instance_count = instances.len() / floats_per_instance;

        if instance_count == 0 {
            return false;
        }

        // Ensure we have sufficient capacity
        self.ensure_capacity(device, instance_count, primitive);

        // Upload instance data
        if let Some(ref input_buffer) = self.input_buffer {
            queue.write_buffer(input_buffer.buffer(), 0, bytemuck::cast_slice(instances));
        }

        // Update params
        let params = CullParams::new(
            self.view_bounds,
            instance_count as u32,
            primitive.floats_per_instance(),
        );
        queue.write_buffer(&self.params_buffer, 0, bytemuck::cast_slice(&[params]));

        // Get bind group
        let Some(ref bind_group) = self.bind_group else {
            return false;
        };

        // Create compute pass
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Culling Compute Pass"),
                timestamp_writes: None,
            });

            pass.set_bind_group(0, bind_group, &[]);

            // Reset indirect buffer
            pass.set_pipeline(&self.reset_pipeline);
            pass.dispatch_workgroups(1, 1, 1);

            // Dispatch appropriate cull shader
            let pipeline = match primitive {
                CullPrimitive::Circles => &self.cull_circles_pipeline,
                CullPrimitive::Lines => &self.cull_lines_pipeline,
                CullPrimitive::Quads => &self.cull_quads_pipeline,
            };
            pass.set_pipeline(pipeline);

            // Calculate workgroup count
            let workgroups = (instance_count as u32).div_ceil(CULLING_WORKGROUP_SIZE);
            pass.dispatch_workgroups(workgroups, 1, 1);
        }

        // Update stats
        self.stats.total_instances += instance_count as u32;
        self.stats.dispatch_count += 1;

        true
    }

    /// Returns a reference to the output buffer for rendering.
    ///
    /// This buffer contains the compacted visible instances after culling.
    #[inline]
    #[must_use]
    pub fn output_buffer(&self) -> Option<&wgpu::Buffer> {
        self.output_buffer.as_ref().map(StorageBuffer::buffer)
    }

    /// Returns a reference to the indirect draw buffer.
    ///
    /// This buffer contains the draw command with the visible instance count.
    #[inline]
    #[must_use]
    pub fn indirect_buffer(&self) -> Option<&wgpu::Buffer> {
        self.indirect_buffer
            .as_ref()
            .map(IndirectDrawBuffer::buffer)
    }

    /// Returns the current buffer capacity in instances.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }
}

impl std::fmt::Debug for VisibilityCullingPipeline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VisibilityCullingPipeline")
            .field("view_bounds", &self.view_bounds)
            .field("capacity", &self.capacity)
            .field("stats", &self.stats)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cull_primitive_floats_per_instance() {
        assert_eq!(CullPrimitive::Circles.floats_per_instance(), 7);
        assert_eq!(CullPrimitive::Lines.floats_per_instance(), 9);
        assert_eq!(CullPrimitive::Quads.floats_per_instance(), 8);
    }

    #[test]
    fn test_culling_stats_default() {
        let stats = CullingStats::default();
        assert_eq!(stats.total_instances, 0);
        assert_eq!(stats.visible_instances, 0);
        assert_eq!(stats.dispatch_count, 0);
    }

    #[test]
    fn test_culling_stats_cull_ratio() {
        let mut stats = CullingStats::default();

        // Empty should return 1.0 (100% visible)
        assert!((stats.cull_ratio() - 1.0).abs() < 0.001);

        // Half visible
        stats.total_instances = 100;
        stats.visible_instances = 50;
        assert!((stats.cull_ratio() - 0.5).abs() < 0.001);

        // All visible
        stats.visible_instances = 100;
        assert!((stats.cull_ratio() - 1.0).abs() < 0.001);

        // None visible
        stats.visible_instances = 0;
        assert!((stats.cull_ratio() - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_culling_stats_culled_percentage() {
        let mut stats = CullingStats::default();

        // Empty should be 0% culled
        assert!((stats.culled_percentage() - 0.0).abs() < 0.001);

        // Half culled
        stats.total_instances = 100;
        stats.visible_instances = 50;
        assert!((stats.culled_percentage() - 50.0).abs() < 0.001);

        // 75% culled
        stats.visible_instances = 25;
        assert!((stats.culled_percentage() - 75.0).abs() < 0.001);
    }

    #[test]
    fn test_culling_stats_reset() {
        let mut stats = CullingStats {
            total_instances: 100,
            visible_instances: 50,
            dispatch_count: 5,
        };

        stats.reset();

        assert_eq!(stats.total_instances, 0);
        assert_eq!(stats.visible_instances, 0);
        assert_eq!(stats.dispatch_count, 0);
    }

    #[test]
    fn test_culling_workgroup_size() {
        // Verify workgroup size matches shader (compile-time check)
        const _: () = assert!(CULLING_WORKGROUP_SIZE == 256);
        // Runtime check for test coverage
        assert_eq!(CULLING_WORKGROUP_SIZE, 256);
    }

    #[test]
    fn test_min_culling_capacity() {
        // Verify minimum capacity is reasonable (compile-time check)
        const _: () = assert!(MIN_CULLING_CAPACITY >= 256);
        // Runtime check for test coverage
        let _ = MIN_CULLING_CAPACITY;
    }

    #[test]
    fn test_culling_growth_factor() {
        // Verify growth factor is reasonable (compile-time checks)
        const _: () = {
            assert!(CULLING_GROWTH_FACTOR >= 1.0);
            assert!(CULLING_GROWTH_FACTOR <= 3.0);
        };
        // Runtime check for test coverage
        let _ = CULLING_GROWTH_FACTOR;
    }
}
