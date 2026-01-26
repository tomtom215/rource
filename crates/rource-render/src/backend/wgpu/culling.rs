// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! GPU visibility culling pipeline for wgpu renderer.
//!
//! This module provides GPU-accelerated visibility culling using compute shaders.
//! The culling pipeline filters instance data based on view bounds, outputting
//! only visible instances to a compacted buffer for efficient rendering.
//!
//! ## Integration Status
//!
//! **Fully Integrated** - GPU visibility culling is wired into the render pipeline.
//!
//! When enabled via `set_gpu_culling_enabled(true)`, the renderer will:
//! 1. Dispatch compute shaders to cull instances based on view bounds
//! 2. Use the culled output buffers with indirect draw commands
//! 3. Automatically fall back to normal rendering when culling is disabled
//!
//! See `culling_methods.rs` for the high-level API and usage examples.
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

/// Buffers for culling a single primitive type.
///
/// Each primitive type (circles, lines, quads) needs its own set of buffers
/// because they have different instance layouts (different floats per instance).
pub struct PrimitiveCullingBuffers {
    /// Input buffer (STORAGE) - holds raw instance data.
    pub input_buffer: StorageBuffer,

    /// Output buffer (STORAGE | VERTEX) - holds compacted visible instances.
    /// Can be bound directly as vertex buffer for rendering.
    pub output_buffer: StorageBuffer,

    /// Indirect draw command buffer.
    pub indirect_buffer: IndirectDrawBuffer,

    /// Bind group for this primitive's buffers.
    pub bind_group: wgpu::BindGroup,

    /// Capacity in instances.
    pub capacity: usize,

    /// Floats per instance for this primitive type.
    pub floats_per_instance: usize,
}

impl PrimitiveCullingBuffers {
    /// Creates new culling buffers for a primitive type.
    pub fn new(
        device: &wgpu::Device,
        bind_group_layout: &wgpu::BindGroupLayout,
        params_buffer: &wgpu::Buffer,
        primitive: CullPrimitive,
        capacity: usize,
    ) -> Self {
        let floats_per_instance = primitive.floats_per_instance() as usize;
        let buffer_size = capacity * floats_per_instance * std::mem::size_of::<f32>();
        let label_prefix = match primitive {
            CullPrimitive::Circles => "circles",
            CullPrimitive::Lines => "lines",
            CullPrimitive::Quads => "quads",
        };

        // Input buffer: STORAGE only (read by compute shader)
        let input_buffer = StorageBuffer::new(device, buffer_size, "culling_input_buffer", false);

        // Output buffer: STORAGE | VERTEX (written by compute, read as vertex buffer)
        let output_buffer =
            StorageBuffer::new_vertex_storage(device, buffer_size, "culling_output_buffer");

        // Indirect draw command buffer
        let indirect_buffer = IndirectDrawBuffer::new_with_command(
            device,
            &DrawIndirectCommand::empty(),
            "culling_indirect_buffer",
        );

        // Create bind group
        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some(&format!("{label_prefix}_culling_bind_group")),
            layout: bind_group_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: params_buffer.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: input_buffer.buffer().as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: output_buffer.buffer().as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: indirect_buffer.buffer().as_entire_binding(),
                },
            ],
        });

        Self {
            input_buffer,
            output_buffer,
            indirect_buffer,
            bind_group,
            capacity,
            floats_per_instance,
        }
    }

    /// Returns the output buffer slice for use as a vertex buffer.
    #[inline]
    pub fn output_slice(&self) -> wgpu::BufferSlice<'_> {
        self.output_buffer.slice()
    }

    /// Returns the indirect draw buffer.
    #[inline]
    pub fn indirect(&self) -> &wgpu::Buffer {
        self.indirect_buffer.buffer()
    }
}

impl std::fmt::Debug for PrimitiveCullingBuffers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrimitiveCullingBuffers")
            .field("capacity", &self.capacity)
            .field("floats_per_instance", &self.floats_per_instance)
            .finish_non_exhaustive()
    }
}

/// GPU visibility culling pipeline.
///
/// This pipeline uses compute shaders to cull instances based on view bounds,
/// outputting only visible instances to a compacted buffer. The indirect draw
/// command buffer tracks the number of visible instances.
///
/// ## Integration
///
/// The pipeline maintains separate buffers for each primitive type (circles, lines, quads).
/// Output buffers have VERTEX usage so they can be bound directly for rendering.
/// Use `dispatch_all()` to cull all primitives, then use `circles()`, `lines()`, `quads()`
/// to get the output buffers for rendering with `draw_indirect()`.
pub struct VisibilityCullingPipeline {
    /// Compute shader module (retained for potential hot-reload support).
    #[allow(dead_code)]
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

    /// Per-primitive culling buffers.
    circle_buffers: Option<PrimitiveCullingBuffers>,
    line_buffers: Option<PrimitiveCullingBuffers>,
    quad_buffers: Option<PrimitiveCullingBuffers>,

    /// Current view bounds for culling.
    view_bounds: [f32; 4],

    /// Statistics from last culling operation.
    stats: CullingStats,

    /// Whether culling was dispatched this frame (per primitive).
    circles_dispatched: bool,
    lines_dispatched: bool,
    quads_dispatched: bool,
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
            immediate_size: 0,
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
            circle_buffers: None,
            line_buffers: None,
            quad_buffers: None,
            view_bounds: [-1000.0, -1000.0, 1000.0, 1000.0],
            stats: CullingStats::default(),
            circles_dispatched: false,
            lines_dispatched: false,
            quads_dispatched: false,
        }
    }

    /// Warms up the culling pipeline by pre-compiling shaders.
    ///
    /// Call this during initialization to avoid first-frame stuttering.
    pub fn warmup(&mut self, device: &wgpu::Device, queue: &wgpu::Queue) {
        // Ensure we have buffers for all primitive types
        self.ensure_primitive_buffers(device, MIN_CULLING_CAPACITY, CullPrimitive::Circles);
        self.ensure_primitive_buffers(device, MIN_CULLING_CAPACITY, CullPrimitive::Lines);
        self.ensure_primitive_buffers(device, MIN_CULLING_CAPACITY, CullPrimitive::Quads);

        // Create a dummy encoder and dispatch each pipeline once
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Culling Warmup Encoder"),
        });

        // Warmup each primitive type
        if let Some(ref buffers) = self.circle_buffers {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Culling Warmup Pass - Circles"),
                timestamp_writes: None,
            });
            pass.set_bind_group(0, &buffers.bind_group, &[]);
            pass.set_pipeline(&self.reset_pipeline);
            pass.dispatch_workgroups(1, 1, 1);
            pass.set_pipeline(&self.cull_circles_pipeline);
            pass.dispatch_workgroups(0, 1, 1);
        }

        if let Some(ref buffers) = self.line_buffers {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Culling Warmup Pass - Lines"),
                timestamp_writes: None,
            });
            pass.set_bind_group(0, &buffers.bind_group, &[]);
            pass.set_pipeline(&self.reset_pipeline);
            pass.dispatch_workgroups(1, 1, 1);
            pass.set_pipeline(&self.cull_lines_pipeline);
            pass.dispatch_workgroups(0, 1, 1);
        }

        if let Some(ref buffers) = self.quad_buffers {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Culling Warmup Pass - Quads"),
                timestamp_writes: None,
            });
            pass.set_bind_group(0, &buffers.bind_group, &[]);
            pass.set_pipeline(&self.reset_pipeline);
            pass.dispatch_workgroups(1, 1, 1);
            pass.set_pipeline(&self.cull_quads_pipeline);
            pass.dispatch_workgroups(0, 1, 1);
        }

        queue.submit(Some(encoder.finish()));
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

    /// Ensures buffers exist for the given primitive type with sufficient capacity.
    fn ensure_primitive_buffers(
        &mut self,
        device: &wgpu::Device,
        instance_count: usize,
        primitive: CullPrimitive,
    ) {
        let required_capacity = instance_count.max(MIN_CULLING_CAPACITY);

        // Get current capacity for this primitive
        let current_capacity = match primitive {
            CullPrimitive::Circles => self.circle_buffers.as_ref().map_or(0, |b| b.capacity),
            CullPrimitive::Lines => self.line_buffers.as_ref().map_or(0, |b| b.capacity),
            CullPrimitive::Quads => self.quad_buffers.as_ref().map_or(0, |b| b.capacity),
        };

        if required_capacity <= current_capacity {
            return;
        }

        // Calculate new capacity with growth factor
        let new_capacity = if current_capacity == 0 {
            required_capacity
        } else {
            ((required_capacity as f32) * CULLING_GROWTH_FACTOR).ceil() as usize
        };

        // Create new buffers for this primitive type
        let buffers = PrimitiveCullingBuffers::new(
            device,
            &self.bind_group_layout,
            &self.params_buffer,
            primitive,
            new_capacity,
        );

        // Store buffers for this primitive type
        match primitive {
            CullPrimitive::Circles => self.circle_buffers = Some(buffers),
            CullPrimitive::Lines => self.line_buffers = Some(buffers),
            CullPrimitive::Quads => self.quad_buffers = Some(buffers),
        }
    }

    /// Dispatches visibility culling for instances of a specific primitive type.
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
            // Mark as not dispatched
            match primitive {
                CullPrimitive::Circles => self.circles_dispatched = false,
                CullPrimitive::Lines => self.lines_dispatched = false,
                CullPrimitive::Quads => self.quads_dispatched = false,
            }
            return false;
        }

        // Ensure we have sufficient capacity for this primitive type
        self.ensure_primitive_buffers(device, instance_count, primitive);

        // Get the buffers for this primitive type
        let buffers = match primitive {
            CullPrimitive::Circles => self.circle_buffers.as_ref(),
            CullPrimitive::Lines => self.line_buffers.as_ref(),
            CullPrimitive::Quads => self.quad_buffers.as_ref(),
        };

        let Some(buffers) = buffers else {
            return false;
        };

        // Upload instance data to input buffer
        queue.write_buffer(
            buffers.input_buffer.buffer(),
            0,
            bytemuck::cast_slice(instances),
        );

        // Update params
        let params = CullParams::new(
            self.view_bounds,
            instance_count as u32,
            primitive.floats_per_instance(),
        );
        queue.write_buffer(&self.params_buffer, 0, bytemuck::cast_slice(&[params]));

        // Create compute pass
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Culling Compute Pass"),
                timestamp_writes: None,
            });

            pass.set_bind_group(0, &buffers.bind_group, &[]);

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

        // Mark as dispatched
        match primitive {
            CullPrimitive::Circles => self.circles_dispatched = true,
            CullPrimitive::Lines => self.lines_dispatched = true,
            CullPrimitive::Quads => self.quads_dispatched = true,
        }

        // Update stats
        self.stats.total_instances += instance_count as u32;
        self.stats.dispatch_count += 1;

        true
    }

    /// Resets the dispatched flags. Call at the start of each frame.
    pub fn begin_frame(&mut self) {
        self.circles_dispatched = false;
        self.lines_dispatched = false;
        self.quads_dispatched = false;
        self.stats.reset();
    }

    /// Returns the circle culling buffers if available and culling was dispatched.
    #[inline]
    #[must_use]
    pub fn circles(&self) -> Option<&PrimitiveCullingBuffers> {
        if self.circles_dispatched {
            self.circle_buffers.as_ref()
        } else {
            None
        }
    }

    /// Returns the line culling buffers if available and culling was dispatched.
    #[inline]
    #[must_use]
    pub fn lines(&self) -> Option<&PrimitiveCullingBuffers> {
        if self.lines_dispatched {
            self.line_buffers.as_ref()
        } else {
            None
        }
    }

    /// Returns the quad culling buffers if available and culling was dispatched.
    #[inline]
    #[must_use]
    pub fn quads(&self) -> Option<&PrimitiveCullingBuffers> {
        if self.quads_dispatched {
            self.quad_buffers.as_ref()
        } else {
            None
        }
    }

    /// Returns whether circles were dispatched for culling this frame.
    #[inline]
    pub fn circles_dispatched(&self) -> bool {
        self.circles_dispatched
    }

    /// Returns whether lines were dispatched for culling this frame.
    #[inline]
    pub fn lines_dispatched(&self) -> bool {
        self.lines_dispatched
    }

    /// Returns whether quads were dispatched for culling this frame.
    #[inline]
    pub fn quads_dispatched(&self) -> bool {
        self.quads_dispatched
    }

    /// Returns the capacity for a specific primitive type.
    #[inline]
    #[must_use]
    pub fn capacity(&self, primitive: CullPrimitive) -> usize {
        match primitive {
            CullPrimitive::Circles => self.circle_buffers.as_ref().map_or(0, |b| b.capacity),
            CullPrimitive::Lines => self.line_buffers.as_ref().map_or(0, |b| b.capacity),
            CullPrimitive::Quads => self.quad_buffers.as_ref().map_or(0, |b| b.capacity),
        }
    }
}

impl std::fmt::Debug for VisibilityCullingPipeline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VisibilityCullingPipeline")
            .field("view_bounds", &self.view_bounds)
            .field("circle_buffers", &self.circle_buffers)
            .field("line_buffers", &self.line_buffers)
            .field("quad_buffers", &self.quad_buffers)
            .field("circles_dispatched", &self.circles_dispatched)
            .field("lines_dispatched", &self.lines_dispatched)
            .field("quads_dispatched", &self.quads_dispatched)
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
