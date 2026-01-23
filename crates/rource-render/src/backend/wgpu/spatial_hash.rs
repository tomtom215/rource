// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! O(N) GPU Spatial Hash Pipeline.
//!
//! This module implements a proper spatial hash that enables O(N) neighbor queries
//! instead of O(N²) brute force. The algorithm is:
//!
//! 1. **Clear Counts**: Zero cell count buffer
//! 2. **Count Entities**: Atomic increment per entity's cell
//! 3. **Prefix Sum**: Parallel exclusive scan for cell offsets
//! 4. **Scatter Entities**: Sort entity indices by cell
//! 5. **Calculate Forces**: Query only 3x3 neighborhood
//! 6. **Integrate**: Apply forces to velocities and positions
//!
//! ## Performance Comparison
//!
//! With 5000 entities and a 64×64 grid:
//! - O(N²): 25,000,000 comparisons
//! - O(N): ~11,000 comparisons (2200× speedup)
//!
//! ## Usage
//!
//! ```ignore
//! let mut pipeline = SpatialHashPipeline::new(&device)?;
//! pipeline.upload_entities(&queue, &entities);
//! pipeline.dispatch(&mut encoder, &queue, dt);
//! let updated = pipeline.download_entities(&device, &queue).await;
//! ```

use super::compute::{ComputeEntity, ComputeStats, PhysicsConfig, ENTITY_SIZE};
use super::shaders::PHYSICS_SPATIAL_HASH_SHADER;

#[cfg(feature = "wgpu")]
use wgpu::{
    BindGroup, BindGroupDescriptor, BindGroupEntry, BindGroupLayout, BindGroupLayoutDescriptor,
    BindGroupLayoutEntry, BindingType, Buffer, BufferBindingType, BufferDescriptor, BufferUsages,
    CommandEncoder, ComputePipeline as WgpuComputePipeline, ComputePipelineDescriptor, Device,
    Queue, ShaderModule, ShaderModuleDescriptor, ShaderSource, ShaderStages,
};

/// Workgroup size matching the shader.
pub const WORKGROUP_SIZE: u32 = 256;

/// Minimum entity buffer capacity.
pub const MIN_ENTITY_CAPACITY: usize = 256;

/// Physics parameters uniform buffer.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct PhysicsParams {
    entity_count: u32,
    delta_time: f32,
    repulsion_strength: f32,
    attraction_strength: f32,
    damping: f32,
    max_speed: f32,
    grid_size: f32,
    grid_cells: u32,
}

impl PhysicsParams {
    fn new(config: &PhysicsConfig, entity_count: u32, delta_time: f32) -> Self {
        Self {
            entity_count,
            delta_time,
            repulsion_strength: config.repulsion_strength,
            attraction_strength: config.attraction_strength,
            damping: config.damping,
            max_speed: config.max_speed,
            grid_size: config.grid_cell_size,
            grid_cells: config.grid_cells,
        }
    }
}

/// O(N) Spatial Hash Compute Pipeline.
///
/// Uses a proper spatial hash with prefix sum to enable neighbor-only queries.
#[cfg(feature = "wgpu")]
#[allow(dead_code)]
pub struct SpatialHashPipeline {
    // Shader module
    shader: ShaderModule,

    // Compute pipelines for each pass
    clear_counts_pipeline: WgpuComputePipeline,
    count_entities_pipeline: WgpuComputePipeline,
    prefix_sum_local_pipeline: WgpuComputePipeline,
    prefix_sum_partials_pipeline: WgpuComputePipeline,
    prefix_sum_add_pipeline: WgpuComputePipeline,
    init_scatter_pipeline: WgpuComputePipeline,
    scatter_entities_pipeline: WgpuComputePipeline,
    calculate_forces_pipeline: WgpuComputePipeline,
    integrate_pipeline: WgpuComputePipeline,

    // Bind group layout
    bind_group_layout: BindGroupLayout,

    // Buffers
    params_buffer: Buffer,
    entity_buffer: Buffer,
    cell_counts_buffer: Buffer,
    cell_offsets_buffer: Buffer,
    entity_indices_buffer: Buffer,
    scatter_offsets_buffer: Buffer,
    partial_sums_buffer: Buffer,
    staging_buffer: Option<Buffer>,

    // Bind group (recreated when buffers change)
    bind_group: Option<BindGroup>,

    // Configuration
    config: PhysicsConfig,

    // State
    entity_capacity: usize,
    entity_count: usize,

    // Statistics
    stats: ComputeStats,
}

#[cfg(feature = "wgpu")]
impl SpatialHashPipeline {
    /// Creates a new O(N) spatial hash pipeline.
    pub fn new(device: &Device) -> Self {
        // Create shader module
        let shader = device.create_shader_module(ShaderModuleDescriptor {
            label: Some("Spatial Hash Physics Shader"),
            source: ShaderSource::Wgsl(PHYSICS_SPATIAL_HASH_SHADER.into()),
        });

        // Create bind group layout with all 7 bindings
        let bind_group_layout = device.create_bind_group_layout(&BindGroupLayoutDescriptor {
            label: Some("Spatial Hash Bind Group Layout"),
            entries: &[
                // binding 0: params (uniform)
                BindGroupLayoutEntry {
                    binding: 0,
                    visibility: ShaderStages::COMPUTE,
                    ty: BindingType::Buffer {
                        ty: BufferBindingType::Uniform,
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // binding 1: entities (storage, read_write)
                BindGroupLayoutEntry {
                    binding: 1,
                    visibility: ShaderStages::COMPUTE,
                    ty: BindingType::Buffer {
                        ty: BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // binding 2: cell_counts (storage, read_write)
                BindGroupLayoutEntry {
                    binding: 2,
                    visibility: ShaderStages::COMPUTE,
                    ty: BindingType::Buffer {
                        ty: BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // binding 3: cell_offsets (storage, read_write)
                BindGroupLayoutEntry {
                    binding: 3,
                    visibility: ShaderStages::COMPUTE,
                    ty: BindingType::Buffer {
                        ty: BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // binding 4: entity_indices (storage, read_write)
                BindGroupLayoutEntry {
                    binding: 4,
                    visibility: ShaderStages::COMPUTE,
                    ty: BindingType::Buffer {
                        ty: BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // binding 5: scatter_offsets (storage, read_write)
                BindGroupLayoutEntry {
                    binding: 5,
                    visibility: ShaderStages::COMPUTE,
                    ty: BindingType::Buffer {
                        ty: BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                // binding 6: partial_sums (storage, read_write)
                BindGroupLayoutEntry {
                    binding: 6,
                    visibility: ShaderStages::COMPUTE,
                    ty: BindingType::Buffer {
                        ty: BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
            ],
        });

        // Create pipeline layout
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("Spatial Hash Pipeline Layout"),
            bind_group_layouts: &[&bind_group_layout],
            push_constant_ranges: &[],
        });

        // Create all compute pipelines
        let clear_counts_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Clear Cell Counts Pipeline"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("cs_clear_cell_counts"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let count_entities_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Count Entities Pipeline"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("cs_count_entities_per_cell"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let prefix_sum_local_pipeline =
            device.create_compute_pipeline(&ComputePipelineDescriptor {
                label: Some("Prefix Sum Local Pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some("cs_prefix_sum_local"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        let prefix_sum_partials_pipeline =
            device.create_compute_pipeline(&ComputePipelineDescriptor {
                label: Some("Prefix Sum Partials Pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some("cs_prefix_sum_partials"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        let prefix_sum_add_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Prefix Sum Add Pipeline"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("cs_prefix_sum_add"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let init_scatter_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Init Scatter Offsets Pipeline"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("cs_init_scatter_offsets"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let scatter_entities_pipeline =
            device.create_compute_pipeline(&ComputePipelineDescriptor {
                label: Some("Scatter Entities Pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some("cs_scatter_entities"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        let calculate_forces_pipeline =
            device.create_compute_pipeline(&ComputePipelineDescriptor {
                label: Some("Calculate Forces Spatial Pipeline"),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some("cs_calculate_forces_spatial"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        let integrate_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Integrate Spatial Pipeline"),
            layout: Some(&pipeline_layout),
            module: &shader,
            entry_point: Some("cs_integrate_spatial"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let config = PhysicsConfig::default();
        let initial_capacity = MIN_ENTITY_CAPACITY;
        let grid_cells = config.grid_cells;
        let total_cells = (grid_cells * grid_cells) as usize;
        let num_workgroups = total_cells.div_ceil(WORKGROUP_SIZE as usize);

        // Create buffers
        let params_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Spatial Hash Params Buffer"),
            size: std::mem::size_of::<PhysicsParams>() as u64,
            usage: BufferUsages::UNIFORM | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let entity_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Entity Buffer"),
            size: (initial_capacity * ENTITY_SIZE) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST | BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });

        let cell_counts_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Cell Counts Buffer"),
            size: (total_cells * 4) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        // +1 for end marker
        let cell_offsets_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Cell Offsets Buffer"),
            size: ((total_cells + 1) * 4) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let entity_indices_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Entity Indices Buffer"),
            size: (initial_capacity * 4) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let scatter_offsets_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Scatter Offsets Buffer"),
            size: (total_cells * 4) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let partial_sums_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Partial Sums Buffer"),
            size: (num_workgroups * 4) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        Self {
            shader,
            clear_counts_pipeline,
            count_entities_pipeline,
            prefix_sum_local_pipeline,
            prefix_sum_partials_pipeline,
            prefix_sum_add_pipeline,
            init_scatter_pipeline,
            scatter_entities_pipeline,
            calculate_forces_pipeline,
            integrate_pipeline,
            bind_group_layout,
            params_buffer,
            entity_buffer,
            cell_counts_buffer,
            cell_offsets_buffer,
            entity_indices_buffer,
            scatter_offsets_buffer,
            partial_sums_buffer,
            staging_buffer: None,
            bind_group: None,
            config,
            entity_capacity: initial_capacity,
            entity_count: 0,
            stats: ComputeStats::default(),
        }
    }

    /// Sets the physics configuration.
    pub fn set_config(&mut self, config: PhysicsConfig) {
        self.config = config;
    }

    /// Returns the current physics configuration.
    #[must_use]
    pub fn config(&self) -> &PhysicsConfig {
        &self.config
    }

    /// Returns the number of entities currently loaded.
    #[must_use]
    pub fn entity_count(&self) -> usize {
        self.entity_count
    }

    /// Returns statistics from the last dispatch.
    #[must_use]
    pub fn stats(&self) -> &ComputeStats {
        &self.stats
    }

    /// Resets statistics.
    pub fn reset_stats(&mut self) {
        self.stats.reset();
    }

    /// Uploads entities to the GPU.
    pub fn upload_entities(&mut self, device: &Device, queue: &Queue, entities: &[ComputeEntity]) {
        self.entity_count = entities.len();
        self.stats.entity_count = entities.len() as u32;

        if entities.is_empty() {
            return;
        }

        // Grow buffer if needed
        if entities.len() > self.entity_capacity {
            let new_capacity = (entities.len() * 2).max(MIN_ENTITY_CAPACITY);
            self.resize_buffers(device, new_capacity);
        }

        // Upload entity data
        let data = bytemuck::cast_slice(entities);
        queue.write_buffer(&self.entity_buffer, 0, data);
        self.stats.bytes_uploaded += data.len();

        // Ensure bind group is created
        if self.bind_group.is_none() {
            self.create_bind_group(device);
        }
    }

    /// Resizes all entity-dependent buffers.
    fn resize_buffers(&mut self, device: &Device, new_capacity: usize) {
        self.entity_capacity = new_capacity;

        self.entity_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Entity Buffer"),
            size: (new_capacity * ENTITY_SIZE) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST | BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });

        self.entity_indices_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Entity Indices Buffer"),
            size: (new_capacity * 4) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        // Invalidate bind group and staging buffer
        self.bind_group = None;
        self.staging_buffer = None;
    }

    /// Creates the bind group.
    fn create_bind_group(&mut self, device: &Device) {
        self.bind_group = Some(device.create_bind_group(&BindGroupDescriptor {
            label: Some("Spatial Hash Bind Group"),
            layout: &self.bind_group_layout,
            entries: &[
                BindGroupEntry {
                    binding: 0,
                    resource: self.params_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 1,
                    resource: self.entity_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 2,
                    resource: self.cell_counts_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 3,
                    resource: self.cell_offsets_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 4,
                    resource: self.entity_indices_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 5,
                    resource: self.scatter_offsets_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 6,
                    resource: self.partial_sums_buffer.as_entire_binding(),
                },
            ],
        }));
    }

    /// Dispatches all compute passes for one physics simulation step.
    ///
    /// The pass sequence is:
    /// 1. Clear cell counts
    /// 2. Count entities per cell
    /// 3. Prefix sum (local + partials + add)
    /// 4. Init scatter offsets
    /// 5. Scatter entities
    /// 6. Calculate forces (O(N) neighbor queries)
    /// 7. Integrate
    pub fn dispatch(&mut self, encoder: &mut CommandEncoder, queue: &Queue, delta_time: f32) {
        if self.entity_count == 0 {
            return;
        }

        let Some(bind_group) = &self.bind_group else {
            return;
        };

        // Upload parameters
        let params = PhysicsParams::new(&self.config, self.entity_count as u32, delta_time);
        queue.write_buffer(&self.params_buffer, 0, bytemuck::bytes_of(&params));
        self.stats.bytes_uploaded += std::mem::size_of::<PhysicsParams>();

        let entity_workgroups = (self.entity_count as u32).div_ceil(WORKGROUP_SIZE);
        let total_cells = self.config.grid_cells * self.config.grid_cells;
        let cell_workgroups = total_cells.div_ceil(WORKGROUP_SIZE);

        // Pass 1: Clear cell counts
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Clear Cell Counts Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.clear_counts_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(cell_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(cell_workgroups * WORKGROUP_SIZE));
        }

        // Pass 2: Count entities per cell
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Count Entities Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.count_entities_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(entity_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(entity_workgroups * WORKGROUP_SIZE));
        }

        // Pass 3a: Prefix sum local (workgroup scan + store partials)
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Prefix Sum Local Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.prefix_sum_local_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(cell_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(cell_workgroups * WORKGROUP_SIZE));
        }

        // Pass 3b: Scan partial sums (single workgroup)
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Prefix Sum Partials Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.prefix_sum_partials_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(1, 1, 1);
            self.stats.record_dispatch(u64::from(WORKGROUP_SIZE));
        }

        // Pass 3c: Add partials to complete scan
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Prefix Sum Add Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.prefix_sum_add_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(cell_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(cell_workgroups * WORKGROUP_SIZE));
        }

        // Pass 4a: Initialize scatter offsets
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Init Scatter Offsets Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.init_scatter_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(cell_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(cell_workgroups * WORKGROUP_SIZE));
        }

        // Pass 4b: Scatter entities into sorted order
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Scatter Entities Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.scatter_entities_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(entity_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(entity_workgroups * WORKGROUP_SIZE));
        }

        // Pass 5: Calculate forces using spatial hash
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Calculate Forces Spatial Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.calculate_forces_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(entity_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(entity_workgroups * WORKGROUP_SIZE));
        }

        // Pass 6: Integrate velocities and positions
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Integrate Spatial Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.integrate_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(entity_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(entity_workgroups * WORKGROUP_SIZE));
        }
    }

    /// Downloads entities from the GPU (sync, WASM compatible).
    ///
    /// This method uses device polling to synchronously wait for buffer mapping.
    /// Suitable for use in synchronous frame loops like `requestAnimationFrame`.
    #[cfg(target_arch = "wasm32")]
    pub fn download_entities_sync(&mut self, device: &Device, queue: &Queue) -> Vec<ComputeEntity> {
        if self.entity_count == 0 {
            return Vec::new();
        }

        let buffer_size = self.entity_count * ENTITY_SIZE;

        // Create staging buffer if needed
        if self.staging_buffer.is_none() {
            self.staging_buffer = Some(device.create_buffer(&BufferDescriptor {
                label: Some("Entity Staging Buffer"),
                size: (self.entity_capacity * ENTITY_SIZE) as u64,
                usage: BufferUsages::MAP_READ | BufferUsages::COPY_DST,
                mapped_at_creation: false,
            }));
        }

        let staging = self.staging_buffer.as_ref().unwrap();

        // Copy from entity buffer to staging
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Download Entities Encoder"),
        });
        encoder.copy_buffer_to_buffer(&self.entity_buffer, 0, staging, 0, buffer_size as u64);
        queue.submit(Some(encoder.finish()));

        // Map and read using polling (sync)
        let slice = staging.slice(0..buffer_size as u64);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        device.poll(wgpu::Maintain::Wait);

        let data = slice.get_mapped_range();
        let entities: Vec<ComputeEntity> = bytemuck::cast_slice(&data).to_vec();
        drop(data);
        staging.unmap();

        self.stats.bytes_downloaded += buffer_size;
        entities
    }

    /// Downloads entities from the GPU (sync, native only).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn download_entities_sync(&mut self, device: &Device, queue: &Queue) -> Vec<ComputeEntity> {
        if self.entity_count == 0 {
            return Vec::new();
        }

        let buffer_size = self.entity_count * ENTITY_SIZE;

        // Create staging buffer if needed
        if self.staging_buffer.is_none() {
            self.staging_buffer = Some(device.create_buffer(&BufferDescriptor {
                label: Some("Entity Staging Buffer"),
                size: (self.entity_capacity * ENTITY_SIZE) as u64,
                usage: BufferUsages::MAP_READ | BufferUsages::COPY_DST,
                mapped_at_creation: false,
            }));
        }

        let staging = self.staging_buffer.as_ref().unwrap();

        // Copy from entity buffer to staging
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Download Entities Encoder"),
        });
        encoder.copy_buffer_to_buffer(&self.entity_buffer, 0, staging, 0, buffer_size as u64);
        queue.submit(Some(encoder.finish()));

        // Map and read
        let slice = staging.slice(0..buffer_size as u64);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        device.poll(wgpu::Maintain::Wait);

        let data = slice.get_mapped_range();
        let entities: Vec<ComputeEntity> = bytemuck::cast_slice(&data).to_vec();
        drop(data);
        staging.unmap();

        self.stats.bytes_downloaded += buffer_size;
        entities
    }

    /// Warms up all compute pipelines by running zero-sized dispatches.
    pub fn warmup(&mut self, device: &Device, queue: &Queue) {
        // Create a temporary bind group if needed
        let needs_temp = self.bind_group.is_none();
        if needs_temp {
            self.create_bind_group(device);
        }

        let Some(bind_group) = &self.bind_group else {
            return;
        };

        let mut encoder =
            device.create_command_encoder(&wgpu::CommandEncoderDescriptor { label: None });

        // Run each pipeline with 0 workgroups to trigger compilation
        for pipeline in [
            &self.clear_counts_pipeline,
            &self.count_entities_pipeline,
            &self.prefix_sum_local_pipeline,
            &self.prefix_sum_partials_pipeline,
            &self.prefix_sum_add_pipeline,
            &self.init_scatter_pipeline,
            &self.scatter_entities_pipeline,
            &self.calculate_forces_pipeline,
            &self.integrate_pipeline,
        ] {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: None,
                timestamp_writes: None,
            });
            pass.set_pipeline(pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            // Don't actually dispatch (0 workgroups) - just binding triggers compilation
        }

        queue.submit(Some(encoder.finish()));

        // Clean up temp bind group
        if needs_temp {
            self.bind_group = None;
        }
    }
}

#[cfg(all(test, feature = "wgpu"))]
mod tests {
    use super::*;

    #[test]
    fn test_physics_params_size() {
        // PhysicsParams must be exactly 32 bytes for GPU uniform alignment
        assert_eq!(std::mem::size_of::<PhysicsParams>(), 32);
    }

    #[test]
    fn test_workgroup_size() {
        // Workgroup size must match shader constant
        assert_eq!(WORKGROUP_SIZE, 256);
    }

    #[test]
    fn test_shader_has_all_entry_points() {
        // Verify shader contains all required entry points
        let shader = PHYSICS_SPATIAL_HASH_SHADER;

        // Pass 1: Clear counts
        assert!(shader.contains("fn cs_clear_cell_counts"));

        // Pass 2: Count entities
        assert!(shader.contains("fn cs_count_entities_per_cell"));

        // Pass 3: Prefix sum
        assert!(shader.contains("fn cs_prefix_sum_local"));
        assert!(shader.contains("fn cs_prefix_sum_partials"));
        assert!(shader.contains("fn cs_prefix_sum_add"));

        // Pass 4: Scatter
        assert!(shader.contains("fn cs_init_scatter_offsets"));
        assert!(shader.contains("fn cs_scatter_entities"));

        // Pass 5-6: Forces and integrate
        assert!(shader.contains("fn cs_calculate_forces_spatial"));
        assert!(shader.contains("fn cs_integrate_spatial"));
    }

    #[test]
    fn test_shader_has_spatial_hash_buffers() {
        let shader = PHYSICS_SPATIAL_HASH_SHADER;

        // Verify all required buffer bindings exist
        assert!(shader.contains("@group(0) @binding(0)"));
        assert!(shader.contains("@group(0) @binding(1)"));
        assert!(shader.contains("@group(0) @binding(2)"));
        assert!(shader.contains("@group(0) @binding(3)"));
        assert!(shader.contains("@group(0) @binding(4)"));
        assert!(shader.contains("@group(0) @binding(5)"));
        assert!(shader.contains("@group(0) @binding(6)"));

        // Verify buffer declarations
        assert!(shader.contains("cell_counts"));
        assert!(shader.contains("cell_offsets"));
        assert!(shader.contains("entity_indices"));
        assert!(shader.contains("scatter_offsets"));
        assert!(shader.contains("partial_sums"));
    }

    #[test]
    fn test_shader_uses_neighbor_query() {
        let shader = PHYSICS_SPATIAL_HASH_SHADER;

        // Verify 3x3 neighbor query pattern in force calculation
        assert!(shader.contains("for (var dy = -1; dy <= 1; dy++)"));
        assert!(shader.contains("for (var dx = -1; dx <= 1; dx++)"));

        // Verify it uses cell_offsets for range queries
        assert!(shader.contains("cell_offsets[neighbor_cell]"));
        assert!(shader.contains("cell_offsets[neighbor_cell + 1u]"));

        // Verify it reads from entity_indices
        assert!(shader.contains("entity_indices[i]"));
    }

    #[test]
    fn test_shader_has_blelloch_scan() {
        let shader = PHYSICS_SPATIAL_HASH_SHADER;

        // Blelloch scan has up-sweep and down-sweep phases
        // Up-sweep: shared_data[bi] += shared_data[ai]
        // Down-sweep: shared_data[ai] = shared_data[bi], shared_data[bi] += tmp
        assert!(shader.contains("shared_data[bi] += shared_data[ai]"));
        assert!(shader.contains("shared_data[ai] = shared_data[bi]"));
    }

    #[test]
    fn test_entity_size_matches_compute() {
        // Entity size must match between this module and compute module
        assert_eq!(
            std::mem::size_of::<ComputeEntity>(),
            super::super::compute::ENTITY_SIZE
        );
    }
}
