//! GPU compute pipeline for physics simulation.
//!
//! This module provides GPU-accelerated physics simulation using compute shaders.
//! The physics simulation implements force-directed layout with:
//!
//! - **Repulsion forces**: Entities push each other apart using inverse-square law
//! - **Attraction forces**: Children are pulled toward their parents via spring forces
//! - **Velocity damping**: Stabilizes the simulation over time
//! - **Spatial hashing**: Efficient neighbor queries on GPU
//!
//! ## Architecture
//!
//! The compute pipeline consists of multiple passes:
//!
//! 1. **Clear Grid**: Reset the spatial hash grid
//! 2. **Build Grid**: Populate grid cells with entity counts
//! 3. **Calculate Forces**: Compute repulsion and attraction forces
//! 4. **Integrate**: Apply forces to velocities and update positions
//! 5. **Calculate Bounds**: Parallel reduction for scene bounding box
//!
//! ## Usage
//!
//! ```ignore
//! use rource_render::backend::wgpu::compute::{ComputePipeline, PhysicsConfig, ComputeEntity};
//!
//! // Create pipeline
//! let mut pipeline = ComputePipeline::new(&device)?;
//!
//! // Configure physics
//! pipeline.set_config(PhysicsConfig::default());
//!
//! // Update entities from CPU
//! pipeline.upload_entities(&queue, &entities);
//!
//! // Run simulation step
//! let encoder = device.create_command_encoder(&Default::default());
//! pipeline.dispatch(&mut encoder, dt);
//! queue.submit(Some(encoder.finish()));
//!
//! // Download results back to CPU
//! let updated = pipeline.download_entities(&device, &queue).await;
//! ```
//!
//! ## Performance Characteristics
//!
//! | Aspect | Value |
//! |--------|-------|
//! | Workgroup Size | 64 threads |
//! | Entity Capacity | Dynamic, grows as needed |
//! | Grid Resolution | Configurable (default 64x64) |
//! | Memory Overhead | ~48 bytes per entity + grid buffer |
//!
//! ## Determinism
//!
//! The compute pipeline produces deterministic results when given identical input:
//! - Same entity positions and velocities
//! - Same delta time
//! - Same configuration parameters

use super::shaders::{BOUNDS_SHADER, PHYSICS_FORCE_SHADER};
use super::stats::FrameStats;

#[cfg(feature = "wgpu")]
use wgpu::{
    BindGroup, BindGroupDescriptor, BindGroupEntry, BindGroupLayout, BindGroupLayoutDescriptor,
    BindGroupLayoutEntry, BindingType, Buffer, BufferBindingType, BufferDescriptor, BufferUsages,
    CommandEncoder, ComputePipeline as WgpuComputePipeline, ComputePipelineDescriptor, Device,
    Queue, ShaderModule, ShaderModuleDescriptor, ShaderSource, ShaderStages,
};

/// Workgroup size for compute shaders.
pub const WORKGROUP_SIZE: u32 = 64;

/// Default spatial hash grid size (cells per dimension).
pub const DEFAULT_GRID_CELLS: u32 = 64;

/// Minimum buffer capacity (number of entities).
pub const MIN_ENTITY_CAPACITY: usize = 256;

/// Growth factor when buffer needs to expand.
pub const BUFFER_GROWTH_FACTOR: f32 = 2.0;

/// Configuration for physics simulation.
#[derive(Debug, Clone, Copy)]
pub struct PhysicsConfig {
    /// Repulsion strength between entities.
    /// Higher values push entities apart more aggressively.
    pub repulsion_strength: f32,

    /// Attraction strength toward parent entities.
    /// Higher values pull children closer to parents.
    pub attraction_strength: f32,

    /// Velocity damping factor (0.0 - 1.0).
    /// Applied each frame to stabilize the simulation.
    pub damping: f32,

    /// Maximum velocity magnitude.
    /// Prevents entities from moving too fast.
    pub max_speed: f32,

    /// Spatial hash grid cell size.
    /// Should be roughly 2x the average entity interaction radius.
    pub grid_cell_size: f32,

    /// Number of grid cells per dimension.
    /// Total cells = `grid_cells` * `grid_cells`.
    pub grid_cells: u32,
}

impl Default for PhysicsConfig {
    fn default() -> Self {
        Self {
            repulsion_strength: 1000.0,
            attraction_strength: 0.05,
            damping: 0.9,
            max_speed: 500.0,
            grid_cell_size: 100.0,
            grid_cells: DEFAULT_GRID_CELLS,
        }
    }
}

impl PhysicsConfig {
    /// Creates a configuration optimized for dense layouts.
    ///
    /// Uses stronger repulsion to separate tightly packed entities.
    #[must_use]
    pub fn dense() -> Self {
        Self {
            repulsion_strength: 2000.0,
            attraction_strength: 0.1,
            damping: 0.85,
            max_speed: 600.0,
            grid_cell_size: 50.0,
            grid_cells: 128,
        }
    }

    /// Creates a configuration optimized for sparse layouts.
    ///
    /// Uses weaker forces for more spread-out entities.
    #[must_use]
    pub fn sparse() -> Self {
        Self {
            repulsion_strength: 500.0,
            attraction_strength: 0.02,
            damping: 0.95,
            max_speed: 300.0,
            grid_cell_size: 200.0,
            grid_cells: 32,
        }
    }

    /// Creates a configuration for fast convergence.
    ///
    /// Uses higher damping and stronger forces for quick settling.
    #[must_use]
    pub fn fast_converge() -> Self {
        Self {
            repulsion_strength: 1500.0,
            attraction_strength: 0.08,
            damping: 0.8,
            max_speed: 400.0,
            grid_cell_size: 100.0,
            grid_cells: 64,
        }
    }
}

/// Entity data for GPU physics simulation.
///
/// This struct is designed for efficient GPU transfer with proper alignment.
/// The layout matches the WGSL struct in `PHYSICS_FORCE_SHADER`.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default, bytemuck::Pod, bytemuck::Zeroable)]
pub struct ComputeEntity {
    /// Current position in world coordinates.
    pub position: [f32; 2],

    /// Current velocity vector.
    pub velocity: [f32; 2],

    /// Accumulated force (internal use, cleared after integration).
    pub force: [f32; 2],

    /// Entity mass (affects acceleration from force).
    pub mass: f32,

    /// Entity radius (affects collision/repulsion distance).
    pub radius: f32,
}

impl ComputeEntity {
    /// Creates a new entity with the given position and radius.
    #[must_use]
    pub fn new(x: f32, y: f32, radius: f32) -> Self {
        Self {
            position: [x, y],
            velocity: [0.0, 0.0],
            force: [0.0, 0.0],
            mass: 1.0,
            radius,
        }
    }

    /// Creates an entity with velocity.
    #[must_use]
    pub fn with_velocity(mut self, vx: f32, vy: f32) -> Self {
        self.velocity = [vx, vy];
        self
    }

    /// Creates an entity with custom mass.
    #[must_use]
    pub fn with_mass(mut self, mass: f32) -> Self {
        self.mass = mass;
        self
    }

    /// Returns the entity's position as a tuple.
    #[inline]
    #[must_use]
    pub fn position(&self) -> (f32, f32) {
        (self.position[0], self.position[1])
    }

    /// Returns the entity's velocity as a tuple.
    #[inline]
    #[must_use]
    pub fn velocity(&self) -> (f32, f32) {
        (self.velocity[0], self.velocity[1])
    }

    /// Returns the speed (velocity magnitude).
    #[inline]
    #[must_use]
    pub fn speed(&self) -> f32 {
        let (vx, vy) = self.velocity();
        vx.hypot(vy)
    }
}

/// Size of `ComputeEntity` in bytes.
pub const ENTITY_SIZE: usize = std::mem::size_of::<ComputeEntity>();

/// Physics parameters uniform buffer data.
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

/// Bounds parameters for the bounds calculation shader.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct BoundsParams {
    entity_count: u32,
    _padding: [u32; 3],
}

/// Computed bounds result from GPU.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
pub struct ComputedBounds {
    /// Minimum coordinates (bottom-left corner).
    pub min: [f32; 2],
    /// Maximum coordinates (top-right corner).
    pub max: [f32; 2],
}

impl Default for ComputedBounds {
    fn default() -> Self {
        Self {
            min: [f32::MAX, f32::MAX],
            max: [f32::MIN, f32::MIN],
        }
    }
}

impl ComputedBounds {
    /// Returns the width of the bounding box.
    #[inline]
    #[must_use]
    pub fn width(&self) -> f32 {
        self.max[0] - self.min[0]
    }

    /// Returns the height of the bounding box.
    #[inline]
    #[must_use]
    pub fn height(&self) -> f32 {
        self.max[1] - self.min[1]
    }

    /// Returns the center of the bounding box.
    #[inline]
    #[must_use]
    pub fn center(&self) -> (f32, f32) {
        (
            (self.min[0] + self.max[0]) * 0.5,
            (self.min[1] + self.max[1]) * 0.5,
        )
    }

    /// Returns true if the bounds are valid (min < max).
    #[inline]
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.min[0] < self.max[0] && self.min[1] < self.max[1]
    }
}

/// Statistics for compute pipeline execution.
#[derive(Debug, Clone, Copy, Default)]
pub struct ComputeStats {
    /// Number of entities processed.
    pub entity_count: u32,

    /// Number of compute dispatches.
    pub dispatch_count: u32,

    /// Total invocations across all dispatches.
    pub total_invocations: u64,

    /// Bytes uploaded to GPU this frame.
    pub bytes_uploaded: usize,

    /// Bytes downloaded from GPU this frame.
    pub bytes_downloaded: usize,

    /// Whether bounds calculation was performed.
    pub bounds_calculated: bool,
}

impl ComputeStats {
    /// Resets all statistics to zero.
    pub fn reset(&mut self) {
        *self = Self::default();
    }

    /// Records a dispatch operation.
    pub fn record_dispatch(&mut self, invocations: u64) {
        self.dispatch_count += 1;
        self.total_invocations += invocations;
    }

    /// Returns a summary string.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "Entities: {}, Dispatches: {}, Invocations: {}, Upload: {} bytes, Download: {} bytes",
            self.entity_count,
            self.dispatch_count,
            self.total_invocations,
            self.bytes_uploaded,
            self.bytes_downloaded
        )
    }
}

/// GPU compute pipeline for physics simulation.
///
/// Manages compute shaders, buffers, and bind groups for running
/// force-directed layout simulation on the GPU.
#[cfg(feature = "wgpu")]
#[allow(dead_code)]
pub struct ComputePipeline {
    // Shader modules (retained for pipeline recreation)
    physics_shader: ShaderModule,
    bounds_shader: ShaderModule,

    // Compute pipelines
    clear_grid_pipeline: WgpuComputePipeline,
    build_grid_pipeline: WgpuComputePipeline,
    calculate_forces_pipeline: WgpuComputePipeline,
    integrate_pipeline: WgpuComputePipeline,
    calculate_bounds_pipeline: WgpuComputePipeline,

    // Bind group layouts
    physics_bind_group_layout: BindGroupLayout,
    bounds_bind_group_layout: BindGroupLayout,

    // Buffers
    params_buffer: Buffer,
    entity_buffer: Buffer,
    spatial_hash_buffer: Buffer,
    bounds_params_buffer: Buffer,
    bounds_result_buffer: Buffer,
    staging_buffer: Option<Buffer>,

    // Bind groups (recreated when buffers change)
    physics_bind_group: Option<BindGroup>,
    bounds_bind_group: Option<BindGroup>,

    // Configuration
    config: PhysicsConfig,

    // State
    entity_capacity: usize,
    entity_count: usize,

    // Statistics
    stats: ComputeStats,
}

#[cfg(feature = "wgpu")]
impl ComputePipeline {
    /// Creates a new compute pipeline.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for creating GPU resources
    ///
    /// # Returns
    ///
    /// A new `ComputePipeline` ready for physics simulation.
    pub fn new(device: &Device) -> Self {
        // Create shader modules
        let physics_shader = device.create_shader_module(ShaderModuleDescriptor {
            label: Some("Physics Compute Shader"),
            source: ShaderSource::Wgsl(PHYSICS_FORCE_SHADER.into()),
        });

        let bounds_shader = device.create_shader_module(ShaderModuleDescriptor {
            label: Some("Bounds Compute Shader"),
            source: ShaderSource::Wgsl(BOUNDS_SHADER.into()),
        });

        // Create bind group layouts
        let physics_bind_group_layout =
            device.create_bind_group_layout(&BindGroupLayoutDescriptor {
                label: Some("Physics Bind Group Layout"),
                entries: &[
                    // Params uniform buffer
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
                    // Entity storage buffer
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
                    // Spatial hash storage buffer
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
                ],
            });

        let bounds_bind_group_layout =
            device.create_bind_group_layout(&BindGroupLayoutDescriptor {
                label: Some("Bounds Bind Group Layout"),
                entries: &[
                    // Params uniform buffer
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
                    // Entity storage buffer (read-only)
                    BindGroupLayoutEntry {
                        binding: 1,
                        visibility: ShaderStages::COMPUTE,
                        ty: BindingType::Buffer {
                            ty: BufferBindingType::Storage { read_only: true },
                            has_dynamic_offset: false,
                            min_binding_size: None,
                        },
                        count: None,
                    },
                    // Bounds result buffer
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
                ],
            });

        // Create pipeline layouts
        let physics_pipeline_layout =
            device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("Physics Pipeline Layout"),
                bind_group_layouts: &[&physics_bind_group_layout],
                push_constant_ranges: &[],
            });

        let bounds_pipeline_layout =
            device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("Bounds Pipeline Layout"),
                bind_group_layouts: &[&bounds_bind_group_layout],
                push_constant_ranges: &[],
            });

        // Create compute pipelines
        let clear_grid_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Clear Grid Pipeline"),
            layout: Some(&physics_pipeline_layout),
            module: &physics_shader,
            entry_point: Some("cs_clear_grid"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let build_grid_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Build Grid Pipeline"),
            layout: Some(&physics_pipeline_layout),
            module: &physics_shader,
            entry_point: Some("cs_build_grid"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let calculate_forces_pipeline =
            device.create_compute_pipeline(&ComputePipelineDescriptor {
                label: Some("Calculate Forces Pipeline"),
                layout: Some(&physics_pipeline_layout),
                module: &physics_shader,
                entry_point: Some("cs_calculate_forces"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        let integrate_pipeline = device.create_compute_pipeline(&ComputePipelineDescriptor {
            label: Some("Integrate Pipeline"),
            layout: Some(&physics_pipeline_layout),
            module: &physics_shader,
            entry_point: Some("cs_integrate"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });

        let calculate_bounds_pipeline =
            device.create_compute_pipeline(&ComputePipelineDescriptor {
                label: Some("Calculate Bounds Pipeline"),
                layout: Some(&bounds_pipeline_layout),
                module: &bounds_shader,
                entry_point: Some("cs_calculate_bounds"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        // Create buffers with initial capacity
        let config = PhysicsConfig::default();
        let initial_capacity = MIN_ENTITY_CAPACITY;

        let params_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Physics Params Buffer"),
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

        let grid_size = (config.grid_cells * config.grid_cells) as usize;
        let spatial_hash_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Spatial Hash Buffer"),
            size: (grid_size * 4) as u64, // u32 per cell
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let bounds_params_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Bounds Params Buffer"),
            size: std::mem::size_of::<BoundsParams>() as u64,
            usage: BufferUsages::UNIFORM | BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let bounds_result_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Bounds Result Buffer"),
            size: std::mem::size_of::<ComputedBounds>() as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST | BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });

        Self {
            physics_shader,
            bounds_shader,
            clear_grid_pipeline,
            build_grid_pipeline,
            calculate_forces_pipeline,
            integrate_pipeline,
            calculate_bounds_pipeline,
            physics_bind_group_layout,
            bounds_bind_group_layout,
            params_buffer,
            entity_buffer,
            spatial_hash_buffer,
            bounds_params_buffer,
            bounds_result_buffer,
            staging_buffer: None,
            physics_bind_group: None,
            bounds_bind_group: None,
            config,
            entity_capacity: initial_capacity,
            entity_count: 0,
            stats: ComputeStats::default(),
        }
    }

    /// Returns the current physics configuration.
    #[inline]
    #[must_use]
    pub fn config(&self) -> &PhysicsConfig {
        &self.config
    }

    /// Sets the physics configuration.
    pub fn set_config(&mut self, config: PhysicsConfig) {
        self.config = config;
    }

    /// Returns the current entity count.
    #[inline]
    #[must_use]
    pub fn entity_count(&self) -> usize {
        self.entity_count
    }

    /// Returns the current entity buffer capacity.
    #[inline]
    #[must_use]
    pub fn entity_capacity(&self) -> usize {
        self.entity_capacity
    }

    /// Returns statistics from the last frame.
    #[inline]
    #[must_use]
    pub fn stats(&self) -> &ComputeStats {
        &self.stats
    }

    /// Resets frame statistics.
    pub fn reset_stats(&mut self) {
        self.stats.reset();
    }

    /// Uploads entity data to the GPU.
    ///
    /// This resizes the entity buffer if necessary and recreates bind groups.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for creating buffers
    /// * `queue` - wgpu queue for uploading data
    /// * `entities` - slice of entities to upload
    pub fn upload_entities(&mut self, device: &Device, queue: &Queue, entities: &[ComputeEntity]) {
        self.entity_count = entities.len();
        self.stats.entity_count = entities.len() as u32;

        if entities.is_empty() {
            return;
        }

        // Resize buffer if needed
        if entities.len() > self.entity_capacity {
            let new_capacity = (entities.len() as f32 * BUFFER_GROWTH_FACTOR).ceil() as usize;
            let new_capacity = new_capacity.max(MIN_ENTITY_CAPACITY);
            self.resize_entity_buffer(device, new_capacity);
        }

        // Upload entity data
        let data = bytemuck::cast_slice(entities);
        queue.write_buffer(&self.entity_buffer, 0, data);
        self.stats.bytes_uploaded += data.len();

        // Recreate bind groups
        self.create_bind_groups(device);
    }

    /// Resizes the entity buffer and related resources.
    fn resize_entity_buffer(&mut self, device: &Device, new_capacity: usize) {
        self.entity_capacity = new_capacity;

        self.entity_buffer = device.create_buffer(&BufferDescriptor {
            label: Some("Entity Buffer"),
            size: (new_capacity * ENTITY_SIZE) as u64,
            usage: BufferUsages::STORAGE | BufferUsages::COPY_DST | BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });

        // Invalidate bind groups
        self.physics_bind_group = None;
        self.bounds_bind_group = None;
        self.staging_buffer = None;
    }

    /// Creates or recreates bind groups.
    fn create_bind_groups(&mut self, device: &Device) {
        self.physics_bind_group = Some(device.create_bind_group(&BindGroupDescriptor {
            label: Some("Physics Bind Group"),
            layout: &self.physics_bind_group_layout,
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
                    resource: self.spatial_hash_buffer.as_entire_binding(),
                },
            ],
        }));

        self.bounds_bind_group = Some(device.create_bind_group(&BindGroupDescriptor {
            label: Some("Bounds Bind Group"),
            layout: &self.bounds_bind_group_layout,
            entries: &[
                BindGroupEntry {
                    binding: 0,
                    resource: self.bounds_params_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 1,
                    resource: self.entity_buffer.as_entire_binding(),
                },
                BindGroupEntry {
                    binding: 2,
                    resource: self.bounds_result_buffer.as_entire_binding(),
                },
            ],
        }));
    }

    /// Dispatches the physics simulation compute passes.
    ///
    /// # Arguments
    ///
    /// * `encoder` - command encoder to record compute passes
    /// * `queue` - queue for uploading uniform data
    /// * `delta_time` - time step in seconds
    pub fn dispatch(&mut self, encoder: &mut CommandEncoder, queue: &Queue, delta_time: f32) {
        if self.entity_count == 0 {
            return;
        }

        let Some(bind_group) = &self.physics_bind_group else {
            return;
        };

        // Upload parameters
        let params = PhysicsParams::new(&self.config, self.entity_count as u32, delta_time);
        queue.write_buffer(&self.params_buffer, 0, bytemuck::bytes_of(&params));
        self.stats.bytes_uploaded += std::mem::size_of::<PhysicsParams>();

        let entity_workgroups = (self.entity_count as u32).div_ceil(WORKGROUP_SIZE);
        let grid_total = self.config.grid_cells * self.config.grid_cells;
        let grid_workgroups = grid_total.div_ceil(WORKGROUP_SIZE);

        // Clear spatial hash grid
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Clear Grid Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.clear_grid_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(grid_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(grid_workgroups * WORKGROUP_SIZE));
        }

        // Build spatial hash grid
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Build Grid Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.build_grid_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(entity_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(entity_workgroups * WORKGROUP_SIZE));
        }

        // Calculate forces
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Calculate Forces Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.calculate_forces_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(entity_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(entity_workgroups * WORKGROUP_SIZE));
        }

        // Integrate velocities and positions
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Integrate Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.integrate_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(entity_workgroups, 1, 1);
            self.stats
                .record_dispatch(u64::from(entity_workgroups * WORKGROUP_SIZE));
        }
    }

    /// Dispatches bounds calculation compute pass.
    ///
    /// Call this after `dispatch()` to calculate the bounding box of all entities.
    pub fn dispatch_bounds(&mut self, encoder: &mut CommandEncoder, queue: &Queue) {
        if self.entity_count == 0 {
            return;
        }

        let Some(bind_group) = &self.bounds_bind_group else {
            return;
        };

        // Upload bounds parameters
        let params = BoundsParams {
            entity_count: self.entity_count as u32,
            _padding: [0; 3],
        };
        queue.write_buffer(&self.bounds_params_buffer, 0, bytemuck::bytes_of(&params));

        // Reset bounds to extreme values
        let initial_bounds = ComputedBounds::default();
        queue.write_buffer(
            &self.bounds_result_buffer,
            0,
            bytemuck::bytes_of(&initial_bounds),
        );

        self.stats.bytes_uploaded +=
            std::mem::size_of::<BoundsParams>() + std::mem::size_of::<ComputedBounds>();

        // Dispatch bounds calculation (using larger workgroup for parallel reduction)
        let workgroups = (self.entity_count as u32).div_ceil(256);
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Calculate Bounds Pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.calculate_bounds_pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(workgroups, 1, 1);
            self.stats.record_dispatch(u64::from(workgroups * 256));
        }

        self.stats.bounds_calculated = true;
    }

    /// Prepares to read entity data back from GPU.
    ///
    /// This copies entity data to a staging buffer that can be mapped for reading.
    /// Call this after `dispatch()` and before submitting the command buffer.
    pub fn prepare_readback(&mut self, device: &Device, encoder: &mut CommandEncoder) {
        if self.entity_count == 0 {
            return;
        }

        let size = (self.entity_count * ENTITY_SIZE) as u64;

        // Create or resize staging buffer
        if self.staging_buffer.is_none()
            || self
                .staging_buffer
                .as_ref()
                .is_some_and(|b| b.size() < size)
        {
            self.staging_buffer = Some(device.create_buffer(&BufferDescriptor {
                label: Some("Entity Staging Buffer"),
                size: (self.entity_capacity * ENTITY_SIZE) as u64,
                usage: BufferUsages::MAP_READ | BufferUsages::COPY_DST,
                mapped_at_creation: false,
            }));
        }

        // Copy entity buffer to staging
        encoder.copy_buffer_to_buffer(
            &self.entity_buffer,
            0,
            self.staging_buffer.as_ref().unwrap(),
            0,
            size,
        );
    }

    /// Downloads entity data from the staging buffer.
    ///
    /// This is an async operation that waits for the GPU to complete.
    /// Call `prepare_readback()` first and submit the command buffer.
    ///
    /// # Returns
    ///
    /// Vector of updated entity data, or empty vector if no staging buffer.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn download_entities(&mut self, device: &Device) -> Vec<ComputeEntity> {
        use wgpu::BufferSlice;

        let Some(staging) = &self.staging_buffer else {
            return Vec::new();
        };

        if self.entity_count == 0 {
            return Vec::new();
        }

        let size = (self.entity_count * ENTITY_SIZE) as u64;
        let slice: BufferSlice = staging.slice(0..size);

        // Map buffer for reading
        let (tx, rx) = std::sync::mpsc::channel();
        slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = tx.send(result);
        });

        device.poll(wgpu::Maintain::Wait);

        if rx.recv().is_ok() {
            let data = slice.get_mapped_range();
            let entities: Vec<ComputeEntity> = bytemuck::cast_slice(&data).to_vec();
            drop(data);
            staging.unmap();
            self.stats.bytes_downloaded += entities.len() * ENTITY_SIZE;
            entities
        } else {
            Vec::new()
        }
    }

    /// Downloads entity data from the staging buffer (WASM version).
    #[cfg(target_arch = "wasm32")]
    pub async fn download_entities_async(&mut self, device: &Device) -> Vec<ComputeEntity> {
        use wgpu::BufferSlice;

        let Some(staging) = &self.staging_buffer else {
            return Vec::new();
        };

        if self.entity_count == 0 {
            return Vec::new();
        }

        let size = (self.entity_count * ENTITY_SIZE) as u64;
        let slice: BufferSlice = staging.slice(0..size);

        // Map buffer for reading
        slice.map_async(wgpu::MapMode::Read, |_| {});
        device.poll(wgpu::Maintain::Wait);

        let data = slice.get_mapped_range();
        let entities: Vec<ComputeEntity> = bytemuck::cast_slice(&data).to_vec();
        drop(data);
        staging.unmap();
        self.stats.bytes_downloaded += entities.len() * ENTITY_SIZE;
        entities
    }

    /// Applies compute statistics to frame stats.
    pub fn apply_to_frame_stats(&self, stats: &mut FrameStats) {
        stats.compute_dispatches += self.stats.dispatch_count;
        stats.bytes_uploaded += self.stats.bytes_uploaded as u64;
    }

    /// Warms up compute pipelines by performing a minimal dispatch.
    ///
    /// This forces shader compilation which may otherwise cause stuttering
    /// on the first real dispatch.
    pub fn warmup(&mut self, device: &Device, queue: &Queue) {
        // Create a single test entity
        let test_entity = ComputeEntity::new(0.0, 0.0, 1.0);
        self.upload_entities(device, queue, &[test_entity]);

        // Create a minimal command encoder
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Compute Warmup Encoder"),
        });

        // Dispatch with zero-length operations to trigger pipeline compilation
        self.dispatch(&mut encoder, queue, 0.016);
        self.dispatch_bounds(&mut encoder, queue);

        // Submit and wait for completion
        queue.submit(Some(encoder.finish()));

        #[cfg(not(target_arch = "wasm32"))]
        device.poll(wgpu::Maintain::Wait);

        // Reset state
        self.entity_count = 0;
        self.stats.reset();
    }
}

/// Helper to calculate workgroup dispatch count.
#[inline]
#[must_use]
pub fn workgroups_for(count: u32, workgroup_size: u32) -> u32 {
    count.div_ceil(workgroup_size)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_physics_config_default() {
        let config = PhysicsConfig::default();
        assert_eq!(config.repulsion_strength, 1000.0);
        assert_eq!(config.attraction_strength, 0.05);
        assert_eq!(config.damping, 0.9);
        assert_eq!(config.max_speed, 500.0);
        assert_eq!(config.grid_cells, DEFAULT_GRID_CELLS);
    }

    #[test]
    fn test_physics_config_presets() {
        let dense = PhysicsConfig::dense();
        let sparse = PhysicsConfig::sparse();

        // Dense should have stronger repulsion
        assert!(dense.repulsion_strength > sparse.repulsion_strength);

        // Dense should have more grid cells
        assert!(dense.grid_cells > sparse.grid_cells);

        // Sparse should have lower damping (higher value = more preservation)
        assert!(sparse.damping > dense.damping);
    }

    #[test]
    fn test_physics_config_fast_converge() {
        let config = PhysicsConfig::fast_converge();
        assert!(config.damping < PhysicsConfig::default().damping);
    }

    #[test]
    fn test_compute_entity_new() {
        let entity = ComputeEntity::new(100.0, 200.0, 10.0);

        assert_eq!(entity.position, [100.0, 200.0]);
        assert_eq!(entity.velocity, [0.0, 0.0]);
        assert_eq!(entity.force, [0.0, 0.0]);
        assert_eq!(entity.mass, 1.0);
        assert_eq!(entity.radius, 10.0);
    }

    #[test]
    fn test_compute_entity_with_velocity() {
        let entity = ComputeEntity::new(0.0, 0.0, 5.0).with_velocity(10.0, -5.0);

        assert_eq!(entity.velocity, [10.0, -5.0]);
    }

    #[test]
    fn test_compute_entity_with_mass() {
        let entity = ComputeEntity::new(0.0, 0.0, 5.0).with_mass(2.5);

        assert_eq!(entity.mass, 2.5);
    }

    #[test]
    fn test_compute_entity_position() {
        let entity = ComputeEntity::new(50.0, 75.0, 10.0);

        assert_eq!(entity.position(), (50.0, 75.0));
    }

    #[test]
    fn test_compute_entity_velocity() {
        let entity = ComputeEntity::new(0.0, 0.0, 5.0).with_velocity(3.0, 4.0);

        assert_eq!(entity.velocity(), (3.0, 4.0));
    }

    #[test]
    fn test_compute_entity_speed() {
        let entity = ComputeEntity::new(0.0, 0.0, 5.0).with_velocity(3.0, 4.0);

        // 3-4-5 triangle
        assert!((entity.speed() - 5.0).abs() < 0.001);
    }

    #[test]
    fn test_entity_size_alignment() {
        // Entity should be 32 bytes for proper GPU alignment
        assert_eq!(ENTITY_SIZE, 32);
    }

    #[test]
    fn test_computed_bounds_default() {
        let bounds = ComputedBounds::default();

        assert_eq!(bounds.min, [f32::MAX, f32::MAX]);
        assert_eq!(bounds.max, [f32::MIN, f32::MIN]);
        assert!(!bounds.is_valid());
    }

    #[test]
    fn test_computed_bounds_dimensions() {
        let bounds = ComputedBounds {
            min: [10.0, 20.0],
            max: [100.0, 80.0],
        };

        assert_eq!(bounds.width(), 90.0);
        assert_eq!(bounds.height(), 60.0);
        assert!(bounds.is_valid());
    }

    #[test]
    fn test_computed_bounds_center() {
        let bounds = ComputedBounds {
            min: [0.0, 0.0],
            max: [100.0, 200.0],
        };

        assert_eq!(bounds.center(), (50.0, 100.0));
    }

    #[test]
    fn test_compute_stats_default() {
        let stats = ComputeStats::default();

        assert_eq!(stats.entity_count, 0);
        assert_eq!(stats.dispatch_count, 0);
        assert_eq!(stats.total_invocations, 0);
        assert_eq!(stats.bytes_uploaded, 0);
        assert_eq!(stats.bytes_downloaded, 0);
        assert!(!stats.bounds_calculated);
    }

    #[test]
    fn test_compute_stats_reset() {
        let mut stats = ComputeStats {
            entity_count: 100,
            dispatch_count: 4,
            total_invocations: 10000,
            bytes_uploaded: 5000,
            bytes_downloaded: 5000,
            bounds_calculated: true,
        };

        stats.reset();

        assert_eq!(stats.entity_count, 0);
        assert_eq!(stats.dispatch_count, 0);
        assert!(!stats.bounds_calculated);
    }

    #[test]
    fn test_compute_stats_record_dispatch() {
        let mut stats = ComputeStats::default();

        stats.record_dispatch(1000);
        stats.record_dispatch(500);

        assert_eq!(stats.dispatch_count, 2);
        assert_eq!(stats.total_invocations, 1500);
    }

    #[test]
    fn test_compute_stats_summary() {
        let stats = ComputeStats {
            entity_count: 1000,
            dispatch_count: 4,
            total_invocations: 4096,
            bytes_uploaded: 32000,
            bytes_downloaded: 32000,
            bounds_calculated: true,
        };

        let summary = stats.summary();

        assert!(summary.contains("1000"));
        assert!(summary.contains('4'));
        assert!(summary.contains("32000"));
    }

    #[test]
    fn test_workgroups_for() {
        assert_eq!(workgroups_for(64, 64), 1);
        assert_eq!(workgroups_for(65, 64), 2);
        assert_eq!(workgroups_for(128, 64), 2);
        assert_eq!(workgroups_for(1, 64), 1);
        assert_eq!(workgroups_for(0, 64), 0);
    }

    #[test]
    fn test_physics_params_creation() {
        let config = PhysicsConfig::default();
        let params = PhysicsParams::new(&config, 100, 0.016);

        assert_eq!(params.entity_count, 100);
        assert_eq!(params.delta_time, 0.016);
        assert_eq!(params.repulsion_strength, config.repulsion_strength);
        assert_eq!(params.attraction_strength, config.attraction_strength);
        assert_eq!(params.damping, config.damping);
        assert_eq!(params.max_speed, config.max_speed);
        assert_eq!(params.grid_size, config.grid_cell_size);
        assert_eq!(params.grid_cells, config.grid_cells);
    }

    #[test]
    fn test_entity_bytemuck_cast() {
        let entity = ComputeEntity::new(1.0, 2.0, 3.0);
        let bytes: &[u8] = bytemuck::bytes_of(&entity);

        assert_eq!(bytes.len(), ENTITY_SIZE);

        // Cast back
        let restored: ComputeEntity = *bytemuck::from_bytes(bytes);
        assert_eq!(restored.position, entity.position);
        assert_eq!(restored.radius, entity.radius);
    }

    #[test]
    fn test_bounds_params_padding() {
        let params = BoundsParams {
            entity_count: 42,
            _padding: [0; 3],
        };

        // Should be 16 bytes (4 + 12 padding)
        assert_eq!(std::mem::size_of::<BoundsParams>(), 16);

        let bytes = bytemuck::bytes_of(&params);
        assert_eq!(bytes[0..4], 42u32.to_le_bytes());
    }

    #[test]
    fn test_constants() {
        // Verify constants are accessible (actual validation is at compile time)
        assert_eq!(WORKGROUP_SIZE, 64);
        assert_eq!(DEFAULT_GRID_CELLS, 64);
        assert_eq!(MIN_ENTITY_CAPACITY, 256);
        let _ = BUFFER_GROWTH_FACTOR;
    }

    #[test]
    fn test_physics_config_grid_total_cells() {
        let config = PhysicsConfig::default();
        let total_cells = config.grid_cells * config.grid_cells;

        // 64 x 64 = 4096 cells
        assert_eq!(total_cells, 4096);

        // Dense config has more cells
        let dense = PhysicsConfig::dense();
        let dense_cells = dense.grid_cells * dense.grid_cells;
        assert_eq!(dense_cells, 128 * 128);
    }
}

// Compile-time constant validation
const _: () = {
    assert!(BUFFER_GROWTH_FACTOR > 1.0);
};
