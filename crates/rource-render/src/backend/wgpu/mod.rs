// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! wgpu rendering backend for cross-platform GPU-accelerated rendering.
//!
//! This module provides a wgpu-based renderer that implements the [`Renderer`] trait,
//! enabling GPU-accelerated rendering on native (Vulkan, Metal, DX12) and web (WebGPU).
//!
//! ## Features
//!
//! - Instanced rendering for efficient draw call batching
//! - Anti-aliased primitives (circles, lines) via WGSL shaders
//! - Font atlas for efficient text rendering
//! - GPU bloom and shadow post-processing effects
//! - GPU compute for physics simulation
//! - State caching to minimize API overhead
//! - Deterministic output for identical inputs
//!
//! ## Usage
//!
//! ### Native
//!
//! ```ignore
//! use rource_render::backend::wgpu::WgpuRenderer;
//!
//! // Create renderer with a window
//! let renderer = WgpuRenderer::new_with_window(&window)?;
//!
//! // Or create headless for offscreen rendering
//! let renderer = WgpuRenderer::new_headless(800, 600)?;
//! ```
//!
//! ### WASM (WebGPU)
//!
//! ```ignore
//! use rource_render::backend::wgpu::WgpuRenderer;
//!
//! let canvas: web_sys::HtmlCanvasElement = ...;
//! let renderer = WgpuRenderer::new_from_canvas(&canvas).await?;
//! ```
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                         WgpuRenderer                                │
//! │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────────┐ │
//! │  │ PipelineManager │ FontAtlas │ │BloomPipeline│ │ComputePipeline│ │
//! │  │ (pipelines) │ │ (textures) │ │ (effects)  │ │ (physics)    │ │
//! │  └─────────────┘ └─────────────┘ └─────────────┘ └───────────────┘ │
//! │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────────┐ │
//! │  │ InstanceBuffers│ RenderState │ │ShadowPipeline│ │  FrameStats  │ │
//! │  │ (batching)  │ │ (caching)  │ │ (effects)  │ │ (metrics)    │ │
//! │  └─────────────┘ └─────────────┘ └─────────────┘ └───────────────┘ │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Performance Characteristics
//!
//! | Aspect | Details |
//! |--------|---------|
//! | Draw Batching | All primitives use GPU instancing |
//! | State Caching | Redundant binds avoided via `RenderState` |
//! | Buffer Updates | Sub-data updates when capacity permits |
//! | Post-Processing | FBO-based bloom and shadow effects |
//! | Physics | GPU compute shaders for force simulation |
//! | Determinism | Identical input produces identical output |
//!
//! ## Module Structure
//!
//! The wgpu backend is split into focused modules:
//!
//! | Module | Purpose |
//! |--------|---------|
//! | `error` | Error types for wgpu operations |
//! | `bloom` | GPU bloom post-processing pipeline |
//! | `shadow` | GPU shadow post-processing pipeline |
//! | `buffers` | Instance and vertex buffer management |
//! | `compute` | GPU compute shaders for physics |
//! | `culling` | GPU visibility culling pipeline |
//! | `pipeline` | Render pipeline creation and management |
//! | `shaders` | WGSL shader source code |
//! | `state` | Render state caching |
//! | `stats` | Frame statistics tracking |
//! | `textures` | Font atlas and texture management |
//! | `effects_methods` | Bloom/shadow configuration methods |
//! | `physics_methods` | Physics dispatch methods |
//! | `culling_methods` | GPU culling methods |
//! | `flush_passes` | Flush pass rendering methods |

// Allow common patterns in new code
#![allow(clippy::too_many_lines)]
#![allow(clippy::map_unwrap_or)]
#![allow(clippy::too_many_arguments)]
// On WASM, wgpu types aren't Send/Sync due to browser single-threaded runtime.
// These warnings are expected and safe to ignore for WASM targets.
#![cfg_attr(target_arch = "wasm32", allow(clippy::future_not_send))]
#![cfg_attr(target_arch = "wasm32", allow(clippy::arc_with_non_send_sync))]

// Core submodules (public API)
pub mod bloom;
pub mod buffers;
pub mod compute;
pub mod culling;
pub mod error;
pub mod icons;
pub mod pipeline;
pub mod shaders;
pub mod shadow;
pub mod spatial_hash;
pub mod state;
pub mod stats;
pub mod textures;

// Internal implementation modules (methods on WgpuRenderer)
mod culling_methods;
mod effects_methods;
mod flush_passes;
mod icons_methods;
mod physics_methods;

use rustc_hash::FxHashMap as HashMap;
use std::sync::Arc;

use rource_math::{Bounds, Color, Mat4, Vec2};

use crate::{FontCache, FontId, Renderer, TextureId};

use bloom::BloomPipeline;
use buffers::{InstanceBuffer, UniformBuffer, VertexBuffers};
use compute::ComputePipeline;
use pipeline::PipelineManager;
use shadow::ShadowPipeline;
use state::RenderState;
use stats::FrameStats;
use textures::{FontAtlas, GlyphKey, ManagedTexture, TextureArray};

use culling::VisibilityCullingPipeline;
use spatial_hash::SpatialHashPipeline;

// Re-export key types for external use
pub use bloom::BloomConfig;
pub use compute::{ComputeEntity, ComputeStats, PhysicsConfig};
pub use culling::{CullPrimitive, CullingStats};
pub use effects_methods::VsyncMode;
pub use error::WgpuError;
pub use shadow::ShadowConfig;
pub use stats::ActivePrimitives;

// GpuInfo is defined at the end of this file, accessible via `use crate::backend::wgpu::GpuInfo`

/// wgpu renderer implementing the Renderer trait.
///
/// This renderer uses wgpu for GPU-accelerated rendering across native and web platforms.
/// It batches draw calls using instanced rendering for optimal performance.
#[allow(dead_code, clippy::struct_excessive_bools)]
pub struct WgpuRenderer {
    /// wgpu instance (retained for context recovery).
    instance: wgpu::Instance,

    /// wgpu adapter (retained for device recreation).
    adapter: wgpu::Adapter,

    /// wgpu device.
    device: Arc<wgpu::Device>,

    /// wgpu queue.
    queue: Arc<wgpu::Queue>,

    /// Render surface (None for headless).
    surface: Option<wgpu::Surface<'static>>,

    /// Surface configuration (None for headless).
    surface_config: Option<wgpu::SurfaceConfiguration>,

    /// Viewport width.
    width: u32,

    /// Viewport height.
    height: u32,

    /// Current transformation matrix.
    transform: Mat4,

    /// Clip rectangle stack.
    clips: Vec<Bounds>,

    /// Font cache for glyph rasterization.
    font_cache: FontCache,

    /// Font atlas for GPU text rendering.
    font_atlas: FontAtlas,

    /// User-loaded textures.
    textures: HashMap<TextureId, ManagedTexture>,

    /// Next texture ID.
    next_texture_id: u32,

    /// Shared uniform buffer.
    uniform_buffer: UniformBuffer,

    /// Shared bind group for uniforms.
    uniform_bind_group: wgpu::BindGroup,

    /// Uniform bind group layout.
    uniform_bind_group_layout: wgpu::BindGroupLayout,

    /// Vertex buffers for unit quads.
    vertex_buffers: VertexBuffers,

    /// Pipeline manager for render pipelines (created lazily).
    pipeline_manager: Option<PipelineManager>,

    /// Texture bind group layout for font atlas and user textures.
    texture_bind_group_layout: wgpu::BindGroupLayout,

    /// Instance buffer for circles.
    circle_instances: InstanceBuffer,

    /// Instance buffer for rings.
    ring_instances: InstanceBuffer,

    /// Instance buffer for lines.
    line_instances: InstanceBuffer,

    /// Instance buffer for Catmull-Rom curves.
    curve_instances: InstanceBuffer,

    /// Instance buffer for solid quads.
    quad_instances: InstanceBuffer,

    /// Instance buffers for textured quads (grouped by texture).
    textured_quad_instances: HashMap<TextureId, InstanceBuffer>,

    /// Instance buffer for text glyphs.
    text_instances: InstanceBuffer,

    /// Instance buffer for file icons (texture array quads).
    file_icon_instances: InstanceBuffer,

    /// GPU bloom post-processing pipeline.
    bloom_pipeline: Option<BloomPipeline>,

    /// GPU shadow post-processing pipeline.
    shadow_pipeline: Option<ShadowPipeline>,

    /// GPU compute pipeline for physics (O(N²) brute force - legacy).
    compute_pipeline: Option<ComputePipeline>,

    /// O(N) GPU spatial hash pipeline for physics (preferred).
    spatial_hash_pipeline: Option<SpatialHashPipeline>,

    /// Whether to use O(N) spatial hash (true) or O(N²) brute force (false).
    /// Default is true for optimal performance with large entity counts.
    use_spatial_hash: bool,

    /// GPU state cache.
    render_state: RenderState,

    /// Frame statistics.
    frame_stats: FrameStats,

    /// Current frame's command encoder.
    current_encoder: Option<wgpu::CommandEncoder>,

    /// Current frame's surface texture.
    current_surface_texture: Option<wgpu::SurfaceTexture>,

    /// Current frame's render target view.
    current_target_view: Option<wgpu::TextureView>,

    /// Scene FBO for post-processing (render-to-texture).
    scene_texture: Option<wgpu::Texture>,

    /// Scene texture view.
    scene_texture_view: Option<wgpu::TextureView>,

    /// Whether bloom is enabled.
    bloom_enabled: bool,

    /// Whether shadow is enabled.
    shadow_enabled: bool,

    /// Reusable buffer for texture IDs (avoids per-frame allocation in `upload_textured_quads`).
    cached_texture_ids: Vec<TextureId>,

    /// GPU visibility culling pipeline.
    culling_pipeline: Option<VisibilityCullingPipeline>,

    /// Whether GPU visibility culling is enabled.
    gpu_culling_enabled: bool,

    /// Current cull bounds in world coordinates (`min_x`, `min_y`, `max_x`, `max_y`).
    cull_bounds: [f32; 4],

    /// Current scissor rectangle in screen coordinates (x, y, width, height).
    /// None means no scissor (full viewport).
    current_scissor: Option<ScissorRect>,

    /// File icon texture array (opt-in, call `init_file_icons()` to enable).
    file_icon_array: Option<TextureArray>,
}

/// A scissor rectangle in screen coordinates.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct ScissorRect {
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
}

// ============================================================================
// Constructor and Initialization Methods
// ============================================================================

impl WgpuRenderer {
    /// Creates a new headless wgpu renderer for offscreen rendering.
    ///
    /// # Arguments
    ///
    /// * `width` - Viewport width in pixels
    /// * `height` - Viewport height in pixels
    ///
    /// # Returns
    ///
    /// A new `WgpuRenderer` or an error if initialization fails.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn new_headless(width: u32, height: u32) -> Result<Self, WgpuError> {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
            backends: wgpu::Backends::all(),
            ..Default::default()
        });

        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: None,
            force_fallback_adapter: false,
        }))
        .ok_or(WgpuError::AdapterNotFound)?;

        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("Rource Device"),
                required_features: wgpu::Features::empty(),
                required_limits: wgpu::Limits::default(),
                memory_hints: wgpu::MemoryHints::default(),
            },
            None,
        ))
        .map_err(|e| WgpuError::DeviceCreationFailed(e.to_string()))?;

        let device = Arc::new(device);
        let queue = Arc::new(queue);

        Self::initialize(instance, adapter, device, queue, None, None, width, height)
    }

    /// Creates a new wgpu renderer from a raw window handle.
    ///
    /// # Safety
    ///
    /// The window handle must be valid for the lifetime of the renderer.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn new_with_window<W>(window: W) -> Result<Self, WgpuError>
    where
        W: raw_window_handle::HasWindowHandle
            + raw_window_handle::HasDisplayHandle
            + Send
            + Sync
            + 'static,
    {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
            backends: wgpu::Backends::all(),
            ..Default::default()
        });

        // Get window size (default to 800x600 if not available)
        let (width, height) = (800, 600);

        let surface = instance
            .create_surface(window)
            .map_err(|e| WgpuError::SurfaceCreationFailed(e.to_string()))?;

        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: Some(&surface),
            force_fallback_adapter: false,
        }))
        .ok_or(WgpuError::AdapterNotFound)?;

        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("Rource Device"),
                required_features: wgpu::Features::empty(),
                required_limits: wgpu::Limits::default(),
                memory_hints: wgpu::MemoryHints::default(),
            },
            None,
        ))
        .map_err(|e| WgpuError::DeviceCreationFailed(e.to_string()))?;

        let device = Arc::new(device);
        let queue = Arc::new(queue);

        let surface_caps = surface.get_capabilities(&adapter);
        let surface_format = surface_caps
            .formats
            .iter()
            .copied()
            .find(wgpu::TextureFormat::is_srgb)
            .unwrap_or(surface_caps.formats[0]);

        let surface_config = wgpu::SurfaceConfiguration {
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
            format: surface_format,
            width,
            height,
            present_mode: wgpu::PresentMode::Fifo,
            alpha_mode: surface_caps.alpha_modes[0],
            view_formats: vec![],
            desired_maximum_frame_latency: 2,
        };

        surface.configure(&device, &surface_config);

        Self::initialize(
            instance,
            adapter,
            device,
            queue,
            Some(surface),
            Some(surface_config),
            width,
            height,
        )
    }

    /// Creates a new wgpu renderer from a canvas element (WASM).
    ///
    /// # Note on Send/Sync
    ///
    /// This function is not `Send` on WASM because browser APIs are single-threaded.
    /// wgpu types cannot be `Send`/`Sync` in the browser environment, which is expected
    /// and safe for single-threaded WASM usage.
    #[cfg(target_arch = "wasm32")]
    #[allow(clippy::future_not_send)]
    pub async fn new_from_canvas(canvas: &web_sys::HtmlCanvasElement) -> Result<Self, WgpuError> {
        // Only use WebGPU backend - if it's not available, we fall back to our
        // dedicated WebGL2Renderer which provides clearer error reporting and
        // deterministic behavior. Using BROWSER_WEBGPU | GL would silently fall
        // back to WebGL through wgpu, making it unclear which backend is used.
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
            backends: wgpu::Backends::BROWSER_WEBGPU,
            ..Default::default()
        });

        let width = canvas.width();
        let height = canvas.height();

        let surface = instance
            .create_surface(wgpu::SurfaceTarget::Canvas(canvas.clone()))
            .map_err(|e| WgpuError::SurfaceCreationFailed(e.to_string()))?;

        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                compatible_surface: Some(&surface),
                force_fallback_adapter: false,
            })
            .await
            .ok_or(WgpuError::AdapterNotFound)?;

        let (device, queue) = adapter
            .request_device(
                &wgpu::DeviceDescriptor {
                    label: Some("Rource Device"),
                    required_features: wgpu::Features::empty(),
                    required_limits: wgpu::Limits::downlevel_webgl2_defaults(),
                    memory_hints: wgpu::MemoryHints::default(),
                },
                None,
            )
            .await
            .map_err(|e| WgpuError::DeviceCreationFailed(e.to_string()))?;

        let device = Arc::new(device);
        let queue = Arc::new(queue);

        let surface_caps = surface.get_capabilities(&adapter);
        let surface_format = surface_caps
            .formats
            .iter()
            .copied()
            .find(wgpu::TextureFormat::is_srgb)
            .unwrap_or(surface_caps.formats[0]);

        let surface_config = wgpu::SurfaceConfiguration {
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
            format: surface_format,
            width,
            height,
            present_mode: wgpu::PresentMode::Fifo,
            alpha_mode: surface_caps.alpha_modes[0],
            view_formats: vec![],
            desired_maximum_frame_latency: 2,
        };

        surface.configure(&device, &surface_config);

        Self::initialize(
            instance,
            adapter,
            device,
            queue,
            Some(surface),
            Some(surface_config),
            width,
            height,
        )
    }

    /// Internal initialization shared by all constructors.
    #[allow(clippy::unnecessary_wraps)]
    fn initialize(
        instance: wgpu::Instance,
        adapter: wgpu::Adapter,
        device: Arc<wgpu::Device>,
        queue: Arc<wgpu::Queue>,
        surface: Option<wgpu::Surface<'static>>,
        surface_config: Option<wgpu::SurfaceConfiguration>,
        width: u32,
        height: u32,
    ) -> Result<Self, WgpuError> {
        // Create uniform bind group layout
        let uniform_bind_group_layout =
            device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("Uniform Bind Group Layout"),
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

        // Create uniform buffer
        let uniform_buffer = UniformBuffer::new(&device);

        // Create uniform bind group
        let uniform_bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("Uniform Bind Group"),
            layout: &uniform_bind_group_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: uniform_buffer.buffer().as_entire_binding(),
            }],
        });

        // Create vertex buffers
        let vertex_buffers = VertexBuffers::new(&device);

        // Create texture bind group layout (for font atlas and user textures)
        let texture_bind_group_layout =
            device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("Texture Bind Group Layout"),
                entries: &[
                    wgpu::BindGroupLayoutEntry {
                        binding: 0,
                        visibility: wgpu::ShaderStages::FRAGMENT,
                        ty: wgpu::BindingType::Texture {
                            sample_type: wgpu::TextureSampleType::Float { filterable: true },
                            view_dimension: wgpu::TextureViewDimension::D2,
                            multisampled: false,
                        },
                        count: None,
                    },
                    wgpu::BindGroupLayoutEntry {
                        binding: 1,
                        visibility: wgpu::ShaderStages::FRAGMENT,
                        ty: wgpu::BindingType::Sampler(wgpu::SamplerBindingType::Filtering),
                        count: None,
                    },
                ],
            });

        // Create instance buffers with initial capacity
        // Floats per instance = bytes / 4
        let circle_instances = InstanceBuffer::new(&device, 7, 1000, "circle_instances"); // 7 floats = 28 bytes
        let ring_instances = InstanceBuffer::new(&device, 8, 500, "ring_instances"); // 8 floats = 32 bytes
        let line_instances = InstanceBuffer::new(&device, 9, 1000, "line_instances"); // 9 floats = 36 bytes
        let curve_instances = InstanceBuffer::new(&device, 14, 500, "curve_instances"); // 14 floats = 56 bytes
        let quad_instances = InstanceBuffer::new(&device, 8, 500, "quad_instances"); // 8 floats = 32 bytes
        let text_instances = InstanceBuffer::new(&device, 12, 2000, "text_instances"); // 12 floats = 48 bytes
        let file_icon_instances = InstanceBuffer::new(&device, 13, 500, "file_icon_instances"); // 13 values = 52 bytes

        // Create font atlas
        let font_atlas = FontAtlas::new(&device, &texture_bind_group_layout);

        let mut renderer = Self {
            instance,
            adapter,
            device,
            queue,
            surface,
            surface_config,
            width,
            height,
            transform: Mat4::IDENTITY,
            clips: Vec::new(),
            font_cache: FontCache::new(),
            font_atlas,
            textures: HashMap::default(),
            next_texture_id: 1,
            uniform_buffer,
            uniform_bind_group,
            uniform_bind_group_layout,
            vertex_buffers,
            pipeline_manager: None,
            texture_bind_group_layout,
            circle_instances,
            ring_instances,
            line_instances,
            curve_instances,
            quad_instances,
            textured_quad_instances: HashMap::default(),
            text_instances,
            file_icon_instances,
            bloom_pipeline: None,
            shadow_pipeline: None,
            compute_pipeline: None,
            spatial_hash_pipeline: None,
            use_spatial_hash: true, // Use O(N) by default
            render_state: RenderState::new(),
            frame_stats: FrameStats::new(),
            current_encoder: None,
            current_surface_texture: None,
            current_target_view: None,
            scene_texture: None,
            scene_texture_view: None,
            bloom_enabled: false,
            shadow_enabled: false,
            cached_texture_ids: Vec::with_capacity(16),
            culling_pipeline: None,
            gpu_culling_enabled: false,
            cull_bounds: [-10000.0, -10000.0, 10000.0, 10000.0],
            current_scissor: None,
            file_icon_array: None,
        };

        // Initialize pipelines
        renderer.initialize_pipelines();

        Ok(renderer)
    }

    /// Initializes render pipelines.
    fn initialize_pipelines(&mut self) {
        let format = self
            .surface_config
            .as_ref()
            .map(|c| c.format)
            .unwrap_or(wgpu::TextureFormat::Bgra8UnormSrgb);

        // Create pipeline manager with the surface format
        let mut pipeline_manager = PipelineManager::new(&self.device, format);

        // Warmup all pipelines
        pipeline_manager.warmup(&self.device);

        self.pipeline_manager = Some(pipeline_manager);
    }
}

// ============================================================================
// Accessor Methods
// ============================================================================

impl WgpuRenderer {
    /// Returns the wgpu device.
    #[inline]
    pub fn device(&self) -> &wgpu::Device {
        &self.device
    }

    /// Returns the wgpu queue.
    #[inline]
    pub fn queue(&self) -> &wgpu::Queue {
        &self.queue
    }

    /// Returns frame statistics from the last completed frame.
    #[inline]
    pub fn frame_stats(&self) -> &FrameStats {
        &self.frame_stats
    }

    /// Returns GPU adapter information for diagnostics.
    ///
    /// This provides hardware details useful for:
    /// - Debugging rendering issues
    /// - Feature capability detection
    /// - Performance profiling and optimization decisions
    #[must_use]
    pub fn get_gpu_info(&self) -> GpuInfo {
        let info = self.adapter.get_info();
        let limits = self.adapter.limits();

        GpuInfo {
            name: info.name.clone(),
            vendor: info.vendor,
            device: info.device,
            device_type: format!("{:?}", info.device_type),
            backend: format!("{:?}", info.backend),
            // Key limits for production diagnostics
            max_texture_dimension_2d: limits.max_texture_dimension_2d,
            max_buffer_size: limits.max_buffer_size,
            max_storage_buffer_binding_size: limits.max_storage_buffer_binding_size,
            max_compute_workgroup_size_x: limits.max_compute_workgroup_size_x,
            max_compute_invocations_per_workgroup: limits.max_compute_invocations_per_workgroup,
        }
    }
}

/// GPU adapter information for diagnostics and capability detection.
///
/// Contains hardware details and key limits useful for debugging,
/// performance profiling, and feature capability detection.
#[derive(Debug, Clone)]
pub struct GpuInfo {
    /// Human-readable name of the GPU adapter.
    pub name: String,
    /// Vendor ID (PCI vendor code).
    pub vendor: u32,
    /// Device ID (PCI device code).
    pub device: u32,
    /// Device type (e.g., `DiscreteGpu`, `IntegratedGpu`, `Cpu`).
    pub device_type: String,
    /// Graphics backend (e.g., `Vulkan`, `Metal`, `Dx12`, `BrowserWebGpu`).
    pub backend: String,
    /// Maximum 2D texture dimension (width/height).
    pub max_texture_dimension_2d: u32,
    /// Maximum buffer size in bytes.
    pub max_buffer_size: u64,
    /// Maximum storage buffer binding size in bytes.
    pub max_storage_buffer_binding_size: u32,
    /// Maximum compute workgroup size in X dimension.
    pub max_compute_workgroup_size_x: u32,
    /// Maximum compute invocations per workgroup.
    pub max_compute_invocations_per_workgroup: u32,
}

// ============================================================================
// Internal Helper Methods
// ============================================================================

impl WgpuRenderer {
    /// Transforms a point from world to screen coordinates.
    #[inline]
    fn transform_point(&self, point: Vec2) -> Vec2 {
        let p = self
            .transform
            .transform_point(rource_math::Vec3::from_vec2(point, 0.0));
        Vec2::new(p.x, p.y)
    }

    /// Flushes pending draw calls before changing scissor state.
    ///
    /// This ensures that primitives drawn before a clip change are rendered
    /// with the previous scissor rect, and primitives drawn after use the new one.
    fn flush_for_scissor_change(&mut self) {
        // Only flush if we have pending instances and an active encoder
        let has_pending = !self.circle_instances.is_empty()
            || !self.ring_instances.is_empty()
            || !self.line_instances.is_empty()
            || !self.curve_instances.is_empty()
            || !self.quad_instances.is_empty()
            || !self.text_instances.is_empty()
            || !self.file_icon_instances.is_empty()
            || self.textured_quad_instances.values().any(|b| !b.is_empty());

        if has_pending && self.current_encoder.is_some() && self.current_target_view.is_some() {
            // Take ownership temporarily for the flush
            // We take target_view as well to avoid borrow conflicts
            let mut encoder = self.current_encoder.take().unwrap();
            let target_view = self.current_target_view.take().unwrap();

            self.flush(&mut encoder, &target_view);

            // Put both back
            self.current_encoder = Some(encoder);
            self.current_target_view = Some(target_view);
        }
    }

    /// Updates the current scissor rectangle based on the clip stack.
    ///
    /// Calculates the intersection of all clip bounds to get the effective scissor rect.
    fn update_scissor_rect(&mut self) {
        if self.clips.is_empty() {
            self.current_scissor = None;
            return;
        }

        // Start with the first clip
        let mut result = self.clips[0];

        // Intersect with remaining clips
        for clip in &self.clips[1..] {
            result = Bounds::new(
                Vec2::new(result.min.x.max(clip.min.x), result.min.y.max(clip.min.y)),
                Vec2::new(result.max.x.min(clip.max.x), result.max.y.min(clip.max.y)),
            );
        }

        // Clamp to viewport and ensure non-negative dimensions
        let x = result.min.x.max(0.0) as u32;
        let y = result.min.y.max(0.0) as u32;
        let max_x = (result.max.x.min(self.width as f32) as u32).max(x);
        let max_y = (result.max.y.min(self.height as f32) as u32).max(y);

        let width = max_x.saturating_sub(x);
        let height = max_y.saturating_sub(y);

        // Only set scissor if we have a valid rect
        if width > 0 && height > 0 {
            self.current_scissor = Some(ScissorRect {
                x,
                y,
                width,
                height,
            });
        } else {
            // Degenerate scissor (nothing visible) - set to minimal rect
            self.current_scissor = Some(ScissorRect {
                x: 0,
                y: 0,
                width: 0,
                height: 0,
            });
        }
    }

    /// Ensures the scene texture exists and is the correct size.
    pub(crate) fn ensure_scene_texture(&mut self) {
        let needs_recreate = self.scene_texture.as_ref().is_none_or(|tex| {
            let size = tex.size();
            size.width != self.width || size.height != self.height
        });

        if needs_recreate && (self.bloom_enabled || self.shadow_enabled) {
            let format = self
                .surface_config
                .as_ref()
                .map(|c| c.format)
                .unwrap_or(wgpu::TextureFormat::Bgra8UnormSrgb);

            let texture = self.device.create_texture(&wgpu::TextureDescriptor {
                label: Some("Scene Texture"),
                size: wgpu::Extent3d {
                    width: self.width,
                    height: self.height,
                    depth_or_array_layers: 1,
                },
                mip_level_count: 1,
                sample_count: 1,
                dimension: wgpu::TextureDimension::D2,
                format,
                usage: wgpu::TextureUsages::RENDER_ATTACHMENT
                    | wgpu::TextureUsages::TEXTURE_BINDING,
                view_formats: &[],
            });

            self.scene_texture_view = Some(texture.create_view(&wgpu::TextureViewDescriptor {
                label: Some("Scene Texture View"),
                ..Default::default()
            }));
            self.scene_texture = Some(texture);
        }
    }

    /// Interpolates a Catmull-Rom spline for drawing.
    ///
    /// Note: This function is kept for test coverage. Production code uses
    /// the zero-allocation streaming version in `draw_spline`.
    #[cfg(test)]
    fn interpolate_spline(points: &[Vec2], segments_per_span: usize) -> Vec<Vec2> {
        if points.len() < 2 {
            return points.to_vec();
        }

        if points.len() == 2 {
            return points.to_vec();
        }

        let mut result = Vec::with_capacity(points.len() * segments_per_span);

        // Pre-compute reciprocal to avoid per-segment division
        let inv_segments = 1.0 / segments_per_span as f32;

        for i in 0..points.len() - 1 {
            let p0 = points[i.saturating_sub(1)];
            let p1 = points[i];
            let p2 = points[(i + 1).min(points.len() - 1)];
            let p3 = points[(i + 2).min(points.len() - 1)];

            for j in 0..segments_per_span {
                let t = j as f32 * inv_segments;
                let t2 = t * t;
                let t3 = t2 * t;

                // Catmull-Rom coefficients
                let x = 0.5
                    * ((2.0 * p1.x)
                        + (-p0.x + p2.x) * t
                        + (2.0 * p0.x - 5.0 * p1.x + 4.0 * p2.x - p3.x) * t2
                        + (-p0.x + 3.0 * p1.x - 3.0 * p2.x + p3.x) * t3);
                let y = 0.5
                    * ((2.0 * p1.y)
                        + (-p0.y + p2.y) * t
                        + (2.0 * p0.y - 5.0 * p1.y + 4.0 * p2.y - p3.y) * t2
                        + (-p0.y + 3.0 * p1.y - 3.0 * p2.y + p3.y) * t3);

                result.push(Vec2::new(x, y));
            }
        }

        // Add final point
        result.push(*points.last().unwrap());

        result
    }
}

// ============================================================================
// Renderer Trait Implementation
// ============================================================================

impl Renderer for WgpuRenderer {
    fn begin_frame(&mut self) {
        // Reset frame stats
        self.frame_stats.reset();
        self.render_state.begin_frame(self.width, self.height);

        // Clear scissor/clip state for new frame
        self.clips.clear();
        self.current_scissor = None;

        // Get surface texture if available
        if let Some(ref surface) = self.surface {
            match surface.get_current_texture() {
                Ok(texture) => {
                    self.current_surface_texture = Some(texture);
                }
                Err(_) => {
                    // Surface lost, will skip frame
                    return;
                }
            }
        }

        // Create command encoder
        self.current_encoder = Some(self.device.create_command_encoder(
            &wgpu::CommandEncoderDescriptor {
                label: Some("Frame Command Encoder"),
            },
        ));

        // Determine render target based on post-processing state
        if self.bloom_enabled {
            // Bloom manages its own scene render target - use that
            if let Some(ref mut bloom) = self.bloom_pipeline {
                bloom.ensure_size(&self.device, self.width, self.height);
                self.current_target_view = bloom.scene_view().cloned();
            }
        } else if self.shadow_enabled {
            // Shadow-only: use renderer's scene texture
            self.ensure_scene_texture();
            if let Some(ref mut shadow) = self.shadow_pipeline {
                shadow.ensure_size(&self.device, self.width, self.height);
            }
            self.current_target_view = self.scene_texture_view.clone();
        } else if let Some(ref texture) = self.current_surface_texture {
            // No post-processing: render directly to surface
            self.current_target_view =
                Some(texture.texture.create_view(&wgpu::TextureViewDescriptor {
                    label: Some("Surface Texture View"),
                    ..Default::default()
                }));
        }
    }

    fn end_frame(&mut self) {
        let Some(mut encoder) = self.current_encoder.take() else {
            return;
        };

        let Some(target_view) = self.current_target_view.take() else {
            return;
        };

        // Flush all batched draw calls
        self.flush(&mut encoder, &target_view);

        // Apply post-processing if enabled
        if let Some(ref surface_texture) = self.current_surface_texture {
            let surface_view = surface_texture
                .texture
                .create_view(&wgpu::TextureViewDescriptor::default());

            // Handle post-processing effects
            // Priority: bloom takes precedence, then shadow-only
            if self.bloom_enabled {
                if let Some(ref bloom) = self.bloom_pipeline {
                    bloom.apply(&self.device, &self.queue, &mut encoder, &surface_view);
                    self.frame_stats.bloom_applied = true;
                }
            } else if self.shadow_enabled {
                if let Some(ref shadow) = self.shadow_pipeline {
                    if let Some(ref scene_view) = self.scene_texture_view {
                        shadow.apply(
                            &self.device,
                            &self.queue,
                            &mut encoder,
                            scene_view,
                            &surface_view,
                        );
                        self.frame_stats.shadow_applied = true;
                    }
                }
            }
        }

        // Submit command buffer
        self.queue.submit(Some(encoder.finish()));

        // Present surface
        if let Some(texture) = self.current_surface_texture.take() {
            texture.present();
        }
    }

    fn clear(&mut self, color: Color) {
        let Some(ref mut encoder) = self.current_encoder else {
            return;
        };

        let Some(ref target_view) = self.current_target_view else {
            return;
        };

        // Create clear render pass
        let _render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
            label: Some("Clear Pass"),
            color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                view: target_view,
                resolve_target: None,
                ops: wgpu::Operations {
                    load: wgpu::LoadOp::Clear(wgpu::Color {
                        r: f64::from(color.r),
                        g: f64::from(color.g),
                        b: f64::from(color.b),
                        a: f64::from(color.a),
                    }),
                    store: wgpu::StoreOp::Store,
                },
            })],
            depth_stencil_attachment: None,
            timestamp_writes: None,
            occlusion_query_set: None,
        });
        // Render pass is dropped, executing the clear
    }

    #[inline]
    fn draw_circle(&mut self, center: Vec2, radius: f32, width: f32, color: Color) {
        let center = self.transform_point(center);

        // Ring instance: center(2) + radius(1) + width(1) + color(4)
        self.ring_instances.push_raw(&[
            center.x, center.y, radius, width, color.r, color.g, color.b, color.a,
        ]);
    }

    #[inline]
    fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color) {
        let center = self.transform_point(center);

        // Circle instance: center(2) + radius(1) + color(4)
        self.circle_instances.push_raw(&[
            center.x, center.y, radius, color.r, color.g, color.b, color.a,
        ]);
    }

    #[inline]
    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color) {
        let start = self.transform_point(start);
        let end = self.transform_point(end);

        // Line instance: start(2) + end(2) + width(1) + color(4)
        self.line_instances.push_raw(&[
            start.x, start.y, end.x, end.y, width, color.r, color.g, color.b, color.a,
        ]);
    }

    fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color) {
        // LOD thresholds for curve rendering (in screen pixels)
        // Below MIN_CURVE_LENGTH: use a straight line (visually equivalent)
        // Above: use GPU curve tessellation
        const MIN_CURVE_LENGTH_SQ: f32 = 16.0; // 4 pixels squared

        if points.len() < 2 {
            return;
        }

        // For 2-point splines, just draw a line (no interpolation needed)
        if points.len() == 2 {
            self.draw_line(points[0], points[1], width, color);
            return;
        }

        // Use GPU curve tessellation for 3+ points
        // Each span (from point i to i+1) becomes one curve instance
        for i in 0..points.len() - 1 {
            let p0 = self.transform_point(points[i.saturating_sub(1)]);
            let p1 = self.transform_point(points[i]);
            let p2 = self.transform_point(points[(i + 1).min(points.len() - 1)]);
            let p3 = self.transform_point(points[(i + 2).min(points.len() - 1)]);

            // LOD: Calculate screen-space distance for this span
            let dx = p2.x - p1.x;
            let dy = p2.y - p1.y;
            let length_sq = dx * dx + dy * dy;

            // For very short spans, a straight line is visually equivalent
            // and avoids curve tessellation overhead
            if length_sq < MIN_CURVE_LENGTH_SQ {
                // Draw as simple line - skip curve overhead
                self.line_instances.push_raw(&[
                    p1.x, p1.y, p2.x, p2.y, width, color.r, color.g, color.b, color.a,
                ]);
                continue;
            }

            // For longer spans, use GPU curve tessellation
            // The segments field can be used for adaptive tessellation in the future
            // Currently using CURVE_SEGMENTS (8) for all curves
            self.curve_instances.push_raw(&[
                p0.x,
                p0.y,
                p1.x,
                p1.y,
                p2.x,
                p2.y,
                p3.x,
                p3.y,
                width,
                color.r,
                color.g,
                color.b,
                color.a,
                buffers::CURVE_SEGMENTS as f32,
            ]);
        }
    }

    fn draw_quad(&mut self, bounds: Bounds, texture: Option<TextureId>, color: Color) {
        let min = self.transform_point(bounds.min);
        let max = self.transform_point(bounds.max);

        if let Some(tex_id) = texture {
            // Textured quad
            let instances = self.get_or_create_textured_quad_buffer(tex_id);

            // bounds(4) + uv_bounds(4) + color(4)
            instances.push_raw(&[
                min.x, min.y, max.x, max.y, 0.0, 0.0, 1.0, 1.0, // UV bounds
                color.r, color.g, color.b, color.a,
            ]);
        } else {
            // Solid quad: bounds(4) + color(4)
            self.quad_instances.push_raw(&[
                min.x, min.y, max.x, max.y, color.r, color.g, color.b, color.a,
            ]);
        }
    }

    fn draw_text(&mut self, text: &str, position: Vec2, font: FontId, size: f32, color: Color) {
        let position = self.transform_point(position);

        // Verify font exists
        if self.font_cache.get(font).is_none() {
            return;
        }

        let mut cursor_x = position.x;

        for ch in text.chars() {
            // Get or rasterize glyph using FontCache
            let Some(glyph) = self.font_cache.rasterize(font, ch, size) else {
                continue;
            };

            let metrics = glyph.metrics;
            let bitmap = &glyph.bitmap;

            // Skip if glyph has no visual representation
            if metrics.width == 0 || metrics.height == 0 {
                cursor_x += metrics.advance_width;
                continue;
            }

            // Get or insert glyph in GPU atlas
            let glyph_key = GlyphKey::new(ch, size);
            let region = if let Some(region) = self.font_atlas.get(&glyph_key) {
                *region
            } else if let Some(region) = self.font_atlas.insert(
                &self.device,
                &self.texture_bind_group_layout,
                glyph_key,
                metrics.width as u32,
                metrics.height as u32,
                bitmap,
            ) {
                region
            } else {
                // Atlas full, skip this glyph
                cursor_x += metrics.advance_width;
                continue;
            };

            // Calculate glyph position
            let x = cursor_x + metrics.xmin as f32;
            let y = position.y + (size - metrics.ymin as f32 - metrics.height as f32);
            let w = metrics.width as f32;
            let h = metrics.height as f32;

            // Get UV coordinates
            let atlas_size = self.font_atlas.size();
            let (u_min, v_min, u_max, v_max) = region.uv_bounds(atlas_size);

            // Text instance: bounds(4) + uv_bounds(4) + color(4)
            self.text_instances.push_raw(&[
                x,
                y,
                x + w,
                y + h,
                u_min,
                v_min,
                u_max,
                v_max,
                color.r,
                color.g,
                color.b,
                color.a,
            ]);

            cursor_x += metrics.advance_width;
        }
    }

    fn set_transform(&mut self, transform: Mat4) {
        self.transform = transform;
    }

    fn transform(&self) -> Mat4 {
        self.transform
    }

    fn push_clip(&mut self, bounds: Bounds) {
        // Flush pending draw calls before changing scissor state
        self.flush_for_scissor_change();

        // Transform bounds to screen space
        let min = self.transform_point(bounds.min);
        let max = self.transform_point(bounds.max);
        let screen_bounds = Bounds::new(min, max);
        self.clips.push(screen_bounds);

        // Calculate new scissor rect (intersection of all clip bounds)
        self.update_scissor_rect();
    }

    fn pop_clip(&mut self) {
        // Flush pending draw calls before changing scissor state
        self.flush_for_scissor_change();

        self.clips.pop();

        // Update scissor rect based on remaining clips
        self.update_scissor_rect();
    }

    fn width(&self) -> u32 {
        self.width
    }

    fn height(&self) -> u32 {
        self.height
    }

    fn resize(&mut self, width: u32, height: u32) {
        if width == 0 || height == 0 {
            return;
        }

        self.width = width;
        self.height = height;

        // Reconfigure surface
        if let (Some(ref surface), Some(ref mut config)) = (&self.surface, &mut self.surface_config)
        {
            config.width = width;
            config.height = height;
            surface.configure(&self.device, config);
        }

        // Invalidate scene texture
        self.scene_texture = None;
        self.scene_texture_view = None;
    }

    fn load_texture(&mut self, width: u32, height: u32, data: &[u8]) -> TextureId {
        let id = TextureId::new(self.next_texture_id);
        self.next_texture_id += 1;

        let label = format!("texture_{}", id.raw());
        let managed = ManagedTexture::new(
            &self.device,
            &self.queue,
            &self.texture_bind_group_layout,
            width,
            height,
            data,
            &label,
        );
        self.textures.insert(id, managed);

        id
    }

    fn unload_texture(&mut self, texture: TextureId) {
        self.textures.remove(&texture);
        self.textured_quad_instances.remove(&texture);
    }

    fn load_font(&mut self, data: &[u8]) -> Option<FontId> {
        self.font_cache.load(data)
    }

    // File icon methods - delegate to icons_methods.rs implementations

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

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use state::PipelineId;

    #[test]
    fn test_interpolate_spline_empty() {
        let points: Vec<Vec2> = vec![];
        let result = WgpuRenderer::interpolate_spline(&points, 8);
        assert!(result.is_empty());
    }

    #[test]
    fn test_interpolate_spline_single() {
        let points = vec![Vec2::new(0.0, 0.0)];
        let result = WgpuRenderer::interpolate_spline(&points, 8);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_interpolate_spline_two_points() {
        let points = vec![Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        let result = WgpuRenderer::interpolate_spline(&points, 8);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_interpolate_spline_multiple() {
        let points = vec![
            Vec2::new(0.0, 0.0),
            Vec2::new(10.0, 10.0),
            Vec2::new(20.0, 5.0),
            Vec2::new(30.0, 15.0),
        ];
        let result = WgpuRenderer::interpolate_spline(&points, 8);

        // Should have many more points than input
        assert!(result.len() > points.len());

        // First and last should be close to original
        assert!((result[0] - points[0]).length() < 0.001);
        assert!((result[result.len() - 1] - points[points.len() - 1]).length() < 0.001);
    }

    #[test]
    fn test_frame_stats_tracking() {
        let mut stats = FrameStats::new();
        assert_eq!(stats.draw_calls, 0);
        assert_eq!(stats.total_instances, 0);

        stats.draw_calls = 5;
        stats.total_instances = 100;
        stats.circle_instances = 50;

        assert_eq!(stats.instances_per_draw_call(), 20.0);

        stats.reset();
        assert_eq!(stats.draw_calls, 0);
    }

    #[test]
    fn test_active_primitives() {
        let mut primitives = ActivePrimitives::none();
        assert!(!primitives.is_set(ActivePrimitives::CIRCLES));

        primitives.set(ActivePrimitives::CIRCLES);
        assert!(primitives.is_set(ActivePrimitives::CIRCLES));

        primitives.set(ActivePrimitives::LINES);
        assert_eq!(primitives.count(), 2);
    }

    #[test]
    fn test_render_state() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();

        // First set should return true
        assert!(state.set_pipeline(PipelineId::Circle, &mut stats));

        // Same pipeline should return false
        assert!(!state.set_pipeline(PipelineId::Circle, &mut stats));

        // Different pipeline should return true
        assert!(state.set_pipeline(PipelineId::Ring, &mut stats));

        // Reset and try again
        state.invalidate();
        assert!(state.set_pipeline(PipelineId::Circle, &mut stats));
    }

    #[test]
    fn test_pipeline_id_variants() {
        let ids = [
            PipelineId::Circle,
            PipelineId::Ring,
            PipelineId::Line,
            PipelineId::Quad,
            PipelineId::TexturedQuad,
            PipelineId::Text,
        ];

        // All should be distinct
        for (i, id1) in ids.iter().enumerate() {
            for (j, id2) in ids.iter().enumerate() {
                if i == j {
                    assert_eq!(id1, id2);
                } else {
                    assert_ne!(id1, id2);
                }
            }
        }
    }

    #[test]
    fn test_scissor_rect_struct() {
        let rect = ScissorRect {
            x: 10,
            y: 20,
            width: 100,
            height: 200,
        };

        assert_eq!(rect.x, 10);
        assert_eq!(rect.y, 20);
        assert_eq!(rect.width, 100);
        assert_eq!(rect.height, 200);

        // Test equality
        let rect2 = ScissorRect {
            x: 10,
            y: 20,
            width: 100,
            height: 200,
        };
        assert_eq!(rect, rect2);

        // Test inequality
        let rect3 = ScissorRect {
            x: 10,
            y: 20,
            width: 101,
            height: 200,
        };
        assert_ne!(rect, rect3);
    }

    #[test]
    fn test_scissor_rect_copy() {
        let rect = ScissorRect {
            x: 10,
            y: 20,
            width: 100,
            height: 200,
        };

        // Test Copy trait
        let rect_copy = rect;
        assert_eq!(rect, rect_copy);
    }

    #[test]
    fn test_curve_lod_threshold() {
        // Test that the LOD threshold constant is reasonable
        // MIN_CURVE_LENGTH_SQ = 16.0 means 4 pixels
        // This ensures very short curves become lines
        const MIN_CURVE_LENGTH_SQ: f32 = 16.0;

        // A 3-pixel span should be below threshold
        let short_span = 3.0_f32 * 3.0;
        assert!(short_span < MIN_CURVE_LENGTH_SQ);

        // A 5-pixel span should be above threshold
        let long_span = 5.0_f32 * 5.0;
        assert!(long_span > MIN_CURVE_LENGTH_SQ);
    }
}
