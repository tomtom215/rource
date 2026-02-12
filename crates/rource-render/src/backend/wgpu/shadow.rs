// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! GPU shadow effect implementation for wgpu.
//!
//! This module provides a drop shadow effect that renders shadows behind
//! scene elements. The implementation uses render targets for efficient
//! GPU-based processing.
//!
//! ## Pipeline
//!
//! The shadow effect is implemented as a multi-pass post-processing pipeline:
//!
//! 1. **Silhouette Pass**: Extract alpha channel from scene
//! 2. **Blur Pass**: Optional Gaussian blur for soft shadows
//! 3. **Composite Pass**: Render shadow offset behind scene

use wgpu::util::DeviceExt;

use super::bloom::RenderTarget;
use super::buffers::FULLSCREEN_QUAD;
use super::shaders::{BLOOM_BLUR_SHADER, SHADOW_COMPOSITE_SHADER, SHADOW_SILHOUETTE_SHADER};

/// Default shadow X offset in pixels.
pub const DEFAULT_SHADOW_OFFSET_X: f32 = 4.0;

/// Default shadow Y offset in pixels.
pub const DEFAULT_SHADOW_OFFSET_Y: f32 = 4.0;

/// Default shadow opacity.
pub const DEFAULT_SHADOW_OPACITY: f32 = 0.5;

/// Default number of shadow blur passes.
pub const DEFAULT_SHADOW_BLUR_PASSES: u32 = 1;

/// Default shadow downscale factor.
pub const DEFAULT_SHADOW_DOWNSCALE: u32 = 2;

/// Configuration for the GPU shadow effect.
#[derive(Debug, Clone, Copy)]
pub struct ShadowConfig {
    /// Whether shadow effect is enabled.
    pub enabled: bool,
    /// X offset in normalized coordinates.
    pub offset_x: f32,
    /// Y offset in normalized coordinates.
    pub offset_y: f32,
    /// Shadow opacity (0.0 - 1.0).
    pub opacity: f32,
    /// Number of blur passes.
    pub blur_passes: u32,
    /// Downscale factor for shadow buffers.
    pub downscale: u32,
    /// Shadow color (RGBA).
    pub color: [f32; 4],
}

impl Default for ShadowConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            offset_x: DEFAULT_SHADOW_OFFSET_X,
            offset_y: DEFAULT_SHADOW_OFFSET_Y,
            opacity: DEFAULT_SHADOW_OPACITY,
            blur_passes: DEFAULT_SHADOW_BLUR_PASSES,
            downscale: DEFAULT_SHADOW_DOWNSCALE,
            color: [0.0, 0.0, 0.0, 1.0], // Black shadow
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
            downscale: 2,
            color: [0.0, 0.0, 0.0, 1.0],
        }
    }

    /// Creates a strong shadow configuration.
    #[must_use]
    pub fn strong() -> Self {
        Self {
            enabled: true,
            offset_x: 6.0,
            offset_y: 6.0,
            opacity: 0.7,
            blur_passes: 2,
            downscale: 1,
            color: [0.0, 0.0, 0.0, 1.0],
        }
    }
}

/// Shadow composite uniform data.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct ShadowCompositeUniforms {
    offset: [f32; 2],
    opacity: f32,
    _padding: f32,
    color: [f32; 4],
}

/// Shadow blur uniform data.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct ShadowBlurUniforms {
    direction: [f32; 2],
    resolution: [f32; 2],
}

/// Cached bind groups for shadow pipeline to avoid per-frame allocations.
///
/// These bind groups reference GPU resources (buffers, textures, samplers) that
/// persist across frames. By caching them, we eliminate ~5 allocations per frame.
///
/// Note: `scene_texture_bg` is NOT cached because it depends on the `scene_view`
/// parameter passed to `apply()`, which may vary between calls.
///
/// Bind groups are recreated when:
/// - Render targets are resized (viewport change)
/// - Pipeline is first initialized
#[derive(Debug)]
#[allow(clippy::struct_field_names)] // All fields are bind groups, `_bg` suffix is intentional
struct CachedShadowBindGroups {
    /// Blur pass uniform bind group (references `blur_uniforms` buffer).
    blur_uniform_bg: wgpu::BindGroup,

    /// Composite pass uniform bind group (references `composite_uniforms` buffer).
    composite_uniform_bg: wgpu::BindGroup,

    /// Shadow target texture bind group (references `shadow_target` texture view).
    shadow_texture_bg: wgpu::BindGroup,

    /// Blur target texture bind group (references `blur_target` texture view).
    blur_texture_bg: wgpu::BindGroup,

    /// Final shadow texture bind group for composite (references `shadow_target`).
    shadow_final_texture_bg: wgpu::BindGroup,
}

/// GPU shadow effect pipeline.
#[derive(Debug)]
pub struct ShadowPipeline {
    /// Shadow configuration.
    pub config: ShadowConfig,

    /// Shadow silhouette target.
    shadow_target: Option<RenderTarget>,

    /// Blur intermediate target.
    blur_target: Option<RenderTarget>,

    /// Silhouette pass pipeline.
    silhouette_pipeline: wgpu::RenderPipeline,

    /// Blur pass pipeline.
    blur_pipeline: wgpu::RenderPipeline,

    /// Composite pass pipeline.
    composite_pipeline: wgpu::RenderPipeline,

    /// Blur uniform buffer.
    blur_uniforms: wgpu::Buffer,

    /// Composite uniform buffer.
    composite_uniforms: wgpu::Buffer,

    /// Uniform bind group layout.
    uniform_layout: wgpu::BindGroupLayout,

    /// Texture bind group layout.
    texture_layout: wgpu::BindGroupLayout,

    /// Composite texture bind group layout (two textures).
    composite_texture_layout: wgpu::BindGroupLayout,

    /// Linear sampler.
    sampler: wgpu::Sampler,

    /// Fullscreen quad vertex buffer.
    fullscreen_quad: wgpu::Buffer,

    /// Cached full resolution.
    cached_size: (u32, u32),

    /// Target surface format.
    surface_format: wgpu::TextureFormat,

    /// Whether the pipeline is initialized.
    initialized: bool,

    /// Cached bind groups to avoid per-frame allocations.
    /// Created in `ensure_size()` when render targets are allocated.
    /// Note: `scene_texture_bg` is NOT cached (depends on `apply()` parameter).
    cached_bind_groups: Option<CachedShadowBindGroups>,
}

impl ShadowPipeline {
    /// Creates a new shadow pipeline.
    pub fn new(device: &wgpu::Device, surface_format: wgpu::TextureFormat) -> Self {
        // Create bind group layouts
        let uniform_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("shadow_uniform_layout"),
            entries: &[wgpu::BindGroupLayoutEntry {
                binding: 0,
                visibility: wgpu::ShaderStages::FRAGMENT,
                ty: wgpu::BindingType::Buffer {
                    ty: wgpu::BufferBindingType::Uniform,
                    has_dynamic_offset: false,
                    min_binding_size: None,
                },
                count: None,
            }],
        });

        let texture_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("shadow_texture_layout"),
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

        let composite_texture_layout =
            device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("shadow_composite_texture_layout"),
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

        // Create pipelines
        let silhouette_pipeline =
            Self::create_silhouette_pipeline(device, &texture_layout, surface_format);
        let blur_pipeline =
            Self::create_blur_pipeline(device, &uniform_layout, &texture_layout, surface_format);
        let composite_pipeline = Self::create_composite_pipeline(
            device,
            &uniform_layout,
            &texture_layout,
            &composite_texture_layout,
            surface_format,
        );

        // Create uniform buffers
        let blur_uniforms = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("shadow_blur_uniforms"),
            contents: bytemuck::cast_slice(&[ShadowBlurUniforms {
                direction: [1.0, 0.0],
                resolution: [1.0, 1.0],
            }]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });

        let composite_uniforms = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("shadow_composite_uniforms"),
            contents: bytemuck::cast_slice(&[ShadowCompositeUniforms {
                offset: [0.0, 0.0],
                opacity: DEFAULT_SHADOW_OPACITY,
                _padding: 0.0,
                color: [0.0, 0.0, 0.0, 1.0],
            }]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });

        // Create sampler
        let sampler = device.create_sampler(&wgpu::SamplerDescriptor {
            label: Some("shadow_sampler"),
            address_mode_u: wgpu::AddressMode::ClampToEdge,
            address_mode_v: wgpu::AddressMode::ClampToEdge,
            address_mode_w: wgpu::AddressMode::ClampToEdge,
            mag_filter: wgpu::FilterMode::Linear,
            min_filter: wgpu::FilterMode::Linear,
            mipmap_filter: wgpu::MipmapFilterMode::Nearest,
            ..Default::default()
        });

        // Create fullscreen quad
        let fullscreen_quad = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("shadow_fullscreen_quad"),
            contents: bytemuck::cast_slice(&FULLSCREEN_QUAD),
            usage: wgpu::BufferUsages::VERTEX,
        });

        Self {
            config: ShadowConfig::default(),
            shadow_target: None,
            blur_target: None,
            silhouette_pipeline,
            blur_pipeline,
            composite_pipeline,
            blur_uniforms,
            composite_uniforms,
            uniform_layout,
            texture_layout,
            composite_texture_layout,
            sampler,
            fullscreen_quad,
            cached_size: (0, 0),
            surface_format,
            initialized: true,
            cached_bind_groups: None,
        }
    }

    /// Returns whether shadow is enabled and ready.
    #[inline]
    pub fn is_active(&self) -> bool {
        self.config.enabled && self.initialized && self.shadow_target.is_some()
    }

    /// Ensures render targets are sized correctly.
    ///
    /// This method also creates and caches bind groups when render targets are
    /// (re)allocated, eliminating per-frame bind group creation overhead.
    pub fn ensure_size(&mut self, device: &wgpu::Device, width: u32, height: u32) {
        if !self.config.enabled {
            return;
        }

        // Guard: WebGPU cannot create textures with 0 dimensions. This can happen
        // when set_shadow_enabled() is called before the canvas has been sized.
        if width == 0 || height == 0 {
            return;
        }

        if self.cached_size == (width, height) && self.shadow_target.is_some() {
            return;
        }

        self.cached_size = (width, height);

        // Create shadow targets at downscaled resolution
        let shadow_width = (width / self.config.downscale).max(1);
        let shadow_height = (height / self.config.downscale).max(1);

        self.shadow_target = Some(RenderTarget::new(
            device,
            shadow_width,
            shadow_height,
            self.surface_format,
            "shadow_target",
        ));

        self.blur_target = Some(RenderTarget::new(
            device,
            shadow_width,
            shadow_height,
            self.surface_format,
            "shadow_blur_target",
        ));

        // Cache bind groups now that render targets exist
        // This eliminates ~5 bind group allocations per frame
        // Note: `scene_texture_bg` is NOT cached (depends on `apply()` parameter)
        self.create_cached_bind_groups(device);
    }

    /// Creates and caches bind groups used in the shadow pipeline.
    ///
    /// Bind groups reference GPU resources (uniform buffers, texture views, samplers)
    /// that persist across frames. By caching them, we avoid per-frame allocations.
    ///
    /// Note: `scene_texture_bg` cannot be cached because it depends on the `scene_view`
    /// parameter passed to `apply()`, which may vary between calls.
    fn create_cached_bind_groups(&mut self, device: &wgpu::Device) {
        let shadow_target = self
            .shadow_target
            .as_ref()
            .expect("shadow_target must exist");
        let blur_target = self.blur_target.as_ref().expect("blur_target must exist");

        // Uniform bind groups - reference buffers updated via queue.write_buffer()
        let blur_uniform_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("shadow_blur_uniform_bg_cached"),
            layout: &self.uniform_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: self.blur_uniforms.as_entire_binding(),
            }],
        });

        let composite_uniform_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("shadow_composite_uniform_bg_cached"),
            layout: &self.uniform_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: self.composite_uniforms.as_entire_binding(),
            }],
        });

        // Texture bind groups - reference texture views that change when targets resize
        let shadow_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("shadow_texture_bg_cached"),
            layout: &self.texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(shadow_target.view()),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&self.sampler),
                },
            ],
        });

        let blur_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("shadow_blur_texture_bg_cached"),
            layout: &self.texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(blur_target.view()),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&self.sampler),
                },
            ],
        });

        // Final shadow texture for composite pass (same as shadow_target)
        let shadow_final_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("shadow_final_texture_bg_cached"),
            layout: &self.composite_texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(shadow_target.view()),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&self.sampler),
                },
            ],
        });

        self.cached_bind_groups = Some(CachedShadowBindGroups {
            blur_uniform_bg,
            composite_uniform_bg,
            shadow_texture_bg,
            blur_texture_bg,
            shadow_final_texture_bg,
        });
    }

    /// Applies the shadow effect using cached bind groups where possible.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device (used only for `scene_texture_bg` which cannot be cached)
    /// * `queue` - wgpu queue (for uniform buffer updates)
    /// * `encoder` - Command encoder
    /// * `scene_view` - Scene texture view (from bloom pipeline or direct)
    /// * `output_view` - Output view (surface)
    ///
    /// # Performance
    ///
    /// This method uses bind groups cached in `ensure_size()`, eliminating ~5
    /// bind group allocations per frame. Only `scene_texture_bg` is created
    /// per-call because it depends on the `scene_view` parameter.
    pub fn apply(
        &self,
        device: &wgpu::Device,
        queue: &wgpu::Queue,
        encoder: &mut wgpu::CommandEncoder,
        scene_view: &wgpu::TextureView,
        output_view: &wgpu::TextureView,
    ) {
        if !self.is_active() {
            return;
        }

        // Get cached bind groups - they must exist if is_active() returned true
        let cached = self
            .cached_bind_groups
            .as_ref()
            .expect("cached_bind_groups must exist when shadow is active");

        let shadow_target = self.shadow_target.as_ref().unwrap();
        let blur_target = self.blur_target.as_ref().unwrap();
        let shadow_dims = shadow_target.dimensions();

        // Calculate normalized offset
        let offset_x = self.config.offset_x / self.cached_size.0 as f32;
        let offset_y = self.config.offset_y / self.cached_size.1 as f32;

        // Update uniform buffer data (cheap GPU-side copy, no allocation)
        queue.write_buffer(
            &self.composite_uniforms,
            0,
            bytemuck::cast_slice(&[ShadowCompositeUniforms {
                offset: [offset_x, offset_y],
                opacity: self.config.opacity,
                _padding: 0.0,
                color: self.config.color,
            }]),
        );

        // scene_texture_bg cannot be cached because scene_view is a parameter
        // that may vary between calls (different callers, different sources)
        let scene_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("shadow_scene_texture_bg"),
            layout: &self.texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(scene_view),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&self.sampler),
                },
            ],
        });

        // =====================================================================
        // Pass 1: Extract silhouette (alpha channel from scene)
        // =====================================================================
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("shadow_silhouette_pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: shadow_target.view(),
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color::TRANSPARENT),
                        store: wgpu::StoreOp::Store,
                    },
                    depth_slice: None,
                })],
                depth_stencil_attachment: None,
                timestamp_writes: None,
                occlusion_query_set: None,
                multiview_mask: None,
            });

            render_pass.set_pipeline(&self.silhouette_pipeline);
            render_pass.set_bind_group(0, &scene_texture_bg, &[]);
            render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
            render_pass.draw(0..4, 0..1);
        }

        // =====================================================================
        // Pass 2: Optional blur (ping-pong between shadow and blur targets)
        // =====================================================================
        if self.config.blur_passes > 0 {
            for _ in 0..self.config.blur_passes {
                // Horizontal blur: shadow -> blur
                {
                    queue.write_buffer(
                        &self.blur_uniforms,
                        0,
                        bytemuck::cast_slice(&[ShadowBlurUniforms {
                            direction: [1.0, 0.0],
                            resolution: [shadow_dims.0 as f32, shadow_dims.1 as f32],
                        }]),
                    );

                    let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                        label: Some("shadow_blur_h_pass"),
                        color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                            view: blur_target.view(),
                            resolve_target: None,
                            ops: wgpu::Operations {
                                load: wgpu::LoadOp::Clear(wgpu::Color::TRANSPARENT),
                                store: wgpu::StoreOp::Store,
                            },
                            depth_slice: None,
                        })],
                        depth_stencil_attachment: None,
                        timestamp_writes: None,
                        occlusion_query_set: None,
                        multiview_mask: None,
                    });

                    render_pass.set_pipeline(&self.blur_pipeline);
                    render_pass.set_bind_group(0, &cached.blur_uniform_bg, &[]);
                    render_pass.set_bind_group(1, &cached.shadow_texture_bg, &[]);
                    render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
                    render_pass.draw(0..4, 0..1);
                }

                // Vertical blur: blur -> shadow
                {
                    queue.write_buffer(
                        &self.blur_uniforms,
                        0,
                        bytemuck::cast_slice(&[ShadowBlurUniforms {
                            direction: [0.0, 1.0],
                            resolution: [shadow_dims.0 as f32, shadow_dims.1 as f32],
                        }]),
                    );

                    let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                        label: Some("shadow_blur_v_pass"),
                        color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                            view: shadow_target.view(),
                            resolve_target: None,
                            ops: wgpu::Operations {
                                load: wgpu::LoadOp::Clear(wgpu::Color::TRANSPARENT),
                                store: wgpu::StoreOp::Store,
                            },
                            depth_slice: None,
                        })],
                        depth_stencil_attachment: None,
                        timestamp_writes: None,
                        occlusion_query_set: None,
                        multiview_mask: None,
                    });

                    render_pass.set_pipeline(&self.blur_pipeline);
                    render_pass.set_bind_group(0, &cached.blur_uniform_bg, &[]);
                    render_pass.set_bind_group(1, &cached.blur_texture_bg, &[]);
                    render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
                    render_pass.draw(0..4, 0..1);
                }
            }
        }

        // =====================================================================
        // Pass 3: Composite shadow with scene
        // =====================================================================
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("shadow_composite_pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: output_view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color::BLACK),
                        store: wgpu::StoreOp::Store,
                    },
                    depth_slice: None,
                })],
                depth_stencil_attachment: None,
                timestamp_writes: None,
                occlusion_query_set: None,
                multiview_mask: None,
            });

            render_pass.set_pipeline(&self.composite_pipeline);
            render_pass.set_bind_group(0, &cached.composite_uniform_bg, &[]);
            render_pass.set_bind_group(1, &scene_texture_bg, &[]);
            render_pass.set_bind_group(2, &cached.shadow_final_texture_bg, &[]);
            render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
            render_pass.draw(0..4, 0..1);
        }
    }

    fn create_silhouette_pipeline(
        device: &wgpu::Device,
        texture_layout: &wgpu::BindGroupLayout,
        format: wgpu::TextureFormat,
    ) -> wgpu::RenderPipeline {
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("shadow_silhouette_shader"),
            source: wgpu::ShaderSource::Wgsl(SHADOW_SILHOUETTE_SHADER.into()),
        });

        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("shadow_silhouette_layout"),
            bind_group_layouts: &[texture_layout],
            immediate_size: 0,
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("shadow_silhouette_pipeline"),
            layout: Some(&layout),
            vertex: wgpu::VertexState {
                module: &shader,
                entry_point: Some("vs_fullscreen"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[wgpu::VertexBufferLayout {
                    array_stride: 8,
                    step_mode: wgpu::VertexStepMode::Vertex,
                    attributes: &[wgpu::VertexAttribute {
                        format: wgpu::VertexFormat::Float32x2,
                        offset: 0,
                        shader_location: 0,
                    }],
                }],
            },
            fragment: Some(wgpu::FragmentState {
                module: &shader,
                entry_point: Some("fs_shadow_silhouette"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format,
                    blend: None,
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                ..Default::default()
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview_mask: None,
            cache: None,
        })
    }

    fn create_blur_pipeline(
        device: &wgpu::Device,
        uniform_layout: &wgpu::BindGroupLayout,
        texture_layout: &wgpu::BindGroupLayout,
        format: wgpu::TextureFormat,
    ) -> wgpu::RenderPipeline {
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("shadow_blur_shader"),
            source: wgpu::ShaderSource::Wgsl(BLOOM_BLUR_SHADER.into()),
        });

        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("shadow_blur_layout"),
            bind_group_layouts: &[uniform_layout, texture_layout],
            immediate_size: 0,
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("shadow_blur_pipeline"),
            layout: Some(&layout),
            vertex: wgpu::VertexState {
                module: &shader,
                entry_point: Some("vs_fullscreen"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[wgpu::VertexBufferLayout {
                    array_stride: 8,
                    step_mode: wgpu::VertexStepMode::Vertex,
                    attributes: &[wgpu::VertexAttribute {
                        format: wgpu::VertexFormat::Float32x2,
                        offset: 0,
                        shader_location: 0,
                    }],
                }],
            },
            fragment: Some(wgpu::FragmentState {
                module: &shader,
                entry_point: Some("fs_bloom_blur"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format,
                    blend: None,
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                ..Default::default()
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview_mask: None,
            cache: None,
        })
    }

    fn create_composite_pipeline(
        device: &wgpu::Device,
        uniform_layout: &wgpu::BindGroupLayout,
        scene_texture_layout: &wgpu::BindGroupLayout,
        shadow_texture_layout: &wgpu::BindGroupLayout,
        format: wgpu::TextureFormat,
    ) -> wgpu::RenderPipeline {
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("shadow_composite_shader"),
            source: wgpu::ShaderSource::Wgsl(SHADOW_COMPOSITE_SHADER.into()),
        });

        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("shadow_composite_layout"),
            bind_group_layouts: &[uniform_layout, scene_texture_layout, shadow_texture_layout],
            immediate_size: 0,
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("shadow_composite_pipeline"),
            layout: Some(&layout),
            vertex: wgpu::VertexState {
                module: &shader,
                entry_point: Some("vs_fullscreen"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[wgpu::VertexBufferLayout {
                    array_stride: 8,
                    step_mode: wgpu::VertexStepMode::Vertex,
                    attributes: &[wgpu::VertexAttribute {
                        format: wgpu::VertexFormat::Float32x2,
                        offset: 0,
                        shader_location: 0,
                    }],
                }],
            },
            fragment: Some(wgpu::FragmentState {
                module: &shader,
                entry_point: Some("fs_shadow_composite"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format,
                    blend: None,
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                ..Default::default()
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview_mask: None,
            cache: None,
        })
    }
}

// Compile-time constant validation
const _: () = {
    assert!(DEFAULT_SHADOW_OPACITY > 0.0);
    assert!(DEFAULT_SHADOW_OPACITY <= 1.0);
    assert!(DEFAULT_SHADOW_BLUR_PASSES > 0);
    assert!(DEFAULT_SHADOW_DOWNSCALE > 0);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shadow_config_default() {
        let config = ShadowConfig::default();
        assert!(!config.enabled);
        assert!((config.offset_x - DEFAULT_SHADOW_OFFSET_X).abs() < 0.001);
        assert!((config.offset_y - DEFAULT_SHADOW_OFFSET_Y).abs() < 0.001);
        assert!((config.opacity - DEFAULT_SHADOW_OPACITY).abs() < 0.001);
    }

    #[test]
    fn test_shadow_config_subtle() {
        let config = ShadowConfig::subtle();
        assert!(config.enabled);
        assert!(config.opacity < DEFAULT_SHADOW_OPACITY);
    }

    #[test]
    fn test_shadow_config_strong() {
        let config = ShadowConfig::strong();
        assert!(config.enabled);
        assert!(config.opacity > DEFAULT_SHADOW_OPACITY);
    }

    #[test]
    fn test_shadow_composite_uniforms_size() {
        assert_eq!(std::mem::size_of::<ShadowCompositeUniforms>(), 32);
    }

    #[test]
    fn test_shadow_blur_uniforms_size() {
        assert_eq!(std::mem::size_of::<ShadowBlurUniforms>(), 16);
    }

    #[test]
    fn test_constants() {
        // Verify constants are accessible (actual validation is at compile time)
        let _ = DEFAULT_SHADOW_OPACITY;
        let _ = DEFAULT_SHADOW_BLUR_PASSES;
        let _ = DEFAULT_SHADOW_DOWNSCALE;
    }
}
