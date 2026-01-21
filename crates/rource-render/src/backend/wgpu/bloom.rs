//! GPU bloom effect implementation for wgpu.
//!
//! This module provides a high-performance GPU-based bloom effect that creates
//! a glow around bright areas of the rendered scene. The implementation uses
//! render targets for render-to-texture operations.
//!
//! ## Pipeline
//!
//! The bloom effect is implemented as a multi-pass post-processing pipeline:
//!
//! 1. **Scene Render**: Scene is rendered to the scene render target
//! 2. **Bright Pass**: Extract pixels above brightness threshold to bloom target
//! 3. **Blur Pass (H)**: Horizontal Gaussian blur on bloom target
//! 4. **Blur Pass (V)**: Vertical Gaussian blur (ping-pong to second target)
//! 5. **Composite**: Additively blend bloom with original scene
//!
//! ## Performance
//!
//! - Bloom is rendered at configurable downscale (default 4x) for efficiency
//! - Separable Gaussian blur (two 1D passes instead of one 2D pass)
//! - Lazy resource creation - resources allocated only when bloom is enabled
//! - Automatic resize handling when viewport dimensions change

use wgpu::util::DeviceExt;

use super::buffers::FULLSCREEN_QUAD;
use super::shaders::{BLOOM_BLUR_SHADER, BLOOM_BRIGHT_SHADER, BLOOM_COMPOSITE_SHADER};

/// Default brightness threshold for bloom extraction.
pub const DEFAULT_BLOOM_THRESHOLD: f32 = 0.7;

/// Default bloom intensity multiplier.
pub const DEFAULT_BLOOM_INTENSITY: f32 = 1.0;

/// Default downscale factor for bloom buffers.
pub const DEFAULT_BLOOM_DOWNSCALE: u32 = 4;

/// Default number of blur passes.
pub const DEFAULT_BLOOM_PASSES: u32 = 2;

/// Configuration for the GPU bloom effect.
#[derive(Debug, Clone, Copy)]
pub struct BloomConfig {
    /// Whether bloom effect is enabled.
    pub enabled: bool,
    /// Brightness threshold (0.0 - 1.0).
    pub threshold: f32,
    /// Bloom intensity multiplier.
    pub intensity: f32,
    /// Downscale factor for bloom buffers.
    pub downscale: u32,
    /// Number of blur passes.
    pub passes: u32,
}

impl Default for BloomConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            threshold: DEFAULT_BLOOM_THRESHOLD,
            intensity: DEFAULT_BLOOM_INTENSITY,
            downscale: DEFAULT_BLOOM_DOWNSCALE,
            passes: DEFAULT_BLOOM_PASSES,
        }
    }
}

impl BloomConfig {
    /// Creates a new bloom configuration with default values.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a subtle bloom configuration.
    #[must_use]
    pub fn subtle() -> Self {
        Self {
            enabled: true,
            threshold: 0.8,
            intensity: 0.5,
            downscale: 4,
            passes: 1,
        }
    }

    /// Creates an intense bloom configuration.
    #[must_use]
    pub fn intense() -> Self {
        Self {
            enabled: true,
            threshold: 0.5,
            intensity: 2.0,
            downscale: 2,
            passes: 3,
        }
    }
}

/// Render target for post-processing.
#[derive(Debug)]
pub struct RenderTarget {
    /// The texture.
    texture: wgpu::Texture,
    /// Texture view for rendering/sampling.
    view: wgpu::TextureView,
    /// Width in pixels.
    width: u32,
    /// Height in pixels.
    height: u32,
}

impl RenderTarget {
    /// Creates a new render target.
    pub fn new(
        device: &wgpu::Device,
        width: u32,
        height: u32,
        format: wgpu::TextureFormat,
        label: &str,
    ) -> Self {
        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: Some(label),
            size: wgpu::Extent3d {
                width,
                height,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format,
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT | wgpu::TextureUsages::TEXTURE_BINDING,
            view_formats: &[],
        });

        let view = texture.create_view(&wgpu::TextureViewDescriptor::default());

        Self {
            texture,
            view,
            width,
            height,
        }
    }

    /// Returns the texture view.
    #[inline]
    pub fn view(&self) -> &wgpu::TextureView {
        &self.view
    }

    /// Returns the texture.
    #[inline]
    pub fn texture(&self) -> &wgpu::Texture {
        &self.texture
    }

    /// Returns the dimensions.
    #[inline]
    pub fn dimensions(&self) -> (u32, u32) {
        (self.width, self.height)
    }
}

/// Bloom bright pass uniform data.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct BloomBrightUniforms {
    threshold: f32,
    intensity: f32,
    _padding: [f32; 2],
}

/// Bloom blur pass uniform data.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct BloomBlurUniforms {
    direction: [f32; 2],
    resolution: [f32; 2],
}

/// Bloom composite pass uniform data.
#[repr(C)]
#[derive(Debug, Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct BloomCompositeUniforms {
    intensity: f32,
    _padding: [f32; 3],
}

/// GPU bloom effect pipeline.
#[derive(Debug)]
pub struct BloomPipeline {
    /// Bloom configuration.
    pub config: BloomConfig,

    /// Scene render target (full resolution).
    scene_target: Option<RenderTarget>,

    /// Bloom target A (downscaled).
    bloom_target_a: Option<RenderTarget>,

    /// Bloom target B (downscaled, ping-pong).
    bloom_target_b: Option<RenderTarget>,

    /// Bright pass pipeline.
    bright_pipeline: wgpu::RenderPipeline,

    /// Blur pass pipeline.
    blur_pipeline: wgpu::RenderPipeline,

    /// Composite pass pipeline.
    composite_pipeline: wgpu::RenderPipeline,

    /// Bright pass uniform buffer.
    bright_uniforms: wgpu::Buffer,

    /// Blur pass uniform buffer.
    blur_uniforms: wgpu::Buffer,

    /// Composite pass uniform buffer.
    composite_uniforms: wgpu::Buffer,

    /// Uniform bind group layout.
    uniform_layout: wgpu::BindGroupLayout,

    /// Texture bind group layout.
    texture_layout: wgpu::BindGroupLayout,

    /// Texture bind group layout for composite (two textures).
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
}

impl BloomPipeline {
    /// Creates a new bloom pipeline.
    pub fn new(device: &wgpu::Device, surface_format: wgpu::TextureFormat) -> Self {
        // Create bind group layouts
        let uniform_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("bloom_uniform_layout"),
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
            label: Some("bloom_texture_layout"),
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
                label: Some("bloom_composite_texture_layout"),
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
        let bright_pipeline =
            Self::create_bright_pipeline(device, &uniform_layout, &texture_layout, surface_format);
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
        let bright_uniforms = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("bloom_bright_uniforms"),
            contents: bytemuck::cast_slice(&[BloomBrightUniforms {
                threshold: DEFAULT_BLOOM_THRESHOLD,
                intensity: DEFAULT_BLOOM_INTENSITY,
                _padding: [0.0; 2],
            }]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });

        let blur_uniforms = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("bloom_blur_uniforms"),
            contents: bytemuck::cast_slice(&[BloomBlurUniforms {
                direction: [1.0, 0.0],
                resolution: [1.0, 1.0],
            }]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });

        let composite_uniforms = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("bloom_composite_uniforms"),
            contents: bytemuck::cast_slice(&[BloomCompositeUniforms {
                intensity: 1.0,
                _padding: [0.0; 3],
            }]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });

        // Create sampler
        let sampler = device.create_sampler(&wgpu::SamplerDescriptor {
            label: Some("bloom_sampler"),
            address_mode_u: wgpu::AddressMode::ClampToEdge,
            address_mode_v: wgpu::AddressMode::ClampToEdge,
            address_mode_w: wgpu::AddressMode::ClampToEdge,
            mag_filter: wgpu::FilterMode::Linear,
            min_filter: wgpu::FilterMode::Linear,
            mipmap_filter: wgpu::FilterMode::Nearest,
            ..Default::default()
        });

        // Create fullscreen quad
        let fullscreen_quad = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("bloom_fullscreen_quad"),
            contents: bytemuck::cast_slice(&FULLSCREEN_QUAD),
            usage: wgpu::BufferUsages::VERTEX,
        });

        Self {
            config: BloomConfig::default(),
            scene_target: None,
            bloom_target_a: None,
            bloom_target_b: None,
            bright_pipeline,
            blur_pipeline,
            composite_pipeline,
            bright_uniforms,
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
        }
    }

    /// Returns whether bloom is enabled and ready.
    #[inline]
    pub fn is_active(&self) -> bool {
        self.config.enabled && self.initialized && self.scene_target.is_some()
    }

    /// Ensures render targets are sized correctly.
    pub fn ensure_size(&mut self, device: &wgpu::Device, width: u32, height: u32) {
        if !self.config.enabled {
            return;
        }

        if self.cached_size == (width, height) && self.scene_target.is_some() {
            return;
        }

        self.cached_size = (width, height);

        // Create scene target at full resolution
        self.scene_target = Some(RenderTarget::new(
            device,
            width,
            height,
            self.surface_format,
            "bloom_scene_target",
        ));

        // Create bloom targets at downscaled resolution
        let bloom_width = (width / self.config.downscale).max(1);
        let bloom_height = (height / self.config.downscale).max(1);

        self.bloom_target_a = Some(RenderTarget::new(
            device,
            bloom_width,
            bloom_height,
            self.surface_format,
            "bloom_target_a",
        ));

        self.bloom_target_b = Some(RenderTarget::new(
            device,
            bloom_width,
            bloom_height,
            self.surface_format,
            "bloom_target_b",
        ));
    }

    /// Returns the scene render target view for rendering the scene.
    pub fn scene_view(&self) -> Option<&wgpu::TextureView> {
        self.scene_target.as_ref().map(RenderTarget::view)
    }

    /// Applies the bloom effect.
    ///
    /// Call this after rendering the scene to the scene target.
    /// The result is written to the provided output view (typically the surface).
    pub fn apply(
        &self,
        device: &wgpu::Device,
        queue: &wgpu::Queue,
        encoder: &mut wgpu::CommandEncoder,
        output_view: &wgpu::TextureView,
    ) {
        if !self.is_active() {
            return;
        }

        let scene_target = self.scene_target.as_ref().unwrap();
        let bloom_a = self.bloom_target_a.as_ref().unwrap();
        let bloom_b = self.bloom_target_b.as_ref().unwrap();

        // Update uniforms
        queue.write_buffer(
            &self.bright_uniforms,
            0,
            bytemuck::cast_slice(&[BloomBrightUniforms {
                threshold: self.config.threshold,
                intensity: self.config.intensity,
                _padding: [0.0; 2],
            }]),
        );

        queue.write_buffer(
            &self.composite_uniforms,
            0,
            bytemuck::cast_slice(&[BloomCompositeUniforms {
                intensity: 1.0,
                _padding: [0.0; 3],
            }]),
        );

        // Create bind groups
        let uniform_bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bloom_bright_uniform_bg"),
            layout: &self.uniform_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: self.bright_uniforms.as_entire_binding(),
            }],
        });

        let scene_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bloom_scene_texture_bg"),
            layout: &self.texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(scene_target.view()),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&self.sampler),
                },
            ],
        });

        // =====================================================================
        // Pass 1: Extract bright pixels
        // =====================================================================
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("bloom_bright_pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: bloom_a.view(),
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color::BLACK),
                        store: wgpu::StoreOp::Store,
                    },
                })],
                depth_stencil_attachment: None,
                timestamp_writes: None,
                occlusion_query_set: None,
            });

            render_pass.set_pipeline(&self.bright_pipeline);
            render_pass.set_bind_group(0, &uniform_bind_group, &[]);
            render_pass.set_bind_group(1, &scene_texture_bg, &[]);
            render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
            render_pass.draw(0..4, 0..1);
        }

        // =====================================================================
        // Pass 2: Gaussian blur (ping-pong)
        // =====================================================================
        let bloom_dims = bloom_a.dimensions();

        for _ in 0..self.config.passes {
            // Horizontal blur: A -> B
            {
                queue.write_buffer(
                    &self.blur_uniforms,
                    0,
                    bytemuck::cast_slice(&[BloomBlurUniforms {
                        direction: [1.0, 0.0],
                        resolution: [bloom_dims.0 as f32, bloom_dims.1 as f32],
                    }]),
                );

                let blur_uniform_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("bloom_blur_h_uniform_bg"),
                    layout: &self.uniform_layout,
                    entries: &[wgpu::BindGroupEntry {
                        binding: 0,
                        resource: self.blur_uniforms.as_entire_binding(),
                    }],
                });

                let bloom_a_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("bloom_a_texture_bg"),
                    layout: &self.texture_layout,
                    entries: &[
                        wgpu::BindGroupEntry {
                            binding: 0,
                            resource: wgpu::BindingResource::TextureView(bloom_a.view()),
                        },
                        wgpu::BindGroupEntry {
                            binding: 1,
                            resource: wgpu::BindingResource::Sampler(&self.sampler),
                        },
                    ],
                });

                let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                    label: Some("bloom_blur_h_pass"),
                    color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                        view: bloom_b.view(),
                        resolve_target: None,
                        ops: wgpu::Operations {
                            load: wgpu::LoadOp::Clear(wgpu::Color::BLACK),
                            store: wgpu::StoreOp::Store,
                        },
                    })],
                    depth_stencil_attachment: None,
                    timestamp_writes: None,
                    occlusion_query_set: None,
                });

                render_pass.set_pipeline(&self.blur_pipeline);
                render_pass.set_bind_group(0, &blur_uniform_bg, &[]);
                render_pass.set_bind_group(1, &bloom_a_texture_bg, &[]);
                render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
                render_pass.draw(0..4, 0..1);
            }

            // Vertical blur: B -> A
            {
                queue.write_buffer(
                    &self.blur_uniforms,
                    0,
                    bytemuck::cast_slice(&[BloomBlurUniforms {
                        direction: [0.0, 1.0],
                        resolution: [bloom_dims.0 as f32, bloom_dims.1 as f32],
                    }]),
                );

                let blur_uniform_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("bloom_blur_v_uniform_bg"),
                    layout: &self.uniform_layout,
                    entries: &[wgpu::BindGroupEntry {
                        binding: 0,
                        resource: self.blur_uniforms.as_entire_binding(),
                    }],
                });

                let bloom_b_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("bloom_b_texture_bg"),
                    layout: &self.texture_layout,
                    entries: &[
                        wgpu::BindGroupEntry {
                            binding: 0,
                            resource: wgpu::BindingResource::TextureView(bloom_b.view()),
                        },
                        wgpu::BindGroupEntry {
                            binding: 1,
                            resource: wgpu::BindingResource::Sampler(&self.sampler),
                        },
                    ],
                });

                let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                    label: Some("bloom_blur_v_pass"),
                    color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                        view: bloom_a.view(),
                        resolve_target: None,
                        ops: wgpu::Operations {
                            load: wgpu::LoadOp::Clear(wgpu::Color::BLACK),
                            store: wgpu::StoreOp::Store,
                        },
                    })],
                    depth_stencil_attachment: None,
                    timestamp_writes: None,
                    occlusion_query_set: None,
                });

                render_pass.set_pipeline(&self.blur_pipeline);
                render_pass.set_bind_group(0, &blur_uniform_bg, &[]);
                render_pass.set_bind_group(1, &bloom_b_texture_bg, &[]);
                render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
                render_pass.draw(0..4, 0..1);
            }
        }

        // =====================================================================
        // Pass 3: Composite
        // =====================================================================
        {
            let composite_uniform_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("bloom_composite_uniform_bg"),
                layout: &self.uniform_layout,
                entries: &[wgpu::BindGroupEntry {
                    binding: 0,
                    resource: self.composite_uniforms.as_entire_binding(),
                }],
            });

            let bloom_final_texture_bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("bloom_final_texture_bg"),
                layout: &self.composite_texture_layout,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: wgpu::BindingResource::TextureView(bloom_a.view()),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: wgpu::BindingResource::Sampler(&self.sampler),
                    },
                ],
            });

            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("bloom_composite_pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: output_view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color::BLACK),
                        store: wgpu::StoreOp::Store,
                    },
                })],
                depth_stencil_attachment: None,
                timestamp_writes: None,
                occlusion_query_set: None,
            });

            render_pass.set_pipeline(&self.composite_pipeline);
            render_pass.set_bind_group(0, &composite_uniform_bg, &[]);
            render_pass.set_bind_group(1, &scene_texture_bg, &[]);
            render_pass.set_bind_group(2, &bloom_final_texture_bg, &[]);
            render_pass.set_vertex_buffer(0, self.fullscreen_quad.slice(..));
            render_pass.draw(0..4, 0..1);
        }
    }

    fn create_bright_pipeline(
        device: &wgpu::Device,
        uniform_layout: &wgpu::BindGroupLayout,
        texture_layout: &wgpu::BindGroupLayout,
        format: wgpu::TextureFormat,
    ) -> wgpu::RenderPipeline {
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("bloom_bright_shader"),
            source: wgpu::ShaderSource::Wgsl(BLOOM_BRIGHT_SHADER.into()),
        });

        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("bloom_bright_layout"),
            bind_group_layouts: &[uniform_layout, texture_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("bloom_bright_pipeline"),
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
                entry_point: Some("fs_bloom_bright"),
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
            multiview: None,
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
            label: Some("bloom_blur_shader"),
            source: wgpu::ShaderSource::Wgsl(BLOOM_BLUR_SHADER.into()),
        });

        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("bloom_blur_layout"),
            bind_group_layouts: &[uniform_layout, texture_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("bloom_blur_pipeline"),
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
            multiview: None,
            cache: None,
        })
    }

    fn create_composite_pipeline(
        device: &wgpu::Device,
        uniform_layout: &wgpu::BindGroupLayout,
        scene_texture_layout: &wgpu::BindGroupLayout,
        bloom_texture_layout: &wgpu::BindGroupLayout,
        format: wgpu::TextureFormat,
    ) -> wgpu::RenderPipeline {
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("bloom_composite_shader"),
            source: wgpu::ShaderSource::Wgsl(BLOOM_COMPOSITE_SHADER.into()),
        });

        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("bloom_composite_layout"),
            bind_group_layouts: &[uniform_layout, scene_texture_layout, bloom_texture_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("bloom_composite_pipeline"),
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
                entry_point: Some("fs_bloom_composite"),
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
            multiview: None,
            cache: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_config_default() {
        let config = BloomConfig::default();
        assert!(config.enabled);
        assert!((config.threshold - DEFAULT_BLOOM_THRESHOLD).abs() < 0.001);
        assert!((config.intensity - DEFAULT_BLOOM_INTENSITY).abs() < 0.001);
        assert_eq!(config.downscale, DEFAULT_BLOOM_DOWNSCALE);
        assert_eq!(config.passes, DEFAULT_BLOOM_PASSES);
    }

    #[test]
    fn test_bloom_config_subtle() {
        let config = BloomConfig::subtle();
        assert!(config.enabled);
        assert!(config.threshold > DEFAULT_BLOOM_THRESHOLD);
        assert!(config.intensity < DEFAULT_BLOOM_INTENSITY);
    }

    #[test]
    fn test_bloom_config_intense() {
        let config = BloomConfig::intense();
        assert!(config.enabled);
        assert!(config.threshold < DEFAULT_BLOOM_THRESHOLD);
        assert!(config.intensity > DEFAULT_BLOOM_INTENSITY);
    }

    #[test]
    fn test_bloom_bright_uniforms_size() {
        assert_eq!(std::mem::size_of::<BloomBrightUniforms>(), 16);
    }

    #[test]
    fn test_bloom_blur_uniforms_size() {
        assert_eq!(std::mem::size_of::<BloomBlurUniforms>(), 16);
    }

    #[test]
    fn test_bloom_composite_uniforms_size() {
        assert_eq!(std::mem::size_of::<BloomCompositeUniforms>(), 16);
    }

    #[test]
    fn test_constants() {
        // These are const assertions moved to module level
        // Just verify the values are accessible
        let _ = DEFAULT_BLOOM_THRESHOLD;
        let _ = DEFAULT_BLOOM_INTENSITY;
        let _ = DEFAULT_BLOOM_DOWNSCALE;
        let _ = DEFAULT_BLOOM_PASSES;
    }
}

// Compile-time constant validation
const _: () = {
    assert!(DEFAULT_BLOOM_THRESHOLD > 0.0);
    assert!(DEFAULT_BLOOM_THRESHOLD < 1.0);
    assert!(DEFAULT_BLOOM_INTENSITY > 0.0);
    assert!(DEFAULT_BLOOM_DOWNSCALE >= 1);
    assert!(DEFAULT_BLOOM_PASSES >= 1);
};
