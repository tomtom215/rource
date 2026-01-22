// Allow const inside function - common pattern for array initialization
#![allow(clippy::items_after_statements)]

//! Render pipeline management for wgpu renderer.
//!
//! This module handles creation and caching of render pipelines for all
//! primitive types. Each pipeline encapsulates:
//!
//! - Vertex and fragment shaders
//! - Vertex buffer layouts (position + instance data)
//! - Blend state configuration
//! - Bind group layouts for uniforms and textures
//!
//! ## Pipeline Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                        Pipeline Manager                          │
//! ├─────────────────────────────────────────────────────────────────┤
//! │ Shader Module (compiled once)                                    │
//! │   └─ Contains all primitive shader entry points                  │
//! ├─────────────────────────────────────────────────────────────────┤
//! │ Bind Group Layouts                                               │
//! │   ├─ Uniforms (group 0): resolution, time                        │
//! │   └─ Textures (group 1): texture + sampler                       │
//! ├─────────────────────────────────────────────────────────────────┤
//! │ Render Pipelines (created on demand)                             │
//! │   ├─ Circle     (vs_circle, fs_circle)                          │
//! │   ├─ Ring       (vs_ring, fs_ring)                              │
//! │   ├─ Line       (vs_line, fs_line)                              │
//! │   ├─ Quad       (vs_quad, fs_quad)                              │
//! │   ├─ TexturedQuad (vs_textured_quad, fs_textured_quad)          │
//! │   └─ Text       (vs_text, fs_text)                              │
//! └─────────────────────────────────────────────────────────────────┘
//! ```

use super::shaders::{CURVE_SHADER, PRIMITIVE_SHADER};
use super::state::PipelineId;

// Re-export instance sizes at module level for convenience.
pub use vertex_layouts::strides::CIRCLE as CIRCLE_INSTANCE_SIZE;
pub use vertex_layouts::strides::CURVE as CURVE_INSTANCE_SIZE;
pub use vertex_layouts::strides::LINE as LINE_INSTANCE_SIZE;
pub use vertex_layouts::strides::QUAD as QUAD_INSTANCE_SIZE;
pub use vertex_layouts::strides::RING as RING_INSTANCE_SIZE;
pub use vertex_layouts::strides::TEXTURED_QUAD as TEXTURED_QUAD_INSTANCE_SIZE;

/// Vertex attribute layouts for instance data.
pub mod vertex_layouts {
    use wgpu::VertexAttribute;

    /// Position-only vertex layout (location 0).
    pub const POSITION: [VertexAttribute; 1] = [VertexAttribute {
        format: wgpu::VertexFormat::Float32x2,
        offset: 0,
        shader_location: 0,
    }];

    /// Circle instance attributes: center (vec2), radius (f32), color (vec4).
    pub const CIRCLE_INSTANCE: [VertexAttribute; 3] = [
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 0,
            shader_location: 1, // center
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32,
            offset: 8,
            shader_location: 2, // radius
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 12,
            shader_location: 3, // color
        },
    ];

    /// Ring instance attributes: center (vec2), radius (f32), width (f32), color (vec4).
    pub const RING_INSTANCE: [VertexAttribute; 4] = [
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 0,
            shader_location: 1, // center
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32,
            offset: 8,
            shader_location: 2, // radius
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32,
            offset: 12,
            shader_location: 3, // width
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 16,
            shader_location: 4, // color
        },
    ];

    /// Line instance attributes: start (vec2), end (vec2), width (f32), color (vec4).
    pub const LINE_INSTANCE: [VertexAttribute; 4] = [
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 0,
            shader_location: 1, // start
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 8,
            shader_location: 2, // end
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32,
            offset: 16,
            shader_location: 3, // width
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 20,
            shader_location: 4, // color
        },
    ];

    /// Quad instance attributes: bounds (vec4), color (vec4).
    pub const QUAD_INSTANCE: [VertexAttribute; 2] = [
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 0,
            shader_location: 1, // bounds
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 16,
            shader_location: 2, // color
        },
    ];

    /// Textured quad instance attributes: bounds (vec4), `uv_bounds` (vec4), color (vec4).
    pub const TEXTURED_QUAD_INSTANCE: [VertexAttribute; 3] = [
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 0,
            shader_location: 1, // bounds
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 16,
            shader_location: 2, // uv_bounds
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 32,
            shader_location: 3, // color
        },
    ];

    /// Curve instance attributes: p0-p3 (4×vec2), width (f32), color (vec4), segments (u32).
    pub const CURVE_INSTANCE: [VertexAttribute; 7] = [
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 0,
            shader_location: 1, // p0
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 8,
            shader_location: 2, // p1
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 16,
            shader_location: 3, // p2
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x2,
            offset: 24,
            shader_location: 4, // p3
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32,
            offset: 32,
            shader_location: 5, // width
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Float32x4,
            offset: 36,
            shader_location: 6, // color
        },
        VertexAttribute {
            format: wgpu::VertexFormat::Uint32,
            offset: 52,
            shader_location: 7, // segments
        },
    ];

    /// Instance stride calculations.
    pub mod strides {
        /// Circle: center (2) + radius (1) + color (4) = 7 floats = 28 bytes.
        pub const CIRCLE: u64 = 28;
        /// Ring: center (2) + radius (1) + width (1) + color (4) = 8 floats = 32 bytes.
        pub const RING: u64 = 32;
        /// Line: start (2) + end (2) + width (1) + color (4) = 9 floats = 36 bytes.
        pub const LINE: u64 = 36;
        /// Quad: bounds (4) + color (4) = 8 floats = 32 bytes.
        pub const QUAD: u64 = 32;
        /// Textured quad: bounds (4) + `uv_bounds` (4) + color (4) = 12 floats = 48 bytes.
        pub const TEXTURED_QUAD: u64 = 48;
        /// Curve: p0-p3 (8) + width (1) + color (4) + segments (1) = 14 floats = 56 bytes.
        pub const CURVE: u64 = 56;
    }
}

/// Standard alpha blending state.
///
/// Uses pre-multiplied alpha: src * srcAlpha + dst * (1 - srcAlpha)
pub fn alpha_blend_state() -> wgpu::BlendState {
    wgpu::BlendState {
        color: wgpu::BlendComponent {
            src_factor: wgpu::BlendFactor::SrcAlpha,
            dst_factor: wgpu::BlendFactor::OneMinusSrcAlpha,
            operation: wgpu::BlendOperation::Add,
        },
        alpha: wgpu::BlendComponent {
            src_factor: wgpu::BlendFactor::One,
            dst_factor: wgpu::BlendFactor::OneMinusSrcAlpha,
            operation: wgpu::BlendOperation::Add,
        },
    }
}

/// Additive blending state (for bloom).
pub fn additive_blend_state() -> wgpu::BlendState {
    wgpu::BlendState {
        color: wgpu::BlendComponent {
            src_factor: wgpu::BlendFactor::One,
            dst_factor: wgpu::BlendFactor::One,
            operation: wgpu::BlendOperation::Add,
        },
        alpha: wgpu::BlendComponent {
            src_factor: wgpu::BlendFactor::One,
            dst_factor: wgpu::BlendFactor::One,
            operation: wgpu::BlendOperation::Add,
        },
    }
}

/// Manages render pipeline creation and caching.
///
/// Pipelines are created lazily when first requested and cached for reuse.
/// The manager handles shader compilation and bind group layout creation.
#[derive(Debug)]
pub struct PipelineManager {
    /// Compiled shader module containing all primitive shaders.
    shader_module: wgpu::ShaderModule,

    /// Compiled shader module for curve rendering (separate for modularity).
    curve_shader_module: Option<wgpu::ShaderModule>,

    /// Bind group layout for uniforms (group 0).
    uniform_layout: wgpu::BindGroupLayout,

    /// Bind group layout for textures (group 1).
    texture_layout: wgpu::BindGroupLayout,

    /// Cached render pipelines.
    pipelines: [Option<wgpu::RenderPipeline>; PipelineId::count()],

    /// Target texture format.
    surface_format: wgpu::TextureFormat,
}

impl PipelineManager {
    /// Creates a new pipeline manager.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for resource creation
    /// * `surface_format` - Target surface texture format
    ///
    /// # Returns
    ///
    /// A new pipeline manager with compiled shaders.
    pub fn new(device: &wgpu::Device, surface_format: wgpu::TextureFormat) -> Self {
        // Compile the primitive shader module
        let shader_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("primitive_shader"),
            source: wgpu::ShaderSource::Wgsl(PRIMITIVE_SHADER.into()),
        });

        // Create uniform bind group layout (group 0)
        let uniform_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
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

        // Create texture bind group layout (group 1)
        let texture_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("texture_bind_group_layout"),
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

        // Initialize pipeline cache with None
        const INIT: Option<wgpu::RenderPipeline> = None;
        let pipelines = [INIT; PipelineId::count()];

        Self {
            shader_module,
            curve_shader_module: None,
            uniform_layout,
            texture_layout,
            pipelines,
            surface_format,
        }
    }

    /// Returns the uniform bind group layout.
    #[inline]
    pub fn uniform_layout(&self) -> &wgpu::BindGroupLayout {
        &self.uniform_layout
    }

    /// Returns the texture bind group layout.
    #[inline]
    pub fn texture_layout(&self) -> &wgpu::BindGroupLayout {
        &self.texture_layout
    }

    /// Gets or creates a render pipeline for the given primitive type.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for pipeline creation
    /// * `id` - Pipeline identifier
    ///
    /// # Returns
    ///
    /// Reference to the render pipeline.
    pub fn get_pipeline(&mut self, device: &wgpu::Device, id: PipelineId) -> &wgpu::RenderPipeline {
        let index = id as usize;

        if self.pipelines[index].is_none() {
            self.pipelines[index] = Some(self.create_pipeline(device, id));
        }

        self.pipelines[index].as_ref().unwrap()
    }

    /// Creates a render pipeline for the given primitive type.
    fn create_pipeline(&mut self, device: &wgpu::Device, id: PipelineId) -> wgpu::RenderPipeline {
        match id {
            PipelineId::Circle => self.create_circle_pipeline(device),
            PipelineId::Ring => self.create_ring_pipeline(device),
            PipelineId::Line => self.create_line_pipeline(device),
            PipelineId::Quad => self.create_quad_pipeline(device),
            PipelineId::TexturedQuad => self.create_textured_quad_pipeline(device),
            PipelineId::Text => self.create_text_pipeline(device),
            PipelineId::Curve => self.create_curve_pipeline(device),
            _ => panic!("Pipeline {id:?} should be created through specific methods"),
        }
    }

    /// Creates the circle rendering pipeline.
    fn create_circle_pipeline(&self, device: &wgpu::Device) -> wgpu::RenderPipeline {
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("circle_pipeline_layout"),
            bind_group_layouts: &[&self.uniform_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("circle_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &self.shader_module,
                entry_point: Some("vs_circle"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[
                    // Vertex buffer (position)
                    wgpu::VertexBufferLayout {
                        array_stride: 8,
                        step_mode: wgpu::VertexStepMode::Vertex,
                        attributes: &vertex_layouts::POSITION,
                    },
                    // Instance buffer
                    wgpu::VertexBufferLayout {
                        array_stride: vertex_layouts::strides::CIRCLE,
                        step_mode: wgpu::VertexStepMode::Instance,
                        attributes: &vertex_layouts::CIRCLE_INSTANCE,
                    },
                ],
            },
            fragment: Some(wgpu::FragmentState {
                module: &self.shader_module,
                entry_point: Some("fs_circle"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.surface_format,
                    blend: Some(alpha_blend_state()),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                unclipped_depth: false,
                polygon_mode: wgpu::PolygonMode::Fill,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
            cache: None,
        })
    }

    /// Creates the ring rendering pipeline.
    fn create_ring_pipeline(&self, device: &wgpu::Device) -> wgpu::RenderPipeline {
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("ring_pipeline_layout"),
            bind_group_layouts: &[&self.uniform_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("ring_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &self.shader_module,
                entry_point: Some("vs_ring"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[
                    wgpu::VertexBufferLayout {
                        array_stride: 8,
                        step_mode: wgpu::VertexStepMode::Vertex,
                        attributes: &vertex_layouts::POSITION,
                    },
                    wgpu::VertexBufferLayout {
                        array_stride: vertex_layouts::strides::RING,
                        step_mode: wgpu::VertexStepMode::Instance,
                        attributes: &vertex_layouts::RING_INSTANCE,
                    },
                ],
            },
            fragment: Some(wgpu::FragmentState {
                module: &self.shader_module,
                entry_point: Some("fs_ring"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.surface_format,
                    blend: Some(alpha_blend_state()),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                unclipped_depth: false,
                polygon_mode: wgpu::PolygonMode::Fill,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
            cache: None,
        })
    }

    /// Creates the line rendering pipeline.
    fn create_line_pipeline(&self, device: &wgpu::Device) -> wgpu::RenderPipeline {
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("line_pipeline_layout"),
            bind_group_layouts: &[&self.uniform_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("line_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &self.shader_module,
                entry_point: Some("vs_line"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[
                    wgpu::VertexBufferLayout {
                        array_stride: 8,
                        step_mode: wgpu::VertexStepMode::Vertex,
                        attributes: &vertex_layouts::POSITION,
                    },
                    wgpu::VertexBufferLayout {
                        array_stride: vertex_layouts::strides::LINE,
                        step_mode: wgpu::VertexStepMode::Instance,
                        attributes: &vertex_layouts::LINE_INSTANCE,
                    },
                ],
            },
            fragment: Some(wgpu::FragmentState {
                module: &self.shader_module,
                entry_point: Some("fs_line"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.surface_format,
                    blend: Some(alpha_blend_state()),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                unclipped_depth: false,
                polygon_mode: wgpu::PolygonMode::Fill,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
            cache: None,
        })
    }

    /// Creates the solid quad rendering pipeline.
    fn create_quad_pipeline(&self, device: &wgpu::Device) -> wgpu::RenderPipeline {
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("quad_pipeline_layout"),
            bind_group_layouts: &[&self.uniform_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("quad_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &self.shader_module,
                entry_point: Some("vs_quad"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[
                    wgpu::VertexBufferLayout {
                        array_stride: 8,
                        step_mode: wgpu::VertexStepMode::Vertex,
                        attributes: &vertex_layouts::POSITION,
                    },
                    wgpu::VertexBufferLayout {
                        array_stride: vertex_layouts::strides::QUAD,
                        step_mode: wgpu::VertexStepMode::Instance,
                        attributes: &vertex_layouts::QUAD_INSTANCE,
                    },
                ],
            },
            fragment: Some(wgpu::FragmentState {
                module: &self.shader_module,
                entry_point: Some("fs_quad"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.surface_format,
                    blend: Some(alpha_blend_state()),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                unclipped_depth: false,
                polygon_mode: wgpu::PolygonMode::Fill,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
            cache: None,
        })
    }

    /// Creates the textured quad rendering pipeline.
    fn create_textured_quad_pipeline(&self, device: &wgpu::Device) -> wgpu::RenderPipeline {
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("textured_quad_pipeline_layout"),
            bind_group_layouts: &[&self.uniform_layout, &self.texture_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("textured_quad_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &self.shader_module,
                entry_point: Some("vs_textured_quad"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[
                    wgpu::VertexBufferLayout {
                        array_stride: 8,
                        step_mode: wgpu::VertexStepMode::Vertex,
                        attributes: &vertex_layouts::POSITION,
                    },
                    wgpu::VertexBufferLayout {
                        array_stride: vertex_layouts::strides::TEXTURED_QUAD,
                        step_mode: wgpu::VertexStepMode::Instance,
                        attributes: &vertex_layouts::TEXTURED_QUAD_INSTANCE,
                    },
                ],
            },
            fragment: Some(wgpu::FragmentState {
                module: &self.shader_module,
                entry_point: Some("fs_textured_quad"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.surface_format,
                    blend: Some(alpha_blend_state()),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                unclipped_depth: false,
                polygon_mode: wgpu::PolygonMode::Fill,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
            cache: None,
        })
    }

    /// Creates the text rendering pipeline.
    fn create_text_pipeline(&self, device: &wgpu::Device) -> wgpu::RenderPipeline {
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("text_pipeline_layout"),
            bind_group_layouts: &[&self.uniform_layout, &self.texture_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("text_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &self.shader_module,
                entry_point: Some("vs_text"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[
                    wgpu::VertexBufferLayout {
                        array_stride: 8,
                        step_mode: wgpu::VertexStepMode::Vertex,
                        attributes: &vertex_layouts::POSITION,
                    },
                    wgpu::VertexBufferLayout {
                        array_stride: vertex_layouts::strides::TEXTURED_QUAD,
                        step_mode: wgpu::VertexStepMode::Instance,
                        attributes: &vertex_layouts::TEXTURED_QUAD_INSTANCE,
                    },
                ],
            },
            fragment: Some(wgpu::FragmentState {
                module: &self.shader_module,
                entry_point: Some("fs_text"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.surface_format,
                    blend: Some(alpha_blend_state()),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                unclipped_depth: false,
                polygon_mode: wgpu::PolygonMode::Fill,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
            cache: None,
        })
    }

    /// Creates the curve rendering pipeline.
    ///
    /// This pipeline renders Catmull-Rom spline curves using a separate shader module.
    fn create_curve_pipeline(&mut self, device: &wgpu::Device) -> wgpu::RenderPipeline {
        // Compile curve shader module if not already done
        if self.curve_shader_module.is_none() {
            self.curve_shader_module =
                Some(device.create_shader_module(wgpu::ShaderModuleDescriptor {
                    label: Some("curve_shader"),
                    source: wgpu::ShaderSource::Wgsl(CURVE_SHADER.into()),
                }));
        }

        let curve_shader = self.curve_shader_module.as_ref().unwrap();

        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("curve_pipeline_layout"),
            bind_group_layouts: &[&self.uniform_layout],
            push_constant_ranges: &[],
        });

        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("curve_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: curve_shader,
                entry_point: Some("vs_curve"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[
                    // Vertex buffer (position)
                    wgpu::VertexBufferLayout {
                        array_stride: 8,
                        step_mode: wgpu::VertexStepMode::Vertex,
                        attributes: &vertex_layouts::POSITION,
                    },
                    // Instance buffer
                    wgpu::VertexBufferLayout {
                        array_stride: vertex_layouts::strides::CURVE,
                        step_mode: wgpu::VertexStepMode::Instance,
                        attributes: &vertex_layouts::CURVE_INSTANCE,
                    },
                ],
            },
            fragment: Some(wgpu::FragmentState {
                module: curve_shader,
                entry_point: Some("fs_curve"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.surface_format,
                    blend: Some(alpha_blend_state()),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleStrip,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None,
                unclipped_depth: false,
                polygon_mode: wgpu::PolygonMode::Fill,
                conservative: false,
            },
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            multiview: None,
            cache: None,
        })
    }

    /// Returns whether a pipeline is already cached.
    #[inline]
    pub fn has_pipeline(&self, id: PipelineId) -> bool {
        self.pipelines[id as usize].is_some()
    }

    /// Returns the surface format.
    #[inline]
    pub fn surface_format(&self) -> wgpu::TextureFormat {
        self.surface_format
    }

    /// Pre-creates all primitive pipelines.
    ///
    /// Call this during initialization to avoid first-frame stutters
    /// from lazy pipeline creation.
    pub fn warmup(&mut self, device: &wgpu::Device) {
        for id in PipelineId::primitives() {
            let _ = self.get_pipeline(device, id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_instance_strides() {
        // Verify stride calculations match expected sizes
        use vertex_layouts::strides;

        // Circle: 7 floats
        assert_eq!(strides::CIRCLE, 7 * 4);
        // Ring: 8 floats
        assert_eq!(strides::RING, 8 * 4);
        // Line: 9 floats
        assert_eq!(strides::LINE, 9 * 4);
        // Quad: 8 floats
        assert_eq!(strides::QUAD, 8 * 4);
        // Textured quad: 12 floats
        assert_eq!(strides::TEXTURED_QUAD, 12 * 4);
        // Curve: 14 floats (p0-p3 (8) + width (1) + color (4) + segments (1))
        assert_eq!(strides::CURVE, 14 * 4);
    }

    #[test]
    fn test_circle_instance_layout() {
        let attrs = &vertex_layouts::CIRCLE_INSTANCE;
        assert_eq!(attrs.len(), 3);

        // center at location 1
        assert_eq!(attrs[0].shader_location, 1);
        assert_eq!(attrs[0].offset, 0);

        // radius at location 2
        assert_eq!(attrs[1].shader_location, 2);
        assert_eq!(attrs[1].offset, 8);

        // color at location 3
        assert_eq!(attrs[2].shader_location, 3);
        assert_eq!(attrs[2].offset, 12);
    }

    #[test]
    fn test_ring_instance_layout() {
        let attrs = &vertex_layouts::RING_INSTANCE;
        assert_eq!(attrs.len(), 4);

        // Check sequential shader locations
        assert_eq!(attrs[0].shader_location, 1);
        assert_eq!(attrs[1].shader_location, 2);
        assert_eq!(attrs[2].shader_location, 3);
        assert_eq!(attrs[3].shader_location, 4);
    }

    #[test]
    fn test_line_instance_layout() {
        let attrs = &vertex_layouts::LINE_INSTANCE;
        assert_eq!(attrs.len(), 4);

        // start (vec2) at offset 0
        assert_eq!(attrs[0].offset, 0);
        // end (vec2) at offset 8
        assert_eq!(attrs[1].offset, 8);
        // width (f32) at offset 16
        assert_eq!(attrs[2].offset, 16);
        // color (vec4) at offset 20
        assert_eq!(attrs[3].offset, 20);
    }

    #[test]
    fn test_quad_instance_layout() {
        let attrs = &vertex_layouts::QUAD_INSTANCE;
        assert_eq!(attrs.len(), 2);

        // bounds (vec4) at offset 0
        assert_eq!(attrs[0].offset, 0);
        // color (vec4) at offset 16
        assert_eq!(attrs[1].offset, 16);
    }

    #[test]
    fn test_textured_quad_instance_layout() {
        let attrs = &vertex_layouts::TEXTURED_QUAD_INSTANCE;
        assert_eq!(attrs.len(), 3);

        // bounds (vec4) at offset 0
        assert_eq!(attrs[0].offset, 0);
        // uv_bounds (vec4) at offset 16
        assert_eq!(attrs[1].offset, 16);
        // color (vec4) at offset 32
        assert_eq!(attrs[2].offset, 32);
    }

    #[test]
    fn test_alpha_blend_state() {
        let blend = alpha_blend_state();
        assert_eq!(blend.color.src_factor, wgpu::BlendFactor::SrcAlpha);
        assert_eq!(blend.color.dst_factor, wgpu::BlendFactor::OneMinusSrcAlpha);
        assert_eq!(blend.color.operation, wgpu::BlendOperation::Add);
    }

    #[test]
    fn test_additive_blend_state() {
        let blend = additive_blend_state();
        assert_eq!(blend.color.src_factor, wgpu::BlendFactor::One);
        assert_eq!(blend.color.dst_factor, wgpu::BlendFactor::One);
        assert_eq!(blend.color.operation, wgpu::BlendOperation::Add);
    }

    #[test]
    fn test_position_layout() {
        let attrs = &vertex_layouts::POSITION;
        assert_eq!(attrs.len(), 1);
        assert_eq!(attrs[0].shader_location, 0);
        assert_eq!(attrs[0].offset, 0);
    }

    #[test]
    fn test_curve_instance_layout() {
        let attrs = &vertex_layouts::CURVE_INSTANCE;
        assert_eq!(attrs.len(), 7);

        // p0 (vec2) at offset 0, location 1
        assert_eq!(attrs[0].offset, 0);
        assert_eq!(attrs[0].shader_location, 1);

        // p1 (vec2) at offset 8, location 2
        assert_eq!(attrs[1].offset, 8);
        assert_eq!(attrs[1].shader_location, 2);

        // p2 (vec2) at offset 16, location 3
        assert_eq!(attrs[2].offset, 16);
        assert_eq!(attrs[2].shader_location, 3);

        // p3 (vec2) at offset 24, location 4
        assert_eq!(attrs[3].offset, 24);
        assert_eq!(attrs[3].shader_location, 4);

        // width (f32) at offset 32, location 5
        assert_eq!(attrs[4].offset, 32);
        assert_eq!(attrs[4].shader_location, 5);

        // color (vec4) at offset 36, location 6
        assert_eq!(attrs[5].offset, 36);
        assert_eq!(attrs[5].shader_location, 6);

        // segments (u32) at offset 52, location 7
        assert_eq!(attrs[6].offset, 52);
        assert_eq!(attrs[6].shader_location, 7);
    }
}
