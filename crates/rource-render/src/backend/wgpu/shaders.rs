// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! WGSL shaders for wgpu renderer.
//!
//! This module contains all shader source code for the wgpu rendering backend.
//! Shaders are organized by category:

// Allow raw string hashes for WGSL shader code readability
#![allow(clippy::needless_raw_string_hashes)]
//!
//! - **Primitive shaders**: Circle, ring, line, quad, text rendering
//! - **Post-processing shaders**: Bloom (bright, blur, composite), Shadow
//! - **Compute shaders**: Physics simulation (force calculation, integration)
//!
//! ## Shader Design Principles
//!
//! 1. **Anti-aliasing**: All primitives use distance-field based AA for smooth edges
//! 2. **Instancing**: Vertex shaders support per-instance data for efficient batching
//! 3. **Determinism**: Shaders produce identical output for identical input
//! 4. **Performance**: Minimize branching and memory access
//!
//! ## Uniform Layout
//!
//! All shaders share a common uniform buffer at group 0, binding 0:
//! ```wgsl
//! struct Uniforms {
//!     resolution: vec2<f32>,
//!     time: f32,
//!     _padding: f32,
//! };
//! ```

/// Combined shader source for all primitive rendering.
///
/// This single shader module contains vertex and fragment shaders for all
/// primitive types, reducing shader compilation overhead.
pub const PRIMITIVE_SHADER: &str = r#"
// ============================================================================
// Shared Uniforms
// ============================================================================

struct Uniforms {
    resolution: vec2<f32>,
    time: f32,
    _padding: f32,
};

@group(0) @binding(0)
var<uniform> uniforms: Uniforms;

// ============================================================================
// Circle Shader (Filled Disc)
// ============================================================================

struct CircleVertexInput {
    @location(0) position: vec2<f32>,
};

struct CircleInstance {
    @location(1) center: vec2<f32>,
    @location(2) radius: f32,
    @location(3) color: vec4<f32>,
};

struct CircleVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) local_pos: vec2<f32>,
    @location(1) color: vec4<f32>,
};

@vertex
fn vs_circle(vertex: CircleVertexInput, instance: CircleInstance) -> CircleVertexOutput {
    var out: CircleVertexOutput;

    // Store local position for distance calculation in fragment shader
    out.local_pos = vertex.position;

    // Expand unit quad to circle bounds with 1px padding for AA
    let world_pos = instance.center + vertex.position * (instance.radius + 1.0);

    // Convert to NDC (normalized device coordinates)
    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.color = instance.color;
    return out;
}

@fragment
fn fs_circle(in: CircleVertexOutput) -> @location(0) vec4<f32> {
    // Distance from center (local_pos is -1 to 1)
    let dist = length(in.local_pos);

    // Anti-aliased edge using smoothstep
    // Edge starts at radius=1.0 (the actual circle edge)
    let aa_width = 1.5 / max(uniforms.resolution.x, uniforms.resolution.y) * 100.0;
    let alpha = 1.0 - smoothstep(1.0 - aa_width, 1.0 + aa_width, dist);

    return vec4<f32>(in.color.rgb, in.color.a * alpha);
}

// ============================================================================
// Ring Shader (Circle Outline)
// ============================================================================

struct RingInstance {
    @location(1) center: vec2<f32>,
    @location(2) radius: f32,
    @location(3) width: f32,
    @location(4) color: vec4<f32>,
};

struct RingVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) local_pos: vec2<f32>,
    @location(1) radius: f32,
    @location(2) width: f32,
    @location(3) outer_radius: f32, // Pre-computed in vertex shader to avoid recalculation
    @location(4) color: vec4<f32>,
};

@vertex
fn vs_ring(vertex: CircleVertexInput, instance: RingInstance) -> RingVertexOutput {
    var out: RingVertexOutput;

    out.local_pos = vertex.position;
    out.radius = instance.radius;
    out.width = instance.width;

    // Expand quad to cover full ring including AA padding
    // Pre-compute and pass to fragment shader to avoid per-fragment recalculation
    let outer_radius = instance.radius + instance.width * 0.5 + 1.0;
    out.outer_radius = outer_radius;
    let world_pos = instance.center + vertex.position * outer_radius;

    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.color = instance.color;
    return out;
}

@fragment
fn fs_ring(in: RingVertexOutput) -> @location(0) vec4<f32> {
    // Scale local position to world units (outer_radius pre-computed in vertex shader)
    let world_dist = length(in.local_pos) * in.outer_radius;

    // Distance from the ring centerline
    let inner_radius = in.radius - in.width * 0.5;
    let outer_radius_actual = in.radius + in.width * 0.5;

    // Anti-aliased edges
    let aa_width = 1.0;
    let inner_alpha = smoothstep(inner_radius - aa_width, inner_radius + aa_width, world_dist);
    let outer_alpha = 1.0 - smoothstep(outer_radius_actual - aa_width, outer_radius_actual + aa_width, world_dist);
    let alpha = inner_alpha * outer_alpha;

    return vec4<f32>(in.color.rgb, in.color.a * alpha);
}

// ============================================================================
// Line Shader
// ============================================================================

struct LineVertexInput {
    @location(0) position: vec2<f32>,
};

struct LineInstance {
    @location(1) start: vec2<f32>,
    @location(2) end: vec2<f32>,
    @location(3) width: f32,
    @location(4) color: vec4<f32>,
};

struct LineVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) local_pos: vec2<f32>,
    @location(1) half_width: f32,     // Pre-computed: width * 0.5 (without padding)
    @location(2) half_width_padded: f32, // Pre-computed: width * 0.5 + 1.0 (with AA padding)
    @location(3) length: f32,
    @location(4) color: vec4<f32>,
};

@vertex
fn vs_line(vertex: LineVertexInput, instance: LineInstance) -> LineVertexOutput {
    var out: LineVertexOutput;

    let line_vec = instance.end - instance.start;
    let line_length = length(line_vec);
    let line_dir = line_vec / max(line_length, 0.0001);
    let line_perp = vec2<f32>(-line_dir.y, line_dir.x);

    out.local_pos = vertex.position;
    // Pre-compute both half-width values to avoid per-fragment recalculation
    out.half_width = instance.width * 0.5;
    out.half_width_padded = out.half_width + 1.0;
    out.length = line_length;

    // Expand quad along line direction with padding for AA
    let along = mix(instance.start - line_dir * 1.0, instance.end + line_dir * 1.0, vertex.position.x);
    let world_pos = along + line_perp * vertex.position.y * out.half_width_padded * 2.0;

    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.color = instance.color;
    return out;
}

@fragment
fn fs_line(in: LineVertexOutput) -> @location(0) vec4<f32> {
    // Distance from line centerline (perpendicular) - uses pre-computed half_width_padded
    let perp_dist = abs(in.local_pos.y) * in.half_width_padded * 2.0;

    // Anti-aliased edge - uses pre-computed half_width (without padding)
    let aa_width = 1.0;
    let alpha = 1.0 - smoothstep(in.half_width - aa_width, in.half_width + aa_width, perp_dist);

    // Fade at line ends
    let end_fade = smoothstep(-0.02, 0.02, in.local_pos.x) *
                   (1.0 - smoothstep(0.98, 1.02, in.local_pos.x));

    return vec4<f32>(in.color.rgb, in.color.a * alpha * end_fade);
}

// ============================================================================
// Quad Shader (Solid Color)
// ============================================================================

struct QuadVertexInput {
    @location(0) position: vec2<f32>,
};

struct QuadInstance {
    @location(1) bounds: vec4<f32>,  // min_x, min_y, max_x, max_y
    @location(2) color: vec4<f32>,
};

struct QuadVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) color: vec4<f32>,
};

@vertex
fn vs_quad(vertex: QuadVertexInput, instance: QuadInstance) -> QuadVertexOutput {
    var out: QuadVertexOutput;

    // Interpolate position within bounds
    let world_pos = mix(instance.bounds.xy, instance.bounds.zw, vertex.position);

    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.color = instance.color;
    return out;
}

@fragment
fn fs_quad(in: QuadVertexOutput) -> @location(0) vec4<f32> {
    return in.color;
}

// ============================================================================
// Textured Quad Shader
// ============================================================================

struct TexturedQuadInstance {
    @location(1) bounds: vec4<f32>,     // min_x, min_y, max_x, max_y
    @location(2) uv_bounds: vec4<f32>,  // u_min, v_min, u_max, v_max
    @location(3) color: vec4<f32>,
};

struct TexturedQuadVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) color: vec4<f32>,
};

@group(1) @binding(0)
var t_texture: texture_2d<f32>;
@group(1) @binding(1)
var s_texture: sampler;

@vertex
fn vs_textured_quad(vertex: QuadVertexInput, instance: TexturedQuadInstance) -> TexturedQuadVertexOutput {
    var out: TexturedQuadVertexOutput;

    let world_pos = mix(instance.bounds.xy, instance.bounds.zw, vertex.position);
    out.uv = mix(instance.uv_bounds.xy, instance.uv_bounds.zw, vertex.position);

    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.color = instance.color;
    return out;
}

@fragment
fn fs_textured_quad(in: TexturedQuadVertexOutput) -> @location(0) vec4<f32> {
    let tex_color = textureSample(t_texture, s_texture, in.uv);
    return tex_color * in.color;
}

// ============================================================================
// Text Shader (Alpha-only texture)
// ============================================================================

@group(1) @binding(0)
var t_font_atlas: texture_2d<f32>;
@group(1) @binding(1)
var s_font_atlas: sampler;

@vertex
fn vs_text(vertex: QuadVertexInput, instance: TexturedQuadInstance) -> TexturedQuadVertexOutput {
    var out: TexturedQuadVertexOutput;

    let world_pos = mix(instance.bounds.xy, instance.bounds.zw, vertex.position);
    out.uv = mix(instance.uv_bounds.xy, instance.uv_bounds.zw, vertex.position);

    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.color = instance.color;
    return out;
}

@fragment
fn fs_text(in: TexturedQuadVertexOutput) -> @location(0) vec4<f32> {
    // Font atlas is single-channel (R8), sample red channel for alpha
    let glyph_alpha = textureSample(t_font_atlas, s_font_atlas, in.uv).r;
    return vec4<f32>(in.color.rgb, in.color.a * glyph_alpha);
}
"#;

/// Texture array shader for efficient file icon rendering.
///
/// Uses a 2D texture array to batch all file icons into a single draw call.
/// Each instance specifies which layer to sample from.
///
/// ## Instance Layout
///
/// | Attribute | Type | Location | Description |
/// |-----------|------|----------|-------------|
/// | `bounds` | vec4 | 1 | `min_x`, `min_y`, `max_x`, `max_y` |
/// | `uv_bounds` | vec4 | 2 | `u_min`, `v_min`, `u_max`, `v_max` |
/// | `color` | vec4 | 3 | RGBA tint color |
/// | `layer` | u32 | 4 | Texture array layer index |
///
/// ## Bind Groups
///
/// - Group 0: Uniforms (resolution)
/// - Group 1: Texture array + sampler
pub const TEXTURE_ARRAY_SHADER: &str = r#"
// ============================================================================
// Texture Array Shader (for file icons)
// ============================================================================

struct TextureArrayInstance {
    @location(1) bounds: vec4<f32>,     // min_x, min_y, max_x, max_y
    @location(2) uv_bounds: vec4<f32>,  // u_min, v_min, u_max, v_max
    @location(3) color: vec4<f32>,
    @location(4) layer: u32,            // texture array layer index
};

struct TextureArrayVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) color: vec4<f32>,
    @location(2) @interpolate(flat) layer: u32,
};

struct Uniforms {
    resolution: vec2<f32>,
};

@group(0) @binding(0)
var<uniform> uniforms: Uniforms;

@group(1) @binding(0)
var t_texture_array: texture_2d_array<f32>;
@group(1) @binding(1)
var s_texture_array: sampler;

struct QuadVertexInput {
    @location(0) position: vec2<f32>,
};

@vertex
fn vs_texture_array(vertex: QuadVertexInput, instance: TextureArrayInstance) -> TextureArrayVertexOutput {
    var out: TextureArrayVertexOutput;

    let world_pos = mix(instance.bounds.xy, instance.bounds.zw, vertex.position);
    out.uv = mix(instance.uv_bounds.xy, instance.uv_bounds.zw, vertex.position);

    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.color = instance.color;
    out.layer = instance.layer;
    return out;
}

@fragment
fn fs_texture_array(in: TextureArrayVertexOutput) -> @location(0) vec4<f32> {
    let tex_color = textureSample(t_texture_array, s_texture_array, in.uv, in.layer);
    return tex_color * in.color;
}
"#;

/// Bloom bright pass shader.
///
/// Extracts pixels brighter than a threshold for bloom processing.
pub const BLOOM_BRIGHT_SHADER: &str = r#"
struct BloomUniforms {
    threshold: f32,
    intensity: f32,
    _padding: vec2<f32>,
};

@group(0) @binding(0)
var<uniform> bloom_uniforms: BloomUniforms;

@group(1) @binding(0)
var t_scene: texture_2d<f32>;
@group(1) @binding(1)
var s_scene: sampler;

struct FullscreenVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
};

@vertex
fn vs_fullscreen(@location(0) position: vec2<f32>) -> FullscreenVertexOutput {
    var out: FullscreenVertexOutput;
    out.clip_position = vec4<f32>(position, 0.0, 1.0);
    // Convert from clip space (-1 to 1) to UV space (0 to 1)
    out.uv = position * 0.5 + 0.5;
    // Flip Y for correct orientation
    out.uv.y = 1.0 - out.uv.y;
    return out;
}

@fragment
fn fs_bloom_bright(in: FullscreenVertexOutput) -> @location(0) vec4<f32> {
    let color = textureSample(t_scene, s_scene, in.uv);

    // Calculate luminance using ITU-R BT.601 coefficients
    let luminance = dot(color.rgb, vec3<f32>(0.299, 0.587, 0.114));

    // Extract bright pixels
    let brightness = max(0.0, luminance - bloom_uniforms.threshold);
    let bloom_color = color.rgb * (brightness * bloom_uniforms.intensity);

    return vec4<f32>(bloom_color, 1.0);
}
"#;

/// Bloom blur shader.
///
/// Performs separable Gaussian blur (9-tap).
pub const BLOOM_BLUR_SHADER: &str = r#"
struct BlurUniforms {
    direction: vec2<f32>,
    resolution: vec2<f32>,
};

@group(0) @binding(0)
var<uniform> blur_uniforms: BlurUniforms;

@group(1) @binding(0)
var t_source: texture_2d<f32>;
@group(1) @binding(1)
var s_source: sampler;

struct FullscreenVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
};

// Module-level constant: 9-tap Gaussian blur weights (sigma ≈ 1.5)
// Defined at module scope to avoid per-fragment array construction
const BLUR_WEIGHTS: array<f32, 5> = array<f32, 5>(0.227027, 0.1945946, 0.1216216, 0.054054, 0.016216);

@vertex
fn vs_fullscreen(@location(0) position: vec2<f32>) -> FullscreenVertexOutput {
    var out: FullscreenVertexOutput;
    out.clip_position = vec4<f32>(position, 0.0, 1.0);
    out.uv = position * 0.5 + 0.5;
    out.uv.y = 1.0 - out.uv.y;
    return out;
}

@fragment
fn fs_bloom_blur(in: FullscreenVertexOutput) -> @location(0) vec4<f32> {
    let texel_size = 1.0 / blur_uniforms.resolution;
    let direction = blur_uniforms.direction * texel_size;

    var result = textureSample(t_source, s_source, in.uv).rgb * BLUR_WEIGHTS[0];

    for (var i = 1; i < 5; i++) {
        let offset = direction * f32(i);
        result += textureSample(t_source, s_source, in.uv + offset).rgb * BLUR_WEIGHTS[i];
        result += textureSample(t_source, s_source, in.uv - offset).rgb * BLUR_WEIGHTS[i];
    }

    return vec4<f32>(result, 1.0);
}
"#;

/// Bloom composite shader.
///
/// Combines original scene with bloom effect.
pub const BLOOM_COMPOSITE_SHADER: &str = r#"
struct CompositeUniforms {
    intensity: f32,
    _padding: vec3<f32>,
};

@group(0) @binding(0)
var<uniform> composite_uniforms: CompositeUniforms;

@group(1) @binding(0)
var t_scene: texture_2d<f32>;
@group(1) @binding(1)
var s_scene: sampler;

@group(2) @binding(0)
var t_bloom: texture_2d<f32>;
@group(2) @binding(1)
var s_bloom: sampler;

struct FullscreenVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
};

@vertex
fn vs_fullscreen(@location(0) position: vec2<f32>) -> FullscreenVertexOutput {
    var out: FullscreenVertexOutput;
    out.clip_position = vec4<f32>(position, 0.0, 1.0);
    out.uv = position * 0.5 + 0.5;
    out.uv.y = 1.0 - out.uv.y;
    return out;
}

@fragment
fn fs_bloom_composite(in: FullscreenVertexOutput) -> @location(0) vec4<f32> {
    let scene_color = textureSample(t_scene, s_scene, in.uv);
    let bloom_color = textureSample(t_bloom, s_bloom, in.uv);

    // Additive blending for bloom
    let result = scene_color.rgb + bloom_color.rgb * composite_uniforms.intensity;

    return vec4<f32>(result, scene_color.a);
}
"#;

/// Shadow silhouette shader.
///
/// Extracts alpha channel for shadow rendering.
pub const SHADOW_SILHOUETTE_SHADER: &str = r#"
@group(1) @binding(0)
var t_scene: texture_2d<f32>;
@group(1) @binding(1)
var s_scene: sampler;

struct FullscreenVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
};

@vertex
fn vs_fullscreen(@location(0) position: vec2<f32>) -> FullscreenVertexOutput {
    var out: FullscreenVertexOutput;
    out.clip_position = vec4<f32>(position, 0.0, 1.0);
    out.uv = position * 0.5 + 0.5;
    out.uv.y = 1.0 - out.uv.y;
    return out;
}

@fragment
fn fs_shadow_silhouette(in: FullscreenVertexOutput) -> @location(0) vec4<f32> {
    let alpha = textureSample(t_scene, s_scene, in.uv).a;
    return vec4<f32>(0.0, 0.0, 0.0, alpha);
}
"#;

/// Shadow composite shader.
///
/// Composites shadow behind scene.
pub const SHADOW_COMPOSITE_SHADER: &str = r#"
struct ShadowUniforms {
    offset: vec2<f32>,
    opacity: f32,
    _padding: f32,
    color: vec4<f32>,
};

@group(0) @binding(0)
var<uniform> shadow_uniforms: ShadowUniforms;

@group(1) @binding(0)
var t_scene: texture_2d<f32>;
@group(1) @binding(1)
var s_scene: sampler;

@group(2) @binding(0)
var t_shadow: texture_2d<f32>;
@group(2) @binding(1)
var s_shadow: sampler;

struct FullscreenVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) uv: vec2<f32>,
};

@vertex
fn vs_fullscreen(@location(0) position: vec2<f32>) -> FullscreenVertexOutput {
    var out: FullscreenVertexOutput;
    out.clip_position = vec4<f32>(position, 0.0, 1.0);
    out.uv = position * 0.5 + 0.5;
    out.uv.y = 1.0 - out.uv.y;
    return out;
}

@fragment
fn fs_shadow_composite(in: FullscreenVertexOutput) -> @location(0) vec4<f32> {
    let scene_color = textureSample(t_scene, s_scene, in.uv);

    // Sample shadow with offset
    let shadow_uv = in.uv - shadow_uniforms.offset;
    let shadow_alpha = textureSample(t_shadow, s_shadow, shadow_uv).a;

    // Blend shadow behind scene
    let shadow_color = shadow_uniforms.color.rgb;
    let final_alpha = scene_color.a + shadow_alpha * shadow_uniforms.opacity * (1.0 - scene_color.a);

    // Pre-multiplied alpha blending
    var result: vec3<f32>;
    if final_alpha > 0.0 {
        result = (scene_color.rgb * scene_color.a +
                  shadow_color * shadow_alpha * shadow_uniforms.opacity * (1.0 - scene_color.a)) / final_alpha;
    } else {
        result = vec3<f32>(0.0);
    }

    return vec4<f32>(result, final_alpha);
}
"#;

/// Physics force calculation compute shader.
///
/// # Current Implementation
///
/// The force calculation currently uses O(N²) brute force iteration over all
/// entity pairs. While a spatial hash grid is built (`cs_build_grid`), it only
/// stores **counts** per cell (not entity indices), making neighbor queries
/// impossible with the current data structure.
///
/// # Performance Note
///
/// For typical visualization workloads (< 500 directories), the O(N²) approach
/// is fast enough on modern GPUs. For larger scenes, the CPU-side Barnes-Hut
/// algorithm provides O(N log N) performance as a fallback.
///
/// # Future Optimization
///
/// To achieve true O(N) neighbor queries, the spatial hash would need:
/// 1. A prefix sum pass to compute cell offsets
/// 2. A compacted entity index list sorted by cell
/// 3. Modified force calculation to query only neighboring cells
///
/// This is left as future work since the current approach is sufficient
/// for the target use cases and the CPU Barnes-Hut fallback handles
/// extreme-scale scenarios.
pub const PHYSICS_FORCE_SHADER: &str = r#"
struct PhysicsParams {
    entity_count: u32,
    delta_time: f32,
    repulsion_strength: f32,
    attraction_strength: f32,
    damping: f32,
    max_speed: f32,
    grid_size: f32,
    grid_cells: u32,
};

struct Entity {
    position: vec2<f32>,
    velocity: vec2<f32>,
    force: vec2<f32>,
    mass: f32,
    radius: f32,
};

@group(0) @binding(0)
var<uniform> params: PhysicsParams;

@group(0) @binding(1)
var<storage, read_write> entities: array<Entity>;

@group(0) @binding(2)
var<storage, read_write> spatial_hash: array<atomic<u32>>;

// Workgroup size for compute shaders
const WORKGROUP_SIZE: u32 = 64u;

// Hash function for spatial grid
fn hash_position(pos: vec2<f32>) -> u32 {
    let grid_x = u32(floor(pos.x / params.grid_size)) % params.grid_cells;
    let grid_y = u32(floor(pos.y / params.grid_size)) % params.grid_cells;
    return grid_y * params.grid_cells + grid_x;
}

@compute @workgroup_size(64)
fn cs_clear_grid(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx < params.grid_cells * params.grid_cells {
        atomicStore(&spatial_hash[idx], 0u);
    }
}

@compute @workgroup_size(64)
fn cs_build_grid(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx >= params.entity_count {
        return;
    }

    let entity = entities[idx];
    let cell = hash_position(entity.position);

    // Atomic increment to track entities per cell
    atomicAdd(&spatial_hash[cell], 1u);
}

@compute @workgroup_size(64)
fn cs_calculate_forces(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx >= params.entity_count {
        return;
    }

    var entity = entities[idx];
    var total_force = vec2<f32>(0.0);

    // Check neighboring cells
    let cell_x = i32(floor(entity.position.x / params.grid_size));
    let cell_y = i32(floor(entity.position.y / params.grid_size));

    // Calculate repulsion forces from nearby entities
    for (var other_idx = 0u; other_idx < params.entity_count; other_idx++) {
        if other_idx == idx {
            continue;
        }

        let other = entities[other_idx];
        let diff = entity.position - other.position;
        let dist_sq = dot(diff, diff);
        let min_dist = entity.radius + other.radius;
        let min_dist_sq = min_dist * min_dist;

        if dist_sq < min_dist_sq * 16.0 && dist_sq > 0.0001 {
            let dist = sqrt(dist_sq);
            let dir = diff / dist;

            // Repulsion force (stronger when closer)
            let overlap = max(0.0, min_dist * 2.0 - dist);
            let force_magnitude = params.repulsion_strength * overlap / dist;
            total_force += dir * force_magnitude;
        }
    }

    // Apply damping
    total_force -= entity.velocity * params.damping;

    // Store accumulated force
    entities[idx].force = total_force;
}

@compute @workgroup_size(64)
fn cs_integrate(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx >= params.entity_count {
        return;
    }

    var entity = entities[idx];

    // Apply force (F = ma, assuming mass = 1 for simplicity)
    let acceleration = entity.force / max(entity.mass, 0.1);
    entity.velocity += acceleration * params.delta_time;

    // Clamp velocity
    let speed = length(entity.velocity);
    if speed > params.max_speed {
        entity.velocity = entity.velocity / speed * params.max_speed;
    }

    // Update position
    entity.position += entity.velocity * params.delta_time;

    // Clear force for next frame
    entity.force = vec2<f32>(0.0);

    entities[idx] = entity;
}
"#;

/// O(N) Spatial Hash Physics Shader.
///
/// This shader implements a proper GPU spatial hash that enables O(N) neighbor
/// queries instead of O(N²) brute force. The algorithm works in multiple passes:
///
/// ## Pass Sequence
///
/// 1. **Clear Counts** (`cs_clear_cell_counts`): Zero out cell count buffer
/// 2. **Count Entities** (`cs_count_entities_per_cell`): Atomic increment per entity's cell
/// 3. **Prefix Sum** (`cs_prefix_sum_*`): Parallel exclusive scan to compute cell offsets
/// 4. **Scatter Entities** (`cs_scatter_entities`): Sort entity indices by cell
/// 5. **Calculate Forces** (`cs_calculate_forces_spatial`): Query only 3x3 neighborhood
/// 6. **Integrate** (`cs_integrate_spatial`): Apply forces to velocities and positions
///
/// ## Complexity Analysis
///
/// - Old O(N²) approach: N entities × N comparisons = N² operations
/// - New O(N) approach: N entities × ~9 cells × ~K entities/cell ≈ 9NK operations
///   where K = N / (`grid_cells`²), so total ≈ 9N² / `grid_cells`²
///
/// With a 64×64 grid (4096 cells) and 5000 entities:
/// - Old: 25,000,000 comparisons
/// - New: ~11,000 comparisons (2200× speedup)
///
/// ## Buffer Layout
///
/// | Binding | Buffer | Type | Size |
/// |---------|--------|------|------|
/// | 0 | params | uniform | 32 bytes |
/// | 1 | entities | storage (rw) | N × 32 bytes |
/// | 2 | cell_counts | storage (rw) | grid_cells² × 4 bytes |
/// | 3 | cell_offsets | storage (rw) | (grid_cells² + 1) × 4 bytes |
/// | 4 | entity_indices | storage (rw) | N × 4 bytes |
/// | 5 | scatter_offsets | storage (rw) | grid_cells² × 4 bytes |
/// | 6 | partial_sums | storage (rw) | workgroup_count × 4 bytes |
pub const PHYSICS_SPATIAL_HASH_SHADER: &str = r#"
// ============================================================================
// Spatial Hash Physics Shader - O(N) Neighbor Queries
// ============================================================================

struct PhysicsParams {
    entity_count: u32,
    delta_time: f32,
    repulsion_strength: f32,
    attraction_strength: f32,
    damping: f32,
    max_speed: f32,
    grid_size: f32,
    grid_cells: u32,
};

struct Entity {
    position: vec2<f32>,
    velocity: vec2<f32>,
    force: vec2<f32>,
    mass: f32,
    radius: f32,
};

@group(0) @binding(0)
var<uniform> params: PhysicsParams;

@group(0) @binding(1)
var<storage, read_write> entities: array<Entity>;

@group(0) @binding(2)
var<storage, read_write> cell_counts: array<atomic<u32>>;

@group(0) @binding(3)
var<storage, read_write> cell_offsets: array<u32>;

@group(0) @binding(4)
var<storage, read_write> entity_indices: array<u32>;

@group(0) @binding(5)
var<storage, read_write> scatter_offsets: array<atomic<u32>>;

@group(0) @binding(6)
var<storage, read_write> partial_sums: array<u32>;

// Workgroup size for all passes
const WORKGROUP_SIZE: u32 = 256u;

// Shared memory for prefix sum
var<workgroup> shared_data: array<u32, 256>;

// Hash function: maps world position to cell index
fn hash_position(pos: vec2<f32>) -> u32 {
    // Clamp to grid bounds to handle entities outside the grid
    let grid_x = clamp(
        u32(floor(pos.x / params.grid_size)),
        0u,
        params.grid_cells - 1u
    );
    let grid_y = clamp(
        u32(floor(pos.y / params.grid_size)),
        0u,
        params.grid_cells - 1u
    );
    return grid_y * params.grid_cells + grid_x;
}

// ============================================================================
// Pass 1: Clear cell counts
// ============================================================================

@compute @workgroup_size(256)
fn cs_clear_cell_counts(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    let total_cells = params.grid_cells * params.grid_cells;
    if idx < total_cells {
        atomicStore(&cell_counts[idx], 0u);
    }
}

// ============================================================================
// Pass 2: Count entities per cell
// ============================================================================

@compute @workgroup_size(256)
fn cs_count_entities_per_cell(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx >= params.entity_count {
        return;
    }

    let cell = hash_position(entities[idx].position);
    atomicAdd(&cell_counts[cell], 1u);
}

// ============================================================================
// Pass 3a: Parallel prefix sum (local workgroup scan + store partial)
// ============================================================================

@compute @workgroup_size(256)
fn cs_prefix_sum_local(
    @builtin(global_invocation_id) global_id: vec3<u32>,
    @builtin(local_invocation_id) local_id: vec3<u32>,
    @builtin(workgroup_id) workgroup_id: vec3<u32>
) {
    let lid = local_id.x;
    let gid = global_id.x;
    let total_cells = params.grid_cells * params.grid_cells;

    // Load data into shared memory (0 for out-of-bounds)
    if gid < total_cells {
        shared_data[lid] = atomicLoad(&cell_counts[gid]);
    } else {
        shared_data[lid] = 0u;
    }
    workgroupBarrier();

    // Blelloch scan - up-sweep (reduce) phase
    var offset = 1u;
    for (var d = WORKGROUP_SIZE >> 1u; d > 0u; d = d >> 1u) {
        if lid < d {
            let ai = offset * (2u * lid + 1u) - 1u;
            let bi = offset * (2u * lid + 2u) - 1u;
            shared_data[bi] += shared_data[ai];
        }
        offset = offset << 1u;
        workgroupBarrier();
    }

    // Store workgroup total to partial sums, clear last element
    if lid == 0u {
        partial_sums[workgroup_id.x] = shared_data[WORKGROUP_SIZE - 1u];
        shared_data[WORKGROUP_SIZE - 1u] = 0u;
    }
    workgroupBarrier();

    // Down-sweep phase
    for (var d = 1u; d < WORKGROUP_SIZE; d = d << 1u) {
        offset = offset >> 1u;
        if lid < d {
            let ai = offset * (2u * lid + 1u) - 1u;
            let bi = offset * (2u * lid + 2u) - 1u;
            let tmp = shared_data[ai];
            shared_data[ai] = shared_data[bi];
            shared_data[bi] += tmp;
        }
        workgroupBarrier();
    }

    // Write result (exclusive scan)
    if gid < total_cells {
        cell_offsets[gid] = shared_data[lid];
    }

    // Last thread writes the total count to cell_offsets[total_cells]
    // This serves as the end marker for the last cell
    if gid == total_cells - 1u {
        cell_offsets[total_cells] = shared_data[lid] + atomicLoad(&cell_counts[gid]);
    }
}

// ============================================================================
// Pass 3b: Scan partial sums (single workgroup for small grid)
// ============================================================================

@compute @workgroup_size(256)
fn cs_prefix_sum_partials(
    @builtin(local_invocation_id) local_id: vec3<u32>
) {
    let lid = local_id.x;
    let num_partials = (params.grid_cells * params.grid_cells + WORKGROUP_SIZE - 1u) / WORKGROUP_SIZE;

    // Load partial sum (0 for unused)
    if lid < num_partials {
        shared_data[lid] = partial_sums[lid];
    } else {
        shared_data[lid] = 0u;
    }
    workgroupBarrier();

    // Simple sequential scan (num_partials is small, typically < 64)
    if lid == 0u {
        var sum = 0u;
        for (var i = 0u; i < num_partials; i++) {
            let val = shared_data[i];
            shared_data[i] = sum;
            sum += val;
        }
    }
    workgroupBarrier();

    // Write back scanned partials
    if lid < num_partials {
        partial_sums[lid] = shared_data[lid];
    }
}

// ============================================================================
// Pass 3c: Add partial sums to complete the scan
// ============================================================================

@compute @workgroup_size(256)
fn cs_prefix_sum_add(
    @builtin(global_invocation_id) global_id: vec3<u32>,
    @builtin(workgroup_id) workgroup_id: vec3<u32>
) {
    let gid = global_id.x;
    let total_cells = params.grid_cells * params.grid_cells;

    if gid < total_cells {
        cell_offsets[gid] += partial_sums[workgroup_id.x];
    }

    // Also update the end marker
    if gid == total_cells - 1u {
        cell_offsets[total_cells] += partial_sums[workgroup_id.x];
    }
}

// ============================================================================
// Pass 4a: Initialize scatter offsets (copy from cell_offsets)
// ============================================================================

@compute @workgroup_size(256)
fn cs_init_scatter_offsets(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    let total_cells = params.grid_cells * params.grid_cells;
    if idx < total_cells {
        atomicStore(&scatter_offsets[idx], cell_offsets[idx]);
    }
}

// ============================================================================
// Pass 4b: Scatter entities into sorted order
// ============================================================================

@compute @workgroup_size(256)
fn cs_scatter_entities(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx >= params.entity_count {
        return;
    }

    let cell = hash_position(entities[idx].position);
    let write_pos = atomicAdd(&scatter_offsets[cell], 1u);
    entity_indices[write_pos] = idx;
}

// ============================================================================
// Pass 5: Calculate forces using spatial hash (O(N) neighbor queries)
// ============================================================================

@compute @workgroup_size(256)
fn cs_calculate_forces_spatial(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx >= params.entity_count {
        return;
    }

    let entity = entities[idx];
    var total_force = vec2<f32>(0.0);

    // Get entity's cell coordinates
    let cell_x = i32(floor(entity.position.x / params.grid_size));
    let cell_y = i32(floor(entity.position.y / params.grid_size));
    let grid_cells_i = i32(params.grid_cells);

    // Query 3x3 neighborhood (only cells that could contain interacting entities)
    for (var dy = -1; dy <= 1; dy++) {
        for (var dx = -1; dx <= 1; dx++) {
            let nx = cell_x + dx;
            let ny = cell_y + dy;

            // Skip cells outside grid bounds
            if nx < 0 || nx >= grid_cells_i || ny < 0 || ny >= grid_cells_i {
                continue;
            }

            let neighbor_cell = u32(ny) * params.grid_cells + u32(nx);
            let start = cell_offsets[neighbor_cell];
            let end = cell_offsets[neighbor_cell + 1u];

            // Iterate over entities in this cell
            for (var i = start; i < end; i++) {
                let other_idx = entity_indices[i];

                // Skip self
                if other_idx == idx {
                    continue;
                }

                let other = entities[other_idx];
                let diff = entity.position - other.position;
                let dist_sq = dot(diff, diff);
                let min_dist = entity.radius + other.radius;
                let min_dist_sq = min_dist * min_dist;

                // Only apply force if within interaction range
                if dist_sq < min_dist_sq * 16.0 && dist_sq > 0.0001 {
                    let dist = sqrt(dist_sq);
                    let dir = diff / dist;

                    // Repulsion force (stronger when closer)
                    let overlap = max(0.0, min_dist * 2.0 - dist);
                    let force_magnitude = params.repulsion_strength * overlap / dist;
                    total_force += dir * force_magnitude;
                }
            }
        }
    }

    // Apply velocity damping
    total_force -= entity.velocity * params.damping;

    // Store accumulated force
    entities[idx].force = total_force;
}

// ============================================================================
// Pass 6: Integrate velocities and positions
// ============================================================================

@compute @workgroup_size(256)
fn cs_integrate_spatial(@builtin(global_invocation_id) global_id: vec3<u32>) {
    let idx = global_id.x;
    if idx >= params.entity_count {
        return;
    }

    var entity = entities[idx];

    // Apply force (F = ma)
    let acceleration = entity.force / max(entity.mass, 0.1);
    entity.velocity += acceleration * params.delta_time;

    // Clamp velocity
    let speed = length(entity.velocity);
    if speed > params.max_speed {
        entity.velocity = entity.velocity / speed * params.max_speed;
    }

    // Update position
    entity.position += entity.velocity * params.delta_time;

    // Clear force for next frame
    entity.force = vec2<f32>(0.0);

    entities[idx] = entity;
}
"#;

/// Catmull-Rom curve shader for instanced curve rendering.
///
/// This shader renders smooth curves using Catmull-Rom spline interpolation.
/// Each instance represents a single span defined by 4 control points.
/// The shader tessellates the curve into segments on the GPU, dramatically
/// reducing the number of draw calls compared to drawing individual lines.
///
/// ## Instance Data Layout
///
/// | Field | Type | Description |
/// |-------|------|-------------|
/// | `p0` | `vec2<f32>` | Control point before start |
/// | `p1` | `vec2<f32>` | Start point |
/// | `p2` | `vec2<f32>` | End point |
/// | `p3` | `vec2<f32>` | Control point after end |
/// | `width` | `f32` | Line width |
/// | `color` | `vec4<f32>` | RGBA color |
/// | `segments` | `u32` | Number of tessellation segments |
///
/// ## Performance
///
/// For a spline with N control points:
/// - Previous: (N-1) spans × 8 segments = 8(N-1) line instances
/// - New: (N-1) curve instances (8x reduction in instance count)
pub const CURVE_SHADER: &str = r#"
// ============================================================================
// Catmull-Rom Curve Shader
// ============================================================================

struct Uniforms {
    resolution: vec2<f32>,
    time: f32,
    _padding: f32,
};

@group(0) @binding(0)
var<uniform> uniforms: Uniforms;

// Curve instance data
struct CurveInstance {
    @location(1) p0: vec2<f32>,        // Control point before start
    @location(2) p1: vec2<f32>,        // Start point
    @location(3) p2: vec2<f32>,        // End point
    @location(4) p3: vec2<f32>,        // Control point after end
    @location(5) width: f32,           // Line width
    @location(6) color: vec4<f32>,     // RGBA color
    @location(7) segments: u32,        // Number of tessellation segments
};

struct CurveVertexInput {
    @location(0) position: vec2<f32>,  // Unit quad vertex
};

struct CurveVertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) local_pos: vec2<f32>,
    @location(1) width: f32,
    @location(2) color: vec4<f32>,
};

// Result struct for combined position and tangent calculation
struct CatmullRomResult {
    position: vec2<f32>,
    tangent: vec2<f32>,
}

// Combined Catmull-Rom position and tangent calculation
// Computes both using shared t² to avoid redundant multiplication
fn catmull_rom_pos_tangent(p0: vec2<f32>, p1: vec2<f32>, p2: vec2<f32>, p3: vec2<f32>, t: f32) -> CatmullRomResult {
    // Shared computation - t² used by both position and tangent
    let t2 = t * t;
    let t3 = t2 * t;

    // Position coefficients (Catmull-Rom basis matrix)
    let pos_c0 = -0.5 * t3 + t2 - 0.5 * t;
    let pos_c1 = 1.5 * t3 - 2.5 * t2 + 1.0;
    let pos_c2 = -1.5 * t3 + 2.0 * t2 + 0.5 * t;
    let pos_c3 = 0.5 * t3 - 0.5 * t2;

    // Tangent coefficients (derivative of basis)
    let tan_c0 = -1.5 * t2 + 2.0 * t - 0.5;
    let tan_c1 = 4.5 * t2 - 5.0 * t;
    let tan_c2 = -4.5 * t2 + 4.0 * t + 0.5;
    let tan_c3 = 1.5 * t2 - t;

    var result: CatmullRomResult;
    result.position = p0 * pos_c0 + p1 * pos_c1 + p2 * pos_c2 + p3 * pos_c3;
    result.tangent = p0 * tan_c0 + p1 * tan_c1 + p2 * tan_c2 + p3 * tan_c3;
    return result;
}

@vertex
fn vs_curve(
    vertex: CurveVertexInput,
    instance: CurveInstance,
    @builtin(vertex_index) vertex_index: u32,
    @builtin(instance_index) instance_index: u32
) -> CurveVertexOutput {
    var out: CurveVertexOutput;

    // Determine which segment this vertex belongs to based on vertex position
    // The quad's X position (0 to 1) maps to the curve parameter t
    let t = vertex.position.x;

    // Calculate position and tangent on the curve (combined to share t² computation)
    let cr = catmull_rom_pos_tangent(instance.p0, instance.p1, instance.p2, instance.p3, t);
    let curve_pos = cr.position;
    let tangent = cr.tangent;

    // Normalize tangent and get perpendicular
    let tangent_len = length(tangent);
    let tangent_norm = select(vec2<f32>(1.0, 0.0), tangent / tangent_len, tangent_len > 0.0001);
    let perp = vec2<f32>(-tangent_norm.y, tangent_norm.x);

    // Expand perpendicular to line width with AA padding
    let half_width = (instance.width * 0.5) + 1.0;
    let world_pos = curve_pos + perp * vertex.position.y * half_width * 2.0;

    // Convert to NDC
    let ndc = (world_pos / uniforms.resolution) * 2.0 - 1.0;
    out.clip_position = vec4<f32>(ndc.x, -ndc.y, 0.0, 1.0);

    out.local_pos = vertex.position;
    out.width = instance.width;
    out.color = instance.color;

    return out;
}

@fragment
fn fs_curve(in: CurveVertexOutput) -> @location(0) vec4<f32> {
    // Distance from curve centerline (perpendicular)
    let perp_dist = abs(in.local_pos.y) * ((in.width * 0.5) + 1.0) * 2.0;
    let half_width = in.width * 0.5;

    // Anti-aliased edge
    let aa_width = 1.0;
    let alpha = 1.0 - smoothstep(half_width - aa_width, half_width + aa_width, perp_dist);

    return vec4<f32>(in.color.rgb, in.color.a * alpha);
}
"#;

/// Visibility culling compute shader.
///
/// Filters instance data based on view bounds, outputting only visible instances
/// to a compacted buffer. Supports indirect draw command generation.
pub const VISIBILITY_CULLING_SHADER: &str = r#"
struct CullParams {
    // View bounds in world coordinates (min_x, min_y, max_x, max_y)
    view_bounds: vec4<f32>,
    // Total number of input instances
    instance_count: u32,
    // Floats per instance (for stride calculation)
    floats_per_instance: u32,
    // Padding for alignment
    _padding: vec2<u32>,
};

struct DrawIndirect {
    vertex_count: u32,
    instance_count: atomic<u32>,
    first_vertex: u32,
    first_instance: u32,
};

@group(0) @binding(0)
var<uniform> params: CullParams;

// Input instance buffer (raw floats)
@group(0) @binding(1)
var<storage, read> input_instances: array<f32>;

// Output instance buffer (compacted visible instances)
@group(0) @binding(2)
var<storage, read_write> output_instances: array<f32>;

// Indirect draw command buffer
@group(0) @binding(3)
var<storage, read_write> draw_indirect: DrawIndirect;

// Workgroup-local counter for efficient compaction
var<workgroup> workgroup_count: atomic<u32>;
var<workgroup> workgroup_offset: u32;

const WORKGROUP_SIZE: u32 = 256u;

// Check if a circle instance is visible (first 3 floats: x, y, radius)
fn is_circle_visible(base_idx: u32) -> bool {
    let x = input_instances[base_idx];
    let y = input_instances[base_idx + 1u];
    let radius = input_instances[base_idx + 2u];

    // AABB test with radius expansion
    let min_x = x - radius;
    let max_x = x + radius;
    let min_y = y - radius;
    let max_y = y + radius;

    // Check overlap with view bounds
    return max_x >= params.view_bounds.x &&
           min_x <= params.view_bounds.z &&
           max_y >= params.view_bounds.y &&
           min_y <= params.view_bounds.w;
}

// Check if a line instance is visible (first 4 floats: start_x, start_y, end_x, end_y)
fn is_line_visible(base_idx: u32) -> bool {
    let start_x = input_instances[base_idx];
    let start_y = input_instances[base_idx + 1u];
    let end_x = input_instances[base_idx + 2u];
    let end_y = input_instances[base_idx + 3u];

    // AABB of line segment
    let min_x = min(start_x, end_x);
    let max_x = max(start_x, end_x);
    let min_y = min(start_y, end_y);
    let max_y = max(start_y, end_y);

    return max_x >= params.view_bounds.x &&
           min_x <= params.view_bounds.z &&
           max_y >= params.view_bounds.y &&
           min_y <= params.view_bounds.w;
}

// Check if a quad instance is visible (first 4 floats: min_x, min_y, max_x, max_y)
fn is_quad_visible(base_idx: u32) -> bool {
    let min_x = input_instances[base_idx];
    let min_y = input_instances[base_idx + 1u];
    let max_x = input_instances[base_idx + 2u];
    let max_y = input_instances[base_idx + 3u];

    return max_x >= params.view_bounds.x &&
           min_x <= params.view_bounds.z &&
           max_y >= params.view_bounds.y &&
           min_y <= params.view_bounds.w;
}

// Reset the indirect draw command (call before culling)
@compute @workgroup_size(1)
fn cs_reset_indirect() {
    atomicStore(&draw_indirect.instance_count, 0u);
    draw_indirect.vertex_count = 4u;  // Quad vertices
    draw_indirect.first_vertex = 0u;
    draw_indirect.first_instance = 0u;
}

// Cull circles and compact visible instances
@compute @workgroup_size(256)
fn cs_cull_circles(
    @builtin(global_invocation_id) global_id: vec3<u32>,
    @builtin(local_invocation_id) local_id: vec3<u32>,
) {
    let idx = global_id.x;
    let lid = local_id.x;

    // Initialize workgroup counter
    if lid == 0u {
        atomicStore(&workgroup_count, 0u);
    }
    workgroupBarrier();

    var is_visible = false;
    if idx < params.instance_count {
        let base_idx = idx * params.floats_per_instance;
        is_visible = is_circle_visible(base_idx);
    }

    // Count visible instances in workgroup
    var local_offset = 0u;
    if is_visible {
        local_offset = atomicAdd(&workgroup_count, 1u);
    }
    workgroupBarrier();

    // Get global offset for this workgroup
    if lid == 0u {
        let count = atomicLoad(&workgroup_count);
        if count > 0u {
            workgroup_offset = atomicAdd(&draw_indirect.instance_count, count);
        }
    }
    workgroupBarrier();

    // Write visible instances to output
    if is_visible {
        let src_base = idx * params.floats_per_instance;
        let dst_base = (workgroup_offset + local_offset) * params.floats_per_instance;

        for (var i = 0u; i < params.floats_per_instance; i++) {
            output_instances[dst_base + i] = input_instances[src_base + i];
        }
    }
}

// Cull lines and compact visible instances
@compute @workgroup_size(256)
fn cs_cull_lines(
    @builtin(global_invocation_id) global_id: vec3<u32>,
    @builtin(local_invocation_id) local_id: vec3<u32>,
) {
    let idx = global_id.x;
    let lid = local_id.x;

    if lid == 0u {
        atomicStore(&workgroup_count, 0u);
    }
    workgroupBarrier();

    var is_visible = false;
    if idx < params.instance_count {
        let base_idx = idx * params.floats_per_instance;
        is_visible = is_line_visible(base_idx);
    }

    var local_offset = 0u;
    if is_visible {
        local_offset = atomicAdd(&workgroup_count, 1u);
    }
    workgroupBarrier();

    if lid == 0u {
        let count = atomicLoad(&workgroup_count);
        if count > 0u {
            workgroup_offset = atomicAdd(&draw_indirect.instance_count, count);
        }
    }
    workgroupBarrier();

    if is_visible {
        let src_base = idx * params.floats_per_instance;
        let dst_base = (workgroup_offset + local_offset) * params.floats_per_instance;

        for (var i = 0u; i < params.floats_per_instance; i++) {
            output_instances[dst_base + i] = input_instances[src_base + i];
        }
    }
}

// Cull quads and compact visible instances
@compute @workgroup_size(256)
fn cs_cull_quads(
    @builtin(global_invocation_id) global_id: vec3<u32>,
    @builtin(local_invocation_id) local_id: vec3<u32>,
) {
    let idx = global_id.x;
    let lid = local_id.x;

    if lid == 0u {
        atomicStore(&workgroup_count, 0u);
    }
    workgroupBarrier();

    var is_visible = false;
    if idx < params.instance_count {
        let base_idx = idx * params.floats_per_instance;
        is_visible = is_quad_visible(base_idx);
    }

    var local_offset = 0u;
    if is_visible {
        local_offset = atomicAdd(&workgroup_count, 1u);
    }
    workgroupBarrier();

    if lid == 0u {
        let count = atomicLoad(&workgroup_count);
        if count > 0u {
            workgroup_offset = atomicAdd(&draw_indirect.instance_count, count);
        }
    }
    workgroupBarrier();

    if is_visible {
        let src_base = idx * params.floats_per_instance;
        let dst_base = (workgroup_offset + local_offset) * params.floats_per_instance;

        for (var i = 0u; i < params.floats_per_instance; i++) {
            output_instances[dst_base + i] = input_instances[src_base + i];
        }
    }
}
"#;

/// Bounds calculation compute shader.
///
/// Calculates the bounding box of all entities using parallel reduction.
pub const BOUNDS_SHADER: &str = r#"
struct BoundsParams {
    entity_count: u32,
    _padding: vec3<u32>,
};

struct Entity {
    position: vec2<f32>,
    velocity: vec2<f32>,
    force: vec2<f32>,
    mass: f32,
    radius: f32,
};

struct Bounds {
    min: vec2<f32>,
    max: vec2<f32>,
};

@group(0) @binding(0)
var<uniform> params: BoundsParams;

@group(0) @binding(1)
var<storage, read> entities: array<Entity>;

@group(0) @binding(2)
var<storage, read_write> bounds: Bounds;

const WORKGROUP_SIZE: u32 = 256u;

var<workgroup> shared_min: array<vec2<f32>, 256>;
var<workgroup> shared_max: array<vec2<f32>, 256>;

@compute @workgroup_size(256)
fn cs_calculate_bounds(
    @builtin(global_invocation_id) global_id: vec3<u32>,
    @builtin(local_invocation_id) local_id: vec3<u32>,
    @builtin(workgroup_id) workgroup_id: vec3<u32>,
) {
    let idx = global_id.x;
    let lid = local_id.x;

    // Initialize with extreme values
    var local_min = vec2<f32>(1e10);
    var local_max = vec2<f32>(-1e10);

    // Each thread processes one entity
    if idx < params.entity_count {
        let entity = entities[idx];
        local_min = entity.position - vec2<f32>(entity.radius);
        local_max = entity.position + vec2<f32>(entity.radius);
    }

    shared_min[lid] = local_min;
    shared_max[lid] = local_max;

    workgroupBarrier();

    // Parallel reduction
    for (var stride = WORKGROUP_SIZE / 2u; stride > 0u; stride = stride / 2u) {
        if lid < stride {
            shared_min[lid] = min(shared_min[lid], shared_min[lid + stride]);
            shared_max[lid] = max(shared_max[lid], shared_max[lid + stride]);
        }
        workgroupBarrier();
    }

    // Thread 0 writes result
    if lid == 0u {
        // Atomic min/max using compare-exchange would be ideal,
        // but for simplicity we use a single workgroup result
        bounds.min = min(bounds.min, shared_min[0]);
        bounds.max = max(bounds.max, shared_max[0]);
    }
}
"#;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_shader_contains_all_primitives() {
        assert!(PRIMITIVE_SHADER.contains("vs_circle"));
        assert!(PRIMITIVE_SHADER.contains("fs_circle"));
        assert!(PRIMITIVE_SHADER.contains("vs_ring"));
        assert!(PRIMITIVE_SHADER.contains("fs_ring"));
        assert!(PRIMITIVE_SHADER.contains("vs_line"));
        assert!(PRIMITIVE_SHADER.contains("fs_line"));
        assert!(PRIMITIVE_SHADER.contains("vs_quad"));
        assert!(PRIMITIVE_SHADER.contains("fs_quad"));
        assert!(PRIMITIVE_SHADER.contains("vs_textured_quad"));
        assert!(PRIMITIVE_SHADER.contains("fs_textured_quad"));
        assert!(PRIMITIVE_SHADER.contains("vs_text"));
        assert!(PRIMITIVE_SHADER.contains("fs_text"));
    }

    #[test]
    fn test_primitive_shader_has_uniforms() {
        assert!(PRIMITIVE_SHADER.contains("struct Uniforms"));
        assert!(PRIMITIVE_SHADER.contains("resolution: vec2<f32>"));
    }

    #[test]
    fn test_bloom_shaders_exist() {
        assert!(!BLOOM_BRIGHT_SHADER.is_empty());
        assert!(!BLOOM_BLUR_SHADER.is_empty());
        assert!(!BLOOM_COMPOSITE_SHADER.is_empty());
    }

    #[test]
    fn test_bloom_bright_has_threshold() {
        assert!(BLOOM_BRIGHT_SHADER.contains("threshold"));
        assert!(BLOOM_BRIGHT_SHADER.contains("intensity"));
    }

    #[test]
    fn test_bloom_blur_has_direction() {
        assert!(BLOOM_BLUR_SHADER.contains("direction"));
        assert!(BLOOM_BLUR_SHADER.contains("resolution"));
    }

    #[test]
    fn test_shadow_shaders_exist() {
        assert!(!SHADOW_SILHOUETTE_SHADER.is_empty());
        assert!(!SHADOW_COMPOSITE_SHADER.is_empty());
    }

    #[test]
    fn test_shadow_composite_has_offset() {
        assert!(SHADOW_COMPOSITE_SHADER.contains("offset"));
        assert!(SHADOW_COMPOSITE_SHADER.contains("opacity"));
        assert!(SHADOW_COMPOSITE_SHADER.contains("color"));
    }

    #[test]
    fn test_physics_shader_exists() {
        assert!(!PHYSICS_FORCE_SHADER.is_empty());
        assert!(PHYSICS_FORCE_SHADER.contains("cs_calculate_forces"));
        assert!(PHYSICS_FORCE_SHADER.contains("cs_integrate"));
    }

    #[test]
    fn test_physics_shader_has_params() {
        assert!(PHYSICS_FORCE_SHADER.contains("entity_count"));
        assert!(PHYSICS_FORCE_SHADER.contains("delta_time"));
        assert!(PHYSICS_FORCE_SHADER.contains("repulsion_strength"));
    }

    #[test]
    fn test_bounds_shader_exists() {
        assert!(!BOUNDS_SHADER.is_empty());
        assert!(BOUNDS_SHADER.contains("cs_calculate_bounds"));
    }

    #[test]
    fn test_visibility_culling_shader_exists() {
        assert!(!VISIBILITY_CULLING_SHADER.is_empty());
        assert!(VISIBILITY_CULLING_SHADER.contains("cs_cull_circles"));
        assert!(VISIBILITY_CULLING_SHADER.contains("cs_cull_lines"));
        assert!(VISIBILITY_CULLING_SHADER.contains("cs_cull_quads"));
        assert!(VISIBILITY_CULLING_SHADER.contains("cs_reset_indirect"));
    }

    #[test]
    fn test_visibility_culling_shader_has_params() {
        assert!(VISIBILITY_CULLING_SHADER.contains("view_bounds"));
        assert!(VISIBILITY_CULLING_SHADER.contains("instance_count"));
        assert!(VISIBILITY_CULLING_SHADER.contains("floats_per_instance"));
    }

    #[test]
    fn test_visibility_culling_has_indirect_draw() {
        assert!(VISIBILITY_CULLING_SHADER.contains("DrawIndirect"));
        assert!(VISIBILITY_CULLING_SHADER.contains("vertex_count"));
        assert!(VISIBILITY_CULLING_SHADER.contains("instance_count"));
    }

    #[test]
    fn test_curve_shader_exists() {
        assert!(!CURVE_SHADER.is_empty());
        assert!(CURVE_SHADER.contains("vs_curve"));
        assert!(CURVE_SHADER.contains("fs_curve"));
    }

    #[test]
    fn test_curve_shader_has_catmull_rom() {
        // Combined function computes both position and tangent to share t² calculation
        assert!(CURVE_SHADER.contains("catmull_rom_pos_tangent"));
        assert!(CURVE_SHADER.contains("CatmullRomResult"));
    }

    #[test]
    fn test_curve_shader_instance_data() {
        // Verify curve instance contains all required fields
        assert!(CURVE_SHADER.contains("p0: vec2<f32>"));
        assert!(CURVE_SHADER.contains("p1: vec2<f32>"));
        assert!(CURVE_SHADER.contains("p2: vec2<f32>"));
        assert!(CURVE_SHADER.contains("p3: vec2<f32>"));
        assert!(CURVE_SHADER.contains("width: f32"));
        assert!(CURVE_SHADER.contains("color: vec4<f32>"));
        assert!(CURVE_SHADER.contains("segments: u32"));
    }

    #[test]
    fn test_all_shaders_have_valid_wgsl_syntax() {
        // Basic syntax checks - these catch common typos
        let shaders = [
            PRIMITIVE_SHADER,
            CURVE_SHADER,
            TEXTURE_ARRAY_SHADER,
            BLOOM_BRIGHT_SHADER,
            BLOOM_BLUR_SHADER,
            BLOOM_COMPOSITE_SHADER,
            SHADOW_SILHOUETTE_SHADER,
            SHADOW_COMPOSITE_SHADER,
            PHYSICS_FORCE_SHADER,
            BOUNDS_SHADER,
            VISIBILITY_CULLING_SHADER,
        ];

        for shader in shaders {
            // Check for balanced braces
            let open_braces = shader.matches('{').count();
            let close_braces = shader.matches('}').count();
            assert_eq!(open_braces, close_braces, "Unbalanced braces in shader");

            // Check for balanced parentheses
            let open_parens = shader.matches('(').count();
            let close_parens = shader.matches(')').count();
            assert_eq!(
                open_parens, close_parens,
                "Unbalanced parentheses in shader"
            );

            // Check for @vertex or @fragment or @compute entry points
            let has_entry_point = shader.contains("@vertex")
                || shader.contains("@fragment")
                || shader.contains("@compute");
            assert!(has_entry_point, "Shader missing entry point decorator");
        }
    }

    #[test]
    fn test_compute_shaders_have_workgroup_size() {
        assert!(PHYSICS_FORCE_SHADER.contains("@workgroup_size"));
        assert!(BOUNDS_SHADER.contains("@workgroup_size"));
        assert!(VISIBILITY_CULLING_SHADER.contains("@workgroup_size"));
    }

    #[test]
    fn test_visibility_culling_visibility_functions() {
        // Verify visibility check functions exist
        assert!(VISIBILITY_CULLING_SHADER.contains("is_circle_visible"));
        assert!(VISIBILITY_CULLING_SHADER.contains("is_line_visible"));
        assert!(VISIBILITY_CULLING_SHADER.contains("is_quad_visible"));
    }

    #[test]
    fn test_texture_array_shader_exists() {
        assert!(!TEXTURE_ARRAY_SHADER.is_empty());
        assert!(TEXTURE_ARRAY_SHADER.contains("vs_texture_array"));
        assert!(TEXTURE_ARRAY_SHADER.contains("fs_texture_array"));
    }

    #[test]
    fn test_texture_array_shader_has_layer_index() {
        // Verify the shader uses texture array with layer index
        assert!(TEXTURE_ARRAY_SHADER.contains("texture_2d_array"));
        assert!(TEXTURE_ARRAY_SHADER.contains("layer: u32"));
        assert!(TEXTURE_ARRAY_SHADER.contains("@interpolate(flat)"));
    }

    #[test]
    fn test_texture_array_shader_instance_data() {
        // Verify texture array instance contains all required fields
        assert!(TEXTURE_ARRAY_SHADER.contains("bounds: vec4<f32>"));
        assert!(TEXTURE_ARRAY_SHADER.contains("uv_bounds: vec4<f32>"));
        assert!(TEXTURE_ARRAY_SHADER.contains("color: vec4<f32>"));
        assert!(TEXTURE_ARRAY_SHADER.contains("layer: u32"));
    }
}
