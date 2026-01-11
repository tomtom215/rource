//! GLSL shader sources for WebGL2 rendering.
//!
//! All shaders are written in GLSL ES 3.0 (WebGL2).

// Allow extra hashes in raw strings for consistency in GLSL code
#![allow(clippy::needless_raw_string_hashes)]

/// Vertex shader for drawing filled circles (discs).
///
/// Takes a circle center position, radius, and color as instance data.
/// Uses a quad with UV coordinates to render anti-aliased circles.
///
/// For 3D mode: The application projects 3D world positions to 2D screen
/// coordinates using `Camera3D` before passing to the shader. The shader
/// works with pre-projected screen-space coordinates in both 2D and 3D modes.
pub const CIRCLE_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

// Per-vertex attributes (unit quad: -1 to 1)
layout(location = 0) in vec2 a_position;

// Per-instance attributes
layout(location = 1) in vec2 a_center;      // Circle center in screen space
layout(location = 2) in float a_radius;     // Circle radius in pixels
layout(location = 3) in vec4 a_color;       // RGBA color

// Uniforms
uniform vec2 u_resolution;  // Canvas size in pixels

// Outputs
out vec2 v_uv;          // UV coordinates for fragment shader (-1 to 1)
out vec4 v_color;       // Color for fragment shader

void main() {
    // Calculate vertex position
    vec2 pos = a_center + a_position * (a_radius + 1.0);  // +1 for anti-aliasing

    // Convert to clip space (-1 to 1)
    vec2 clip_pos = (pos / u_resolution) * 2.0 - 1.0;
    clip_pos.y = -clip_pos.y;  // Flip Y (WebGL has Y-up)

    gl_Position = vec4(clip_pos, 0.0, 1.0);
    v_uv = a_position;
    v_color = a_color;
}
"#;

/// Fragment shader for drawing filled circles (discs).
///
/// Uses distance from center to create anti-aliased edges.
pub const CIRCLE_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

in vec2 v_uv;
in vec4 v_color;

out vec4 fragColor;

void main() {
    // Distance from center (0 to 1 at edge, >1 outside)
    float dist = length(v_uv);

    // Anti-aliased edge (smooth transition over ~1 pixel)
    float alpha = 1.0 - smoothstep(0.9, 1.0, dist);

    if (alpha < 0.001) {
        discard;
    }

    fragColor = vec4(v_color.rgb, v_color.a * alpha);
}
"#;

/// Vertex shader for drawing circle outlines (rings).
pub const RING_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

// Per-vertex attributes (unit quad: -1 to 1)
layout(location = 0) in vec2 a_position;

// Per-instance attributes
layout(location = 1) in vec2 a_center;      // Circle center in screen space
layout(location = 2) in float a_radius;     // Circle radius in pixels
layout(location = 3) in float a_width;      // Ring width in pixels
layout(location = 4) in vec4 a_color;       // RGBA color

// Uniforms
uniform vec2 u_resolution;  // Canvas size in pixels

// Outputs
out vec2 v_uv;
out float v_inner_radius;   // Inner radius ratio (0 to 1)
out vec4 v_color;

void main() {
    float outer_radius = a_radius + a_width * 0.5 + 1.0;  // +1 for AA
    vec2 pos = a_center + a_position * outer_radius;

    vec2 clip_pos = (pos / u_resolution) * 2.0 - 1.0;
    clip_pos.y = -clip_pos.y;

    gl_Position = vec4(clip_pos, 0.0, 1.0);
    v_uv = a_position;
    v_inner_radius = (a_radius - a_width * 0.5) / outer_radius;
    v_color = a_color;
}
"#;

/// Fragment shader for drawing circle outlines (rings).
pub const RING_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

in vec2 v_uv;
in float v_inner_radius;
in vec4 v_color;

out vec4 fragColor;

void main() {
    float dist = length(v_uv);

    // Outer edge AA
    float outer_alpha = 1.0 - smoothstep(0.95, 1.0, dist);

    // Inner edge AA
    float inner_alpha = smoothstep(v_inner_radius - 0.05, v_inner_radius, dist);

    float alpha = outer_alpha * inner_alpha;

    if (alpha < 0.001) {
        discard;
    }

    fragColor = vec4(v_color.rgb, v_color.a * alpha);
}
"#;

/// Vertex shader for drawing lines.
///
/// Each line is rendered as a quad with proper orientation.
pub const LINE_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

// Per-vertex attributes (unit quad: 0 to 1 in x, -0.5 to 0.5 in y)
layout(location = 0) in vec2 a_position;

// Per-instance attributes
layout(location = 1) in vec2 a_start;       // Line start in screen space
layout(location = 2) in vec2 a_end;         // Line end in screen space
layout(location = 3) in float a_width;      // Line width in pixels
layout(location = 4) in vec4 a_color;       // RGBA color

// Uniforms
uniform vec2 u_resolution;

// Outputs
out vec2 v_uv;
out vec4 v_color;

void main() {
    // Calculate line direction and perpendicular
    vec2 dir = a_end - a_start;
    float len = length(dir);

    if (len < 0.001) {
        // Degenerate line, make invisible
        gl_Position = vec4(2.0, 2.0, 0.0, 1.0);
        return;
    }

    vec2 unit_dir = dir / len;
    vec2 perp = vec2(-unit_dir.y, unit_dir.x);

    // Calculate vertex position
    // a_position.x: 0 to 1 along line length
    // a_position.y: -0.5 to 0.5 perpendicular to line
    float half_width = (a_width + 2.0) * 0.5;  // +2 for AA
    vec2 pos = a_start + unit_dir * (a_position.x * len) + perp * (a_position.y * half_width * 2.0);

    vec2 clip_pos = (pos / u_resolution) * 2.0 - 1.0;
    clip_pos.y = -clip_pos.y;

    gl_Position = vec4(clip_pos, 0.0, 1.0);
    v_uv = a_position;
    v_color = a_color;
}
"#;

/// Fragment shader for drawing anti-aliased lines.
pub const LINE_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

in vec2 v_uv;
in vec4 v_color;

out vec4 fragColor;

void main() {
    // Anti-alias perpendicular edges
    float edge_dist = abs(v_uv.y);
    float alpha = 1.0 - smoothstep(0.4, 0.5, edge_dist);

    // Anti-alias end caps
    float cap_alpha_start = smoothstep(0.0, 0.02, v_uv.x);
    float cap_alpha_end = 1.0 - smoothstep(0.98, 1.0, v_uv.x);
    alpha *= cap_alpha_start * cap_alpha_end;

    if (alpha < 0.001) {
        discard;
    }

    fragColor = vec4(v_color.rgb, v_color.a * alpha);
}
"#;

/// Vertex shader for drawing solid colored quads.
pub const QUAD_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

// Per-vertex attributes (unit quad: 0 to 1)
layout(location = 0) in vec2 a_position;

// Per-instance attributes
layout(location = 1) in vec4 a_bounds;      // (min_x, min_y, max_x, max_y)
layout(location = 2) in vec4 a_color;       // RGBA color

// Uniforms
uniform vec2 u_resolution;

// Outputs
out vec2 v_uv;
out vec4 v_color;

void main() {
    // Interpolate within bounds
    vec2 pos = mix(a_bounds.xy, a_bounds.zw, a_position);

    vec2 clip_pos = (pos / u_resolution) * 2.0 - 1.0;
    clip_pos.y = -clip_pos.y;

    gl_Position = vec4(clip_pos, 0.0, 1.0);
    v_uv = a_position;
    v_color = a_color;
}
"#;

/// Fragment shader for drawing solid colored quads.
pub const QUAD_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

in vec2 v_uv;
in vec4 v_color;

out vec4 fragColor;

void main() {
    fragColor = v_color;
}
"#;

/// Vertex shader for drawing textured quads.
pub const TEXTURED_QUAD_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

// Per-vertex attributes (unit quad: 0 to 1)
layout(location = 0) in vec2 a_position;

// Per-instance attributes
layout(location = 1) in vec4 a_bounds;      // (min_x, min_y, max_x, max_y)
layout(location = 2) in vec4 a_uv_bounds;   // (u_min, v_min, u_max, v_max)
layout(location = 3) in vec4 a_color;       // Tint color

// Uniforms
uniform vec2 u_resolution;

// Outputs
out vec2 v_uv;
out vec4 v_color;

void main() {
    vec2 pos = mix(a_bounds.xy, a_bounds.zw, a_position);

    vec2 clip_pos = (pos / u_resolution) * 2.0 - 1.0;
    clip_pos.y = -clip_pos.y;

    gl_Position = vec4(clip_pos, 0.0, 1.0);
    v_uv = mix(a_uv_bounds.xy, a_uv_bounds.zw, a_position);
    v_color = a_color;
}
"#;

/// Fragment shader for drawing textured quads.
pub const TEXTURED_QUAD_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_texture;

in vec2 v_uv;
in vec4 v_color;

out vec4 fragColor;

void main() {
    vec4 tex_color = texture(u_texture, v_uv);
    fragColor = tex_color * v_color;
}
"#;

/// Vertex shader for drawing text glyphs.
///
/// Text glyphs are rendered as alpha-blended quads from a font atlas.
pub const TEXT_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

// Per-vertex attributes (unit quad: 0 to 1)
layout(location = 0) in vec2 a_position;

// Per-instance attributes
layout(location = 1) in vec4 a_bounds;      // (min_x, min_y, max_x, max_y) in screen space
layout(location = 2) in vec4 a_uv_bounds;   // (u_min, v_min, u_max, v_max) in atlas
layout(location = 3) in vec4 a_color;       // Text color (uses alpha for coverage)

// Uniforms
uniform vec2 u_resolution;

// Outputs
out vec2 v_uv;
out vec4 v_color;

void main() {
    vec2 pos = mix(a_bounds.xy, a_bounds.zw, a_position);

    vec2 clip_pos = (pos / u_resolution) * 2.0 - 1.0;
    clip_pos.y = -clip_pos.y;

    gl_Position = vec4(clip_pos, 0.0, 1.0);
    v_uv = mix(a_uv_bounds.xy, a_uv_bounds.zw, a_position);
    v_color = a_color;
}
"#;

/// Fragment shader for drawing text glyphs.
///
/// Samples the font atlas (single channel alpha) and multiplies by text color.
pub const TEXT_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_font_atlas;

in vec2 v_uv;
in vec4 v_color;

out vec4 fragColor;

void main() {
    // Font atlas stores coverage in the red channel (grayscale)
    float coverage = texture(u_font_atlas, v_uv).r;

    if (coverage < 0.01) {
        discard;
    }

    fragColor = vec4(v_color.rgb, v_color.a * coverage);
}
"#;

/// Vertex shader for fullscreen post-processing (bloom).
pub const BLOOM_VERTEX_SHADER: &str = r#"#version 300 es
precision highp float;

layout(location = 0) in vec2 a_position;

out vec2 v_uv;

void main() {
    gl_Position = vec4(a_position, 0.0, 1.0);
    v_uv = a_position * 0.5 + 0.5;
}
"#;

/// Fragment shader for bloom blur pass.
pub const BLOOM_BLUR_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_texture;
uniform vec2 u_direction;  // (1,0) for horizontal, (0,1) for vertical
uniform vec2 u_resolution;

in vec2 v_uv;

out vec4 fragColor;

// 9-tap Gaussian blur
const float weights[5] = float[](0.227027, 0.1945946, 0.1216216, 0.054054, 0.016216);

void main() {
    vec2 texel_size = 1.0 / u_resolution;
    vec3 result = texture(u_texture, v_uv).rgb * weights[0];

    for (int i = 1; i < 5; i++) {
        vec2 offset = u_direction * texel_size * float(i);
        result += texture(u_texture, v_uv + offset).rgb * weights[i];
        result += texture(u_texture, v_uv - offset).rgb * weights[i];
    }

    fragColor = vec4(result, 1.0);
}
"#;

/// Fragment shader for bloom composite (add bloom to original).
pub const BLOOM_COMPOSITE_FRAGMENT_SHADER: &str = r#"#version 300 es
precision highp float;

uniform sampler2D u_scene;
uniform sampler2D u_bloom;
uniform float u_intensity;

in vec2 v_uv;

out vec4 fragColor;

void main() {
    vec3 scene_color = texture(u_scene, v_uv).rgb;
    vec3 bloom_color = texture(u_bloom, v_uv).rgb;

    fragColor = vec4(scene_color + bloom_color * u_intensity, 1.0);
}
"#;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shaders_not_empty() {
        assert!(!CIRCLE_VERTEX_SHADER.is_empty());
        assert!(!CIRCLE_FRAGMENT_SHADER.is_empty());
        assert!(!RING_VERTEX_SHADER.is_empty());
        assert!(!RING_FRAGMENT_SHADER.is_empty());
        assert!(!LINE_VERTEX_SHADER.is_empty());
        assert!(!LINE_FRAGMENT_SHADER.is_empty());
        assert!(!QUAD_VERTEX_SHADER.is_empty());
        assert!(!QUAD_FRAGMENT_SHADER.is_empty());
        assert!(!TEXTURED_QUAD_VERTEX_SHADER.is_empty());
        assert!(!TEXTURED_QUAD_FRAGMENT_SHADER.is_empty());
        assert!(!TEXT_VERTEX_SHADER.is_empty());
        assert!(!TEXT_FRAGMENT_SHADER.is_empty());
        assert!(!BLOOM_VERTEX_SHADER.is_empty());
        assert!(!BLOOM_BLUR_FRAGMENT_SHADER.is_empty());
        assert!(!BLOOM_COMPOSITE_FRAGMENT_SHADER.is_empty());
    }

    #[test]
    fn test_shaders_have_version() {
        // All shaders should start with version directive
        assert!(CIRCLE_VERTEX_SHADER.contains("#version 300 es"));
        assert!(CIRCLE_FRAGMENT_SHADER.contains("#version 300 es"));
        assert!(LINE_VERTEX_SHADER.contains("#version 300 es"));
        assert!(LINE_FRAGMENT_SHADER.contains("#version 300 es"));
    }
}
