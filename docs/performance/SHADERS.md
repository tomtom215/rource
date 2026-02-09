# Shader Architecture

This document describes the GPU shader architecture used in Rource's wgpu rendering backend.

## Overview

Rource uses WGSL (WebGPU Shading Language) for GPU shaders. All shaders are embedded in Rust source files for compile-time validation and easy deployment.

## Shader Files

| File | Purpose |
|------|---------|
| `crates/rource-render/src/backend/wgpu/shaders.rs` | Primitive rendering (circles, rings, lines, quads, text) |
| `crates/rource-render/src/backend/wgpu/bloom.rs` | Bloom post-processing (bright pass, blur, composite) |
| `crates/rource-render/src/backend/wgpu/shadow.rs` | Shadow map generation and application |
| `crates/rource-render/src/backend/wgpu/compute.rs` | Physics compute shaders (force calculation, integration) |
| `crates/rource-render/src/backend/wgpu/spatial_hash.rs` | GPU spatial hash for O(n) neighbor queries |
| `crates/rource-render/src/backend/wgpu/culling.rs` | Frustum culling compute shader |

## Design Principles

### 1. Anti-Aliasing

All primitives use signed distance field (SDF) based anti-aliasing:

```wgsl
// Anti-aliased edge using smoothstep
let edge = 1.0 - in.aa_width;
let alpha = 1.0 - smoothstep(edge, 1.0, dist);
```

### 2. Instanced Rendering

Vertex shaders support per-instance data for efficient batching:

```wgsl
struct CircleInstance {
    @location(1) center: vec2<f32>,
    @location(2) radius: f32,
    @location(3) color: vec4<f32>,
};
```

### 3. Uniform Buffer Layout

All shaders share a common uniform buffer:

```wgsl
struct Uniforms {
    resolution: vec2<f32>,
    time: f32,
    _padding: f32,
};

@group(0) @binding(0)
var<uniform> uniforms: Uniforms;
```

### 4. Compute Shader Optimization

Physics compute shaders use workgroup shared memory for efficiency:

```wgsl
var<workgroup> shared_forces: array<vec2<f32>, 256>;
```

## Bloom Effect

The bloom effect uses a 3-pass approach:

1. **Bright Pass**: Extract pixels above brightness threshold
2. **Blur Pass**: Multi-pass Gaussian blur (configurable iterations)
3. **Composite Pass**: Blend blurred result with original

## Spatial Hash (GPU Physics)

The GPU spatial hash reduces force calculation from O(n²) to O(n):

| Stage | Description |
|-------|-------------|
| Clear | Zero out hash grid counters |
| Count | Count entities per cell |
| Prefix Sum | Compute write offsets |
| Scatter | Write entity indices to sorted buffer |
| Forces | Calculate forces using only nearby entities |
| Integrate | Update positions and velocities |

Performance improvement: **2200x** reduction with 5000 entities on 64×64 grid.

## Performance Notes

- Shader compilation is cached by the wgpu backend
- All shaders use `#[inline]` equivalent (single module)
- Branching is minimized for GPU efficiency
- Pre-computed values passed from vertex to fragment shader

---

*Last Updated: 2026-01-26*
