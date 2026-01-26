# ADR 0005: Texture Array Batching for Draw Calls

## Status

Accepted

## Date

2025-01-15

## Context

Rendering user avatars requires displaying many small textures (one per contributor). Traditional approaches bind each texture individually, resulting in one draw call per avatar.

**Problem**: Draw call overhead dominates at scale:
- 500 contributors = 500 draw calls
- Each draw call has ~5µs overhead (GPU state change, validation)
- 500 × 5µs = 2.5ms just in draw call overhead
- Exceeds entire 16.67ms frame budget for 60 FPS

**Constraint**: Must maintain visual quality; can't simply reduce avatar count.

## Decision

Use GPU texture arrays to batch all avatar textures into a single texture array, enabling single-draw-call rendering.

**Implementation**:
```rust
struct TextureArrayBatcher {
    array: TextureArray,  // GPU texture array
    layer_map: HashMap<AvatarId, u32>,  // Avatar -> layer index
}

// All avatars rendered in ONE draw call
fn render_avatars(&self, avatars: &[Avatar]) {
    self.shader.set_texture_array(&self.array);
    for avatar in avatars {
        let layer = self.layer_map[&avatar.id];
        instances.push(Instance { layer, ... });
    }
    self.draw_instanced(instances);  // Single draw call
}
```

**Instance Attributes**:
- Position (vec2)
- Size (float)
- Texture layer index (uint)
- Color tint (vec4)

## Consequences

### Positive

- **99.8% draw call reduction**: 500 draw calls → 1 draw call
- **Measured: O(1) draw time**: 360ps per avatar (was ~5µs)
- **Better GPU utilization**: Instanced rendering is GPU-friendly
- **Scales to thousands**: No increase in draw calls with more avatars

### Negative

- **Texture array limits**: GPU has max layers (typically 256-2048)
- **Memory overhead**: All textures in VRAM at once
- **Complexity**: Texture array management code
- **Upload cost**: Initial upload is O(n) but amortized

### Neutral

- Requires WebGL2 or WebGPU (fallback to individual textures for WebGL1)
- Maximum avatar size constrained by array layer size
- Dynamic addition requires array resize (rare operation)

## Alternatives Considered

### Alternative 1: Texture Atlas

Pack all avatars into single large texture, use UV coordinates.

**Rejected because**:
- UV calculation complexity
- Atlas packing is NP-hard
- Wasted space with varying avatar sizes
- Harder to add/remove dynamically

### Alternative 2: Virtual Texturing

Stream textures on demand.

**Rejected because**:
- Massive implementation complexity
- Overkill for avatar use case
- Latency on texture fetch

### Alternative 3: Draw Call Sorting + Batching

Sort by texture, batch same-texture avatars.

**Rejected because**:
- Still O(unique textures) draw calls
- 500 unique avatars = 500 draw calls (no improvement)
- Sorting overhead

### Alternative 4: Reduce Avatar Count

Only show top N contributors.

**Rejected because**:
- Loses information
- Defeats purpose of visualization
- Poor user experience

## References

- `crates/rource-render/src/webgl2/texture_array.rs` - Implementation
- `docs/performance/CHRONOLOGY.md` - Phase 55: Texture Array Batching
- Benchmark: `cargo bench -p rource-render --bench texture_batching`
- Measured: 360ps ± 6.8ps per instance (constant time)

---

*ADR created: 2025-01-15*
*Last reviewed: 2026-01-26*
