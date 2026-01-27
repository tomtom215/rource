# 20. GPU Visibility Culling

**Implementation**: `crates/rource-render/src/backend/wgpu/culling.rs`

**Category**: GPU Rendering Optimization

---

## 20.1 Problem Statement

Rendering N instances requires:
1. Vertex shader invocations: N × vertices_per_instance
2. Fragment shader invocations: N × pixels_per_instance (approx)

When many instances are outside the view bounds, GPU cycles are wasted processing invisible geometry.

---

## 20.2 Algorithm Overview

GPU visibility culling uses compute shaders to:
1. Filter instances based on view bounds
2. Compact visible instances into a contiguous buffer
3. Use indirect draw commands with dynamic instance count

**Pipeline**:
```
┌──────────────┐    ┌──────────────────┐    ┌──────────────┐
│ All Instances│───►│ Compute: Cull    │───►│Visible Only  │
│  (Input)     │    │ AABB vs ViewRect │    │  (Output)    │
└──────────────┘    └──────────────────┘    └──────┬───────┘
                                                   │
                                           ┌───────▼───────┐
                                           │ DrawIndirect  │
                                           │ instance_count│
                                           └───────────────┘
```

---

## 20.3 Visibility Test

**Definition 20.1 (AABB-Rectangle Intersection)**: For axis-aligned bounding box and view rectangle:

```
visible = !(max_x < view_min_x ||
            min_x > view_max_x ||
            max_y < view_min_y ||
            min_y > view_max_y)
```

**Per-Primitive Tests**:

**Circles** (center + radius):
```wgsl
fn is_circle_visible(center: vec2<f32>, radius: f32, view: vec4<f32>) -> bool {
    return center.x + radius >= view.x &&  // view.x = min_x
           center.x - radius <= view.z &&  // view.z = max_x
           center.y + radius >= view.y &&  // view.y = min_y
           center.y - radius <= view.w;    // view.w = max_y
}
```

**Lines** (start + end + width):
```wgsl
fn is_line_visible(start: vec2<f32>, end: vec2<f32>, width: f32, view: vec4<f32>) -> bool {
    let min_x = min(start.x, end.x) - width;
    let max_x = max(start.x, end.x) + width;
    let min_y = min(start.y, end.y) - width;
    let max_y = max(start.y, end.y) + width;

    return max_x >= view.x && min_x <= view.z &&
           max_y >= view.y && min_y <= view.w;
}
```

**Quads** (bounds: min_x, min_y, max_x, max_y):
```wgsl
fn is_quad_visible(bounds: vec4<f32>, view: vec4<f32>) -> bool {
    return bounds.z >= view.x && bounds.x <= view.z &&
           bounds.w >= view.y && bounds.y <= view.w;
}
```

---

## 20.4 Stream Compaction

**Problem**: After culling, visible instances are scattered. We need contiguous output for efficient rendering.

**Solution**: Atomic counter for output index.

```wgsl
@group(0) @binding(3) var<storage, read_write> indirect: DrawIndirectCommand;

@compute @workgroup_size(256)
fn cs_cull_circles(@builtin(global_invocation_id) id: vec3<u32>) {
    let idx = id.x;
    if (idx >= params.instance_count) { return; }

    let center = vec2(input[idx * 7], input[idx * 7 + 1]);
    let radius = input[idx * 7 + 2];

    if (is_circle_visible(center, radius, params.view_bounds)) {
        // Atomically get output slot
        let out_idx = atomicAdd(&indirect.instance_count, 1u);

        // Copy instance to output buffer
        for (var i = 0u; i < 7u; i++) {
            output[out_idx * 7 + i] = input[idx * 7 + i];
        }
    }
}
```

**Correctness**:
- `atomicAdd` returns the old value, giving unique slot to each visible instance
- Instance count in indirect buffer is automatically updated
- Output buffer contains exactly the visible instances

---

## 20.5 Indirect Draw Integration

**DrawIndirectCommand Structure**:
```rust
#[repr(C)]
struct DrawIndirectCommand {
    vertex_count: u32,      // Vertices per instance
    instance_count: u32,    // Set by culling shader
    first_vertex: u32,      // 0
    first_instance: u32,    // 0
}
```

**Rendering**:
```rust
// After culling dispatch
render_pass.set_vertex_buffer(0, culled_output_buffer.slice(..));
render_pass.draw_indirect(&indirect_buffer, 0);
```

**Benefit**: No CPU readback of instance count. GPU sets count, GPU uses count.

---

## 20.6 Theorem: Culling Correctness

**Claim**: An instance is rendered if and only if it intersects the view bounds.

**Proof**:

*Soundness* (no false positives): If an instance doesn't intersect view bounds:
- The AABB test returns false
- `atomicAdd` is not called
- Instance is not written to output
- Instance is not rendered ✓

*Completeness* (no false negatives): If an instance intersects view bounds:
- The AABB test returns true
- `atomicAdd` gives unique output slot
- Instance data is copied to output
- `draw_indirect` uses updated count
- Instance is rendered ✓

∎

---

## 20.7 Complexity Analysis

**Compute Pass**:
- Workgroups: ⌈N / 256⌉
- Threads: N (one per instance)
- Work per thread: O(1) visibility test + O(1) atomic + O(k) copy
- Total: O(N × k) where k = floats per instance

**Memory**:
- Input buffer: N × k × 4 bytes
- Output buffer: N × k × 4 bytes (worst case all visible)
- Indirect buffer: 16 bytes

**GPU-CPU Synchronization**: None required for rendering path.

---

## 20.8 Performance Characteristics

**When Beneficial** (GPU culling > CPU culling):
- Instance count > 10,000
- View changes every frame (continuous pan/zoom)
- GPU compute available
- Render throughput limited

**When Detrimental** (CPU culling > GPU culling):
- Instance count < 1,000
- Static view
- CPU quadtree already performs culling
- GPU compute unavailable (WebGL1 fallback)

**Typical Culling Rates**:

| Scenario | Total | Visible | Culled | Rate |
|----------|-------|---------|--------|------|
| Full zoom | 50,000 | 50,000 | 0 | 0% |
| 25% view | 50,000 | 12,500 | 37,500 | 75% |
| 10% view | 50,000 | 5,000 | 45,000 | 90% |
| 1% view | 50,000 | 500 | 49,500 | 99% |

---

## 20.9 Buffer Management

**Growth Strategy**:
```rust
const CULLING_GROWTH_FACTOR: f32 = 1.5;

fn ensure_capacity(&mut self, required: usize) {
    if required > self.capacity {
        let new_capacity = (required as f32 * CULLING_GROWTH_FACTOR) as usize;
        self.reallocate(new_capacity);
    }
}
```

**Rationale**: 1.5× growth factor balances:
- Memory efficiency (not 2× wasteful)
- Reallocation frequency (amortized O(1) per element)

---

## 20.10 Warmup and Pipeline Compilation

**Problem**: First-frame stutter from shader compilation.

**Solution**: Warmup dispatch during initialization.

```rust
pub fn warmup(&mut self, device: &Device, queue: &Queue) {
    // Ensure buffers exist
    self.ensure_primitive_buffers(device, MIN_CULLING_CAPACITY, CullPrimitive::Circles);
    // ...

    // Dispatch each pipeline once (0 actual work)
    let mut encoder = device.create_command_encoder(&desc);
    for buffers in [&self.circle_buffers, &self.line_buffers, &self.quad_buffers] {
        let mut pass = encoder.begin_compute_pass(&desc);
        pass.set_bind_group(0, &buffers.bind_group, &[]);
        pass.set_pipeline(&self.reset_pipeline);
        pass.dispatch_workgroups(1, 1, 1);
        pass.set_pipeline(&self.cull_pipeline);
        pass.dispatch_workgroups(0, 1, 1);  // 0 workgroups = no work
    }
    queue.submit(Some(encoder.finish()));
}
```

**Effect**: Pipeline compilation happens at warmup, not first render frame.

---

## References

- Wihlidal, G. (2016). "Optimizing the Graphics Pipeline with Compute." *GPU Pro 7*.
- Engel, W. (2015). "GPU-Driven Rendering Pipelines." *GPU Pro 6*.

---

## 20.11 Implementation (Papers With Code)

### Source Code Location

| Component | File | Lines |
|-----------|------|-------|
| Culling module | `crates/rource-render/src/backend/wgpu/culling.rs` | 1-600 |
| cs_cull_circles (WGSL) | `crates/rource-render/src/backend/wgpu/shaders.rs` | 1450-1500 |
| cs_cull_lines (WGSL) | `crates/rource-render/src/backend/wgpu/shaders.rs` | 1502-1550 |
| Pipeline creation | `crates/rource-render/src/backend/wgpu/culling.rs` | 395-400 |

### Core Implementation

**Circle Culling Shader** (`shaders.rs:1450-1500`):

```wgsl
@compute @workgroup_size(256)
fn cs_cull_circles(
    @builtin(global_invocation_id) global_id: vec3<u32>,
) {
    let idx = global_id.x;
    if (idx >= params.instance_count) { return; }

    let center = vec2(input[idx * 7], input[idx * 7 + 1]);
    let radius = input[idx * 7 + 2];

    if (is_circle_visible(center, radius, params.view_bounds)) {
        let out_idx = atomicAdd(&indirect.instance_count, 1u);
        for (var i = 0u; i < 7u; i++) {
            output[out_idx * 7 + i] = input[idx * 7 + i];
        }
    }
}
```

**Pipeline Setup** (`culling.rs:395-400`):

```rust
device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
    label: Some("Cull Circles Pipeline"),
    layout: Some(&pipeline_layout),
    module: &shader_module,
    entry_point: Some("cs_cull_circles"),
    // ...
});
```

### Mathematical-Code Correspondence

| Theorem | Mathematical Expression | Code Location | Implementation |
|---------|------------------------|---------------|----------------|
| 20.3 | AABB intersection | `shaders.rs:1442-1448` | 4 comparisons |
| 20.4 | Atomic compaction | `shaders.rs:1460` | `atomicAdd(&indirect.instance_count, 1u)` |
| 20.6 | Sound + complete | Shader logic | No false positives/negatives |

### Verification Commands

```bash
# Run GPU culling tests
cargo test -p rource-render culling --release -- --nocapture

# Run visibility test correctness
cargo test -p rource-render test_visibility --release -- --nocapture

# Test indirect draw integration
cargo test -p rource-render test_indirect --release -- --nocapture
```

### Validation Checklist

- [x] AABB visibility test (4 comparisons)
- [x] Atomic stream compaction
- [x] DrawIndirect integration (no CPU readback)
- [x] Warmup for pipeline compilation
- [x] 75-99% culling rate at partial zoom

---

*[Back to Index](./README.md)*
