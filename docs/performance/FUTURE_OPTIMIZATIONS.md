# Future Optimization Opportunities

**Status**: Living Working Document
**Created**: 2026-01-26
**Purpose**: Handover document for future optimization sessions

> **Note**: This is a temporary working document. Once all opportunities are implemented
> and properly documented in CHRONOLOGY.md, BENCHMARKS.md, and SUCCESSFUL_OPTIMIZATIONS.md,
> this file should be deleted to maintain repository cleanliness.

---

## Quick Reference

| Opportunity | Priority | Expected Gain | Complexity | Status |
|-------------|----------|---------------|------------|--------|
| Primitive pipeline consolidation | Medium | 15-25% fewer draw calls | Medium | Not Started |
| Adaptive Barnes-Hut theta | Low | 29-61% physics speedup | Low | **Completed (Phase 62)** |
| GPU visibility pre-culling | Medium | 5-15% buffer upload reduction | High | Not Started |

---

## Opportunity 1: Primitive Pipeline Consolidation (Circle + Ring)

### Priority: Medium
### Expected Gain: 15-25% fewer draw calls
### Complexity: Medium

### Problem Statement

Currently, circles and rings (outlined circles) use separate draw calls even when they
could be batched together. In typical visualizations:
- Files have both a filled disc AND an outline ring
- Users have glow layers (multiple rings) AND a center disc
- Each primitive type triggers a separate draw call

### Analysis Required

Before implementation, benchmark and measure:
1. Current draw call count for circles vs rings
2. Time spent in `flush_circle_instances` vs `flush_ring_instances`
3. GPU state change overhead between circle/ring pipelines

### Proposed Solution

Consolidate circle and ring rendering into a unified "disc" pipeline that uses
instance data to control:
- Fill mode (solid, outline, both)
- Inner radius (0 for solid, >0 for ring)
- Line width (for outline mode)

```rust
// Current: separate pipelines
draw_disc(pos, radius, color);           // Pipeline A
draw_circle(pos, radius, width, color);  // Pipeline B

// Proposed: unified pipeline with mode flag
struct DiscInstance {
    pos: Vec2,
    outer_radius: f32,
    inner_radius: f32,  // 0 = solid disc, >0 = ring
    color: Color,
}
```

### Benchmark Requirements

Create `crates/rource-render/benches/primitive_consolidation.rs`:
- Measure current separate pipeline performance
- Measure consolidated pipeline performance
- Test at entity counts: 100, 300, 500, 1000
- Verify visual output is identical

### Files to Modify

- `crates/rource-render/src/backend/wgpu/shaders.rs` (unified shader)
- `crates/rource-render/src/backend/wgpu/pipeline.rs` (consolidated pipeline)
- `crates/rource-render/src/backend/wgpu/flush_passes.rs` (unified flush)
- `crates/rource-render/src/backend/wgpu/mod.rs` (draw methods)

### Success Criteria

- [ ] Criterion benchmark shows 15-25% fewer draw calls
- [ ] All 1,899+ tests pass
- [ ] Visual output is pixel-identical
- [ ] Documented in all three performance docs

---

## Opportunity 2: Adaptive Barnes-Hut Theta

### ✅ COMPLETED - Phase 62 (2026-01-26)

**Actual Gain**: 29-61% physics speedup (exceeded 10-20% target)

### Implementation Summary

Implemented adaptive theta selection based on entity count using logarithmic scaling.

**Results**:

| Entities | Fixed θ=0.8 | Adaptive θ | Improvement |
|----------|-------------|------------|-------------|
| 100      | 26.10 µs    | 26.83 µs   | ~0% (θ=0.80) |
| 500      | 296.71 µs   | 210.62 µs  | **-29.0%** (θ=1.00) |
| 1000     | 714.81 µs   | 419.96 µs  | **-41.2%** (θ=1.15) |
| 5000     | 4.25 ms     | 1.64 ms    | **-61.4%** (θ=1.50) |

**Implementation**:
```rust
pub fn calculate_adaptive_theta(entity_count: usize) -> f32 {
    if entity_count <= 200 {
        return 0.8;
    }
    let scale_factor = (entity_count as f32 / 200.0).log2() / 25.0f32.log2();
    (0.8 + 0.7 * scale_factor.clamp(0.0, 1.0)).clamp(0.7, 1.5)
}
```

**Files Modified**:
- `crates/rource-core/src/physics/barnes_hut.rs`
- `crates/rource-core/src/physics/force.rs`
- `crates/rource-core/src/scene/layout_methods.rs`
- `crates/rource-core/benches/barnes_hut_theta.rs`

**Documentation**:
- [x] CHRONOLOGY.md - Phase 62 entry
- [x] BENCHMARKS.md - Full benchmark tables
- [x] SUCCESSFUL_OPTIMIZATIONS.md - Implementation details

---

## Opportunity 3: GPU Visibility Pre-Culling

### Priority: Medium
### Expected Gain: 5-15% buffer upload reduction
### Complexity: High

### Problem Statement

Currently, visibility culling happens on the CPU before uploading instance data to GPU:
1. CPU queries QuadTree for visible entities
2. CPU builds instance buffer with visible entities only
3. CPU uploads instance buffer to GPU
4. GPU renders

For large entity counts, step 2 and 3 can be expensive. GPU compute shaders could
perform culling directly, avoiding CPU→GPU transfer of culled entities.

### Analysis Required

Before implementation, benchmark and measure:
1. Current CPU time for visibility queries
2. Current buffer upload size and time
3. GPU compute shader overhead on target platforms
4. Break-even point (entity count where GPU culling wins)

### Proposed Solution

Implement GPU compute shader visibility culling:

```wgsl
// Compute shader: cull entities against view frustum
@compute @workgroup_size(256)
fn cull_entities(
    @builtin(global_invocation_id) id: vec3<u32>,
) {
    let entity_idx = id.x;
    if entity_idx >= entity_count { return; }

    let pos = entity_positions[entity_idx];
    let radius = entity_radii[entity_idx];

    // Frustum test
    if is_visible(pos, radius, view_bounds) {
        let output_idx = atomicAdd(&visible_count, 1u);
        visible_indices[output_idx] = entity_idx;
    }
}
```

### Benchmark Requirements

Create benchmarks in `crates/rource-render/benches/gpu_culling.rs`:
- Measure CPU culling time at entity counts: 500, 2000, 10000, 50000
- Measure GPU culling time (including sync overhead)
- Measure buffer upload reduction
- Test on multiple backends (WebGPU, Vulkan, Metal)

### Files to Modify

- `crates/rource-render/src/backend/wgpu/culling.rs` (new compute shader)
- `crates/rource-render/src/backend/wgpu/shaders.rs` (culling shader source)
- `crates/rource-render/src/backend/wgpu/mod.rs` (culling integration)
- `crates/rource-render/src/backend/wgpu/culling_methods.rs` (dispatch logic)

### Success Criteria

- [ ] Criterion benchmark shows 5-15% reduction in buffer upload time
- [ ] Works correctly on WebGPU, Vulkan, Metal backends
- [ ] Fallback to CPU culling when GPU compute unavailable
- [ ] All tests pass
- [ ] Documented in all three performance docs

---

## Implementation Workflow Reminder

For each opportunity, follow the standard workflow:

```
1. IDENTIFY      - Review this document, understand the opportunity
2. BENCHMARK     - Create criterion benchmarks BEFORE implementation
3. IMPLEMENT     - Make targeted, minimal changes
4. VERIFY        - Run all tests, clippy, rustfmt
5. BENCHMARK     - Run same benchmarks, calculate improvement
6. DOCUMENT      - Update CHRONOLOGY.md, BENCHMARKS.md, SUCCESSFUL_OPTIMIZATIONS.md
7. COMMIT        - Clear message with metrics
8. UPDATE        - Mark as completed in this document
```

When all opportunities are completed:
1. Verify all are documented in the three main performance docs
2. Delete this file (`git rm docs/performance/FUTURE_OPTIMIZATIONS.md`)
3. Commit: `docs: remove FUTURE_OPTIMIZATIONS.md (all items completed)`

---

## Session Handover Notes

### Context from 2026-01-26 Session

The optimization audit identified these opportunities while investigating the 14.5x gap
between peak FPS (43k) and steady FPS (3k). The primary cause was textured quad draw
call explosion, which was addressed in Phase 61 (avatar texture array batching).

These remaining opportunities are lower priority but still valuable for pushing
performance further.

### Starting Point for Next Session

1. Read this document to understand the opportunities
2. Choose one opportunity based on priority and available time
3. Follow the benchmark-first workflow
4. Update this document with progress

### Key Files to Reference

- `docs/performance/CHRONOLOGY.md` - Full optimization history (62 phases)
- `docs/performance/BENCHMARKS.md` - All benchmark data
- `docs/performance/SUCCESSFUL_OPTIMIZATIONS.md` - Implementation details
- `CLAUDE.md` - Project standards and workflow requirements

---

*Document created: 2026-01-26*
*Last updated: 2026-01-26*
