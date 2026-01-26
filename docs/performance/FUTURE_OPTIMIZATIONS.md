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
| Primitive pipeline consolidation | Low | 5-10% CPU-side flush improvement | High | **Analyzed - Deferred (Phase 63)** |
| Adaptive Barnes-Hut theta | Low | 29-61% physics speedup | Low | **Completed (Phase 62)** |
| GPU visibility pre-culling | Medium | Reduced vertex shader invocations | High | **Verified Complete (Phase 64)** |

---

## Opportunity 1: Primitive Pipeline Consolidation (Circle + Ring)

### ⏸️ ANALYZED - DEFERRED (Phase 63, 2026-01-26)

**Recommendation**: Deferred due to modest gains vs implementation complexity

### Analysis Summary

Comprehensive benchmarks were created and run to evaluate consolidating circle and ring
rendering into a unified "disc" pipeline. The analysis revealed that while the optimization
provides measurable improvements, the return on investment is marginal.

### Benchmark Results (CPU-side simulation, criterion, 100 samples, 95% CI)

**Draw Call Reduction**:
| Approach | Draw Calls | Pipeline Switches |
|----------|------------|-------------------|
| Separate | 2 | 1 |
| Unified | 1 | 0 |
| Reduction | **-50%** | **-100%** |

**Instance Population** (adding instances to buffers):
| Entity Count | Separate | Unified | Change |
|--------------|----------|---------|--------|
| 100 | 316.55 ns | 336.23 ns | +6.2% |
| 300 | 899.75 ns | 979.13 ns | +8.8% |
| 500 | 1.52 µs | 1.58 µs | +3.6% |
| 1000 | 3.74 µs | 3.61 µs | **-3.5%** |

**Flush Overhead** (simulated pipeline switch + draw):
| Entity Count | Separate | Unified | Improvement |
|--------------|----------|---------|-------------|
| 100 | 24.48 ns | 22.98 ns | -6.1% |
| 300 | 74.34 ns | 74.51 ns | ~0% |
| 500 | 119.48 ns | 117.38 ns | -1.8% |
| 1000 | 246.73 ns | 221.64 ns | **-10.2%** |

**Full Frame** (populate + flush):
| Entity Count | Separate | Unified | Improvement |
|--------------|----------|---------|-------------|
| 100 | 480.94 ns | 516.49 ns | +7.4% |
| 300 | 1.37 µs | 1.53 µs | +11.7% |
| 500 | 2.79 µs | 2.77 µs | -0.7% |
| 1000 | 5.88 µs | 5.54 µs | **-5.8%** |

**Memory Overhead** (80% circles, 20% rings):
| Entity Count | Separate | Unified | Overhead |
|--------------|----------|---------|----------|
| 100 | 2,880 bytes | 3,200 bytes | +11.1% |
| 1000 | 28,800 bytes | 32,000 bytes | +11.1% |
| 5000 | 144,000 bytes | 160,000 bytes | +11.1% |

### Key Findings

1. **Draw call reduction is 50%** (2→1), but circles and rings are only 2 of ~10 draw
   calls per frame, yielding ~10% net reduction

2. **Pipeline switch elimination** saves GPU state change overhead, but cannot be
   measured with CPU-only benchmarks

3. **Instance population is slightly slower** for unified approach at small entity
   counts due to ring→disc conversion (radius-width/2 calculations)

4. **Memory overhead is constant 11.1%** because circles are padded from 28 to 32 bytes

5. **Net CPU-side improvement is 5-10%** at high entity counts, with regression at
   low entity counts

### Why Deferred

| Factor | Assessment |
|--------|------------|
| CPU gain | 5-10% at high entity counts only |
| GPU gain | Unknown without implementation |
| Memory cost | +11.1% constant overhead |
| Complexity | High (5+ files, shader changes, pipeline restructuring) |
| Risk | Medium (shader bugs, visual regressions) |
| ROI | Marginal (modest gains vs complexity) |

The optimization provides **measurable but modest** improvements. The implementation
requires modifying shaders, pipelines, flush passes, and draw methods across 5+ files.
Given the project's standards for high-confidence optimizations, this is deferred in
favor of higher-impact work.

### Benchmark Artifact

Benchmark file created: `crates/rource-render/benches/primitive_consolidation.rs`

This benchmark can be re-run in future sessions if priorities change or if actual
GPU timing reveals that pipeline switch elimination provides larger gains than
the CPU simulation suggests.

```bash
cargo bench --bench primitive_consolidation -p rource-render
```

### Future Reconsideration Triggers

This optimization may be worth revisiting if:
1. Profiling shows pipeline switches are a significant bottleneck
2. GPU timing tools reveal large gains from switch elimination
3. The codebase is refactored making the implementation simpler
4. Higher-impact optimizations are exhausted

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

### ✅ VERIFIED COMPLETE - Phase 64 (2026-01-26)

**Status**: Feature was already fully implemented prior to this analysis.

### Verification Summary

Phase 64 analyzed this opportunity and discovered that GPU visibility culling was
**already fully implemented** with complete infrastructure:

**Implemented Components:**
- `crates/rource-render/src/backend/wgpu/culling.rs` - VisibilityCullingPipeline (874 lines)
- `crates/rource-render/src/backend/wgpu/shaders.rs` - VISIBILITY_CULLING_SHADER (compute shaders)
- `crates/rource-render/src/backend/wgpu/culling_methods.rs` - Public API (268 lines)
- `crates/rource-render/src/backend/wgpu/flush_passes.rs` - Integration (line 38-41)
- `rource-wasm/src/wasm_api/layout.rs` - WASM API exposure (lines 386-549)

**WASM API Available:**
- `setUseGPUCulling(bool)` - Enable/disable GPU culling
- `isGPUCullingEnabled()` - Check if enabled
- `isGPUCullingActive()` - Check if running (enabled + threshold met)
- `setGPUCullingThreshold(usize)` - Set entity count threshold (default: 10,000)
- `warmupGPUCulling()` - Pre-compile compute shaders

### Clarification: Expected vs Actual Benefit

| Aspect | Original Expectation | Actual Implementation |
|--------|---------------------|----------------------|
| Expected benefit | "5-15% buffer upload reduction" | Reduced vertex shader invocations |
| Data flow | Skip upload of culled entities | All instances uploaded, GPU filters |
| Trade-off | Less data transferred | Same data, fewer GPU draw operations |

**Why the difference?**

The implementation uploads ALL instance data to the GPU culling input buffer, then
runs compute shaders to produce a compacted output buffer with only visible instances.
The regular instance buffer is also uploaded as a fallback path.

This means:
- Buffer upload is NOT reduced (actually slightly increased due to double upload)
- The benefit comes from **indirect draw** with fewer instances rendered
- Vertex shader runs only for visible instances
- GPU decides instance count at draw time

### When GPU Culling Helps

From the implementation documentation (`culling_methods.rs`):
- Scene has **10,000+ visible instances**
- View bounds change every frame (continuous panning/zooming)
- CPU is already saturated with other work

For smaller scenes (< 10,000 instances), CPU quadtree culling may be faster
due to reduced compute dispatch overhead.

### Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│ GPU Culling Data Flow                                            │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. CPU builds instance buffer (all instances)                   │
│  2. dispatch_culling() uploads to culling input buffer           │
│  3. Compute shader: cs_reset_indirect (reset atomic counter)     │
│  4. Compute shader: cs_cull_X (circles/lines/quads)              │
│     └─ Test AABB visibility                                      │
│     └─ Atomic increment + write to output buffer                 │
│  5. Regular instance buffer ALSO uploaded (fallback)             │
│  6. Render pass uses culled output via draw_indirect()           │
│                                                                  │
│  Result: Same upload, fewer vertex shader invocations            │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### Technical Details

**Compute Shaders (shaders.rs:1344-1583):**
- `cs_reset_indirect` - Atomically reset instance counter
- `cs_cull_circles` - AABB test for circles (7 floats/instance)
- `cs_cull_lines` - AABB test for line segments (9 floats/instance)
- `cs_cull_quads` - AABB test for quads (8 floats/instance)

**Workgroup Configuration:**
- Workgroup size: 256 threads
- Minimum buffer capacity: 1,024 instances
- Buffer growth factor: 1.5x

**Visibility Test (AABB):**
```wgsl
fn is_circle_visible(base_idx: u32) -> bool {
    let x = input[base_idx];
    let y = input[base_idx + 1u];
    let r = input[base_idx + 2u];

    return (x + r) >= params.view_bounds.x &&  // min_x
           (x - r) <= params.view_bounds.z &&  // max_x
           (y + r) >= params.view_bounds.y &&  // min_y
           (y - r) <= params.view_bounds.w;    // max_y
}
```

### Success Criteria (Met)

- [x] Works correctly on WebGPU, Vulkan, Metal backends (wgpu abstraction)
- [x] Fallback to CPU culling when GPU compute unavailable
- [x] All tests pass
- [x] WASM API exposed for runtime configuration
- [x] Warmup method to avoid first-frame stutter

### Benchmark Status

No separate benchmark created. The original opportunity description's expected
benefit ("buffer upload reduction") does not match the actual implementation
benefit ("reduced vertex invocations"). CPU-side benchmarks cannot measure
vertex shader workload reduction.

The feature's benefit is best observed through GPU profiling tools (RenderDoc,
WebGPU dev tools) or frame rate analysis on large scenes.

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

### Final Status (2026-01-26)

All three opportunities have been resolved:

| Opportunity | Phase | Outcome |
|-------------|-------|---------|
| Primitive pipeline consolidation | 63 | Analyzed and **deferred** (modest 5-10% gains vs high complexity) |
| Adaptive Barnes-Hut theta | 62 | **Implemented** (29-61% physics speedup) |
| GPU visibility pre-culling | 64 | **Verified complete** (feature already existed, documented) |

### Document Cleanup

Since all opportunities are resolved, this document should be deleted:

```bash
git rm docs/performance/FUTURE_OPTIMIZATIONS.md
git commit -m "docs: remove FUTURE_OPTIMIZATIONS.md (all items resolved)"
```

### Key Files to Reference

- `docs/performance/CHRONOLOGY.md` - Full optimization history (64 phases)
- `docs/performance/BENCHMARKS.md` - All benchmark data
- `docs/performance/SUCCESSFUL_OPTIMIZATIONS.md` - Implementation details
- `CLAUDE.md` - Project standards and workflow requirements

---

*Document created: 2026-01-26*
*Last updated: 2026-01-26 (Phase 64 verification)*
