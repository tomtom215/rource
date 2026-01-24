# Performance Audit Report - CLOSED

**Original Date**: 2026-01-23
**Closed Date**: 2026-01-24
**Final Test Count**: 1,836 tests passing

## Status: All Actionable Items Resolved ✅

This audit has been completed. All actionable items have been either:
- **Fixed**: Code changes applied
- **Verified Non-Issue**: Investigated and found to be false positives or already optimized
- **Won't Fix**: Architectural decisions that would require major restructuring for minimal gain

---

## Summary of Resolutions

### Critical Issues - All Resolved

| # | Issue | Resolution |
|---|-------|------------|
| 2 | `to_lowercase()` per file icon lookup | **Non-Issue**: Stack-based optimization exists; file icons disabled by default |
| 5 | Vec allocation in quadtree query | **Fixed**: Uses `query_for_each()` visitor pattern |
| NEW | Visibility buffers not using `visible_entities_into()` | **Fixed**: lib.rs:1094 uses zero-alloc API |

### High Severity Issues - All Resolved

| # | Issue | Resolution |
|---|-------|------------|
| 13 | `format!` in HUD every frame | **Fixed**: Phase 24 HudCache struct |
| 14 | `path.clone()` in commit loops | **Fixed**: Uses `.as_path()` references |
| 15 | `to_lowercase()` in stats recompute | **Non-Issue**: Extensions already stored lowercase |
| 16-17 | Iterates ALL actions to count active | **Fixed**: `active_action_count` tracked incrementally |
| 19 | Barnes-Hut tree rebuilt every frame | **Fixed**: `clear()` preserves structure, uses `replace_body()` |
| 20 | Division per-fragment in WebGL blur | **Fixed**: `u_texel_size` pre-computed as uniform |

### Medium Severity Issues - All Resolved

| # | Issue | Resolution |
|---|-------|------------|
| 21 | HashMap allocation in `update_file_positions` | **Acceptable**: Cold path, only runs on layout changes |
| 22 | Double user lookup in `spawn_action` | **Non-Issue**: Lookups are mutually exclusive paths |
| 23 | `sort_by` instead of `sort_unstable_by` | **Fixed**: Phase 26, 5 locations changed |
| 24-25 | Redundant entity lookups across phases | **Acceptable**: Intentional for proper layering (nodes before labels) |
| 26 | Blocking GPU sync with channel | **Won't Fix**: Required for synchronous GPU→CPU readback |
| 27 | Extra encoder creation for copy | **Won't Fix**: Standard wgpu pattern, minimal overhead |
| 28 | Per-frame bind group for scene texture | **Cannot Fix**: `scene_view` parameter varies per call |
| 29 | Division per-fragment in curve AA | **Fixed**: AA width computed in vertex shader |

### Low Severity - Addressed

| Category | Resolution |
|----------|------------|
| HashMap optimization | **Fixed**: Phase 26, FxHashMap in 7 rource-render files |
| Missing `#[inline]` | **Fixed**: Hot paths covered; added `try_place_with_fallback` |
| Math SIMD | **Future**: Needs profiling to verify benefit over compiler auto-vectorization |

---

## Optimizations Applied (Phases 1-26)

### Memory/Allocation Optimizations
- Zero-allocation visibility queries (`visible_entities_into()`)
- Zero-allocation bloom/shadow post-processing buffers
- Zero-allocation spline interpolation (streaming computation)
- Reusable instance buffers with `clear()` + `extend()`
- HUD string caching to avoid per-frame `format!`
- Barnes-Hut tree structure preservation across frames

### Hash Table Optimizations
- FxHashMap throughout rource-render (faster than std HashMap for small keys)
- FxHashMap in rource-core scene module

### Sorting Optimizations
- `sort_unstable_by` in 5 hot paths (avoids allocation overhead)

### GPU Optimizations
- Shader warmup/precompilation
- Instance buffer sub-data updates (WebGL2)
- Uniform Buffer Objects (WebGL2)
- Cached bind groups for bloom pipeline
- GPU visibility culling infrastructure (opt-in)
- GPU spatial hash physics O(n) (vs O(n²))
- GPU curve tessellation (single draw call)
- Texture arrays for file icons

### Rendering Optimizations
- LOD culling at multiple levels (files, directories, users, labels, branches)
- State caching (pipeline, VAO, texture binds)
- Frustum culling via quadtree
- `sqrt()` avoided for ~78% of disc pixels

---

## Current Performance Characteristics

| Metric | Value |
|--------|-------|
| Test count | 1,836 |
| WASM size (gzipped) | ~250KB |
| Native binary | ~3.8MB |
| Physics algorithm | O(n log n) Barnes-Hut (CPU) or O(n) spatial hash (GPU) |
| Visibility culling | O(log n) quadtree |
| Render batching | Instanced, single draw call per primitive type |

---

## Future Optimization Opportunities

These items are documented for future consideration but are not blocking:

### Math Library SIMD
- Vec4/Mat4 operations could use explicit SIMD intrinsics
- Requires benchmarking to verify benefit over compiler auto-vectorization
- WASM already has `+simd128` enabled

### Profiling Recommended Before Further Work
- Use actual profilers to identify real bottlenecks
- Test with large repositories (100K+ commits)
- Measure actual frame times, not theoretical estimates

---

*Audit closed: 2026-01-24 | All actionable items resolved*
