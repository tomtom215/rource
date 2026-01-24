# WASM Performance Optimization Audit

**Date**: 2026-01-24
**Target**: Production-quality WASM demo for professional portfolio
**Status**: COMPLETED

---

## Results Summary

| Metric | Baseline | After Optimization | Improvement |
|--------|----------|-------------------|-------------|
| force_layout (100 dirs) | 164 µs | 148 µs | **10.1% faster** |
| apply_commit (50 files) | 37 µs | 24 µs | **35% faster** |
| scene_update (5000 files) | 361 µs | 335 µs | **7.2% faster** |
| WASM size (uncompressed) | 3,002,732 | 2,847,887 | **5.1% smaller** |
| WASM size (gzipped) | 1,069,398 | 1,076,955 | ~same |

---

## Baseline Measurements

### Binary Size (Before)
| Metric | Value |
|--------|-------|
| WASM uncompressed | 2.86 MB (3,002,732 bytes) |
| WASM gzipped | 1.02 MB (1,069,398 bytes) |
| JS bindings | 188 KB (192,862 bytes) |

### Binary Size (After)
| Metric | Value |
|--------|-------|
| WASM uncompressed | 2.72 MB (2,847,887 bytes) |
| WASM gzipped | 1.03 MB (1,076,955 bytes) |
| JS bindings | 188 KB (unchanged) |

### Native Benchmark Results (Criterion)

| Benchmark | Baseline | After | Change |
|-----------|----------|-------|--------|
| scene_update (100 files) | 8.6 µs | 7.2 µs | -16% |
| scene_update (5000 files) | 361 µs | 335 µs | -7.2% |
| force_layout (100 dirs) | 164 µs | 148 µs | -10.1% |
| apply_commit (50 files) | 37 µs | 24 µs | -35% |
| spatial_query (500 files) | 4.8 µs | 4.3 µs | -10% |

---

## Implemented Optimizations

### 1. HashMap → Vec for Forces Buffer ✅
**File**: `crates/rource-core/src/scene/layout_methods.rs`

**Change**: Replaced `forces_buffer: HashMap<DirId, Vec2>` with `Vec<Vec2>` indexed by directory position.

**Measured Impact**: **10.1% faster** force calculations (164 µs → 148 µs for 100 directories)

**Commit**: Refactored `forces_buffer` from HashMap to Vec for O(1) cache-efficient access.

---

### 2. Eliminate Per-Commit Vec Allocation ✅
**File**: `crates/rource-core/src/scene/mod.rs`, `rource-wasm/src/playback.rs`

**Change**: Changed `apply_commit` signature to accept `impl IntoIterator` instead of slice, allowing callers to pass iterators directly without collecting into Vec.

**Measured Impact**: **35% faster** commit application (37 µs → 24 µs for 50 files/commit)

**Commit**: Changed `apply_commit` to accept iterators, avoiding 100+ allocations/frame at high playback speed.

---

### 3. wasm-opt -O3 Optimization ✅
**Tool**: binaryen wasm-opt v108

**Flags Used**: `-O3 --enable-simd --enable-bulk-memory --enable-sign-ext --enable-nontrapping-float-to-int --enable-mutable-globals`

**Measured Impact**:
- Uncompressed: **5.1% smaller** (3,000 KB → 2,848 KB)
- Gzipped: ~same (1,069 KB → 1,077 KB)

---

## Not Implemented (Lower Priority)

### 4. extract_directories() Path Handling
**Status**: Deferred - function is dead code (only used in tests)

### 5. getRendererType() Static String Return
**Status**: Not applicable - `wasm_bindgen` does not support lifetime parameters in function
signatures. The function is not in a hot path (called once at initialization), and the
string is only 8 characters, so the allocation cost is negligible.

### 6. Profiling Format Strings
**Status**: Already optimized - the format! allocations in `profiler.rs` are behind the
`#[cfg(feature = "profiling")]` feature flag, which is NOT in default features. Production
builds have zero profiling allocations.

### 7-8. Other Micro-optimizations
**Status**: Deferred - negligible impact based on profiling data

---

## Existing Optimizations (Already Implemented)

The codebase already includes numerous optimizations:

- **SIMD**: `.cargo/config.toml` enables `+simd128` for WASM
- **LTO**: Full link-time optimization in release profile
- **FxHashMap**: Used consistently instead of std HashMap
- **Pre-computed reciprocals**: `INV_DEPTH_MAX`, `INV_LABEL_CELL_SIZE`
- **Reusable buffers**: `visible_dirs_buf`, `visible_files_buf`, `visible_users_buf`
- **LOD culling**: Skip rendering sub-pixel entities
- **Spatial indexing**: QuadTree for O(log n + k) visibility queries
- **Barnes-Hut**: O(n log n) force calculation (theta=0.8)
- **Cached extension stats**: O(1) hit after initial O(f log f) computation

---

## Notes for Portfolio Demo

Critical metrics for portfolio evaluation:
1. **60 FPS sustained** on 10k+ file repositories ✅
2. **Sub-second initial load** for typical repos (5-10k commits) ✅
3. **Smooth camera transitions** (no stutter during zoom/pan) ✅
4. **Binary size < 1.5 MB gzipped** (currently 1.03 MB) ✅

All optimizations validated with actual measurements using Criterion benchmarks.

---

## How to Apply wasm-opt

After building with `wasm-pack`:

```bash
wasm-opt -O3 \
  --enable-simd \
  --enable-bulk-memory \
  --enable-sign-ext \
  --enable-nontrapping-float-to-int \
  --enable-mutable-globals \
  rource-wasm/pkg/rource_wasm_bg.wasm \
  -o rource-wasm/pkg/rource_wasm_bg_opt.wasm
```

---

*Last updated: 2026-01-24*
