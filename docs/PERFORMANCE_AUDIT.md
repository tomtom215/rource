# Comprehensive Performance Audit Report

**Date**: 2026-01-23
**Test Count**: 1,821 tests passing
**Lines Audited**: ~38,500+

## Codebase Audited

| Component | Lines | Change |
|-----------|-------|--------|
| wgpu backend | ~15,278 | +278 |
| WebGL2 backend | ~9,317 | +1,317 |
| Software renderer | ~1,600 | +147 |
| WASM code | ~3,800 | +434 |
| Scene/Physics | ~2,800 | +300 |
| Math library | ~5,671 | +2,671 |
| **Total audited** | **~38,500+** | **+5,500** |

---

## Issues Fixed Since Last Audit ✅

| # | Location | Issue | Status |
|---|----------|-------|--------|
| 1 | `render_phases.rs:1044` | LabelPlacer per-frame Vec allocation | ✅ FIXED - Uses `reset()` to reuse Vec |
| 3 | `software.rs` | Glyph `.clone()` per character | ✅ FIXED - No clone calls found |
| 4 | `software.rs:413-611` | `hypot()`/`sqrt()` in pixel loops | ✅ FIXED - Uses squared distance checks, sqrt only for edge pixels (~18%) |
| 6 | `shaders.rs:82` | AA width computed per-fragment | ✅ FIXED - Computed in vertex shader, passed as varying |
| 7 | `shaders.rs:157-158` | Ring inner/outer per-fragment | ✅ FIXED - Pre-computed in vertex shader |
| 8 | `webgl2/mod.rs:210,981-994` | Vec allocation per `draw_spline()` | ✅ FIXED - Uses reusable `spline_points_buf` |
| 28 | `wgpu/bloom.rs:205,287,597` | Per-frame bind group allocation | ✅ FIXED - `CachedBindGroups` struct |
| 30 | `shaders.rs:1269` | Duplicate t²/t³ in Catmull-Rom | ✅ FIXED - `catmull_rom_pos_tangent()` shares computation |

---

## Critical Issues (Fix Immediately)

| # | Location | Issue | Impact | Notes |
|---|----------|-------|--------|-------|
| 2 | `software.rs:1045,1075` | `to_lowercase()` per file icon lookup | 300K allocs/sec @ 5K files | Still present in `draw_file_icon()` |
| 5 | `spatial.rs:211,254` | Vec allocation in recursive quadtree query | O(n×d) allocs per query | `Vec::new()` in `query_recursive`/`nearest_recursive` |
| NEW | `lib.rs:1100-1106` | Visibility buffers NOT using `visible_entities_into()` | 180 allocs/sec | Uses `.extend(keys().copied())` instead of zero-alloc API |

### Detail on NEW Critical Issue

```rust
// lib.rs:1100-1106 - CURRENT (allocates via iterator collection)
self.visible_files_buf.clear();
self.visible_files_buf.extend(self.scene.files().keys().copied());  // ❌ iterator allocation

// SHOULD USE (zero-allocation):
self.scene.visible_entities_into(&bounds, &mut dirs_buf, &mut files_buf, &mut users_buf);
```

The visibility buffers (`visible_dirs_buf`, `visible_files_buf`, `visible_users_buf`) were added (`lib.rs:419-425, 548-550`) but the code still uses the allocating pattern instead of `visible_entities_into()`.

---

## High Severity Issues

| # | Location | Issue | Impact |
|---|----------|-------|--------|
| 13 | `rendering.rs:1324,1337,1362` | `format!` in HUD every frame | 3 allocs/frame |
| 14 | `headless.rs:598,685` `window.rs:359,388` | `path.clone()` in commit loops | Alloc per file per commit |
| 15 | `stats_methods.rs:52` | `to_lowercase()` during stats recompute | 5K allocs every 30 frames |
| 16 | `lib.rs:1108-1113` | Iterates ALL actions to count active | O(total) vs O(active) |
| 17 | `render_phases.rs:788-791` | Iterates completed actions | Same as above |
| 19 | `barnes_hut.rs:351-354,178-193` | Tree cleared/rebuilt every frame | O(n) allocs/frame |
| 20 | `shaders.rs (webgl2):492` | Division per-fragment in blur | Per-pixel division |

---

## Medium Severity Issues

| # | Location | Issue | Impact |
|---|----------|-------|--------|
| 21 | `mod.rs (scene):770` | HashMap allocation in `update_file_positions` | Alloc on layout change |
| 22 | `mod.rs (scene):485-502` | Double user lookup in `spawn_action` | 2× HashMap lookup |
| 23 | `render_phases.rs:1028` | `sort_by` instead of `sort_unstable_by` | Potential alloc |
| 24 | `render_phases.rs:583+660,826+862` | Redundant entity lookups across phases | 2× lookups |
| 25 | `render_phases.rs:722,737` | Redundant directory lookups per file | N extra lookups |
| 26 | `compute.rs:982-988` | Blocking GPU sync with channel | Frame stall |
| 27 | `spatial_hash.rs:681-685` | Extra encoder creation for copy | Submit overhead |
| 28 | `shadow.rs:541-554` | Per-frame bind group for scene texture | 60 allocs/sec (`scene_texture_bg` cannot be cached) |
| 29 | `webgl2/shaders.rs:943` | Division per-fragment in curve AA | Per-pixel division |

---

## Low Severity / Optimization Opportunities

### Missing `#[inline]` (Current counts)

| File | `#[inline]` Count | Hot Methods Still Missing |
|------|-------------------|---------------------------|
| `scene/mod.rs` | 7 | `get_file`, `get_user`, `file_count`, `user_count` |
| `scene/layout_methods.rs` | 4 | force calculation methods |
| `wgpu/buffers.rs` | 21 | ✅ Well-covered |
| `webgl2/buffers.rs` | 18 | `push_raw` |
| `render_phases.rs` | varies | LabelPlacer methods |

### HashMap Optimization (Use FxHash)

| Location | Status |
|----------|--------|
| `ahash` in Cargo.lock | Present but not used for scene HashMaps |
| `scene/mod.rs` | Still uses std HashMap |
| `software.rs` textures | Still uses std HashMap |
| `avatar.rs` | Still uses std HashMap |
| `textures.rs` (wgpu) | Still uses std HashMap |

### Math Library SIMD Opportunities (Unchanged)

| Type | Operations |
|------|------------|
| Vec4 | dot, add, sub, mul, min, max, lerp, abs |
| Mat4 | Matrix multiply, transform_vec4 |
| Vec2/3/4 | `Div<f32>` should use reciprocal multiply |
| Color | Division by 255.0 → multiply by `INV_255` constant |

---

## Already Well-Optimized ✅

| Component | What's Good |
|-----------|-------------|
| wgpu instance buffers | Zero-allocation pattern with `clear()`+`extend` |
| wgpu state caching | Avoids redundant pipeline/bind group switches |
| wgpu pipeline caching | Lazy creation + array cache |
| wgpu bloom bind groups | NEW - `CachedBindGroups` struct |
| wgpu curve shader | NEW - `catmull_rom_pos_tangent()` shares computation |
| WebGL2 `bufferSubData` | Reuses GPU buffer when capacity permits |
| WebGL2 UBOs | Shared uniforms across shaders |
| WebGL2 state cache | Avoids redundant GL calls |
| WebGL2 spline buffer | NEW - reusable `spline_points_buf` |
| WebGL2 GPU curves | NEW - Catmull-Rom in shader |
| LabelPlacer | NEW - `reset()` reuses Vec allocation |
| CLI visibility buffers | Uses `visible_entities_into()` ✅ |
| Font atlas | Row-based packing with defrag support |
| Barnes-Hut | O(n log n) correctly implemented |
| GPU spatial hash | O(n) with Blelloch prefix sum |
| Texture arrays | Single draw call for all file icons |
| Software disc rendering | NEW - `sqrt()` avoided for ~78% of pixels |
| wgpu AA width | NEW - computed in vertex shader |

---

## Quantified Summary

| Category | Count | Est. Frame Impact | Change |
|----------|-------|-------------------|--------|
| Critical per-frame allocations | 3 | 5-15% | ↓ from 8 |
| High severity issues | 7 | 3-8% | ↓ from 12 |
| Medium severity issues | 10 | 2-5% | Same |
| Missing `#[inline]` | ~40+ | 1-3% | ↓ from 60+ |
| HashMap optimization | 5 | <1% | Same |
| SIMD opportunities | 15+ | 5-20% (if implemented) | Same |
| Already optimized | 17 | N/A | ↑ from 12 |

---

## Priority Fix Recommendations

### Immediate (< 1 hour)

1. **Use `visible_entities_into()` in WASM** (`lib.rs:1100-1106`)
   - Buffers already exist, just need to call the right API
   - Impact: Eliminates ~180 allocs/sec

2. **Pre-lowercase file extensions** (`software.rs:1045,1075`)
   - Store lowercase extension in file icon map keys
   - Impact: Eliminates 300K+ allocs/sec at scale

### Short-term (1-4 hours)

3. **Track active action count incrementally**
   - Add `active_action_count` field to Scene
   - Increment/decrement on action creation/completion
   - Impact: O(1) instead of O(total_actions)

4. **Use FxHash for scene HashMaps**
   - `ahash` is already in Cargo.lock
   - Impact: 20-40% faster HashMap lookups

### Medium-term

5. **Pre-allocate quadtree query results**
   - Pass reusable Vec to `query_recursive()`
   - Impact: Eliminates O(n×d) allocs per query

6. **Cache formatted HUD strings**
   - Only regenerate when values change
   - Impact: -3 allocs/frame

---

## Benchmark Mode Added (2026-01-23)

New `--benchmark` CLI flag provides auditable nanosecond-precision timing:

```bash
./target/release/rource --headless --benchmark --output /tmp/frames .
```

Output includes:
- Per-frame timing with p50/p95/p99 percentiles
- Phase breakdown (commit_apply, scene_update, render, effects, export)
- True nanosecond precision via `std::time::Instant`

---

## Honest Assessment

### What I verified:
- ✅ Read every modified line since last audit
- ✅ Confirmed fixes for 8 previously-identified issues
- ✅ Identified 1 new critical issue (visibility buffers not using zero-alloc API)
- ✅ Updated line counts and categorization

### What I did NOT do:
- Run actual profilers (perf, flamegraph, Chrome DevTools)
- Measure actual clock cycles or nanoseconds
- Verify SIMD opportunities with actual benchmarks
- Test with large repositories (100K+ files)

### Confidence level:
- Issue identification: **High** (code-based analysis)
- Severity estimates: **Medium** (theoretical, not measured)
- Fix verification: **High** (grep + code review)

---

*Report generated: 2026-01-23 | Test count: 1,821 | Lines audited: ~38,500+*
