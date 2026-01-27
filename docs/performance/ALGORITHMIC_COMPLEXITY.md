# Algorithmic Complexity Audit - Rource Codebase

**Audit Date**: January 2026
**Last Updated**: 2026-01-26
**Test Count**: 2,100+ tests passing

> **See Also**: [COMPLEXITY_VERIFICATION.md](./COMPLEXITY_VERIFICATION.md) for empirical Big-O verification with scaling tests at 5 input sizes.

---

## Executive Summary

| Complexity | Function Count | Percentage | Notes |
|------------|----------------|------------|-------|
| O(1) | ~700 | 87% | Constant-time operations |
| O(log n) | ~30 | 4% | Spatial queries, tree operations |
| O(n) | ~50 | 6% | Iteration, parsing, rendering |
| O(n log n) | ~15 | 2% | Sorting, Barnes-Hut physics |
| O(n²) | ~5 | <1% | Pairwise force calculation (optional fallback) |

**Total Functions Analyzed**: 800+

---

## Table of Contents

1. [Critical Performance Boundaries](#critical-performance-boundaries)
2. [Key Algorithmic Optimizations](#key-algorithmic-optimizations)
3. [rource-math (155+ functions)](#rource-math-155-functions---100-o1)
4. [rource-vcs (Parsing & Caching)](#rource-vcs-parsing--caching)
5. [rource-core: Physics Module](#rource-core-physics-module)
6. [rource-core: Scene Module](#rource-core-scene-module)
7. [rource-core: Other Modules](#rource-core-other-modules)
8. [rource-render](#rource-render)
9. [rource-wasm (API Layer)](#rource-wasm-api-layer)
10. [Known O(n²) Functions](#known-on2-functions-verified)
11. [Complexity Summary by Category](#complexity-summary-by-category)

---

## Critical Performance Boundaries

### Constants That Bound Complexity

```rust
MAX_COMMITS_PER_FRAME = 100      // Bounds frame() loop to O(100)
DEFAULT_MAX_COMMITS = 100_000    // Truncates massive repos
MIN_PREWARM_CYCLES = 5           // Adaptive for large repos
MAX_PREWARM_CYCLES = 30          // Small repos get full prewarm
MAX_ACTIONS = 5000               // Prevents action accumulation
```

These constants ensure that even worst-case operations remain bounded and don't cause UI freezes.

---

## Key Algorithmic Optimizations

| Optimization | Before | After | Location |
|--------------|--------|-------|----------|
| DirNode children/files | O(n) `Vec::contains` | O(1) `FxHashSet` | `dir_node.rs` |
| Force calculation | O(n²) pairwise | O(n log n) Barnes-Hut | `force.rs` |
| Cache serialization | O(f·c) nested loop | O(f) `flat_map` | `cache.rs` |
| Spatial queries | O(n) linear scan | O(log n + k) QuadTree | `spatial.rs` |
| Visibility culling | O(total entities) | O(visible entities) | render backends |

---

## rource-math (155+ functions) - 100% O(1)

All mathematical operations work on fixed-size types (Vec2, Vec3, Vec4, Mat3, Mat4, Color).

| Module | Functions | Complexity | Notes |
|--------|-----------|------------|-------|
| `vec2.rs` | 35+ | O(1) | 2-component operations |
| `vec3.rs` | 30+ | O(1) | 3-component operations |
| `vec4.rs` | 25+ | O(1) | 4-component operations |
| `mat3.rs` | 20+ | O(1) | 3×3 matrix (9 elements fixed) |
| `mat4.rs` | 25+ | O(1) | 4×4 matrix (16 elements fixed) |
| `color.rs` | 25+ | O(1) | RGBA/HSL conversions |
| `rect.rs` | 30+ | O(1) | Bounds/Rect operations |

---

## rource-vcs (Parsing & Caching)

### Parsers

All parsers follow the same complexity pattern:

| Parser | `parse_str()` | `can_parse()` | Notes |
|--------|---------------|---------------|-------|
| GitParser | O(n + c log c) | O(k) k≈20 | n=input size, c=commits, final sort |
| CustomParser | O(n + c log c) | O(k) k≈10 | HashMap grouping + sort |
| SvnParser | O(m + c log c) | O(m) | XML tag extraction |
| MercurialParser | O(n·m + c log c) | O(m) | Line parsing + sort |
| BazaarParser | O(n·m) | O(n·m) | No final sort needed |

### Cache Operations

| Function | Complexity | Justification |
|----------|------------|---------------|
| `VisualizationCache::to_bytes()` | O(c + f + p·s) | c=commits, f=files, p=paths, s=segments |
| `VisualizationCache::from_bytes()` | O(m) | m=serialized data size |
| `build_payload()` | O(c + f) | Phase 39 optimized: flat_map, not nested |
| `reconstruct_store()` | O(c + f + p·s) | Path reconstruction |

### Interning

| Function | Complexity | Justification |
|----------|------------|---------------|
| `StringInterner::intern()` | O(m) | m=string length (hash computation) |
| `StringInterner::resolve()` | O(1) | Vec index lookup |
| `PathInterner::intern()` | O(m) | m=path length, split + intern segments |
| `PathInterner::resolve()` | O(m) | Join segments |

---

## rource-core: Physics Module

### QuadTree (`spatial.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `insert()` | O(log n) amortized | Tree depth bounded |
| `query()` | O(log n + k) | k=results found |
| `query_circle()` | O(log n + k) | Bounds + distance filter |
| `query_for_each()` | O(log n + k) | Zero-allocation variant |
| `nearest()` | O(log n) typical | Branch-and-bound pruning |
| `total_items()` | O(n) | Recursive count |
| `clear()` | O(1) | Drops children pointers |

### ForceSimulation (`force.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `apply_to_slice()` | O(n log n) **DEFAULT** | Barnes-Hut enabled by default |
| `calculate_repulsion_barnes_hut()` | O(n log n) | Tree build + n queries |
| `calculate_repulsion_pairwise()` | O(n²) | **Optional fallback only** |
| `calculate_attraction_forces()` | O(n) | Single parent lookup per node |

### BarnesHutTree (`barnes_hut.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `insert()` | O(log n) average | MAX_DEPTH=16 limit |
| `calculate_force()` | O(log n) typical | theta=0.8 default |
| `clear()` | O(n) | Recursive reset (preserves structure) |

---

## rource-core: Scene Module

### Scene (`mod.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `get_file()`, `get_user()` | O(1) | HashMap lookup |
| `get_or_create_user()` | O(1) | HashMap insert |
| `create_file()` | O(d) | d=path depth |
| `apply_commit()` | O(f·d) | f=files, d=avg depth |
| `update()` | O(f + u + d + a) | Full frame update |
| `spawn_action()` | O(a) | a=active actions per user (typically <5) |

### DirTree (`tree.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `get()`, `get_mut()` | O(1) | Vec index + generation check |
| `get_or_create_path()` | O(p) | p=path components, HashMap lookup per |
| `compute_radial_layout()` | O(d) | d=directories |
| `calculate_subtree_weights()` | O(d log d) | Sort by depth |
| `remove()` | O(d_r + h) | d_r=descendants |

### DirNode (`dir_node.rs`) - Phase 40 Optimized

| Function | Complexity | Notes |
|----------|------------|-------|
| `add_child()`, `remove_child()` | O(1) | FxHashSet operations |
| `add_file()`, `remove_file()` | O(1) | FxHashSet operations |
| `has_child()`, `has_file()` | O(1) | FxHashSet contains |
| `children_len()`, `files_len()` | O(1) | FxHashSet len |

### Spatial Methods (`spatial_methods.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `rebuild_spatial_index()` | O(n log n) | n=total entities |
| `query_entities()` | O(log n + k) | k=results |
| `visible_file_ids()` | O(log n + k) | Spatial + filter |
| `visible_entities_into()` | O(log n + k) | Zero-allocation |

### Layout Methods (`layout_methods.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `apply_force_directed_layout()` | O(d log d) or O(d²) | Adaptive: Barnes-Hut if d≥100 |

### Stats Methods (`stats_methods.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `file_extension_stats()` | O(f log f) | f=files, sort by count |
| `compute_entity_bounds()` | O(d + f + u) | Cached, recomputed when dirty |

---

## rource-core: Other Modules

### Camera (`camera.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| All getters/setters | O(1) | Field access |
| `update()` | O(1) | Smooth interpolation |
| `visible_bounds()` | O(1) | Arithmetic |
| `CameraTracker::weighted_center()` | O(n) | n=tracked positions |
| `CameraTracker::tracked_bounds()` | O(n) | Min/max scan |

### Animation (`tween.rs`, `spline.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `ease()` (26 easing functions) | O(1) | Fixed arithmetic per type |
| `Tween::update()`, `value()` | O(1) | Interpolation |
| `CatmullRomSpline::from_points()` | O(n) | n=points |
| `CatmullRomSpline::interpolate()` | O(1) | Single span evaluation |
| `CatmullRomSpline::ensure_cache()` | O(k·s) | k=spans, s=segments |
| `CatmullRomSpline::closest_point()` | O(m) | m=cached points |

### Entity (`entity.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `IdAllocator::allocate()` | O(1) | Pop from free list or increment |
| `IdAllocator::free()` | O(1) | Push to free list |
| `IdAllocator::clear()` | O(n) | Vec clear |

### Config (`config_*.rs`)

| Function | Complexity | Notes |
|----------|------------|-------|
| `load_env()`, `merge_env()` | O(1) | ~50 env var reads, each O(1) |
| `load_config_file()` | O(k) | k=file size |

---

## rource-render

### Software Renderer (Pixel-based)

| Function | Complexity | Variables | Notes |
|----------|------------|-----------|-------|
| `draw_disc()` | O(r²) | r=radius | Bounding box iteration |
| `draw_circle_aa()` | O((r+w)²) | r=radius, w=width | Ring iteration |
| `draw_line_aa()` | O(length) | line length | Xiaolin Wu algorithm |
| `draw_text()` | O(c × g) | c=chars, g=glyph area | Per-character rasterization |
| `clear()` | O(n) | n=pixels | Fill buffer |

### WebGL2/wgpu Renderers (GPU-accelerated)

| Function | CPU Complexity | Notes |
|----------|----------------|-------|
| `draw_disc()` | O(1) | Instance buffer append |
| `draw_circle()` | O(1) | Instance buffer append |
| `draw_line()` | O(1) | Instance buffer append |
| `draw_spline()` | O(p) | p=control points |
| `draw_text()` | O(c) | c=characters, cached glyphs |
| `flush()` | O(instances) | GPU processes in parallel |

### Effects (bloom, shadow)

| Effect | Complexity | Notes |
|--------|------------|-------|
| Threshold extraction | O(n) | n=pixels |
| Blur pass (separable) | O(n × p) | p=passes (typically 2-3) |
| Downscale | O(n/d²) | d=downscale factor |

---

## rource-wasm (API Layer)

### Critical Performance Functions

| Function | Complexity | Location | Impact |
|----------|------------|----------|--------|
| `frame()` | O(c + d + v) | `lib.rs:819` | c≤100 bounded |
| `seek()` | O(c × e) | `playback.rs:102` | **UI FREEZE RISK** |
| `loadGitLog()` | O(n × k) | `lib.rs:724` | Initial load |
| `get_authors()` | O(c + a log a) | `authors.rs:114` | c=commits scan |
| `get_commit_directory_count()` | O(c × f × d) | `stats.rs:256` | Triple nested |
| `render()` | O(v + r) | `lib.rs:1347` | v=visible only |
| `auto_fit_camera()` | O(e) | `lib.rs:1294` | Every frame if enabled |

### O(1) API Functions (Majority)

All simple getters, setters, and state queries:
- `getFps()`, `getFrameTimeMs()`, `isPlaying()`, `commitCount()`
- `setSpeed()`, `setZoom()`, `setAutoFit()`
- `currentCommit()`, `getVisibleFiles()`, `getTotalEntities()`
- Camera controls, settings, visibility toggles

---

## Known O(n²) Functions (Verified)

Only 5 functions have O(n²) or worse complexity. All are either optional fallbacks, one-time operations, or diagnostic functions:

| Function | Complexity | When Used |
|----------|------------|-----------|
| `calculate_repulsion_pairwise()` | O(n²) | Only if `use_barnes_hut=false` |
| `get_commit_directory_count()` | O(c×f×d) | Stats API, not hot path |
| `seek()` | O(c×e) | User-triggered seek |
| `step_forward/backward()` | O(c×e) | Calls seek() internally |

---

## Complexity Summary by Category

| Category | Best | Typical | Worst | Bottleneck |
|----------|------|---------|-------|------------|
| Math operations | O(1) | O(1) | O(1) | None - all constant |
| Entity lookups | O(1) | O(1) | O(1) | HashMap |
| Spatial queries | O(log n) | O(log n + k) | O(n) | QuadTree |
| Force physics | O(n) | O(n log n) | O(n²) | Barnes-Hut default |
| Commit parsing | O(n) | O(n + c log c) | O(n·m) | Final sort |
| Frame render | O(v) | O(v + effects) | O(n) | Visibility culling |
| Seek operation | O(1) | O(c × e) | O(c × e) | No optimization |

---

## Optimization History

For detailed optimization history through 59 phases, see the [performance documentation](./README.md).

Key milestones:
- **Phase 16**: Barnes-Hut O(n log n) physics
- **Phase 22**: O(n) GPU spatial hash physics
- **Phase 39**: O(f) cache serialization (was O(f·c))
- **Phase 40**: O(1) DirNode children/files operations
- **Phase 41**: Bounded frame processing with commit limits
- **Phase 44-45**: Fixed-point blending and LUT color conversion
- **Phase 58**: LUT-based random direction (13.9x faster)
- **Phase 59**: File glow conditional rendering (scenario-dependent improvement)

---

*Audit covers all 5 crates with 800+ functions analyzed. All complexities verified by code inspection.*
*Last updated: 2026-01-27*
