# Successful Optimizations

This document catalogs all implemented optimizations with measured improvements.
Organized by optimization category with implementation details and code locations.

---

## Table of Contents

1. [Algorithmic Optimizations](#algorithmic-optimizations)
2. [Arithmetic Optimizations](#arithmetic-optimizations)
3. [Memory Optimizations](#memory-optimizations)
4. [Compile-Time Optimizations](#compile-time-optimizations)
5. [Parser Optimizations](#parser-optimizations)
6. [WASM Optimizations](#wasm-optimizations)
7. [Compiler Optimizations](#compiler-optimizations)

---

## Algorithmic Optimizations

### Barnes-Hut O(n log n) Force Layout

**Phase**: 16
**Location**: `crates/rource-core/src/physics/barnes_hut.rs`
**Impact**: O(n^2) to O(n log n)

Implemented Barnes-Hut algorithm for force-directed layout using center-of-mass approximation
instead of pairwise force calculation.

**Configuration**:
- Theta parameter: 0.5-1.0 (accuracy/speed tradeoff)
- Default: Barnes-Hut for all simulations
- Fallback: Pairwise for < 100 directories

**Methods**:
```rust
calculate_repulsion_barnes_hut()  // O(n log n) repulsion
calculate_repulsion_pairwise()    // O(n²) exact (comparison/testing)
ForceConfig::pairwise()           // Preset for exact calculation
```

---

### DirNode HashSet Children

**Phase**: 40
**Location**: `crates/rource-core/src/scene/dir_node.rs`
**Impact**: O(n) to O(1) for membership tests

Replaced `Vec<DirId>` with `FxHashSet<DirId>` for directory children and files.

| Operation       | Before (Vec) | After (HashSet) |
|-----------------|--------------|-----------------|
| `has_child()`   | O(n)         | O(1)            |
| `add_child()`   | O(1)         | O(1)            |
| `remove_child()`| O(n)         | O(1)            |

**New Methods**:
```rust
children_len()   // O(1) - replaces O(n) iteration
has_child()      // O(1) - membership test
files_len()      // O(1) - replaces O(n) iteration
has_file()       // O(1) - membership test
```

---

### GPU Spatial Hash Physics

**Phase**: 22
**Location**: `crates/rource-render/src/backend/wgpu/spatial_hash.rs`
**Impact**: O(n^2) to O(n)

Implemented 9-pass GPU compute pipeline for O(n) force calculation.

**Pipeline**:

| Pass | Operation             | Complexity |
|------|-----------------------|------------|
| 1    | Clear cell counts     | O(cells)   |
| 2    | Count entities/cell   | O(n)       |
| 3    | Prefix sum (local)    | O(n)       |
| 4    | Prefix sum (partials) | O(cells)   |
| 5    | Prefix sum (add)      | O(n)       |
| 6    | Init scatter offsets  | O(cells)   |
| 7    | Scatter entities      | O(n)       |
| 8    | Calculate forces      | O(n)       |
| 9    | Integrate positions   | O(n)       |

**Comparison** (5,000 entities, 64x64 grid):
- Brute force: 25,000,000 comparisons
- Spatial hash: ~11,000 comparisons (2,200x reduction)

---

### QuadTree Spatial Index

**Phase**: 12
**Location**: `crates/rource-core/src/physics/spatial.rs`
**Impact**: O(n) to O(log n) queries

```rust
pub struct QuadTree<T: Clone> {
    bounds: Bounds,
    items: Vec<(Vec2, T)>,
    children: Option<Box<[Self; 4]>>,
    max_items: usize,  // 16
    max_depth: usize,  // 8
}
```

**Query Performance**: 35.7 ns for 500 entities (O(log n))

---

## Arithmetic Optimizations

### Fixed-Point Alpha Blending

**Phase**: 44
**Location**: `crates/rource-render/src/backend/software/renderer.rs`
**Impact**: 21% batch, 81% same-color

Alpha (0.0-1.0) represented as integers (0-256) for shift-based division.

```rust
// Before: floating-point
let new_r = ((src_r * alpha + dst_r * inv_alpha) as u32).min(255);

// After: fixed-point 8.8
let alpha_u16 = (src.a * 256.0) as u16;
let inv_alpha = 256 - alpha_u16;
let new_r = (src_r as u32 * alpha_u16 as u32 +
             dst_r as u32 * inv_alpha as u32) >> 8;
```

**Fast Paths**:
- Opaque (`alpha_u16 >= 256`): Early exit
- Transparent (`alpha_u16 == 0`): Early exit
- Same-color batch: 81% faster via comparison

---

### Force Normalization Sqrt Elimination

**Phase**: 47
**Location**: `crates/rource-core/src/physics/force.rs`
**Impact**: 1 sqrt eliminated per force pair

Reused pre-computed distance instead of calling `normalized()`.

```rust
// Before: Two sqrt operations
let magnitude = k / (d * d);
delta.normalized() * magnitude  // sqrt in normalized()

// After: Zero redundant sqrt
let scale = self.config.repulsion / (safe_distance * safe_distance * distance);
delta * scale
```

**Mathematical Equivalence**:
- Before: `(delta / |delta|) * (k / d²)`
- After: `delta * (k / d³)` using passed `distance`

---

### Perpendicular Vector Optimization

**Phase**: 48
**Location**: `crates/rource-render/src/visual.rs`
**Impact**: 72% operation, 14% throughput

Perpendicular vector `(-y, x)` has same magnitude as `(x, y)`.

```rust
// Before: normalizing then multiplying by length
let perp = Vec2::new(-dir.y, dir.x).normalized();
let offset = perp * length * tension;

// After: skip normalization (they cancel out)
let perp = Vec2::new(-dir.y, dir.x);
let offset = perp * tension;
```

**Proof**: `|(-dy, dx)| = sqrt(dy² + dx²) = sqrt(dx² + dy²) = |(dx, dy)|`

| Benchmark             | Baseline | Optimized | Improvement |
|-----------------------|----------|-----------|-------------|
| Perpendicular single  | 4.65 ns  | 1.28 ns   | -72%        |
| Batch 1000 curves     | 14.04 us | 12.29 us  | -12%        |

---

### Division to Multiplication

**Phase**: 34-35
**Locations**: Multiple
**Impact**: ~14 cycles saved per division

Replaced runtime divisions with multiplication by pre-computed reciprocals.

```rust
// Constants
pub const INV_255: f32 = 1.0 / 255.0;
pub const INV_DEPTH_MAX: f32 = 1.0 / DEPTH_MAX as f32;

// Before: division per pixel
let normalized = value as f32 / 255.0;

// After: multiplication
let normalized = value as f32 * INV_255;
```

---

### Anti-Aliasing Reciprocal

**Phase**: 43
**Location**: `crates/rource-render/src/backend/software/renderer.rs:503`
**Impact**: ~14 cycles per edge pixel

```rust
// Before: division per edge pixel
let t = (outer_radius - dist) / aa_range;

// After: multiplication by pre-computed reciprocal
let inv_aa_range = 1.0 / (2.0 * aa_width);  // computed once
let t = (outer_radius - dist) * inv_aa_range;
```

---

## Memory Optimizations

### Zero-Allocation Spatial Queries

**Phase**: 40
**Location**: `crates/rource-core/src/scene/spatial_methods.rs`
**Impact**: Zero heap allocations in hot path

Added `*_into()` variants that write to pre-allocated buffers.

| Allocating             | Zero-Allocation           |
|------------------------|---------------------------|
| `query_entities()`     | `query_entities_into()`   |
| `query_entities_circle()`| `query_entities_circle_into()` |
| `visible_file_ids()`   | `visible_file_ids_into()` |
| `visible_user_ids()`   | `visible_user_ids_into()` |
| `visible_directory_ids()`| `visible_directory_ids_into()` |

**QuadTree Addition**:
```rust
query_circle_for_each()  // Zero-allocation with visitor pattern
```

---

### HashMap to Vec Forces Buffer

**Phase**: 42
**Location**: `crates/rource-core/src/scene/layout_methods.rs`
**Impact**: 10.1% faster force layout

```rust
// Before: O(1) amortized but with hash overhead
forces_buffer: HashMap<DirId, Vec2>
self.forces_buffer.insert(dir_id, force);

// After: O(1) with direct indexing
forces_buffer: Vec<Vec2>
self.forces_buffer[i] = force;
```

---

### Iterator-Based apply_commit

**Phase**: 42
**Location**: `crates/rource-core/src/scene/mod.rs`
**Impact**: 35% faster, zero allocation

```rust
// Before: caller must allocate Vec
pub fn apply_commit(&mut self, author: &str, files: &[(&Path, ActionType)])

// After: accepts any iterator
pub fn apply_commit<'a, I>(&mut self, author: &str, files: I)
where I: IntoIterator<Item = (&'a Path, ActionType)>
```

At high playback speeds (10x), eliminates 100+ allocations per frame.

---

### String Interning Optimization

**Phase**: 40
**Location**: `crates/rource-vcs/src/intern.rs`
**Impact**: Reduced from 2 allocations to 1 allocation + 1 clone

```rust
// Before: s.to_owned() called twice
// After: Single to_owned() + one clone()
```

---

## Compile-Time Optimizations

### LUT-Based Random Direction

**Phase**: 58
**Location**: `crates/rource-core/src/physics/optimized.rs`
**Impact**: 13.9x faster

Replaced sin/cos with compile-time LUT for overlap push direction.

```rust
// 256-entry compile-time table
pub static RANDOM_DIRECTION_LUT: [(f32, f32); 256] = { /* Taylor series */ };

// Before: ~12 ns (sin/cos expensive)
let offset = Vec2::new((i as f32).sin() * 5.0, (j as f32).cos() * 5.0);

// After: ~0.87 ns (table lookup)
pub fn random_push_direction(i: usize, j: usize) -> Vec2 {
    let idx = ((i.wrapping_mul(17)) ^ (j.wrapping_mul(31))) & 0xFF;
    let (sin_val, cos_val) = RANDOM_DIRECTION_LUT[idx];
    Vec2::new(sin_val * 5.0, cos_val * 5.0)
}
```

| Method     | Time (1000) | Throughput   | Speedup |
|------------|-------------|--------------|---------|
| sin/cos    | 12.1 us     | 82 Melem/s   | 1.0x    |
| LUT-based  | 0.87 us     | 1.13 Gelem/s | 13.9x   |

---

### Color Conversion LUT

**Phase**: 45
**Location**: `crates/rource-math/src/color.rs`
**Impact**: 54% from_hex, 62% to_argb8

```rust
static U8_TO_F32_LUT: [f32; 256] = {
    let mut table = [0.0f32; 256];
    let mut i = 0u32;
    while i < 256 {
        table[i as usize] = i as f32 / 255.0;
        i += 1;
    }
    table
};

// Usage: table lookup vs division
U8_TO_F32_LUT[byte as usize]  // ~50% faster
```

---

### Fast Rounding with +0.5

**Phase**: 45
**Location**: `crates/rource-math/src/color.rs`
**Impact**: 62% faster

```rust
// Before: expensive .round() call (~18ns)
let r = (self.r.clamp(0.0, 1.0) * 255.0).round() as u32;

// After: +0.5 truncation (~6ns)
let r = (self.r.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
```

---

## Parser Optimizations

### VCS Parser Zero-Allocation

**Phase**: 46
**Location**: `crates/rource-vcs/src/parser/`
**Impact**: Zero heap allocations per line

Replaced `.split().collect::<Vec<_>>()` with iterator-based parsing.

```rust
// Before: Allocates Vec for every line
let parts: Vec<&str> = line.split('|').collect();
let timestamp = parts[0].parse()?;
let author = parts[1];

// After: Zero-allocation iterator
let mut parts = line.split('|');
let timestamp: i64 = parts.next()?.parse()?;
let author = parts.next()?;
```

**Files Modified**:
- `custom.rs:73-115` - parse_line()
- `mercurial.rs:143-200` - parse_template()
- `svn.rs:78-143` - parse_svn_date()
- `bazaar.rs:385-403` - parse_bzr_date()
- `stream.rs:72-82` - parse_commit_line()

---

## WASM Optimizations

### Large Repository Protection

**Phase**: 41
**Location**: `rource-wasm/src/lib.rs`
**Impact**: 5x faster load, eliminated crashes

**Solutions**:

| Solution          | Implementation                              |
|-------------------|---------------------------------------------|
| Commit limit      | `DEFAULT_MAX_COMMITS = 100_000`             |
| Adaptive prewarm  | 5-30 cycles based on file count             |
| Auto layout config| `LayoutConfig::massive_repo()` for >10k     |

**Prewarm Scaling**:

| First Commit Files | Prewarm Cycles |
|--------------------|----------------|
| < 1,000            | 30 (full)      |
| 1,000 - 10,000     | 15-30 (scaled) |
| 10,000 - 50,000    | 5-15 (reduced) |
| > 50,000           | 5 (minimum)    |

**API**:
```javascript
rource.setMaxCommits(limit)
rource.getMaxCommits()
rource.wasCommitsTruncated()
rource.getOriginalCommitCount()
```

---

### Bloom Strip-Based Processing

**Phase**: 43
**Location**: `crates/rource-render/src/effects/bloom.rs:486-575`
**Impact**: 6.6% faster

Replaced single-column vertical blur with 8-column strip processing.

```rust
// Before: poor cache locality (stride = width per pixel)
for x in 0..width {
    for y in 0..height {
        let p = src[y * width + x];  // cache miss each y
    }
}

// After: strip-based (8 columns together)
const STRIP_WIDTH: usize = 8;
for strip in 0..(width / STRIP_WIDTH) {
    let x_start = strip * STRIP_WIDTH;
    let mut sums_r = [0u32; 8];  // Fits in registers
    for y in 0..height {
        // Single cache line serves 8 column updates
    }
}
```

---

## Compiler Optimizations

### Rust 1.93.0 Upgrade

**Phase**: 50
**Impact**: Free performance gains

| Category         | Average | Best Case              |
|------------------|---------|------------------------|
| Color Conversion | -12%    | -34% (from_hex)        |
| Alpha Blending   | -30%    | -43% (blend_batch)     |
| Bloom Effect     | -5%     | -9% (bloom_blur)       |
| Scene Operations | -14%    | -17% (apply_commit)    |

**LLVM Improvements**:
- Better loop vectorization
- Improved division handling
- Collection operation optimization
- Memory access pattern optimization

---

### Build Configuration

**Phases**: 1-4
**Location**: `Cargo.toml`, `.cargo/config.toml`

```toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"
strip = true

[target.wasm32-unknown-unknown]
rustflags = ["-C", "target-feature=+simd128"]
```

**wasm-opt** (from build-wasm.sh):
```bash
wasm-opt \
    --enable-simd \
    --enable-bulk-memory \
    --enable-sign-ext \
    --enable-nontrapping-float-to-int \
    --enable-mutable-globals \
    -O3 --converge --low-memory-unused
```

---

## Summary by Impact

### Highest Impact (10x+)

| Optimization           | Phase | Improvement |
|------------------------|-------|-------------|
| LUT random direction   | 58    | 13.9x       |
| Same-color blend       | 44    | 5.3x        |

### High Impact (2-10x)

| Optimization           | Phase | Improvement |
|------------------------|-------|-------------|
| to_argb8 conversion    | 45    | 2.46x       |
| GPU spatial hash       | 22    | 2,200x      |
| DirNode membership     | 40    | O(n) to O(1)|
| Barnes-Hut             | 16    | O(n²) to O(n log n) |

### Medium Impact (30-99%)

| Optimization           | Phase | Improvement |
|------------------------|-------|-------------|
| from_hex LUT           | 45    | 54%         |
| Blend batch 43%        | 50    | 43%         |
| apply_commit iterator  | 42    | 35%         |

---

## Phases 1-26 Audit Resolutions

**Audit Date**: 2026-01-23 | **Closed**: 2026-01-24

A comprehensive performance audit identified and resolved the following issues:

### Critical Issues Resolved

| Issue | Resolution |
|-------|------------|
| `to_lowercase()` per file icon lookup | **Non-Issue**: Stack-based optimization exists |
| Vec allocation in quadtree query | **Fixed**: Uses `query_for_each()` visitor pattern |
| Visibility buffers not using zero-alloc API | **Fixed**: lib.rs:1094 uses `visible_entities_into()` |

### High Severity Issues Resolved

| Issue | Resolution |
|-------|------------|
| `format!` in HUD every frame | **Fixed**: Phase 24 HudCache struct |
| `path.clone()` in commit loops | **Fixed**: Uses `.as_path()` references |
| `to_lowercase()` in stats recompute | **Non-Issue**: Extensions already stored lowercase |
| Iterates ALL actions to count active | **Fixed**: `active_action_count` tracked incrementally |
| Barnes-Hut tree rebuilt every frame | **Fixed**: `clear()` preserves structure |
| Division per-fragment in WebGL blur | **Fixed**: `u_texel_size` pre-computed as uniform |

### Medium Severity Issues Resolved

| Issue | Resolution |
|-------|------------|
| HashMap allocation in `update_file_positions` | **Acceptable**: Cold path |
| Double user lookup in `spawn_action` | **Non-Issue**: Mutually exclusive paths |
| `sort_by` instead of `sort_unstable_by` | **Fixed**: Phase 26, 5 locations |
| Redundant entity lookups across phases | **Acceptable**: Intentional layering |
| Blocking GPU sync with channel | **Won't Fix**: Required for sync readback |
| Per-frame bind group for scene texture | **Cannot Fix**: Parameter varies per call |
| Division per-fragment in curve AA | **Fixed**: AA width in vertex shader |

### Low Severity Items

| Category | Resolution |
|----------|------------|
| HashMap optimization | **Fixed**: Phase 26, FxHashMap in 7 files |
| Missing `#[inline]` | **Fixed**: Hot paths covered |
| Math SIMD | **Future**: Needs profiling |

### Optimizations Applied (Phases 1-26)

**Memory/Allocation**:
- Zero-allocation visibility queries (`visible_entities_into()`)
- Zero-allocation bloom/shadow post-processing buffers
- Zero-allocation spline interpolation
- Reusable instance buffers with `clear()` + `extend()`
- HUD string caching
- Barnes-Hut tree structure preservation

**Hash Table**: FxHashMap in rource-render and rource-core scene module

**Sorting**: `sort_unstable_by` in 5 hot paths

**GPU**:
- Shader warmup/precompilation
- Instance buffer sub-data updates (WebGL2)
- Uniform Buffer Objects (WebGL2)
- Cached bind groups for bloom pipeline
- GPU visibility culling infrastructure
- GPU spatial hash physics O(n)
- GPU curve tessellation

**Rendering**:
- LOD culling at multiple levels
- State caching (pipeline, VAO, texture binds)
- Frustum culling via quadtree
- `sqrt()` avoided for ~78% of disc pixels

---

*Last updated: 2026-01-25*
