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
7. [Rendering Optimizations](#rendering-optimizations)
8. [Browser-Specific Optimizations](#browser-specific-optimizations)
9. [Dependency Optimizations](#dependency-optimizations)
10. [Compiler Optimizations](#compiler-optimizations)
11. [Formal Verification Optimizations](#formal-verification-optimizations)

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

**Methods** (in `crates/rource-core/src/physics/force.rs`):
```rust
calculate_repulsion_barnes_hut()  // O(n log n) repulsion
calculate_repulsion_pairwise()    // O(n²) exact (comparison/testing)
ForceConfig::pairwise()           // Preset for exact calculation
```

---

### Adaptive Barnes-Hut Theta

**Phase**: 62
**Location**: `crates/rource-core/src/physics/barnes_hut.rs`
**Impact**: 29-61% speedup for medium-to-large scenes

Implemented adaptive theta parameter selection based on entity count. The theta parameter
controls accuracy/speed tradeoff in Barnes-Hut approximation.

**Before** (fixed θ=0.8):
```rust
let theta = 0.8;  // Same for all scene sizes
```

**After** (adaptive θ):
```rust
pub fn calculate_adaptive_theta(entity_count: usize) -> f32 {
    if entity_count <= 200 {
        return 0.8;  // Small scenes: accurate
    }
    // Logarithmic scaling to 1.5 for large scenes
    let scale_factor = (entity_count as f32 / 200.0).log2() / 25.0f32.log2();
    (0.8 + 0.7 * scale_factor.clamp(0.0, 1.0)).clamp(0.7, 1.5)
}
```

**Benchmark Results**:

| Entities | Fixed θ=0.8 | Adaptive θ | Improvement |
|----------|-------------|------------|-------------|
| 100      | 26.10 µs    | 26.83 µs   | ~0% (same)  |
| 500      | 296.71 µs   | 210.62 µs  | **-29.0%**  |
| 1000     | 714.81 µs   | 419.96 µs  | **-41.2%**  |
| 5000     | 4.25 ms     | 1.64 ms    | **-61.4%**  |

**Mathematical Basis**:
- θ(n) = 0.8 + 0.7 × clamp(log₂(n/200) / log₂(25), 0, 1)
- Logarithmic scaling prevents sudden jumps
- Clamped to [0.7, 1.5] for safety

**API**:
```rust
// Main function
pub fn calculate_adaptive_theta(entity_count: usize) -> f32;

// With FPS consideration (boosts theta when FPS drops)
pub fn calculate_adaptive_theta_with_fps(
    entity_count: usize,
    current_fps: Option<f32>,
    target_fps: f32,
) -> f32;

// ForceConfig field
pub adaptive_theta: bool,  // Default: true
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

### Label Collision Detection Optimization

**Phase**: 65
**Location**: `rource-wasm/src/render_phases/`
**Impact**: 90× faster grid reset, 7-8× sorting improvement, zero allocations

Optimized label collision detection for 42,000 FPS target (23.8µs frame budget).
The original implementation consumed 82% of frame budget before any rendering.

**Problem Analysis** (at 23.8µs budget):

| Operation | Before | Budget % |
|-----------|--------|----------|
| Grid reset | 17,942 ns | 75.4% |
| Beam sorting | ~850 ns | 3.6% |
| Label sorting | ~720 ns | 3.0% |
| Per-frame allocs | ~100 ns | 0.4% |
| **Total** | **~19.6 µs** | **82.4%** |

**Solution 1: Generation Counter Pattern**

Instead of clearing 1024 grid cells each frame, increment a generation counter.
Entries are stale if their generation doesn't match current.

```rust
pub struct LabelPlacer {
    grid: Vec<Vec<Vec<(usize, u32)>>>,  // (index, generation) tuples
    generation: u32,
    stale_entry_count: usize,
}

pub fn reset(&mut self) {
    self.stale_entry_count += self.placed_labels.len() * 2;
    self.placed_labels.clear();
    self.generation = self.generation.wrapping_add(1);

    // Periodic compaction when stale_entry_count > 2048
    if self.stale_entry_count > LABEL_GRID_STALE_THRESHOLD {
        self.compact_grid();
    }
}
```

**Result**: 17,942 ns → 198 ns (**90× faster**)

**Solution 2: Partial Selection with select_nth_unstable_by**

For beam limiting (15 beams) and label priority, only need top-N elements.
`select_nth_unstable_by` provides O(n) partial ordering vs O(n log n) full sort.

```rust
// O(n) partial selection instead of O(n log n) full sort
let select_count = MAX_CONCURRENT_BEAMS.min(beams.len());
if select_count > 0 && select_count < beams.len() {
    beams.select_nth_unstable_by(select_count - 1, |a, b| {
        b.priority.partial_cmp(&a.priority).unwrap_or(Ordering::Equal)
    });
}
```

**Sorting Results**:
- Beam sorting: ~850 ns → 99 ns (**8.6× faster**)
- User label sorting: ~720 ns → 99 ns (**7.3× faster**)
- File label sorting: ~680 ns → 95 ns (**7.2× faster**)

**Solution 3: Reusable Buffers**

Eliminated per-frame Vec allocations:

```rust
// Before: Allocates new Vec every frame
let mut candidates: Vec<(UserId, Vec2, f32, f32, f32)> = Vec::new();

// After: Reuses pre-allocated buffer in Rource struct
self.user_label_candidates_buf.clear();
```

**Total Overhead Reduction**:
- Before: ~19.6 µs (82.4% of budget)
- After: ~0.7 µs (2.9% of budget)
- Savings: **18.9 µs/frame** (79.5% budget recovered)

---

### Label Width Estimation Fix

**Phase**: 68
**Location**: `crates/rource-render/src/label.rs`, `rource-wasm/src/render_phases/`
**Impact**: 22.4× more accurate width estimation, eliminates UTF-8 label overlaps

Fixed critical bug in `estimate_text_width()` where `text.len()` (bytes) was used instead
of `text.chars().count()` (characters), causing severe width overestimation for UTF-8 text.

**Root Cause**:
- UTF-8 encoding: multi-byte characters inflate `len()` vs actual character count
- Wrong factor: 0.75 used instead of empirically-measured 0.6001

**Before (broken)**:
```rust
pub fn estimate_text_width(text: &str, font_size: f32) -> f32 {
    text.len() as f32 * font_size * 0.75  // bytes, wrong factor
}
// "田中太郎": 12 bytes × 12px × 0.75 = 108px (actual: 28.8px, error: +275%)
```

**After (fixed)**:
```rust
const MONOSPACE_WIDTH_FACTOR: f32 = 0.62;  // 0.6001 + 3% safety margin

pub fn estimate_text_width(text: &str, font_size: f32) -> f32 {
    text.chars().count() as f32 * font_size * MONOSPACE_WIDTH_FACTOR
}
// "田中太郎": 4 chars × 12px × 0.62 = 29.76px (actual: 28.8px, error: +3.3%)
```

**Accuracy Improvement**:

| Metric | OLD Method | NEW Method | Improvement |
|--------|------------|------------|-------------|
| Average Error | 74.4% | 3.3% | **22.4× more accurate** |
| Max Error | 400% (emoji) | 3.3% | **121× more accurate** |
| UTF-8 Handling | Broken | Correct | Fixed |

**Example Improvements** (realistic Git labels):

| Label | OLD Error | NEW Error |
|-------|-----------|-----------|
| main.rs | +25% | +3.3% |
| 日本語ファイル.txt | +160% | +3.3% |
| 田中太郎 | +275% | +3.3% |
| María García | +46% | +3.3% |

**Performance**: Sub-nanosecond (277-309 ps), negligible frame impact (<0.1%)

**Mathematical Verification**:
- Measured Roboto Mono factor: `advance_width` / `font_size` = 7.201 / 12.0 = 0.6001
- Safety margin: 3% overestimate to prevent false collision negatives
- Final factor: 0.6001 × 1.033 ≈ 0.62

**UX Impact**: Labels no longer overlap for international file names and user names,
critical for Git repositories with non-ASCII content.

---

### Disc Overlap Prevention

**Phase**: 69
**Location**: `crates/rource-core/src/scene/dir_node.rs`, `crates/rource-core/src/scene/layout_methods.rs`
**Impact**: Eliminates disc overlap for files and directories with no significant performance regression

Implemented two overlap prevention mechanisms to eliminate visual disc overlap
that persisted even after the physics simulation settled.

**Problem Analysis**:

1. **File Discs**: Files in narrow angular sectors positioned too close, causing overlap
2. **Directory Discs**: Hardcoded `FORCE_MIN_DISTANCE = 5.0` while directory radii scale
   with child count (`5.0 + ln(count) × 10.0`), allowing larger directories to overlap

**File Angular Spacing Issue (before fix)**:

| Files in Sector | Arc Length | Disc Diameter | Overlap? |
|-----------------|------------|---------------|----------|
| 10              | 9.08 px    | 10.0 px       | YES      |
| 20              | 4.30 px    | 10.0 px       | YES      |
| 50              | 1.67 px    | 10.0 px       | YES      |

**Directory FORCE_MIN_DISTANCE Issue (before fix)**:

| Children | Dir Radius | Min for No Overlap | FORCE_MIN_DISTANCE | Gap |
|----------|------------|--------------------|--------------------|-----|
| 3        | 16.0       | 32.0               | 5.0                | +27 |
| 10       | 28.0       | 56.1               | 5.0                | +51 |
| 100      | 51.1       | 102.1              | 5.0                | +97 |

**Solution 1: File Angular Spacing Enforcement**:

```rust
// Calculate minimum distance needed to fit all files without overlap
let min_distance_for_no_overlap = gap_count * 2.0 * file_radius / usable_span;
let file_distance = base_file_distance.max(min_distance_for_no_overlap);
```

**Solution 2: Dynamic FORCE_MIN_DISTANCE**:

```rust
// Phase 69: Dynamic minimum distance based on actual disc radii
let min_distance = (radius_i + radius_j).max(FORCE_MIN_DISTANCE);
let min_distance_sq = min_distance * min_distance;
let clamped_dist_sq = distance_sq.max(min_distance_sq);
```

**Benchmark Results** (criterion, 100 samples):

| Directories | Baseline | After | Change |
|-------------|----------|-------|--------|
| 10          | 2.79 µs  | —     | Improved |
| 50          | 11.71 µs | 12.19 µs | +3.25% |
| 100         | 125.87 µs | 125.44 µs | +1.24% (no change) |
| 200         | 132.21 µs | 119.59 µs | **−7.59%** |

**Mathematical Verification**:

For file overlap prevention:
```
Arc length = angular_spacing × distance
For no overlap: arc_length ≥ 2 × file_radius (diameter)
Therefore: distance ≥ 2 × radius × (n-1) / usable_span
```

For directory overlap prevention:
```
For two circles not to overlap:
distance_between_centers ≥ radius_a + radius_b
```

**UX Impact**: Discs no longer overlap visually, providing clearer visualization
of directory structure and file distributions.

---

### Avatar Texture Array Batching

**Phase**: 61
**Location**: `crates/rource-render/src/backend/wgpu/textures.rs`
**Impact**: O(n) to O(1) draw calls, 93% flush overhead reduction

Replaced per-texture HashMap<TextureId, InstanceBuffer> with GPU texture array batching.

**Before (per-texture path)**:
```rust
// Each texture required separate draw call
textured_quad_instances: HashMap<TextureId, InstanceBuffer>

// Flush iterates all textures
for (texture_id, buffer) in &self.textured_quad_instances {
    set_bind_group(texture_id.bind_group);  // GPU state change
    draw(buffer);                            // Draw call
}
// Result: n textures = n draw calls
```

**After (texture array path)**:
```rust
// Single texture array with layer indices
avatar_texture_array: Option<AvatarTextureArray>
avatar_quad_instances: InstanceBuffer  // Single buffer

// Flush is single draw call
set_bind_group(avatar_array.bind_group);  // One state change
draw(avatar_quad_instances);               // One draw call
// Result: n textures = 1 draw call
```

**Benchmark Results** (300 avatars):

| Metric              | Per-Texture | Texture Array | Improvement |
|---------------------|-------------|---------------|-------------|
| Instance population | 3.94 µs     | 1.72 µs       | -56.3%      |
| Flush overhead      | 875.50 ns   | 62.86 ns      | -92.8%      |
| Full frame          | 4.81 µs     | 1.97 µs       | -59.0%      |
| Draw calls          | 300         | 1             | -99.7%      |

**Mathematical Proof**:
- Per-texture: T(n) = 1.06n ns (linear, O(n))
- Texture array: T(n) = 360 ps (constant, O(1))
- Speedup at n=300: 300/1 = 300x draw call reduction

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

### Zero-Copy Stats Buffer

**Phase**: 84
**Location**: `rource-wasm/src/lib.rs`, `rource-wasm/src/wasm_api/stats.rs`, `rource-wasm/www/js/core/stats-buffer.js`
**Impact**: 618.6x Rust-side speedup (778.46 ns → 1.26 ns per stats update)

Replaced `format!()` JSON serialization + `JSON.parse()` with direct `f32` buffer
writes read via `Float32Array` view over WASM linear memory.

| Path | Cost (ns/op) | Operations |
|------|-------------|-----------|
| JSON (before) | 778.46 | `format!()` + `String` alloc + WASM→JS copy + `JSON.parse()` |
| Buffer (after) | 1.26 | 20 `f32` store instructions, JS `Float32Array` read |

**Methodology**: 100,000 iterations, `f64`-precision division, 3 independent runs.

---

## Rendering Optimizations

### File Glow LOD Culling and Radius Reduction

**Phase**: 70
**Location**: `rource-wasm/src/render_phases/`, `rource-cli/src/rendering.rs`
**Impact**: 43.75% reduction in glow pixel area + LOD culling for small files

Optimized file glow rendering through two complementary strategies:

1. **LOD Culling**: Skip glow rendering when `effective_radius < 3.0` (glow imperceptible)
2. **Radius Reduction**: Reduce glow radius from 2.0x to 1.5x effective_radius

**Before (Phase 59)**:
```rust
// Glow for all touched files, regardless of size
if is_touched {
    let glow_color = color.with_alpha(0.25 * alpha);
    renderer.draw_disc(screen_pos, effective_radius * 2.0, glow_color);
}
```

**After (Phase 70)**:
```rust
// LOD culling + reduced radius
if is_touched && effective_radius >= 3.0 {
    let glow_color = color.with_alpha(0.25 * alpha);
    renderer.draw_disc(screen_pos, effective_radius * 1.5, glow_color);
}
```

**Pixel Area Reduction** (Mathematical Proof):

```
Glow disc area = pi * r_glow^2

Before: A_before = pi * (2.0 * r_eff)^2 = 4.0 * pi * r_eff^2
After:  A_after  = pi * (1.5 * r_eff)^2 = 2.25 * pi * r_eff^2

Reduction = (A_before - A_after) / A_before
          = (4.0 - 2.25) / 4.0
          = 1.75 / 4.0
          = 43.75%
```

**Benchmark Results**:

| Metric | Value | Notes |
|--------|-------|-------|
| LOD culling decision overhead | 0 ns/file | Negligible (single comparison) |
| Glow area reduction | 43.75% | (2.0^2 - 1.5^2) / 2.0^2 |
| Files affected by LOD culling | Variable | Depends on zoom level |

**Test Coverage**:
- `test_glow_lod_culling_threshold_boundary` - Threshold behavior
- `test_glow_radius_calculation` - Area reduction verification
- `test_glow_lod_culling_condition` - Condition logic
- `bench_glow_lod_culling` - Decision overhead measurement

**Visual Impact**: Glow remains visible for normal-sized files, slightly tighter around file discs.
Small files (when zoomed out) no longer have imperceptible glow rendered.

---

### SIMD-Friendly Batch Blending Infrastructure

**Phase**: 71
**Location**: `crates/rource-render/src/backend/software/optimized.rs`
**Impact**: +4% blend throughput; infrastructure for future SIMD optimizations

Implemented batch blending function `blend_scanline_uniform` optimized for LLVM auto-vectorization with WASM SIMD128.

**Key Features**:
1. Processes 4 pixels per iteration (matches SIMD128 width)
2. Pre-computes source terms outside loop
3. Unrolled loop structure enables SLP vectorization

```rust
pub fn blend_scanline_uniform(
    pixels: &mut [u32],
    start_idx: usize,
    count: usize,
    src_r: u8, src_g: u8, src_b: u8,
    alpha: u32,
) {
    // Pre-compute source terms
    let src_r_alpha = src_r as u32 * alpha;
    let inv_alpha = 256 - alpha;

    // Process 4 pixels at a time
    for chunk_idx in 0..chunks {
        let base = chunk_idx * 4;
        // Load, blend, store 4 pixels (enables SIMD)
    }
}
```

**Benchmark Results**:

| Metric | Value |
|--------|-------|
| `blend_scanline_uniform` | 1.72 ns/pixel (1000 pixel batch) |
| Blend throughput improvement | +4% (criterion benchmark) |
| Disc rendering overhead | -2% (run tracking cost) |

**Test Coverage**: 17 new tests
- Batch blend correctness (8 tests)
- SIMD disc parity with original (7 tests)
- Performance benchmarks (2 tests)

**Future Applications**:
- Scanline-based effects (blur, bloom)
- Text rendering with solid fills
- Large disc rendering (radius > 50)

---

### Pre-Computed Inner Bounds Disc Rendering

**Phase**: 72
**Location**: `crates/rource-render/src/backend/software/optimized.rs`
**Impact**: 3.06x to 3.91x speedup for disc rendering (r≥12)

Improved on Phase 71's `draw_disc_simd` by replacing runtime run-length tracking with
**pre-computed inner bounds per scanline** using circle geometry.

**Problem with Phase 71**:
- `Option<i32>` tracking added ~10 ops per pixel
- Double-processing bug on edge-only scanlines

**Solution**:
```rust
// Pre-compute inner bounds (one sqrt per scanline)
let (inner_left, inner_right) = if dy_sq < inner_radius_sq {
    let dx_inner = (inner_radius_sq - dy_sq).sqrt();
    (ceil(cx - dx_inner + 0.5), floor(cx + dx_inner - 0.5))
} else {
    (max_x + 1, max_x)  // No inner region
};

// Process: left edge → inner batch → right edge
```

**Criterion Benchmark Results (100 samples, 95% CI)**:

| Disc Size | Original | Phase 72 | Speedup |
|-----------|----------|----------|---------|
| r=50 | 31.213 µs [31.010, 31.434] | 9.2807 µs [9.2206, 9.3470] | **3.36x** |
| r=150 | 251.48 µs [250.37, 252.67] | 66.705 µs [66.045, 67.444] | **3.77x** |

**Why Faster**:
- Phase 71: O(N) per-pixel Option tracking (N = pixels)
- Phase 72: O(S) per-scanline sqrt (S = scanlines, S << N)
- For r=50: 7850 pixels × 10 ops → 100 scanlines × 22 ops = 35× fewer overhead ops

**Test Coverage**: 9 new tests (bit-exact parity + benchmarks)

**API**: `draw_disc_precomputed(pixels, width, height, cx, cy, radius, color)`

---

## Browser-Specific Optimizations

### Firefox GPU Physics Workaround

**Phase**: 60
**Location**: `rource-wasm/www/js/main.js`
**Impact**: 5-10x performance improvement on Firefox WebGPU

Firefox's WebGPU implementation has significant compute shader overhead compared to
Chrome/Edge. Investigation revealed fundamental differences in how Firefox handles
GPU synchronization and buffer operations.

**Root Cause Analysis**:

| Operation | Chrome/Edge | Firefox |
|-----------|-------------|---------|
| `device.poll(Maintain::Wait)` | Returns quickly | Thread yield/sleep overhead |
| Compute pass submission | Efficient batching | Higher latency per pass |
| Buffer synchronization | Optimized via ANGLE+D3D | Additional memory barriers |
| Staging buffer copies | Pipelined efficiently | Stalls more frequently |
| Atomic shader operations | Fast path | Slower synchronization |

**GPU Physics Pipeline** (9 sequential compute passes):
1. Clear Counts → 2. Count Entities → 3-5. Prefix Sum → 6. Init Scatter →
7. Scatter Entities → 8. Calculate Forces → 9. Integrate

Each pass requires GPU→CPU synchronization, compounding Firefox's overhead.

**Solution**:
```javascript
// Detect Firefox and disable GPU physics (use CPU physics instead)
const isFirefox = navigator.userAgent.includes('Firefox');

if (!isFirefox) {
    rource.warmupGPUPhysics();
    rource.setUseGPUPhysics(true);
    rource.setGPUPhysicsThreshold(500);
} else {
    console.log('Firefox detected: using CPU physics');
}
```

**Key Insight**: GPU rendering (draw calls) remains enabled on Firefox—only compute
shader physics is disabled. Rendering uses different synchronization patterns that
Firefox handles well.

**Performance Impact**:

| Browser | Before | After | Improvement |
|---------|--------|-------|-------------|
| Firefox (WebGPU) | ~6 FPS | ~40 FPS | ~6-7x |
| Chrome (WebGPU) | ~60 FPS | ~60 FPS | Unchanged |

**Future**: May be re-enabled when Firefox WebGPU compute performance improves.

---

## Dependency Optimizations

### rustc-hash 2.x Upgrade

**Phase**: 66
**Location**: `Cargo.toml` (workspace dependency)
**Impact**: 14-19% improvement in hash-heavy operations

Upgraded rustc-hash from 1.1.0 to 2.1.1. The new version includes a redesigned
hash algorithm by Orson Peters (@orlp) with better performance characteristics.

**Before** (rustc-hash 1.1):
```toml
rustc-hash = "1.1"
```

**After** (rustc-hash 2.1):
```toml
rustc-hash = "2.1"
```

**Benchmark Results**:

| Benchmark | Before | After | Improvement |
|-----------|--------|-------|-------------|
| full_label_placement | 42 µs | 35 µs | **-17%** |
| try_place_with_fallback | 269 ns | 245 ns | **-9%** |
| reset | 220 ns | 204 ns | **-7%** |

**Algorithm Changes**:
- Replaces original "fxhash" with new custom hasher
- Better theoretical properties (collision resistance)
- Significantly better string hashing
- Fixes large hashmap regression (rustc #135477)

**Affected Hot Paths**:
- LabelPlacer spatial hash grid (collision detection)
- Scene entity management (FxHashSet)
- Glyph cache (FxHashMap)
- Texture management (FxHashMap)

**Frame Budget Impact**:
- Savings: 7 µs/frame at typical label counts
- At 42,000 FPS target: 29% budget recovered
- At 60 FPS: 420 µs/second saved

**Note**: "Free" performance gain—no code changes, only dependency version bump.

---

### wgpu 28, criterion 0.8, iai-callgrind 0.16 Upgrade

**Phase**: 67
**Location**: Multiple `Cargo.toml` files
**Impact**: No regressions, try_place hot path improved 18-45%

Comprehensive dependency update with rigorous A/B benchmarking:

**Version Changes**:
```toml
# Before
wgpu = "24"
criterion = "0.5"
iai-callgrind = "0.14"

# After
wgpu = "28"
criterion = "0.8"
iai-callgrind = "0.16"
```

**API Migration Required**:
- wgpu 28: Major API changes across 9 backend files
- criterion 0.8: `black_box` moved to `std::hint::black_box` (11 benchmark files)
- iai-callgrind 0.16: Target-specific Linux-only dependency

**Benchmark Results (A/B Comparison)**:

| Benchmark | Before (wgpu 24) | After (wgpu 28) | Change |
|-----------|------------------|-----------------|--------|
| try_place | 11 ns | 6-9 ns | **-18% to -45%** |
| to_argb8 | 92 ns | 82 ns | **-11.9%** |
| full_label_placement | 35-38 µs | 35-37 µs | ~0% |
| try_place_with_fallback | 248 ns | 245-248 ns | ~0% |

**Key wgpu 28 API Changes**:
```rust
// DeviceDescriptor now requires 6 fields
wgpu::DeviceDescriptor {
    label: Some("..."),
    required_features: wgpu::Features::empty(),
    required_limits: wgpu::Limits::default(),
    memory_hints: wgpu::MemoryHints::default(),
    trace: wgpu::Trace::Off,                    // NEW
    experimental_features: wgpu::ExperimentalFeatures::default(), // NEW
}

// RenderPassColorAttachment requires depth_slice
depth_slice: None,  // NEW

// RenderPassDescriptor requires multiview_mask
multiview_mask: None,  // NEW

// Pipeline push_constant_ranges → immediate_size
immediate_size: 0,  // Replaces push_constant_ranges: &[]

// Device poll API change
device.poll(wgpu::PollType::wait_indefinitely());  // Was Maintain::Wait
```

**Note**: wgpu 28 requires API changes but provides no measurable performance regression.
The try_place improvement may be due to LLVM/Rust optimizations in the newer dependency tree.

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
| **Zero-copy stats buffer** | **84** | **618.6x** (Rust-side, `format!()` → buffer writes) |
| Label grid reset       | 65    | 90x         |
| Label width estimation | 68    | 22.4x (accuracy) |
| LUT random direction   | 58    | 13.9x       |
| Label sorting          | 65    | 7-8x        |
| Same-color blend       | 44    | 5.3x        |

### High Impact (2-10x)

| Optimization           | Phase | Improvement |
|------------------------|-------|-------------|
| Avatar texture array   | 61    | 300x (draw calls) |
| Firefox GPU workaround | 60    | 6-7x        |
| **Pre-computed disc bounds** | **72** | **3.36-3.77x** (criterion verified) |
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

### Dependency Upgrades (10-45%)

| Optimization           | Phase | Improvement |
|------------------------|-------|-------------|
| rustc-hash 2.x         | 66    | 14-19%      |
| wgpu 28/criterion 0.8  | 67    | 0% (no regression), try_place -18% to -45% |

---

## Formal Verification Optimizations

### Coq Mat4 Proof Compilation Optimization

**Phase**: 80
**Location**: `crates/rource-math/proofs/coq/Mat4_Proofs.v`
**Impact**: >300× compilation speedup (30+ min → ~6 seconds)

Optimized Mat4_Proofs.v compilation by replacing exponentially slow proof tactics
with efficient decomposition strategies.

**Root Cause**: Two independent issues caused exponential compilation time:

1. **`f_equal` on 16-field records**: Creates nested term structures causing
   `lra`/`ring` to exhibit exponential behavior. A single `f_equal; lra` proof
   timed out after 60 seconds.

2. **Simultaneous polynomial processing**: `mat4_mul_assoc` requires 64 nonlinear
   constraints across 48 variables. Processing all 16 simultaneously causes
   exponential term growth.

**Before** (exponential):
```coq
Theorem mat4_add_comm : forall a b : Mat4,
  mat4_add a b = mat4_add b a.
Proof.
  intros a b. destruct a, b.
  unfold mat4_add. simpl.
  f_equal; lra.       (* TIMEOUT: >60 seconds per theorem *)
Qed.

Theorem mat4_mul_assoc : forall a b c : Mat4,
  mat4_mul (mat4_mul a b) c = mat4_mul a (mat4_mul b c).
Proof.
  intros. destruct a, b, c.
  unfold mat4_mul. simpl.
  f_equal; ring.       (* TIMEOUT: >30 minutes *)
Qed.
```

**After** (linear):
```coq
(* Fix 1: apply mat4_eq instead of f_equal *)
Theorem mat4_add_comm : forall a b : Mat4,
  mat4_add a b = mat4_add b a.
Proof.
  intros a b.
  apply mat4_eq; unfold mat4_add; simpl; lra.  (* ~0.2 seconds *)
Qed.

(* Fix 2: Decompose into 16 independent component lemmas *)
Lemma mat4_mul_assoc_m0 : forall a b c : Mat4,
  m0 (mat4_mul (mat4_mul a b) c) = m0 (mat4_mul a (mat4_mul b c)).
Proof. intros. unfold mat4_mul; simpl; ring. Qed.
(* ... 15 more component lemmas ... *)

Theorem mat4_mul_assoc : forall a b c : Mat4,
  mat4_mul (mat4_mul a b) c = mat4_mul a (mat4_mul b c).
Proof.
  intros a b c.
  apply mat4_eq;
    [ apply mat4_mul_assoc_m0 | ... | apply mat4_mul_assoc_m15 ].
Qed.
```

**Benchmark Results**:

| Approach | Time | Status |
|----------|------|--------|
| Original (`f_equal; ring/lra`) | 30+ min | TIMEOUT |
| `nsatz` (Gröbner bases) | 10+ min | TIMEOUT |
| `nra` (nonlinear real arithmetic) | 5+ min | TIMEOUT |
| `abstract ring` | 10+ min | TIMEOUT |
| **`mat4_eq` + component decomposition** | **~6s** | **SUCCESS** |

**Tactic Selection Guide**:

| Proof Type | Tactic | Example |
|------------|--------|---------|
| Linear arithmetic | `lra` | `a + b = b + a`, `1 * x = x` |
| Polynomial identity | `ring` | `s * (a + b) = s*a + s*b` |
| Structural identity | `reflexivity` | `transpose(transpose(A)) = A` |
| Large record equality | `apply <type>_eq` | Any Mat3/Mat4 equality |
| Complex polynomial (48 vars) | Component decomposition | `mat4_mul_assoc` |

**Mathematical Validity**: Only proof strategies changed, not theorem statements.
Zero admits, zero non-standard axioms, all proofs machine-checked.

---

### Verus Requires-Axiom Decomposition for Degree-3+ Polynomial Identities

**Phase**: 83
**Location**: `crates/rource-math/proofs/mat3_extended_proofs.rs`
**Impact**: Unlocks previously Z3-intractable polynomial identities; 0 → 22 new Mat3 theorems

Discovered that Z3's `by(nonlinear_arith)` operates in an **isolated context** that cannot
expand Verus `open spec fn` definitions. For degree-3+ polynomial identities involving spec
functions (e.g., `det(A^T) = det(A)` with 9 variables), Z3 must both expand the spec functions
AND verify the polynomial equality — exceeding its resource limits.

**Root Cause**: `by(nonlinear_arith)` does not inherit facts from helper lemma calls in the
outer proof body. Distribution lemmas, commutativity facts, and associativity results are
invisible inside `nonlinear_arith` blocks.

**The 4-Phase Decomposition Pattern**:

| Phase | Who Does the Work | What They Do |
|-------|-------------------|--------------|
| 1. EXPAND det(A) | Outer Z3 context | Uses distribution lemmas to expand spec functions; asserts expanded polynomial form |
| 2. EXPAND det(A^T) | Outer Z3 context | Same for the other side of the equality |
| 3. BRIDGE | Individual `nonlinear_arith` blocks | Each proves a single degree-2 commutativity fact (trivial) |
| 4. CLOSE | `nonlinear_arith` with `requires` | Receives pre-expanded polynomials as axioms; only verifies raw integer equality |

**Before** (intractable):
```rust
proof fn mat3_det_transpose(a: SpecMat3)
    ensures mat3_determinant(mat3_transpose(a)) == mat3_determinant(a),
{
    // Z3 TIMEOUT: cannot expand two nested spec functions AND verify
    // a degree-3 polynomial identity over 9 variables simultaneously
    assert(mat3_determinant(mat3_transpose(a)) == mat3_determinant(a))
        by(nonlinear_arith);
}
```

**After** (verified in <1 second):
```rust
proof fn mat3_det_transpose(a: SpecMat3)
    ensures mat3_determinant(mat3_transpose(a)) == mat3_determinant(a),
{
    let da = mat3_determinant(a);
    let dat = mat3_determinant(mat3_transpose(a));

    // Phase 1: Outer Z3 expands det(A) using distribution lemmas
    distrib_sub(a.m0, a.m4 * a.m8, a.m5 * a.m7);
    // ... (2 more distrib_sub calls)
    assert(da == /* 6-term expanded polynomial */);

    // Phase 2: Outer Z3 expands det(A^T)
    distrib_sub(a.m0, a.m4 * a.m8, a.m7 * a.m5);
    // ... (2 more distrib_sub calls)
    assert(dat == /* 6-term expanded polynomial */);

    // Phase 3: Trivial commutativity facts
    assert(a.m0 * (a.m7 * a.m5) == a.m0 * (a.m5 * a.m7)) by(nonlinear_arith);
    // ... (4 more)

    // Phase 4: Close with pre-expanded axioms
    assert(dat == da) by(nonlinear_arith)
        requires da == /* expanded */, dat == /* expanded */;
}
```

**Key Insight**: The `requires` clause feeds axioms directly to `nonlinear_arith`,
decoupling spec-function expansion (outer Z3) from polynomial equality verification
(inner `nonlinear_arith`). This is a **general technique** applicable to any degree-3+
polynomial identity over Verus spec functions.

**Future Applications**:
- Mat4 determinant properties (degree-4, 16 variables)
- Quaternion identities (degree-4, 4 variables)
- Cross product triple product identities (degree-3, 9 variables)
- Cayley-Hamilton theorem proofs

**Verification Results**:
```
mat3_extended_proofs.rs: 45 verified, 0 errors
Total Verus proof functions: 240 → 266 (+26)
Total verified theorems: 796 → 822 (+26)
```

**Mathematical Validity**: Only proof strategies changed, not theorem statements.
Zero admits, zero non-standard axioms, all proofs machine-checked.

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

### Phase 86: Flat Grid + Dirty-Cell LabelPlacer (63.5% Reduction)

**Phase**: 86
**Location**: `rource-wasm/src/render_phases/label_placer.rs`
**Impact**: Per-frame label placement 6,971 ns → 2,542 ns (-63.5%, 2.74x faster)

**Problem**: The spatial hash grid used triple-nested `Vec<Vec<Vec<(usize, u32)>>>` which
required 3 pointer dereferences per cell access plus a generation check branch in the
tight inner loop. At nanosecond scale, each pointer chase (~5-20 ns cache miss) dominated
the per-label cost.

**Solution**: Replace with flat `Vec<Vec<usize>>` indexed as `grid[cy * 32 + cx]` plus
dirty-cell tracking (`Vec<u16>`) for efficient reset.

**Key changes**:
1. Triple indirection → single flat index (eliminates 2 pointer chases per access)
2. Generation counter → dirty-cell tracking (eliminates branch from inner loop)
3. `(usize, u32)` entries → `usize` entries (halves per-entry memory: 8 bytes → 4 bytes)

**Results**:

| Operation | Before | After | Speedup |
|-----------|--------|-------|---------|
| Full frame (80 labels) | 6,971 ns | 2,542 ns | 2.74x |
| `try_place()` | 25 ns | 4 ns | 6.25x |
| `try_place_with_fallback()` | 261 ns | 80 ns | 3.26x |
| `reset()` | 202 ns | 16 ns | 12.6x |

**Tradeoff**: `LabelPlacer::new()` increased from 30 µs to 37 µs (+22%) because
the flat grid allocates 1024 Vecs up front instead of 32 rows of 32. This is a
one-time startup cost (amortized to zero over the millions of frames rendered).

---

### Phase 86: Simulation Time Accumulator (Anti-Flicker)

**Phase**: 86
**Location**: `rource-wasm/src/lib.rs`
**Impact**: Eliminates visual flickering at >2K FPS

**Problem**: At extreme FPS (2K-8K), browser timer resolution (~5 µs in Chrome)
causes stroboscopic dt aliasing: consecutive frames measure dt=0 then dt=2×expected,
causing entity position/alpha jitter visible as flickering.

**Solution**: Accumulate real dt and only step simulation when ≥2.08ms (1/480 Hz)
has elapsed. Rendering still occurs every frame (re-renders identical state when
no simulation step occurs), eliminating visible flicker.

- At 60 FPS: always steps (16.7ms >> 2.08ms) — no behavior change
- At 144 FPS: always steps (6.9ms >> 2.08ms) — no behavior change
- At 2K FPS: steps every ~4 frames — smooth, no jitter
- At 8K FPS: steps every ~17 frames — smooth, no jitter

### Phase 87: Zero-Allocation Branch Drawing + LOD

**Phase**: 87
**Location**: `crates/rource-render/src/visual.rs`, `rource-wasm/src/render_phases/files.rs`,
`rource-wasm/src/render_phases/directories.rs`, `rource-cli/src/rendering.rs`
**Impact**: Full frame: 18.98 µs → 4.23 µs (**-77.7%, 4.48x speedup**)

**Problem**: `draw_curved_branch()` allocated a new `Vec<Vec2>` (~31 points, 248 bytes)
for every branch drawn — 200+ times per frame. Additionally, each branch drew two
`draw_spline` calls (main + 0.15-alpha glow), and short branches received full
Catmull-Rom computation despite being visually identical to straight lines.

**Solution**: Created `draw_curved_branch_buffered()` with three optimizations:

1. **Caller-owned buffer**: Single `Vec<Vec2>` reused across all branch draws,
   eliminating ~220 heap allocations per frame (~54.6 KB/frame saved)
2. **LOD distance threshold**: Branches < ~50px on screen use `draw_line` instead
   of Catmull-Rom splines (squared distance check avoids `sqrt`)
3. **No glow pass**: Removed imperceptible 0.15-alpha glow, halving `draw_spline` calls

Both CLI and WASM builds updated for parity — same `draw_curved_branch_buffered`
function, same reusable buffer pattern.

| Component | Before | After | Speedup |
|-----------|--------|-------|---------|
| `render_files` | 18,108 ns | 2,127 ns | 8.51x |
| `render_directories` | 1,503 ns | 168 ns | 8.95x |
| **Full frame** | **18,975 ns** | **4,231 ns** | **4.48x** |

---

### Phase 88: InsightsIndex O(1) Per-Entity Academic Metrics

**Phase**: 88
**Location**: `crates/rource-core/src/insights/index.rs`, `rource-wasm/src/wasm_api/insights.rs`,
`rource-wasm/www/js/wasm-api.js`
**Impact**: Feature addition — O(1) per-entity academic metrics lookup (no hot-path impact)

**Problem**: 20+ academic metrics computed by `compute_insights()` were only accessible as
separate report sections. No way to get all metrics for a single file or user without
iterating multiple arrays.

**Solution**: Pre-computed `FxHashMap<String, FileMetrics>` and `FxHashMap<String, UserMetrics>`
built once at load time from the `InsightsReport`:

- `FileMetrics`: 15 fields covering hotspots, ownership, churn, coupling, lifecycle, survival
- `UserMetrics`: 12 fields covering profiles, cadence, network, focus, circadian risk
- `IndexSummary`: 6 aggregate statistics
- 5 WASM API functions for per-entity and bulk access
- 22 mutation-killing + JSON serialization tests

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Build index | O(F + U + C) | One-time at load |
| Per-entity lookup | O(1) | `FxHashMap` get |
| Render impact | Zero | No hot-path code touched |

---

*Last updated: 2026-02-12*
