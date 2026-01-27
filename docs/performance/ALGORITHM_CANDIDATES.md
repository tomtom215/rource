# Algorithm Candidates for Future Evaluation

**Status**: Research Document
**Created**: 2026-01-27
**Purpose**: Identify genuinely promising algorithms for picosecond/nanosecond optimization
**Standard**: Expert+ (Never guess, always benchmark)

---

## Executive Summary

After comprehensive research across competitive programming, nature-inspired algorithms,
cache optimization, SIMD techniques, and Google OR-Tools, this document identifies
**5 genuinely promising algorithms** that warrant rigorous A/B benchmarking.

**Critical Caveat**: Rource is already highly optimized (77 phases documented). Most
remaining gains will be in the single-digit nanosecond range. Some candidates may
prove NOT APPLICABLE after benchmarking—this is expected and acceptable.

---

## Research Sources Consulted

### Academic & Technical
- [Cache-Oblivious Algorithms (MIT)](https://jiahai-feng.github.io/posts/cache-oblivious-algorithms/)
- [Erik Demaine's Cache-Oblivious B-Trees (SIAM)](https://erikdemaine.org/papers/CacheObliviousBTrees_SICOMP/paper.pdf)
- [Z-order Curve (Wikipedia)](https://en.wikipedia.org/wiki/Z-order_curve)
- [Morton Encoding Implementations](https://www.forceflow.be/2013/10/07/morton-encodingdecoding-through-bit-interleaving-implementations/)

### Industry & Game Development
- [GDC: Extreme SIMD in Titanfall](https://www.gdcvault.com/play/1025126/Extreme-SIMD-Optimized-Collision-Detection)
- [SIMD-Optimized 2D AABB Representation](https://gist.github.com/mtsamis/441c16f3d6fc86566eaa2a302ed247c9)
- [SoA vs AoS Benchmarks (Algorithmica)](https://en.algorithmica.org/hpc/cpu-cache/aos-soa/)

### GPU & WebGPU
- [Parallel Prefix Sum (NVIDIA GPU Gems 3)](https://developer.nvidia.com/gpugems/gpugems3/part-vi-gpu-computing/chapter-39-parallel-prefix-sum-scan-cuda)
- [WebGPU Prefix Sum (Raph Levien)](https://raphlinus.github.io/gpu/2021/11/17/prefix-sum-portable.html)
- [Modern GPU: Reduce and Scan](https://moderngpu.github.io/scan.html)

### Competitive Programming
- [Bit Manipulation (cp-algorithms)](https://cp-algorithms.com/algebra/bit-manipulation.html)
- [Segment Trees (cp-algorithms)](https://cp-algorithms.com/data_structures/segment_tree.html)
- [GeeksforGeeks Bit Manipulation](https://www.geeksforgeeks.org/competitive-programming/bit-manipulation-for-competitive-programming/)

### Constraint Optimization
- [Google OR-Tools Overview](https://developers.google.com/optimization)
- [CP-SAT Primer](https://d-krupke.github.io/cpsat-primer/)

---

## Algorithms Already Implemented or Evaluated as N/A

Before proposing new algorithms, we must acknowledge what's already been done
(see NOT_APPLICABLE.md and SUCCESSFUL_OPTIMIZATIONS.md):

### Implemented (Working)
| Algorithm | Phase | Complexity | Status |
|-----------|-------|------------|--------|
| Barnes-Hut | 16 | O(n log n) | Optimal for force layout |
| Adaptive Theta | 62 | Dynamic | 29-61% speedup |
| QuadTree | 12 | O(log n) | Optimal for spatial queries |
| GPU Spatial Hash | 22 | O(n) | Optimal for physics |
| Generation Counter | 65 | O(1) reset | 90× faster than clear |
| Compile-time LUT | 63 | O(1) lookup | 13.9× vs sin/cos |
| FxHashMap | 40 | O(1) average | Optimal for point queries |
| SIMD128 | 1 | Enabled | Auto-vectorization active |

### Evaluated as NOT APPLICABLE
| Algorithm | Phase | Reason |
|-----------|-------|--------|
| VEB QuadTree Layout | 77 | Tree fits in L2 cache |
| Hybrid Introsort | 77 | Rust pdqsort equivalent |
| SIMD128 Prefix Sum (CPU) | 77 | No prefix sum in CPU physics |
| Branchless Selection | 77 | Branch prediction not bottleneck |
| Spatial Hash (core lib) | 76 | Overhead > benefit for <100 labels |
| H-PLOC BVH | 75 | No ray tracing |
| LBVH (Linear BVH) | 75 | No ray tracing |
| Relaxed-SIMD | 57 | Breaks determinism |
| Various quantum algorithms | 56 | Scale/domain mismatch |

---

## Candidate 1: Four-Way SIMD AABB Batch Testing

**Source**: [Titanfall GDC Talk](https://www.gdcvault.com/play/1025126/Extreme-SIMD-Optimized-Collision-Detection), [SIMD AABB Gist](https://gist.github.com/mtsamis/441c16f3d6fc86566eaa2a302ed247c9)

**Claimed Gain**: 2-4× for batch AABB collision detection

### Concept

Instead of testing one AABB against one AABB (4 comparisons), test one AABB against
four AABBs simultaneously using SIMD128 (16 comparisons in ~same time).

```
Standard: 4 comparisons × n iterations = 4n operations
SIMD:     4 comparisons × (n/4) iterations = n operations (4× fewer iterations)
```

### Rource Applicability

| Hot Path | Current Implementation | SIMD Batch Applicable? |
|----------|------------------------|------------------------|
| Label collision (`try_place`) | Sequential AABB test | **Yes** - tests against occupied list |
| GPU visibility culling | GPU compute shader | No - already parallel |
| QuadTree queries | Single AABB test | Maybe - small query sets |

**Target**: `crates/rource-render/src/label.rs` - `collides()` function

```rust
// Current: Sequential O(n)
fn collides(&self, bounds: &Rect) -> bool {
    for occupied in &self.occupied {
        if rects_overlap(bounds, occupied) {  // 4 comparisons
            return true;
        }
    }
    false
}

// Proposed: SIMD Batch O(n/4)
fn collides_simd(&self, bounds: &Rect) -> bool {
    let bounds_v = simd_broadcast(bounds);  // Broadcast to 4 lanes
    for chunk in self.occupied.chunks(4) {
        let occupied_v = simd_load_4(chunk);  // Load 4 AABBs
        let overlap = simd_aabb_test(bounds_v, occupied_v);  // 4 tests in parallel
        if any_overlap(overlap) {
            return true;
        }
    }
    false
}
```

### Expected Impact

- Label counts: 30-100 typical
- Current: ~3.26 µs for 80 labels (from Phase 76 benchmark)
- Potential: ~1-2 µs if SIMD reduces iteration count by 4×
- **Net gain**: 1-2 µs per frame (~4-8% of 23.8 µs budget)

### Evaluation Criteria

1. WASM SIMD128 compatibility (f32x4 available)
2. Memory alignment requirements (16-byte for SIMD loads)
3. Remainder handling (when n % 4 ≠ 0)
4. Early-exit efficiency (first collision found)

### Verdict: **WORTH INVESTIGATING**

Small but measurable gain possible. WASM SIMD128 supports f32x4. Key question
is whether LLVM auto-vectorizes the current loop already (need to check assembly).

---

## Candidate 2: Morton Code (Z-Order) Entity Indexing

**Source**: [Z-order Curve Wikipedia](https://en.wikipedia.org/wiki/Z-order_curve), [Morton Encoding](https://www.forceflow.be/2013/10/07/morton-encodingdecoding-through-bit-interleaving-implementations/)

**Claimed Gain**: 2-3× cache locality improvement, 3× faster encoding with PDEP

### Concept

Morton codes interleave x,y coordinate bits to create a 1D index that preserves
2D spatial locality. Entities sorted by Morton code are cache-friendly when
iterating spatially.

```
Position (x=5, y=3):
  x binary: 0101
  y binary: 0011
  Interleaved: 00_01_11_01 = 29 (Morton code)
```

### Rource Applicability

| Data Structure | Current Ordering | Morton Benefit |
|----------------|------------------|----------------|
| Entity arrays | Insertion order | **Possible** - spatial iteration |
| QuadTree nodes | Quadrant-based | Minimal - already spatial |
| GPU buffers | Arbitrary | **Possible** - texture fetch locality |

**Target**: Entity iteration in render phases

```rust
// Current: Iteration in insertion order (cache-unfriendly)
for file in scene.files.values() {
    render_file(file);  // Random memory access pattern
}

// Proposed: Morton-sorted iteration (cache-friendly)
let mut sorted_files: Vec<_> = scene.files.values().collect();
sorted_files.sort_by_key(|f| morton_code(f.position()));
for file in sorted_files {
    render_file(file);  // Sequential memory access pattern
}
```

### Expected Impact

- Sorting cost: O(n log n) per frame (significant overhead)
- Cache benefit: Depends on entity memory layout
- **Net gain**: Likely **NEGATIVE** - sorting cost exceeds cache benefit for small n

### Evaluation Criteria

1. Entity count threshold where sorting pays off (likely >10,000)
2. Frame-to-frame position stability (can reuse sort?)
3. Entity memory layout (are entities contiguous?)

### Verdict: **LIKELY NOT APPLICABLE**

Morton sorting adds O(n log n) overhead per frame. For Rource's typical entity
counts (100-5000), the sorting cost exceeds cache benefits. Would need amortization
strategy (sort once, update incrementally) but entities move continuously.

**Alternative**: Morton-ordered GPU texture storage for better texture fetch locality.
This is already common in GPUs and may be automatic.

---

## Candidate 3: Structure of Arrays (SoA) Entity Layout

**Source**: [SoA vs AoS (Algorithmica)](https://en.algorithmica.org/hpc/cpu-cache/aos-soa/), [Unity DOTS](https://medium.com/@savas/nomad-game-engine-part-4-3-aos-vs-soa-storage-5bec879aa38c)

**Claimed Gain**: 43% measured, up to 16× in Unity DOTS

### Concept

Instead of storing entities as structs containing all fields (AoS), store each
field in its own contiguous array (SoA). This improves cache utilization when
accessing only subset of fields.

```rust
// AoS (current likely pattern)
struct File {
    position: Vec2,    // 8 bytes
    color: Color,      // 4 bytes
    radius: f32,       // 4 bytes
    name: String,      // 24 bytes
    // ... more fields
}
let files: Vec<File>;  // Fields interleaved in memory

// SoA (proposed)
struct FilesData {
    positions: Vec<Vec2>,   // Contiguous positions
    colors: Vec<Color>,     // Contiguous colors
    radii: Vec<f32>,        // Contiguous radii
    names: Vec<String>,     // Contiguous names
}
```

### Rource Applicability

| Operation | Fields Accessed | SoA Benefit |
|-----------|-----------------|-------------|
| Position update (physics) | position, velocity | **High** - only 16 bytes/entity |
| Visibility culling | position, radius | **High** - only 12 bytes/entity |
| Rendering | position, color, radius | **Medium** - 16 bytes/entity |
| Full entity access | All fields | **Low** - multiple arrays |

**Target**: `crates/rource-core/src/entity/` - Entity definitions

### Expected Impact

Highly dependent on current memory layout and access patterns:

- If current structs are >64 bytes and we access <16 bytes: **High benefit**
- If current structs are ~32 bytes: **Medium benefit**
- If current structs are already cache-line aligned: **Low benefit**

### Evaluation Criteria

1. Current entity struct sizes (File, Directory, User, Action)
2. Typical access patterns in hot paths
3. Rust ownership/borrowing implications
4. API changes required (significant refactor)

### Verdict: **HIGH COMPLEXITY, UNCERTAIN GAIN**

This is a significant architectural change. Need to:
1. Measure current struct sizes
2. Profile cache miss rates in hot paths
3. Prototype SoA for one entity type
4. Benchmark before/after

**Recommendation**: Start with a limited prototype (e.g., just positions/velocities
for physics) before committing to full SoA transformation.

---

## Candidate 4: Packed Bit Flags for Entity State

**Source**: [Bit Manipulation (cp-algorithms)](https://cp-algorithms.com/algebra/bit-manipulation.html), [LeetCode Bit Manipulation](https://leetcode.com/problem-list/bit-manipulation/)

**Claimed Gain**: 8-32× memory reduction for flags, SIMD-friendly operations

### Concept

Instead of storing entity states as individual booleans or enums (1-8 bytes each),
pack them into a single integer where each bit represents a flag.

```rust
// Current (hypothetical)
struct EntityFlags {
    visible: bool,         // 1 byte
    active: bool,          // 1 byte
    highlighted: bool,     // 1 byte
    fading_in: bool,       // 1 byte
    fading_out: bool,      // 1 byte
    selected: bool,        // 1 byte
    // 6 bytes + padding = 8 bytes
}

// Proposed: Bitflags
bitflags! {
    struct EntityFlags: u8 {
        const VISIBLE     = 0b00000001;
        const ACTIVE      = 0b00000010;
        const HIGHLIGHTED = 0b00000100;
        const FADING_IN   = 0b00001000;
        const FADING_OUT  = 0b00010000;
        const SELECTED    = 0b00100000;
        // 1 byte total
    }
}
```

### Rource Applicability

Need to audit current entity state representation:

1. Check if entities have boolean/state fields that could be packed
2. Check if state queries are in hot paths
3. Check if bulk state operations would benefit from SIMD

**Potential targets**:
- File visibility flags
- User activity flags
- Animation state flags

### Expected Impact

- Memory: 8× reduction for flag storage (8 bools → 1 byte)
- Cache: More flags per cache line
- SIMD: Can process 128 flags with single SIMD instruction

**However**: Modern CPUs handle booleans efficiently. Gain is real but may be
in single-digit nanoseconds unless flags are accessed millions of times per frame.

### Evaluation Criteria

1. Current flag storage in entity structs
2. Frequency of flag access in hot paths
3. Bulk flag operations (e.g., "hide all files matching X")

### Verdict: **LOW PRIORITY BUT CLEAN WIN**

Bitflags are a clean optimization with no downside. Likely already used for some
flags (check existing code). Low priority because gain is small unless flags are
accessed in tight loops.

---

## Candidate 5: Compile-Time Interval Tree for Static Bounds

**Source**: [Interval Tree (Wikipedia)](https://en.wikipedia.org/wiki/Interval_tree), [Segment Trees (cp-algorithms)](https://cp-algorithms.com/data_structures/segment_tree.html)

**Claimed Gain**: O(log n + k) query time for overlapping intervals

### Concept

For label collision detection, if the Y-axis bounds are relatively stable
(labels don't move vertically much), a 1D interval tree on Y-coordinates
can quickly filter candidate labels before 2D AABB testing.

```
Query: "Find all labels overlapping Y range [100, 150]"

Spatial Hash: O(cells_in_range) - must check all cells in Y range
Interval Tree: O(log n + k) - only returns overlapping intervals
```

### Rource Applicability

| Use Case | Current | Interval Tree Benefit |
|----------|---------|----------------------|
| Label collision | Spatial hash grid | **Maybe** - depends on label distribution |
| Viewport culling | AABB test | **No** - single test |
| Physics queries | QuadTree | **No** - 2D queries |

**Target**: Label collision in `render_phases.rs`

### Expected Impact

For label collision with 80 labels:
- Spatial hash: O(1) amortized with generation counter
- Interval tree: O(log 80) = ~6 comparisons + k overlaps

The spatial hash with generation counter is already extremely efficient.
Interval tree adds tree traversal overhead.

### Evaluation Criteria

1. Label Y-coordinate distribution (clustered or uniform?)
2. Spatial hash cell hit rate (how many labels per cell?)
3. Build cost for interval tree vs. generation counter reset

### Verdict: **LIKELY NOT APPLICABLE**

The existing spatial hash with generation counter achieves O(1) reset and O(k)
query where k is labels in cell. Interval tree adds O(log n) traversal overhead.
Only beneficial if labels are highly clustered in X but spread in Y—unlikely
for typical visualizations.

---

## Novel Algorithm Opportunity Assessment

### Have We Exhausted Known Algorithms?

Based on comprehensive research, Rource has implemented or evaluated:

**Spatial Algorithms**: QuadTree, Barnes-Hut, Spatial Hash, BVH variants ✓
**Cache Optimization**: Generation counter, FxHashMap, LUT ✓
**SIMD**: SIMD128 enabled, auto-vectorization active ✓
**Complexity Reduction**: O(n²)→O(n log n) physics, O(n)→O(1) lookups ✓
**GPU Offloading**: 9-pass spatial hash, visibility culling ✓

### Remaining Opportunities

1. **Data Layout Optimization (SoA)**: Not yet explored, high potential
2. **SIMD Batch Operations**: Explicit SIMD for collision, medium potential
3. **Bitflags**: Clean win if not already used
4. **Profile-Guided Optimization (PGO)**: Not yet explored for WASM

### Novel Algorithm Potential

If all known algorithms prove NOT APPLICABLE after benchmarking, the path forward
would be:

1. **Identify the specific bottleneck** through profiling (not guessing)
2. **Characterize the problem mathematically** (inputs, outputs, constraints)
3. **Search for related problems** in algorithm literature
4. **Design custom solution** if no existing algorithm fits
5. **Prove correctness** mathematically
6. **Benchmark rigorously** against baseline

**Example opportunity**: A hybrid data structure combining spatial hash grid
with interval tree properties, optimized for Rource's specific label placement
pattern (many labels, few collisions, incremental updates).

---

## Recommended Investigation Order

Based on feasibility, expected gain, and implementation complexity:

| Priority | Algorithm | Expected Gain | Complexity | Risk |
|----------|-----------|---------------|------------|------|
| 1 | Four-Way SIMD AABB | 1-2 µs/frame | Low | Medium |
| 2 | Bitflags Audit | 0.1-0.5 µs | Very Low | Very Low |
| 3 | SoA Prototype | Unknown | High | High |
| 4 | Morton Code | Likely negative | Medium | High |
| 5 | Interval Tree | Likely N/A | Medium | High |

### Priority 1: Four-Way SIMD AABB

**Why first**: Low complexity, measurable gain, WASM-compatible, non-invasive.

**Steps**:
1. Check if LLVM already auto-vectorizes the collision loop (inspect WASM)
2. If not, implement explicit f32x4 SIMD version
3. Benchmark A/B with criterion
4. Document in CHRONOLOGY.md

### Priority 2: Bitflags Audit

**Why second**: Zero-risk improvement, clean code benefit.

**Steps**:
1. Audit entity structs for boolean fields
2. Identify if bitflags would reduce memory/improve cache
3. Implement if beneficial
4. No benchmark needed (clear win)

### Priority 3: SoA Prototype

**Why third**: High potential but high risk. Needs prototype first.

**Steps**:
1. Measure current struct sizes
2. Profile cache miss rates
3. Prototype SoA for position/velocity only
4. Benchmark physics loop
5. Decide on full conversion

---

## Google OR-Tools Assessment

### Applicable Techniques

Google OR-Tools specializes in:
- Linear programming (LP)
- Mixed integer programming (MIP)
- Constraint programming (CP)
- Vehicle routing (VRP)
- Graph algorithms

### Rource Relevance

| OR-Tools Domain | Rource Applicability |
|-----------------|---------------------|
| Linear programming | No - no optimization objective |
| Constraint programming | No - continuous physics, not discrete |
| Vehicle routing | No - no routing problems |
| Graph algorithms | Minimal - tree structure, not graph |

### Constraint Propagation Inspiration

The concept of **arc consistency** and **propagation** from CP-SAT could inspire
incremental updates:

- When one label moves, propagate constraints to neighbors
- Avoid full re-evaluation of collision grid

However, Rource's generation counter already achieves O(1) reset, making
incremental propagation unnecessary.

### Verdict: **NO DIRECT APPLICABILITY**

OR-Tools solves discrete optimization problems. Rource's hot paths are continuous
physics simulation and rendering—different problem domains. No applicable techniques
identified.

---

## Conclusion

### Genuinely Promising (Worth Benchmarking)

1. **Four-Way SIMD AABB Batch Testing** - Low risk, measurable gain
2. **Bitflags Audit** - Zero risk, clean improvement

### Uncertain (Requires Prototype)

3. **SoA Entity Layout** - High potential, high complexity

### Likely Not Applicable (But Worth Verifying)

4. **Morton Code Sorting** - Sorting cost exceeds cache benefit
5. **Interval Tree** - Spatial hash already optimal

### Already Exhausted

- Barnes-Hut (implemented)
- Spatial Hash (GPU implemented)
- QuadTree (implemented)
- All BVH variants (N/A - no ray tracing)
- Hybrid Introsort (pdqsort equivalent)
- VEB Layout (tree fits in cache)

### Path to Novel Algorithm

If Candidates 1-5 prove NOT APPLICABLE after rigorous benchmarking, the next
session should:

1. Profile to identify the actual remaining bottleneck
2. Characterize the problem mathematically
3. Design a custom data structure/algorithm
4. Prove correctness formally
5. Benchmark against all known alternatives

---

*Document created: 2026-01-27*
*Standard: Expert+ (Never guess, always benchmark)*
*Sources: See hyperlinks throughout document*
