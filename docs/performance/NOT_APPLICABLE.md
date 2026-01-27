# Not Applicable Optimizations

This document catalogs optimization techniques that were analyzed but determined
to be not applicable to Rource's architecture, constraints, or use case.

---

## Table of Contents

1. [Design Constraint Conflicts](#design-constraint-conflicts)
2. [Domain Mismatches](#domain-mismatches)
3. [Scale Mismatches](#scale-mismatches)
4. [Already Implemented Equivalents](#already-implemented-equivalents)
5. [Browser/Platform Limitations](#browserplatform-limitations)
6. [Theoretical Algorithms](#theoretical-algorithms)
7. [Phase 75: Spatial Acceleration Algorithm Evaluation](#phase-75-spatial-acceleration-algorithm-evaluation)

---

## Design Constraint Conflicts

### Relaxed-SIMD

**Phase**: 57
**Reason**: Breaks determinism guarantee

WebAssembly relaxed-SIMD (Phase 5, standardized) adds `f32x4.relaxed_fma` and
`f32x4.relaxed_reciprocal_sqrt` instructions.

**Claimed Performance**: 15-30% improvement in force calculations

**Why Not Applicable**:

From `optimized.rs`:
```rust
//! # Determinism Guarantee
//!
//! All operations use:
//! - Fixed-point arithmetic (8.8 or 16.16 formats)
//! - Lookup tables for transcendental functions
//! - Explicit rounding modes (round-half-to-even)
//! - No floating-point in hot paths
```

Relaxed-SIMD introduces non-deterministic behavior where identical inputs may produce
slightly different outputs across hardware. This directly conflicts with Rource's
core design goal of reproducible output.

**Trade-off Made**: Determinism > marginal performance gain

---

## Domain Mismatches

### SSSP Algorithms (Sorting Barrier Breakthrough)

**Phase**: 52
**Reference**: arXiv:2504.17033v2

The breakthrough algorithm achieves O(m log^(2/3) n) for single-source shortest paths,
breaking the O(n log n) sorting barrier.

**Why Not Applicable**:

| Rource Component   | Algorithm Used         | SSSP Applicable? |
|--------------------|------------------------|------------------|
| Force Layout       | Barnes-Hut O(n log n)  | No (physics)     |
| Directory Tree     | Tree traversal O(n)    | No (tree)        |
| Spatial Queries    | QuadTree O(log n)      | No (geometric)   |
| Commit Navigation  | Sequential O(c)        | No (linear)      |

Rource operates on trees and spatial structures, not general weighted directed graphs.

---

### Graph Coloring Algorithms

**Phase**: 53
**Algorithms**: Welsh-Powell, DSatur, Greedy

**Why Not Applicable**:

| Area                    | Current Implementation | Coloring Benefit |
|-------------------------|------------------------|------------------|
| Physics Force Calc      | Barnes-Hut O(n log n)  | Already optimized|
| Draw Command Batching   | Sort-key ordering      | Already effective|
| QuadTree Leaves         | 4-quadrant structure   | Inherent 4-color |
| Directory Tree Siblings | Tree structure         | Bipartite (trivial) |

Tree structures are trivially colorable:
- Directory trees: 2-colorable (bipartite)
- QuadTrees: 4-colorable by construction

---

### Quantum Algorithms

**Phase**: 56
**Algorithms**: VQE, QAOA, Grover, QFT, Quantum Annealing

**Why Not Applicable**:

| Algorithm  | Domain              | Rource Need           | Match |
|------------|---------------------|----------------------|-------|
| VQE        | Quantum chemistry   | None                 | No    |
| QAOA       | Discrete optimization| Continuous layout   | No    |
| Grover     | Unstructured search | Structured (hash)    | No    |
| QFT        | Signal processing   | Small-kernel blur    | No    |
| Annealing  | Energy minimization | Continuous positions | No    |

**Key Issues**:
1. Scale mismatch: ~30 qubits vs 10k+ entities
2. Variable type mismatch: Binary vs continuous
3. Grover O(sqrt(n)) is worse than O(1) hash lookup

---

### Hilbert's 6th Problem / Navier-Stokes

**Phase**: 54

Rigorous derivation of fluid equations from Boltzmann kinetic theory.

**Why Not Applicable**: Rource uses discrete particle simulation, not continuum fluid PDEs.

---

### 2025 Mathematical Breakthroughs

**Phase**: 54
**Breakthroughs Analyzed**: 10

| Breakthrough           | Applicability |
|------------------------|---------------|
| Moving Sofa Problem    | 2D corridors, not Rource's use |
| Noperthedron           | 3D geometry, Rource is 2D |
| Prime Distribution     | No prime computation |
| Geometric Langlands    | Abstract, no computation |
| Knot Complexity        | No topology processing |
| Fibonacci Pick-up Sticks| No triangle probability |
| Prime Partitions       | No primality testing |
| Triangle Dissection    | No geometric dissection |
| Prime Counting         | No prime counting |

---

## Scale Mismatches

### Learned Indexes (PGM-Index)

**Phase**: 55
**Claimed Performance**: 3-10x faster than binary search

**Why Not Applicable**:

| Criterion           | PGM-Index              | FxHashMap           |
|---------------------|------------------------|---------------------|
| Lookup complexity   | O(log n / log e)       | O(1) average        |
| Requires sorted keys| Yes                    | No                  |
| Best for            | Range queries          | Point queries       |

Rource's file lookup is point-query dominated (exact path), not range-query dominated.
FxHashMap's O(1) is superior for this workload.

**When PGM Would Help**: Range queries like "all files modified after timestamp X"
(not hot-path operations in Rource).

---

### Quantum Simulation Scale

**Phase**: 56

| Qubits | State Vector Size | Limit      |
|--------|-------------------|------------|
| 20     | 2^20 = 1M         | Fast       |
| 30     | 2^30 = 1B         | Borderline |
| 40     | 2^40 = 1T         | Impractical|

Rource needs 10k-100k+ entities; quantum simulation is limited to ~30 variables.

---

## Already Implemented Equivalents

### GPU Barnes-Hut (GraphWaGu)

**Phase**: 55
**Reference**: Eurographics 2022

**Why Not Applicable**: Rource already has 9-pass GPU spatial hash pipeline.

| GraphWaGu Approach      | Rource Implementation              |
|-------------------------|------------------------------------|
| GPU quadtree construction | GPU spatial hash grid           |
| O(n log n) Barnes-Hut   | O(n) spatial hash (3x3 cells)     |
| 6x|V| buffer            | Prefix sum scatter                |

Rource's spatial hash is better suited for uniform entity distribution.

---

### wasm-opt -O4 Configuration

**Phase**: 57

**Why Not Applicable**: Already using equivalent `-O3 --converge`.

| Setting                 | Recommended | Rource Current    |
|-------------------------|-------------|-------------------|
| Optimization level      | -O4         | -O3               |
| Iterate to convergence  | (implicit)  | --converge        |
| Feature flags           | (none)      | 5 flags enabled   |
| Low memory              | (none)      | --low-memory-unused|

`-O4` is largely equivalent to `-O3` with additional passes; `--converge` achieves same effect.

---

### Tail Call Optimization

**Phase**: 57

**Why Not Applicable**: Already automatic in Rust/LLVM.

Rust's LLVM backend automatically emits `return_call` instructions for tail-recursive
functions when optimization is enabled.

---

## Browser/Platform Limitations

### WebGPU Subgroups

**Phase**: 57
**Claimed Performance**: 30-50% for reduction operations

**Browser Support**:

| Browser  | Status      |
|----------|-------------|
| Chrome   | 128+ (Aug 2024) |
| Firefox  | Development |
| Safari   | Development |

**Why Not Applicable**:
1. Limited browser support (Chrome-only)
2. Requires fallback code (maintenance burden)
3. Current 3-pass Blelloch scan is efficient

**Future Consideration**: When Firefox/Safari ship support (estimated 2026+).

---

### vers-vecs Succinct Data Structures

**Phase**: 55
**Features**: O(1) rank, O(log n) select, EliasFano, WaveletMatrix

**Why Not Applicable**:

> "This crate uses compiler intrinsics for bit-manipulation. The intrinsics are supported
> by all modern x86_64 CPUs, but not by other architectures."

Rource requires WASM compatibility. Fallback implementations would negate benefits.

---

### WASM Threads (UFO Trees)

**Phase**: 55
**Algorithm**: Batch tree updates O(min{k log(1+n/k), kD})

**Why Not Applicable**:
1. Requires SharedArrayBuffer (not universal)
2. Rource processes commits sequentially
3. Directory tree updates are not a bottleneck

---

## Theoretical Algorithms

### Dual Kawase Blur

**Phase**: 57
**Claimed Performance**: 200-400% vs Gaussian for large kernels

**Why Not Applicable**:

Current Rource bloom configuration:
```rust
radius: 2  // 5-pixel kernel
```

| Kernel Size | Sliding Window | Kawase Advantage |
|-------------|----------------|------------------|
| 5 (radius=2)| O(n), 2 passes | None             |
| 15          | O(n), 2 passes | Minimal          |
| 35          | O(n), 2 passes | 2-4x faster      |
| 64+         | O(n), 2 passes | Significant      |

Kawase's advantage comes from O(n * log k) vs O(n * k). Since Rource uses O(n)
sliding window (independent of kernel size) with small kernel, no benefit.

---

### Hierarchical Z-Buffer

**Phase**: 57
**Claimed Performance**: 50-200% for occlusion culling

**Why Not Applicable**:

| Property       | Rource            | Hi-Z Requirement |
|----------------|-------------------|------------------|
| Dimensions     | 2D                | 3D               |
| Depth buffer   | None              | Required         |
| Occlusion      | Draw order        | Depth test       |

Rource is 2D visualization with painter's algorithm; no depth-based rendering.

---

### Tree Balancing (GC-WB, UFO Trees)

**Phase**: 55

**Why Not Applicable**:

Rource's directory tree is not a self-balancing binary search tree:
```rust
pub struct DirTree {
    nodes: Vec<Option<DirNode>>,        // Slot-based storage
    children_by_name: HashMap<...>,     // O(1) child lookup
}
```

It's an n-ary tree with HashMap index. Tree modifications are infrequent; O(1)
HashMap lookup is already optimal.

---

## Phase 75: Spatial Acceleration Algorithm Evaluation

**Date**: 2026-01-27
**Analysis Scope**: 9 candidate algorithms proposed for spatial acceleration

This section documents a comprehensive analysis of algorithms proposed for potential
performance improvement in spatial queries, rendering, and physics.

---

### H-PLOC (High-quality Parallel Locally-Ordered Clustering BVH)

**Phase**: 75
**Expected Gain**: 1.8-3.6× BVH construction
**Claimed Use**: Ray tracing, 3D scene management

**Why Not Applicable**:

| Criterion | H-PLOC Requirement | Rource Reality |
|-----------|-------------------|----------------|
| Dimensions | 3D scenes | 2D visualization |
| Primary use | Ray tracing acceleration | No ray tracing |
| Spatial queries | Hierarchical ray-box tests | QuadTree O(log n) |
| Build frequency | Per-scene or incremental | Per-frame rebuild OK |

**Analysis**:

Rource already has optimal 2D spatial structures:
- **QuadTree**: O(log n) queries for visibility and physics culling
- **GPU Spatial Hash**: O(n) for N-body physics with 3×3 neighbor queries
- **GPU Visibility Culling**: AABB intersection in compute shader

BVH is designed for 3D ray-object intersection with hierarchical early-out.
For 2D AABB-vs-viewport tests, a simple QuadTree provides equivalent O(log n)
performance with simpler implementation and better cache behavior.

**Verdict**: Domain mismatch - QuadTree optimal for 2D

---

### LBVH (Linear BVH via Morton Codes)

**Phase**: 75
**Expected Gain**: 3-6× faster BVH construction
**Claimed Use**: Real-time ray tracing, dynamic scenes

**Why Not Applicable**:

| Criterion | LBVH Requirement | Rource Reality |
|-----------|-----------------|----------------|
| Primary use | Ray tracing | No ray tracing |
| Construction | GPU Morton code sort | Not needed |
| Traversal | Ray-box intersection | AABB-only test |
| Dimensionality | 3D | 2D |

**Analysis**:

LBVH's main benefit is O(n log n) GPU-parallel BVH construction using Z-order
(Morton) curves for spatial locality. This is valuable for:
- Dynamic ray tracing scenes
- Real-time global illumination
- Large-scale collision detection with complex geometry

Rource's use case differs fundamentally:
1. No ray tracing whatsoever
2. Entities are points/circles, not complex meshes
3. Current spatial hash provides O(n) physics with excellent cache locality
4. QuadTree provides O(log n) queries, which is optimal for 2D point data

Morton codes could theoretically improve cache locality for entity iteration,
but current spatial hash grid already achieves this via cell-ordered access.

**Verdict**: Domain mismatch - no ray tracing, existing O(n) spatial hash sufficient

---

### SIMD Frustum Culling (Vectorized 6-Plane Test)

**Phase**: 75
**Expected Gain**: 4-8× CPU frustum culling
**Claimed Use**: 3D rendering with 6-plane frustum

**Why Not Applicable**:

| Criterion | 3D Frustum Culling | Rource 2D Culling |
|-----------|-------------------|-------------------|
| Planes | 6 (near, far, left, right, top, bottom) | 4 bounds (AABB) |
| Test | Point-to-plane signed distance | AABB overlap |
| Operations | 6× dot product + compare | 4× compare |
| SIMD benefit | High (4 planes parallel) | Low (already 4 ops) |

**Analysis**:

Traditional SIMD frustum culling tests a point against 6 frustum planes using
4-wide SIMD to evaluate 4 planes simultaneously:

```
// 3D frustum: 6 planes × (3 multiplies + 2 adds + 1 compare)
visible = dot(plane[i].normal, point) + plane[i].d > 0  // for all 6 planes
```

Rource's 2D culling is fundamentally simpler:

```rust
// 2D AABB: 4 comparisons only
visible = (center.x + radius >= view.min_x) &&
          (center.x - radius <= view.max_x) &&
          (center.y + radius >= view.min_y) &&
          (center.y - radius <= view.max_y)
```

**Current Implementation** (`culling.rs`):
- GPU compute shader performs 4-comparison AABB test in parallel
- All entities processed in one compute dispatch
- No CPU frustum culling needed - GPU handles it

SIMD128 is already enabled in WASM builds. The 4-comparison 2D test is already
optimal and doesn't benefit from explicit SIMD vectorization.

**Verdict**: Domain mismatch - 2D uses 4-comparison AABB, not 6-plane frustum

---

### SweepSAH + AVX2

**Phase**: 75
**Expected Gain**: 4× faster SAH BVH build
**Claimed Use**: High-quality ray tracing BVH construction

**Why Not Applicable**:

| Criterion | Requirement | Rource Constraint |
|-----------|-------------|-------------------|
| CPU arch | x86-64 with AVX2 | WASM required |
| Domain | Ray tracing | No ray tracing |
| SAH use | Split quality metric | N/A |

**Analysis**:

Surface Area Heuristic (SAH) optimizes BVH split planes by minimizing expected
ray traversal cost. AVX2 accelerates the sweep-line SAH evaluation:

```
// SAH cost function
cost(split) = C_trav + (SA_left/SA_parent) × count_left × C_isect
            + (SA_right/SA_parent) × count_right × C_isect
```

**Constraint Violations**:
1. **x86-only**: AVX2 intrinsics don't compile to WASM
2. **No ray tracing**: SAH optimizes ray-box traversal, which Rource doesn't do
3. **No mesh geometry**: SAH assumes triangles/polygons, not point entities

Even with portable SIMD, SAH itself is irrelevant - Rource has no ray queries.

**Verdict**: Platform incompatible (x86-only) + domain mismatch (no ray tracing)

---

### Conservative Rasterization

**Phase**: 75
**Expected Gain**: 1-2× for voxelization/collision
**Claimed Use**: Ensuring all covered pixels generate fragments

**Why Not Applicable**:

| Criterion | Conservative Raster | Rource Collision |
|-----------|--------------------| -----------------|
| Domain | GPU pixel coverage | CPU rectangle test |
| Output | Fragment generation | Boolean overlap |
| Precision | Sub-pixel coverage | Exact AABB |
| Use case | Voxelization, shadow maps | Label placement |

**Analysis**:

Conservative rasterization generates fragments for all pixels that a primitive
touches, even partially. This is useful for:
- Voxelization (3D grids)
- Shadow mapping (avoiding light leaks)
- Collision detection via GPU rendering

Rource's label collision detection uses exact CPU rectangle intersection:

```rust
fn rects_overlap(a: &Rect, b: &Rect) -> bool {
    a.x < b.x + b.width && a.x + a.width > b.x &&
    a.y < b.y + b.height && a.y + a.height > b.y
}
```

This is already mathematically exact - no approximation that conservative
rasterization would improve. The test is O(1) per pair.

For label collision (15-200 labels), the linear scan is acceptable. If scaling
to thousands of labels, a spatial hash grid would be the solution - not
conservative rasterization.

**Verdict**: Domain mismatch - rectangle collision already exact, no GPU raster needed

---

### Welford Online Statistics

**Phase**: 75
**Expected Gain**: 1× (single-pass vs two-pass)
**Claimed Use**: Numerically stable mean/variance calculation

**Why Not Applicable**:

| Criterion | Welford Requirement | Rource Stats |
|-----------|---------------------|--------------|
| Variance | Rolling variance calculation | Not computed |
| Precision | High-precision streaming stats | Simple averages |
| Data | Large streaming datasets | 60-frame windows |

**Analysis**:

Welford's algorithm provides numerically stable one-pass mean and variance:

```python
def welford_update(count, mean, M2, new_value):
    count += 1
    delta = new_value - mean
    mean += delta / count
    delta2 = new_value - mean
    M2 += delta * delta2
    return count, mean, M2
```

Rource's statistics are simple:
- **FPS**: Rolling 60-frame exponential moving average
- **Frame time**: Same rolling average
- **Entity counts**: Instantaneous values

No variance calculations exist in Rource's hot paths. The HudCache
(`rource-core/src/hud.rs`) uses simple averaging that's numerically stable
for the scale of values involved (frame times in milliseconds).

If variance tracking were added (e.g., frame time jitter metrics), Welford
would be the correct choice. Currently, no such requirement exists.

**Verdict**: No variance calculations in hot paths - simple averages sufficient

---

### Quantized AABB (Fixed-Point Bounds)

**Phase**: 75
**Expected Gain**: 2× memory for large BVH
**Claimed Use**: Memory-efficient BVH storage

**Why Not Applicable**:

| Criterion | Quantized AABB | Rource Entities |
|-----------|----------------|-----------------|
| Memory pressure | Large BVH (millions of nodes) | 10k-100k entities |
| Precision | 16-bit sufficient | f32 required for smooth motion |
| Structure | BVH node bounds | Entity positions |
| Access pattern | Traversal-only | Read + write (physics) |

**Analysis**:

Quantized AABBs compress bounds from 6×f32 (24 bytes) to 6×u16 (12 bytes)
by storing offsets relative to parent bounds. This halves BVH memory.

Rource's memory profile (`docs/performance/MEMORY_BUDGET.md`):

| Entity Type | Size | Memory Bottleneck? |
|-------------|------|-------------------|
| File | 128 bytes | No |
| Directory | 256 bytes | No |
| User | 192 bytes | No |
| Action | 64 bytes | No |

At 100k commits:
- Estimated memory: 165 MB
- Actual memory: 198 MB
- Well within WASM limits (~2GB)

**Why f32 is required**:
1. Smooth physics animation needs sub-pixel precision
2. Camera zoom spans 0.01× to 10×, requiring high dynamic range
3. Quantization introduces visual stepping artifacts
4. Physics calculations would need de-quantization every frame

Quantized AABB would be valuable for:
- Ray tracing BVH with millions of triangles
- Mobile GPUs with memory constraints
- Static geometry with read-only traversal

None of these apply to Rource's animated 2D visualization.

**Verdict**: Memory not a bottleneck + f32 precision required for smooth animation

---

## Already Implemented Equivalents (Phase 75 Additions)

### GPU Instancing Indirect

**Phase**: 75
**Expected Gain**: 5-20× draw calls
**Status**: **ALREADY IMPLEMENTED** in `culling.rs`

**Implementation Details**:

Rource already uses GPU-driven indirect rendering:

```rust
// culling.rs - compute shader generates draw commands
render_pass.draw_indirect(culled.indirect(), 0)
```

**Current capabilities**:
- `PrimitiveCullingBuffers` for circles, lines, quads
- GPU compute shader filters instances against view bounds
- `DrawIndirectCommand` populated by GPU, not CPU
- Integrated with visibility culling pipeline

**When enabled** (10,000+ instances, dynamic view):
- GPU determines visible instance count
- Zero CPU-GPU synchronization for instance counting
- Reduces CPU command buffer overhead

**Potential extension** (not yet implemented):
- GPU LOD filtering (combine visibility + size culling)
- GPU physics-based filtering (hide settled entities)

**Verdict**: Core feature already implemented. Extensions are incremental optimization.

---

### Spatial Hash Grid for Core Library LabelPlacer

**Phase**: 76
**Date**: 2026-01-27
**Claimed Performance**: 10-44× improvement for collision detection

**Why Not Applicable**:

The spatial hash grid optimization was evaluated for the core library's `LabelPlacer`
(`crates/rource-render/src/label.rs`). The WASM version already uses spatial hash
(`rource-wasm/src/render_phases.rs`), but the core library uses O(n) linear scan.

**Benchmark Results** (criterion, 100 samples, 95% CI):

| Labels | O(n) Baseline | Spatial Hash | Regression |
|--------|---------------|--------------|------------|
| 0      | 5.8 ns        | 234 ns       | +40× |
| 10     | 88.9 ns       | 1.06 µs      | +12× |
| 50     | 1.46 µs       | 2.87 µs      | +2× |
| 100    | 5.4 µs        | 5.8 µs       | +7% |
| Full frame (80) | 3.26 µs | 18.8 µs  | +5.8× |

**Root Cause Analysis**:

The spatial hash adds overhead that isn't amortized for small label counts:

1. **Grid initialization**: 32×32 = 1024 Vec cells with pre-allocated capacity (~32KB)
2. **Grid registration**: Each `try_place` must push to multiple grid cells
3. **Cell iteration**: Looking up and iterating over cell contents has cache misses
4. **Generation checking**: Additional branch for each entry to skip stale entries

For O(n) linear scan:
- Simple Vec iteration is cache-optimal (sequential memory access)
- AABB intersection is just 4 float comparisons (extremely fast)
- No hash computation or grid cell management

**Crossover Point Analysis**:

For n labels placed sequentially, total comparisons:
- O(n) linear scan: 0 + 1 + 2 + ... + (n-1) = n(n-1)/2 ≈ O(n²/2)
- Spatial hash: n × k where k ≈ constant (labels per cell)

Theoretical crossover at n where O(n²/2) > O(n × overhead).
Empirically, spatial hash only breaks even around 100+ labels.

**Why WASM Uses Spatial Hash**:

The WASM version in `render_phases.rs` uses spatial hash for different reasons:

1. **Frame rate target**: 42,000+ FPS requires O(1) reset (generation counter)
2. **Memory pressure**: WASM heap is constrained; generation counter avoids allocation
3. **Label count**: WASM may render more labels than native CLI
4. **Already implemented**: Phase 33 + 65 optimized the WASM version

**Decision**:

Keep O(n) linear scan for core library:
- Typical label counts: 30-100 per frame
- Sequential Vec iteration is cache-optimal
- Simpler code, less maintenance burden
- Performance is already excellent (3.26 µs for full frame)

**Reference**: `docs/performance/formal-proofs/07-label-collision-detection.md`
(documents the algorithm, but notes WASM-specific applicability)

---

## Summary Table

| Optimization               | Phase | Reason                           |
|----------------------------|-------|----------------------------------|
| Relaxed-SIMD               | 57    | Breaks determinism               |
| SSSP algorithms            | 52    | No graph problems in hot path    |
| Graph coloring             | 53    | Trees don't need coloring        |
| Quantum VQE/QAOA/Grover    | 56    | Domain and scale mismatch        |
| PGM-Index                  | 55    | Point queries, not range         |
| vers-vecs                  | 55    | x86-only, no WASM support        |
| WebGPU subgroups           | 57    | Limited browser support          |
| Kawase blur                | 57    | Small kernel size                |
| Hi-Z buffer                | 57    | 2D only                          |
| Tree balancing             | 55    | Not using BST structure          |
| GPU Barnes-Hut             | 55    | Already have spatial hash        |
| wasm-opt -O4               | 57    | Already equivalent               |
| **H-PLOC (BVH)**           | **75**| **2D visualization, QuadTree optimal** |
| **LBVH (Linear BVH)**      | **75**| **No ray tracing, spatial hash sufficient** |
| **SIMD Frustum Culling**   | **75**| **2D uses AABB, not 6-plane frustum** |
| **SweepSAH + AVX2**        | **75**| **x86-only + no ray tracing** |
| **Conservative Raster**    | **75**| **Rectangle collision already exact** |
| **Welford Statistics**     | **75**| **No variance calculations needed** |
| **Quantized AABB**         | **75**| **Memory not bottleneck, f32 required** |
| **GPU Instancing Indirect**| **75**| **ALREADY IMPLEMENTED** |
| Spatial Hash (core lib)    | 76    | Overhead > benefit for <100 labels |

---

*Last updated: 2026-01-27*
