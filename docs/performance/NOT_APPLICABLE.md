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

---

*Last updated: 2026-01-25*
