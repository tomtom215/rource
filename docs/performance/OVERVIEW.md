# Performance Optimization Overview

This document provides an executive summary of Rource's performance optimization journey,
philosophy, and current state.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Optimization Philosophy](#optimization-philosophy)
3. [Current Performance State](#current-performance-state)
4. [Optimization Methodology](#optimization-methodology)
5. [Key Achievements](#key-achievements)
6. [Design Constraints](#design-constraints)

---

## Executive Summary

Rource has undergone **83 documented optimization phases** from initial development through
2026-01-29. These optimizations span every layer of the application:

| Layer                | Optimization Count | Key Improvements                               |
|----------------------|-------------------|------------------------------------------------|
| Physics Engine       | 13                | Barnes-Hut O(n log n), zero-allocation queries |
| Rendering Pipeline   | 16                | Fixed-point blending, LUT color, label collision |
| VCS Parsers          | 4                 | Iterator-based zero-allocation parsing         |
| WASM Runtime         | 8                 | Commit limits, adaptive prewarm, buffer reuse  |
| Data Structures      | 10                | HashSet membership, Vec over HashMap           |
| Browser Compatibility| 1                 | Firefox WebGPU compute shader workaround       |
| Compiler/Build       | 3                 | Rust 1.93, wasm-opt -O3, LTO                   |
| Theoretical Analysis | 6                 | Algorithm applicability assessment             |

### Portfolio Quality Metrics

| Requirement | Status |
|-------------|--------|
| 60 FPS sustained on 10k+ file repos | Verified |
| Sub-second initial load | Verified (5-10k commits) |
| Binary size < 1.5 MB gzipped | 1.03 MB |
| Test coverage | 3500+ tests passing |
| Deterministic output | Guaranteed across platforms |
| WASM function audit | 132 functions profiled |

---

## Optimization Philosophy

### Core Principles

**1. Mathematical Perfection**

Every optimization must be:
- **Measurable**: Backed by criterion benchmarks with statistical significance
- **Documented**: Added to documentation with before/after measurements
- **Correct**: All tests must pass
- **Clean**: Clippy and rustfmt compliant
- **Verifiable**: Benchmarks can be re-run to reproduce results

**2. Nanosecond and CPU Cycle Level**

We pursue optimizations at the instruction level:

| Level            | Examples                                                     |
|------------------|--------------------------------------------------------------|
| **Algorithmic**  | O(n^2) to O(n log n) via Barnes-Hut, spatial indexing        |
| **Arithmetic**   | Division to multiplication by reciprocal, sqrt elimination   |
| **Memory**       | Zero-allocation hot paths, arena allocation, buffer reuse    |
| **Compile-time** | Lookup tables, const evaluation, precomputed constants       |
| **Instruction**  | Fixed-point arithmetic, bit shifts instead of division       |

**3. Determinism Guarantee**

Rource prioritizes reproducible output over maximum performance. All operations use:
- Fixed-point arithmetic (8.8 or 16.16 formats)
- Lookup tables for transcendental functions
- Explicit rounding modes
- No floating-point approximations that vary by platform

This design decision explicitly rules out relaxed-SIMD and platform-dependent optimizations.

---

## Current Performance State

### Throughput Benchmarks (Rust 1.93.0)

| Operation                   | Throughput       | Notes                       |
|-----------------------------|------------------|-----------------------------|
| Alpha blend (same-color)    | 1.14 Gelem/s     | 5.3x faster than baseline   |
| Color from_hex              | 1.52 Gelem/s     | LUT optimization            |
| Color to_argb8              | 167 Melem/s      | 2.5x faster than baseline   |
| Easing functions            | 200 Melem/s      | Explicit multiplication     |
| Production animation        | 1.1 Gelem/s      | Combined optimizations      |
| Spatial index rebuild       | 21 Melem/s       | QuadTree O(log n)           |
| Branch curves               | 82 Melem/s       | Perpendicular optimization  |
| Bloom blur                  | 30 Melem/s       | Sliding window O(n)         |
| Scene apply_commit          | 1.6 Melem/s      | HashSet-based children      |

### Algorithmic Complexity

| Operation                 | Complexity     | Implementation               |
|---------------------------|----------------|------------------------------|
| Force-directed layout     | O(n log n)     | Barnes-Hut quadtree          |
| Spatial visibility query  | O(log n + k)   | QuadTree + visitor pattern   |
| Alpha blending            | O(pixels)      | Fixed-point SIMD-friendly    |
| Color conversion          | O(1)           | LUT lookup                   |
| Commit application        | O(files)       | HashSet directory lookup     |
| Label collision           | O(n)           | Spatial hash grid            |
| Bloom effect              | O(pixels)      | Sliding window blur          |

### GPU Physics Pipeline (9 Passes)

The GPU spatial hash pipeline achieves O(n) complexity:

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

For 5,000 entities with a 64x64 grid:
- Brute force O(n^2): 25,000,000 comparisons
- Spatial hash O(n): ~11,000 comparisons (2,200x reduction)

---

## Optimization Methodology

Every optimization follows this rigorous process:

### 1. Identify

Profile, grep for patterns, analyze algorithmic complexity.

### 2. Benchmark

Create criterion benchmarks measuring baseline performance:

```rust
fn benchmark_operation(c: &mut Criterion) {
    let mut group = c.benchmark_group("operation_name");
    group.throughput(Throughput::Elements(1000));

    group.bench_function("baseline", |b| {
        b.iter(|| baseline_implementation(black_box(input)))
    });

    group.bench_function("optimized", |b| {
        b.iter(|| optimized_implementation(black_box(input)))
    });

    group.finish();
}
```

### 3. Implement

Make targeted changes with clear before/after comments.

### 4. Verify

Run all tests, clippy, rustfmt.

### 5. Document

Update documentation with measurements and rationale.

### 6. Commit

Clear commit message referencing phase number.

---

## Key Achievements

### Highest Impact Optimizations

| Phase | Optimization               | Improvement       | Category    |
|-------|----------------------------|-------------------|-------------|
| 65    | Label grid reset           | 90x faster        | Generation  |
| 58    | LUT-based random direction | 13.9x faster      | Compile-time|
| 65    | Label sorting              | 7-8x faster       | O(n) select |
| 44    | Same-color alpha blend     | 5.3x faster       | Fixed-point |
| 45    | to_argb8 color conversion  | 2.46x faster      | LUT         |
| 50    | Rust 1.93.0 upgrade        | 43% blend_batch   | Compiler    |
| 42    | apply_commit iterator      | 35% faster        | Zero-alloc  |
| 40    | DirNode HashSet children   | O(n) to O(1)      | Algorithmic |
| 16    | Barnes-Hut force layout    | O(n^2) to O(n log n) | Algorithmic |

### Cumulative Improvements by Area

| Area             | Total Improvement                                   |
|------------------|-----------------------------------------------------|
| Alpha Blending   | 5.3x same-color, 21% batch, 81% optimized path      |
| Color Conversion | 54% from_hex, 36% from_rgba8, 62% to_argb8          |
| Physics          | O(n log n) complexity, sqrt elimination, LUT dirs   |
| Label Collision  | 90x reset, 7-8x sorting, zero per-frame allocations |
| VCS Parsing      | Zero allocations per line parsed                    |
| Scene Operations | 13-17% faster with Rust 1.93                        |

---

## Design Constraints

### Why Some Optimizations Are Not Implemented

| Constraint                 | Impact                                                |
|----------------------------|-------------------------------------------------------|
| Determinism requirement    | Rules out relaxed-SIMD, platform-dependent rounding   |
| 2D rendering only          | 3D techniques (Hi-Z buffer) not applicable            |
| Small blur kernels         | Kawase blur provides no benefit for radius=2          |
| Tree structures            | Graph coloring algorithms not needed                  |
| Point queries              | Learned indexes (PGM) not beneficial                  |
| WASM compatibility         | Some crates (vers-vecs) are x86-only                  |

### Trade-offs Made

| Decision                     | Rationale                                           |
|------------------------------|-----------------------------------------------------|
| Fixed-point over float       | Determinism > marginal performance gain             |
| QuadTree over Morton         | Query speed > rebuild speed (97x faster queries)    |
| HashMap over SoA             | Simplicity > ~5.5% frame time savings               |
| Standard sqrt over Quake     | Modern hardware sqrt is fast; accuracy preserved    |

---

## Navigation

- [Chronology](./CHRONOLOGY.md) - Complete timeline of all 88 phases
- [Benchmarks](./BENCHMARKS.md) - All benchmark data
- [Performance Baseline](./PERFORMANCE_BASELINE.md) - Comprehensive WASM audit
- [Function Profiles](./FUNCTION_PROFILES.md) - Per-function timing profiles
- [Complexity Verification](./COMPLEXITY_VERIFICATION.md) - Empirical Big-O verification
- [Successful Optimizations](./SUCCESSFUL_OPTIMIZATIONS.md) - Implemented improvements
- [Not Applicable](./NOT_APPLICABLE.md) - Analyzed but not applicable
- [Unsuccessful](./UNSUCCESSFUL.md) - Tested but performed worse

---

*Last updated: 2026-01-26*
