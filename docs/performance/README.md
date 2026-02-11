# Rource Performance Documentation

This directory contains the complete performance optimization history, benchmark data, and
analysis documentation for the Rource project. Originally contained in a single 7,700+ line
PERFORMANCE.md file, this documentation has been organized into focused, navigable sections.

---

## Table of Contents

### Core Documentation

| Document | Purpose |
|----------|---------|
| [OVERVIEW.md](./OVERVIEW.md) | Executive summary and optimization philosophy |
| [CHRONOLOGY.md](./CHRONOLOGY.md) | Complete timeline of all 84 optimization phases |
| [BENCHMARKS.md](./BENCHMARKS.md) | All benchmark data with methodology |
| [PERFORMANCE_BASELINE.md](./PERFORMANCE_BASELINE.md) | **NEW** Comprehensive WASM performance audit |
| [FUNCTION_PROFILES.md](./FUNCTION_PROFILES.md) | **NEW** Per-function timing profiles |
| [COMPLEXITY_VERIFICATION.md](./COMPLEXITY_VERIFICATION.md) | **NEW** Empirical Big-O verification |

### Optimization History

| Document | Purpose |
|----------|---------|
| [SUCCESSFUL_OPTIMIZATIONS.md](./SUCCESSFUL_OPTIMIZATIONS.md) | Implemented optimizations with measured gains |
| [NOT_APPLICABLE.md](./NOT_APPLICABLE.md) | Analyzed but not applicable optimizations |
| [UNSUCCESSFUL.md](./UNSUCCESSFUL.md) | Tested optimizations that performed worse |

### Guides and References

| Document | Purpose |
|----------|---------|
| [GUIDE.md](./GUIDE.md) | General performance tips and configuration |
| [PROFILING.md](./PROFILING.md) | Profiling tools and techniques |
| [METHODOLOGY.md](./METHODOLOGY.md) | Benchmark methodology and standards |
| [ALGORITHMIC_COMPLEXITY.md](./ALGORITHMIC_COMPLEXITY.md) | Big-O analysis of all functions |
| [THEORETICAL_ALGORITHMS.md](./THEORETICAL_ALGORITHMS.md) | Advanced algorithmic research reference |
| [formal-proofs/README.md](./formal-proofs/README.md) | Mathematical proofs for core algorithms |
| [SHADERS.md](./SHADERS.md) | GPU shader optimization reference |
| [FUTURE_WORK.md](./FUTURE_WORK.md) | Expert+ technical roadmap |

---

## Quick Navigation

### By Category

**Core Rendering Optimizations**
- Label collision detection (Phase 65) - 90x reset, 7-8x sorting
- Fixed-point alpha blending (Phase 44) - 21% batch improvement
- Color conversion LUTs (Phase 45) - 54% from_hex, 62% to_argb8
- Bloom strip-based processing (Phase 43) - 6.6% improvement

**Physics Optimizations**
- Barnes-Hut O(n log n) force layout (Phase 16)
- Force normalization (Phase 47) - Eliminates redundant sqrt
- LUT-based random direction (Phase 58) - 13.9x faster

**Parser Optimizations**
- Zero-allocation VCS parsing (Phase 46)
- Iterator-based field extraction

**WASM Optimizations**
- Large repository protection (Phase 41)
- HashMap to Vec forces buffer (Phase 42) - 10.1% faster

**Browser-Specific Optimizations**
- Firefox GPU physics workaround (Phase 60) - 6-7x improvement

### By Improvement Magnitude

| Improvement | Phases |
|-------------|--------|
| 10x or greater | 65 (label reset 90x), 58 (LUT directions 13.9x), 65 (label sort 7-8x), 44 (same-color blend 5.3x) |
| 2-10x | 62 (adaptive theta 2.6x), 60 (Firefox workaround 6-7x), 45 (to_argb8 2.46x), 40 (DirNode O(1)) |
| 30-99% | 61 (texture batching 99.8% draw reduction), 42 (apply_commit 35%), 50 (blend_batch 43%) |
| 10-29% | 66 (rustc-hash 2.x 14-19%), 42 (force_layout 10.1%), 50 (apply_commit 17%) |

### By Optimization Type

| Type                  | Examples                                                   |
|-----------------------|------------------------------------------------------------|
| Algorithmic           | Barnes-Hut O(n log n), HashSet for membership              |
| Arithmetic            | Fixed-point, reciprocal multiplication                     |
| Memory                | Zero-allocation, buffer reuse, Vec over HashMap            |
| Compile-time          | LUTs, const evaluation, precomputed constants              |

---

## Algorithm Reference

Quick reference for the core algorithms and their complexities. For formal proofs, see [formal-proofs/README.md](./formal-proofs/README.md).

### Spatial Data Structures

| Algorithm | Complexity | Location |
|-----------|-----------|----------|
| QuadTree | O(log n) query/insert | `rource-core/src/physics/spatial.rs` |
| Barnes-Hut | O(n log n) force calc | `rource-core/src/physics/barnes_hut.rs` |
| GPU Spatial Hash | O(n) with GPU | `rource-render/src/backend/wgpu/spatial_hash.rs` |

### Physics Simulation

| Algorithm | Complexity | Location |
|-----------|-----------|----------|
| Force-Directed Layout | O(n log n) | `rource-core/src/physics/force.rs` |
| Semi-Implicit Euler | O(n) | `rource-core/src/physics/force.rs` |

### Rendering

| Algorithm | Complexity | Location |
|-----------|-----------|----------|
| Software Rasterization | O(pixels) | `rource-render/src/backend/software/` |
| Fixed-Point Blending | O(1) per pixel | `rource-render/src/backend/software/optimized.rs` |
| Kawase Blur (Bloom) | O(pixels × passes) | `rource-render/src/backend/wgpu/bloom.rs` |

### Complexity Distribution

From [ALGORITHMIC_COMPLEXITY.md](./ALGORITHMIC_COMPLEXITY.md):

- **87%** of functions are O(1)
- **4%** are O(log n)
- **6%** are O(n)
- **2%** are O(n log n)
- **<1%** are O(n²) (fallback paths only)

---

## Documentation Standards

All optimization documentation follows these requirements:

1. **Measurable**: Backed by criterion benchmarks with 100+ samples, 95% CI
2. **Documented**: Before/after measurements with clear methodology
3. **Correct**: All 2900+ tests must pass
4. **Clean**: Clippy and rustfmt compliant (zero warnings)
5. **Verifiable**: Benchmarks can be re-run to reproduce results
6. **Complexity Verified**: Big-O claims empirically verified at 5 input sizes

---

## Benchmark Reproduction

To reproduce any benchmark in this documentation:

```bash
# Run all benchmarks
cargo bench

# Run specific benchmark suite
cargo bench --bench blend_perf
cargo bench --bench color_perf
cargo bench --bench visual_perf
cargo bench --bench scene_perf
cargo bench --bench easing_perf
cargo bench --bench micro_opt_analysis

# Run with detailed output
cargo bench -- --verbose
```

---

## Version Information

| Metric | Value |
|--------|-------|
| Total phases | 77 |
| Test count | 2,100+ |
| Last updated | 2026-01-27 |
| Rust version | 1.93.0 |
| Benchmark framework | Criterion 0.8 |
| Platform | x86_64-unknown-linux-gnu |
| Audit coverage | 132 WASM functions profiled |

---

*This documentation represents the culmination of 84 optimization phases, demonstrating
Expert+ portfolio-grade attention to performance at the picosecond and nanosecond level.*
