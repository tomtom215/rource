# Rource Performance Documentation

This directory contains the complete performance optimization history, benchmark data, and
analysis documentation for the Rource project. Originally contained in a single 7,700+ line
PERFORMANCE.md file, this documentation has been organized into focused, navigable sections.

---

## Table of Contents

| Document                                                              | Purpose                                          |
|-----------------------------------------------------------------------|--------------------------------------------------|
| [OVERVIEW.md](./OVERVIEW.md)                                          | Executive summary and optimization philosophy    |
| [CHRONOLOGY.md](./CHRONOLOGY.md)                                      | Complete timeline of all 58 optimization phases  |
| [BENCHMARKS.md](./BENCHMARKS.md)                                      | All benchmark data with methodology              |
| [SUCCESSFUL_OPTIMIZATIONS.md](./SUCCESSFUL_OPTIMIZATIONS.md)          | Implemented optimizations with measured gains    |
| [NOT_APPLICABLE.md](./NOT_APPLICABLE.md)                              | Analyzed but not applicable optimizations        |
| [UNSUCCESSFUL.md](./UNSUCCESSFUL.md)                                  | Tested optimizations that performed worse        |
| [../THEORETICAL_ALGORITHMS.md](../THEORETICAL_ALGORITHMS.md)          | Advanced algorithmic research reference          |

---

## Quick Navigation

### By Category

**Core Rendering Optimizations**
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

### By Improvement Magnitude

| Improvement     | Phases                                                     |
|-----------------|------------------------------------------------------------|
| 10x or greater  | 58 (LUT directions 13.9x), 44 (same-color blend 5.3x)      |
| 2-10x           | 45 (to_argb8 2.46x), 40 (DirNode O(1))                     |
| 30-99%          | 42 (apply_commit 35%), 50 (blend_batch 43%)                |
| 10-29%          | 42 (force_layout 10.1%), 50 (apply_commit 17%)             |

### By Optimization Type

| Type                  | Examples                                                   |
|-----------------------|------------------------------------------------------------|
| Algorithmic           | Barnes-Hut O(n log n), HashSet for membership              |
| Arithmetic            | Fixed-point, reciprocal multiplication                     |
| Memory                | Zero-allocation, buffer reuse, Vec over HashMap            |
| Compile-time          | LUTs, const evaluation, precomputed constants              |

---

## Documentation Standards

All optimization documentation follows these requirements:

1. **Measurable**: Backed by criterion benchmarks with statistical significance
2. **Documented**: Before/after measurements with clear methodology
3. **Correct**: All 1,899+ tests must pass
4. **Clean**: Clippy and rustfmt compliant
5. **Verifiable**: Benchmarks can be re-run to reproduce results

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

| Metric                | Value               |
|-----------------------|---------------------|
| Total phases          | 58                  |
| Test count            | 1,899               |
| Last updated          | 2026-01-25          |
| Rust version          | 1.93.0              |
| Benchmark framework   | Criterion 0.5.1     |

---

*This documentation represents the culmination of 58 optimization phases, demonstrating
portfolio-grade attention to performance at the nanosecond and CPU cycle level.*
