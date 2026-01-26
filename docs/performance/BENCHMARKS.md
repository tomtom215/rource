# Benchmark Data Reference

Comprehensive collection of all benchmark measurements from Rource optimization phases.
All benchmarks use Criterion 0.5.1 with `--sample-size 50` for statistical significance.

---

## Table of Contents

1. [Benchmark Environment](#benchmark-environment)
2. [Reproduction Commands](#reproduction-commands)
3. [Alpha Blending Benchmarks](#alpha-blending-benchmarks)
4. [Color Conversion Benchmarks](#color-conversion-benchmarks)
5. [Physics Benchmarks](#physics-benchmarks)
6. [Rendering Benchmarks](#rendering-benchmarks)
7. [Scene Operation Benchmarks](#scene-operation-benchmarks)
8. [Animation Benchmarks](#animation-benchmarks)
9. [Spatial Index Benchmarks](#spatial-index-benchmarks)
10. [Rust Version Comparison](#rust-version-comparison)

---

## Benchmark Environment

| Component           | Value                               |
|---------------------|-------------------------------------|
| Platform            | x86_64-unknown-linux-gnu            |
| Rust Version        | 1.93.0 (254b59607 2026-01-19)       |
| Benchmark Framework | Criterion 0.5.1                     |
| Test Suite          | 1,899 tests                         |
| Sample Size         | 50 (default for statistical rigor)  |

---

## Reproduction Commands

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

# Run with detailed output and no plots
cargo bench -- --verbose --noplot

# Run specific benchmark function
cargo bench -- "alpha_blend"
```

---

## Alpha Blending Benchmarks

**Source**: `crates/rource-render/benches/blend_perf.rs`
**Phase**: 44

### Single Pixel Operations

| Operation            | Baseline  | Fixed-Point | Improvement |
|----------------------|-----------|-------------|-------------|
| alpha=0.5            | 7.12 ns   | 6.54 ns     | -8%         |
| alpha=0.75           | 7.05 ns   | 6.28 ns     | -11%        |
| alpha=1.0 (opaque)   | 6.70 ns   | 5.19 ns     | -23%        |

### Batch Operations

| Batch Size | Baseline    | Fixed-Point | Throughput (FP) | Improvement |
|------------|-------------|-------------|-----------------|-------------|
| 10,000     | 108.9 us    | 83.9 us     | 119 Melem/s     | -23%        |
| 100,000    | 661 us      | 522 us      | 191 Melem/s     | -21%        |

### Same-Color Optimization

| Batch Size | Baseline    | Fixed-Point | Throughput (FP) | Improvement |
|------------|-------------|-------------|-----------------|-------------|
| 50,000     | 236 us      | 44 us       | 1.13 Gelem/s    | -81%        |

### Rust 1.93.0 Impact on Blending

| Operation              | Rust 1.82 | Rust 1.93 | Improvement |
|------------------------|-----------|-----------|-------------|
| blend_batch/10000      | 108.9 us  | 61.7 us   | -43%        |
| blend_batch/100000     | 1.086 ms  | 635 us    | -42%        |
| blend_batch FP/10000   | 83.9 us   | 51.8 us   | -38%        |
| blend_batch FP/100000  | 835 us    | 527 us    | -37%        |

---

## Color Conversion Benchmarks

**Source**: `crates/rource-math/benches/color_perf.rs`
**Phase**: 45

### Single Operations

| Operation        | Baseline  | LUT/+0.5  | Improvement |
|------------------|-----------|-----------|-------------|
| from_hex         | 8.49 ns   | 3.91 ns   | -54%        |
| from_rgba8       | 11.16 ns  | 7.16 ns   | -36%        |
| to_argb8         | 88.6 ns   | 33.4 ns   | -62%        |

### Batch Operations (1,000 elements)

| Operation           | Baseline  | Optimized | Speedup |
|---------------------|-----------|-----------|---------|
| from_hex batch      | 690 ns    | 656 ns    | -5%     |
| to_argb8 batch      | 14.5 us   | 5.9 us    | -59%    |

### Rust 1.93.0 Impact on Color

| Operation            | Rust 1.82 | Rust 1.93 | Improvement |
|----------------------|-----------|-----------|-------------|
| from_hex_baseline    | 1.050 us  | 0.688 us  | -34%        |
| from_hex_lut         | 757 ns    | 658 ns    | -13%        |
| from_rgba8/lut       | 7.34 ns   | 7.12 ns   | -3%         |
| to_argb8/no_round    | 34.74 ns  | 33.67 ns  | -3%         |

---

## Physics Benchmarks

**Sources**:
- `crates/rource-core/benches/scene_perf.rs`
- `crates/rource-core/benches/micro_opt_analysis.rs`

### Force Layout (Phase 42-43)

| Entity Count | Before    | After     | Improvement |
|--------------|-----------|-----------|-------------|
| 50 dirs      | 11.8 us   | 11.4 us   | -3.2%       |
| 100 dirs     | 164 us    | 148 us    | -10.1%      |
| 100 dirs (µ) | 118.8 us  | 114.4 us  | -3.7%       |

### Random Direction Generation (Phase 58)

| Method     | Time (1000) | Throughput   | Speedup |
|------------|-------------|--------------|---------|
| sin/cos    | 12.1 us     | 82 Melem/s   | 1.0x    |
| Hash-based | 1.4 us      | 715 Melem/s  | 8.7x    |
| LUT-based  | 0.87 us     | 1.13 Gelem/s | 13.9x   |

### Fast Inverse Square Root (Phase 58)

| Method              | Time (1000) | Throughput   | Speedup |
|---------------------|-------------|--------------|---------|
| 1.0/sqrt(x)         | 1.05 us     | 948 Melem/s  | 1.0x    |
| Quake 1-iteration   | 0.79 us     | 1.27 Gelem/s | 1.33x   |
| Quake 2-iteration   | 1.92 us     | 519 Melem/s  | 0.55x   |

### Octant Length Approximation (Phase 58)

| Method           | Time (1000) | Throughput   | Speedup |
|------------------|-------------|--------------|---------|
| sqrt(x^2 + y^2)  | 1.10 us     | 909 Melem/s  | 1.0x    |
| Octant basic     | 1.10 us     | 911 Melem/s  | 1.00x   |
| Octant improved  | 2.15 us     | 464 Melem/s  | 0.51x   |

### Integration Methods (Phase 58)

| Method             | Time (1000) | Throughput   | Speedup |
|--------------------|-------------|--------------|---------|
| Semi-implicit Euler| 2.62 us     | 381 Melem/s  | 1.0x    |
| Verlet             | 2.60 us     | 384 Melem/s  | 1.01x   |
| Velocity Verlet    | 2.86 us     | 349 Melem/s  | 0.92x   |

### Combined Force Calculation (Phase 58)

| Method          | Time (1000) | Throughput   | Result  |
|-----------------|-------------|--------------|---------|
| Standard        | 3.05 us     | 328 Melem/s  | 1.0x    |
| Fast inv_sqrt   | 3.96 us     | 253 Melem/s  | SLOWER  |
| Octant length   | 3.19 us     | 311 Melem/s  | SLOWER  |

---

## Rendering Benchmarks

### Bloom Effect (Phase 43)

**Source**: `crates/rource-render/benches/bloom_perf.rs`

| Resolution  | Before    | After     | Improvement |
|-------------|-----------|-----------|-------------|
| 480x270     | 3.49 ms   | 3.26 ms   | -6.6%       |
| 960x540     | 17.49 ms  | 16.77 ms  | -4.1%       |

### Bloom Pass Scaling

| Passes | Time (480x270) | Throughput   |
|--------|----------------|--------------|
| 1      | 3.06 ms        | 42.3 Melem/s |
| 2      | 4.11 ms        | 31.6 Melem/s |
| 3      | 5.02 ms        | 25.8 Melem/s |
| 4      | 6.21 ms        | 20.9 Melem/s |

### Perpendicular Vector (Phase 48)

**Source**: `crates/rource-render/benches/visual_perf.rs`

| Operation              | Baseline | Optimized | Improvement |
|------------------------|----------|-----------|-------------|
| Perpendicular (horiz)  | 4.51 ns  | 1.28 ns   | -72%        |
| Perpendicular (3-4-5)  | 4.65 ns  | 1.28 ns   | -72%        |
| Branch curve (short)   | 15.07 ns | 14.20 ns  | -6%         |
| Branch curve (medium)  | 15.19 ns | 13.81 ns  | -9%         |
| Branch curve (long)    | 15.30 ns | 13.50 ns  | -12%        |

### Branch Curve Batch

| Batch Size | Baseline   | Optimized  | Throughput (Opt) | Improvement |
|------------|------------|------------|------------------|-------------|
| 1,000      | 14.04 us   | 12.29 us   | 81.4 Melem/s     | -12%        |

---

## Scene Operation Benchmarks

**Source**: `crates/rource-core/benches/scene_perf.rs`

### apply_commit (Phase 42)

| File Count | Before    | After     | Improvement |
|------------|-----------|-----------|-------------|
| 50 files   | 37 us     | 24 us     | -35%        |

### Scene Update (Phase 43)

| File Count | Before    | After     | Improvement |
|------------|-----------|-----------|-------------|
| 500 files  | 200.5 us  | 195.3 us  | -2.6%       |
| 5000 files | 361 us    | 335 us    | -7.2%       |

### Rust 1.93.0 Impact on Scene Operations

| Operation              | Rust 1.82 | Rust 1.93 | Improvement |
|------------------------|-----------|-----------|-------------|
| apply_commit/1         | 150 ns    | 138 ns    | -8%         |
| apply_commit/10        | 5.31 us   | 4.41 us   | -17%        |
| apply_commit/50        | 30.9 us   | 25.9 us   | -16%        |
| apply_commit/100       | 59.5 us   | 49.8 us   | -16%        |
| rebuild_spatial/500    | 46.4 us   | 40.3 us   | -13%        |
| rebuild_spatial/2000   | 122.7 us  | 104.8 us  | -15%        |
| rebuild_spatial/10000  | 553.9 us  | 467.2 us  | -16%        |

---

## Animation Benchmarks

### Easing Functions (Phase 49)

**Source**: `crates/rource-core/benches/easing_perf.rs`

| Easing      | Time (1000) | Throughput   |
|-------------|-------------|--------------|
| Linear      | 5.10 us     | 196 Melem/s  |
| QuadOut     | 5.61 us     | 178 Melem/s  |
| QuadInOut   | 4.97 us     | 201 Melem/s  |
| CubicOut    | 4.91 us     | 204 Melem/s  |
| QuartOut    | 5.03 us     | 199 Melem/s  |
| QuintOut    | 4.99 us     | 200 Melem/s  |

### Production Animation Throughput

| Scenario      | Time (3000) | Throughput   |
|---------------|-------------|--------------|
| QuadOut       | 2.68 us     | 1.12 Gelem/s |
| CubicInOut    | 4.34 us     | 690 Melem/s  |

---

## Spatial Index Benchmarks

### Morton vs QuadTree (Phase 57)

**Rebuild Performance**:

| Entity Count | QuadTree  | Morton    | Speedup    |
|--------------|-----------|-----------|------------|
| 500          | 22.8 us   | 7.7 us    | 3.0x       |
| 2,000        | 83.2 us   | 36.8 us   | 2.3x       |
| 10,000       | 422.6 us  | 195.8 us  | 2.2x       |

**Query Performance**:

| Entity Count | QuadTree  | Morton    | Comparison         |
|--------------|-----------|-----------|-------------------|
| 500          | 35.7 ns   | 945 ns    | QuadTree 26x faster |
| 2,000        | 35.9 ns   | 3.5 us    | QuadTree 97x faster |

**Net Impact Analysis** (10,000 entities):
- Rebuild savings: 45.4 us/frame (every 5 frames)
- Query cost increase: 3.46 us/frame
- With hover (3 queries): 10.4 us per mouse event
- **Conclusion**: Morton is worse for query-heavy workloads

### SoA vs AoS Layout (Phase 57)

**File Update Loop**:

| Entity Count | HashMap AoS | Vec AoS | SoA      | HashMap to SoA |
|--------------|-------------|---------|----------|----------------|
| 500          | 1.20 us     | 0.90 us | 0.75 us  | 1.6x (37%)     |
| 2,000        | 5.16 us     | 3.66 us | 2.80 us  | 1.84x (46%)    |
| 10,000       | 33.5 us     | 19.3 us | 14.9 us  | 2.25x (55%)    |

**Spatial Index Rebuild (positions only)**:

| Entity Count | HashMap Extract | SoA Array | Speedup |
|--------------|-----------------|-----------|---------|
| 500          | 29.4 us         | 27.3 us   | 8%      |
| 2,000        | 111 us          | 91 us     | 22%     |
| 10,000       | 557 us          | 453 us    | 23%     |

**Reality Check**: Frame-level impact is ~5.5%, not 20-200%

---

## Rust Version Comparison

### Rust 1.82.0 vs 1.93.0 Summary

| Category         | Average Improvement | Best Case              |
|------------------|---------------------|------------------------|
| Color Conversion | -12%                | -34% (from_hex_baseline) |
| Alpha Blending   | -30%                | -43% (blend_batch)     |
| Bloom Effect     | -5%                 | -9% (bloom_blur 480)   |
| Scene Operations | -14%                | -17% (apply_commit)    |
| Easing Functions | 0%                  | N/A (already optimal)  |

### LLVM Improvements Observed

1. **Better loop vectorization**: Blend batch 40% faster
2. **Improved division handling**: from_hex_baseline 34% faster
3. **Collection optimization**: HashMap operations faster
4. **Memory access patterns**: Bloom blur cache optimization

---

## Throughput Summary

All measurements in elements per second.

| Operation               | Throughput   | Phase |
|-------------------------|--------------|-------|
| Alpha blend same-color  | 1.14 Gelem/s | 44    |
| Color from_hex LUT      | 1.52 Gelem/s | 45    |
| LUT random direction    | 1.13 Gelem/s | 58    |
| Production animation    | 1.1 Gelem/s  | 49    |
| Color to_argb8          | 167 Melem/s  | 45    |
| Alpha blend batch       | 191 Melem/s  | 44    |
| Easing functions        | 200 Melem/s  | 49    |
| Branch curves           | 82 Melem/s   | 48    |
| Bloom blur              | 30 Melem/s   | 43    |
| Spatial index rebuild   | 21 Melem/s   | 50    |
| Scene apply_commit      | 1.6 Melem/s  | 42    |

---

## Early FPS Benchmarks (2026-01-21)

Historical benchmark data from the first FPS optimization report, superseded by Phases 40-58.

**Test Count at Time**: 245 tests (now 1,899+)

### Allocation Reuse for Hot Path Buffers

**Location**: `rource-core/src/scene/mod.rs`

Reusable buffers added: `completed_actions_buffer`, `files_to_remove_buffer`, `forces_buffer`, `dir_data_buffer`

| Benchmark | Before | After | Change |
|-----------|--------|-------|--------|
| force_layout/10 dirs | 5.18 us | 4.41 us | **-14.5%** |
| force_layout/50 dirs | 60.5 us | 57.9 us | **-4.3%** |
| spatial_query/500 files | 4.53 us | 4.42 us | **-2.4%** |

### Squared Distance Comparisons

**Location**: `rource-core/src/scene/mod.rs`

| Benchmark | Before | After | Change |
|-----------|--------|-------|--------|
| scene_update/1000 files | 437 us | 382 us | **-12.6%** |
| scene_update/5000 files | 524 us | 471 us | **-10.1%** |
| force_layout/100 dirs | 223 us | 199 us | **-10.8%** |

### Extension Statistics Caching

| Benchmark | Before | After | Change |
|-----------|--------|-------|--------|
| extension_stats/500 (cached) | 17.2 us | 549 ns | **-96.8%** |
| extension_stats/2000 (cached) | 62.8 us | 2.0 us | **-96.8%** |

### Cumulative Scene Update Results

| File Count | Baseline | Optimized | Improvement |
|------------|----------|-----------|-------------|
| 100 | 22.2 us | 18.8 us | **-15.3%** |
| 500 | 418 us | 386 us | **-7.7%** |
| 1000 | 401 us | 392 us | **-2.2%** |
| 5000 | 513 us | 487 us | **-5.1%** |

### FPS Impact Analysis (at 60 FPS, 16.67ms frame budget)

| Scene Size | Before | After | FPS Headroom |
|------------|--------|-------|--------------|
| 500 files | 418 us | 386 us | +32 us (~2% more budget) |
| 5000 files | 513 us | 487 us | +26 us (~1.5% more budget) |
| 10000 files | ~1 ms | ~0.9 ms | +100 us (~6% more budget) |

---

## Texture Batching Benchmarks (Phase 61)

**Source**: `crates/rource-render/benches/texture_batching.rs`
**Phase**: 61

These benchmarks measure the CPU-side overhead difference between per-texture HashMap
rendering and texture array batching for avatar textures.

### Instance Population

Time to add instances to buffer structures during render traversal.

| Avatar Count | Per-Texture | Texture Array | Improvement | Array Throughput |
|--------------|-------------|---------------|-------------|------------------|
| 50           | 586.38 ns   | 300.28 ns     | **-48.8%**  | 166.51 Melem/s   |
| 100          | 1.1552 µs   | 564.60 ns     | **-51.1%**  | 177.12 Melem/s   |
| 200          | 2.4142 µs   | 1.1456 µs     | **-52.5%**  | 174.58 Melem/s   |
| 300          | 3.9438 µs   | 1.7219 µs     | **-56.3%**  | 174.23 Melem/s   |
| 500          | 6.7929 µs   | 3.0585 µs     | **-55.0%**  | 163.48 Melem/s   |

### Flush/Dispatch Overhead

Simulated overhead of iterating buffers and dispatching draw calls.

| Avatar Count | Per-Texture | Texture Array | Improvement | Array Throughput |
|--------------|-------------|---------------|-------------|------------------|
| 50           | 139.44 ns   | 11.76 ns      | **-91.6%**  | 4.25 Gelem/s     |
| 100          | 286.01 ns   | 21.32 ns      | **-92.5%**  | 4.69 Gelem/s     |
| 200          | 593.97 ns   | 40.06 ns      | **-93.3%**  | 4.99 Gelem/s     |
| 300          | 875.50 ns   | 62.86 ns      | **-92.8%**  | 4.77 Gelem/s     |
| 500          | 1.4737 µs   | 99.91 ns      | **-93.2%**  | 5.00 Gelem/s     |

### Full Frame Cycle

Complete frame cycle: clear + populate + flush.

| Avatar Count | Per-Texture | Texture Array | Improvement | Array Throughput |
|--------------|-------------|---------------|-------------|------------------|
| 100          | 1.4724 µs   | 641.97 ns     | **-56.4%**  | 155.77 Melem/s   |
| 300          | 4.8063 µs   | 1.9716 µs     | **-59.0%**  | 152.16 Melem/s   |
| 500          | 8.0948 µs   | 3.2591 µs     | **-59.7%**  | 153.41 Melem/s   |

### Draw Call Reduction (Verified)

Mathematical verification of draw call reduction from O(n) to O(1).

| Avatar Count | Per-Texture Draws | Texture Array Draws | Reduction |
|--------------|-------------------|---------------------|-----------|
| 50           | 50                | 1                   | **98.0%** |
| 100          | 100               | 1                   | **99.0%** |
| 200          | 200               | 1                   | **99.5%** |
| 300          | 300               | 1                   | **99.7%** |
| 500          | 500               | 1                   | **99.8%** |

### Algorithmic Complexity Analysis

Verification of O(n) vs O(1) draw call count scaling.

| n (avatars) | Per-Texture Time | Texture Array Time | Per-Texture Scaling |
|-------------|------------------|--------------------|--------------------|
| 10          | 10.00 ns         | 367.39 ps          | 1.00x (baseline)   |
| 50          | 51.82 ns         | 361.46 ps          | 5.18x              |
| 100         | 104.57 ns        | 366.55 ps          | 10.46x             |
| 250         | 263.02 ns        | 351.50 ps          | 26.30x             |
| 500         | 530.72 ns        | 356.67 ps          | 53.07x             |

**Mathematical Proof**:
- Per-texture path: Time ∝ n (linear scaling confirmed)
  - Regression: y ≈ 1.06n ns (R² ≈ 0.999)
- Texture array path: Time ≈ 360 ps (constant, independent of n)
  - Variance: σ = 6.8 ps (< 2% of mean)

**Complexity Classification**:
- Per-texture: **O(n)** draw calls, **O(n)** dispatch time
- Texture array: **O(1)** draw calls, **O(1)** dispatch time

---

## Adaptive Barnes-Hut Theta Benchmarks (Phase 62)

**Source**: `crates/rource-core/benches/barnes_hut_theta.rs`
**Phase**: 62

These benchmarks measure the performance improvement from adaptive theta selection
in the Barnes-Hut force calculation algorithm.

### Fixed θ=0.8 vs Adaptive Theta

Force calculation time comparison between the previous fixed theta and the new adaptive theta.

| Entities | Fixed θ=0.8 | Adaptive θ   | Theta  | Improvement | Throughput (adaptive) |
|----------|-------------|--------------|--------|-------------|----------------------|
| 100      | 26.10 µs    | 26.83 µs     | 0.80   | ~0%         | 3.73 Melem/s         |
| 500      | 296.71 µs   | 210.62 µs    | 1.00   | **-29.0%**  | 2.37 Melem/s         |
| 1000     | 714.81 µs   | 419.96 µs    | 1.15   | **-41.2%**  | 2.38 Melem/s         |
| 5000     | 4.25 ms     | 1.64 ms      | 1.50   | **-61.4%**  | 3.05 Melem/s         |

### Theta Value Scaling

Adaptive theta values computed for different entity counts.

| Entities | Computed θ | Formula Component              |
|----------|------------|--------------------------------|
| 100      | 0.80       | Below threshold, default       |
| 200      | 0.80       | At threshold, default          |
| 500      | 1.00       | log₂(2.5) / log₂(25) × 0.7     |
| 1000     | 1.15       | log₂(5) / log₂(25) × 0.7       |
| 2000     | 1.30       | log₂(10) / log₂(25) × 0.7      |
| 5000     | 1.50       | At max, clamped                |
| 10000    | 1.50       | Above max, clamped             |

### Full Cycle Performance

Complete force layout cycle including tree construction.

| Entities | Fixed θ=0.8 | Adaptive   | Improvement | Throughput (adaptive) |
|----------|-------------|------------|-------------|----------------------|
| 100      | 31.02 µs    | 31.02 µs   | 0%          | 3.22 Melem/s         |
| 500      | 337.72 µs   | 247.51 µs  | **-26.7%**  | 2.02 Melem/s         |
| 1000     | 904.09 µs   | 625.23 µs  | **-30.8%**  | 1.60 Melem/s         |
| 5000     | 4.76 ms     | 2.25 ms    | **-52.7%**  | 2.22 Melem/s         |

### Theta Speed Comparison (All Values)

Force calculation time at different fixed theta values.

| Entities | θ=0.3      | θ=0.5      | θ=0.7      | θ=0.8      | θ=1.0      | θ=1.2      | θ=1.5      |
|----------|------------|------------|------------|------------|------------|------------|------------|
| 100      | 76.30 µs   | 44.13 µs   | 30.84 µs   | 26.83 µs   | 19.56 µs   | 15.29 µs   | 11.42 µs   |
| 500      | 925.60 µs  | 539.27 µs  | 357.04 µs  | 300.92 µs  | 211.09 µs  | 144.48 µs  | 84.16 µs   |
| 1000     | 2.48 ms    | 1.31 ms    | 857.24 µs  | 780.20 µs  | 531.06 µs  | 389.97 µs  | 269.10 µs  |
| 5000     | 18.38 ms   | 8.33 ms    | 5.22 ms    | 4.21 ms    | 3.04 ms    | 2.39 ms    | 1.60 ms    |

### Adaptive Theta Calculation Overhead

Time to compute the adaptive theta value (negligible).

| Entities | Overhead   | Fraction of Force Calc |
|----------|------------|------------------------|
| 100      | 1.31 ns    | 0.005%                 |
| 500      | 1.29 ns    | 0.0004%                |
| 1000     | 1.31 ns    | 0.0002%                |
| 5000     | 1.21 ns    | 0.00003%               |

### Speedup Summary

| Entities | Speedup Factor | Improvement % |
|----------|----------------|---------------|
| 100      | 1.0×           | 0%            |
| 500      | 1.41×          | 29%           |
| 1000     | 1.70×          | 41%           |
| 5000     | 2.59×          | 61%           |

**Mathematical Verification**:
- Speedup(n) = Time(θ=0.8, n) / Time(θ=adaptive, n)
- At n=5000: 4.25 ms / 1.64 ms = 2.59×

---

## Label Collision Detection Benchmarks (Phase 65)

**Source**: `rource-wasm/src/render_phases.rs`
**Phase**: 65
**Target**: 42,000 FPS (23.8µs frame budget)

These benchmarks measure the CPU-side overhead of label collision detection
optimizations for high-frame-rate rendering targeting 42,000 FPS.

### LabelPlacer::reset() - Generation Counter Pattern

Replaced O(1024) grid clearing with O(1) amortized generation counter.

| Operation | Before | After | Improvement |
|-----------|--------|-------|-------------|
| reset() (1024 cells) | 17,942 ns | 198 ns | **90.0×** |

**Mathematical Proof**:
- Before: T(n) = O(cells × avg_entries) = O(1024 × ~17) ≈ 17,942 ns
- After: T(n) = O(1) increment + amortized compaction
- Compaction triggered when stale_entry_count > 2048 (LABEL_GRID_STALE_THRESHOLD)
- Amortized cost: ~198 ns/op (99th percentile)

### LabelPlacer Operations

| Operation | Time | Throughput | Notes |
|-----------|------|------------|-------|
| try_place() | 268 ns | 3.73 Melem/s | Single label placement |
| try_place_with_fallback() | 276 ns | 3.62 Melem/s | With offset fallback |
| reset() (optimized) | 198 ns | 5.05 Melem/s | Generation counter |

### Partial Sorting Optimizations

Replaced O(n log n) full sort with O(n) partial selection using `select_nth_unstable_by`.

| Operation | Before (sort) | After (select) | Improvement |
|-----------|---------------|----------------|-------------|
| Beam sorting (15 beams) | ~850 ns | 99 ns | **8.6×** |
| User label sorting (max_labels) | ~720 ns | 99 ns | **7.3×** |
| File label sorting (max_labels) | ~680 ns | 95 ns | **7.2×** |

**Algorithm**:
```rust
// O(n) partial selection instead of O(n log n) full sort
if select_count > 0 && select_count < candidates.len() {
    candidates.select_nth_unstable_by(select_count - 1, |a, b| {
        b.priority.partial_cmp(&a.priority).unwrap_or(Ordering::Equal)
    });
}
```

### Full Frame Label Rendering

Complete label rendering cycle for typical mobile scene (30 users, 50 files).

| Scenario | Time | Frame Budget | Headroom |
|----------|------|--------------|----------|
| 30 users + 50 files | 33 µs | 23.8 µs | -9.2 µs |
| 15 users + 30 files | 18 µs | 23.8 µs | +5.8 µs |
| 10 users + 20 files | 12 µs | 23.8 µs | +11.8 µs |

**Note**: Full frame time includes label collision detection, placement, and rendering.
At 42,000 FPS target (23.8µs budget), smaller scenes fit within budget while
larger scenes may require adaptive label limits.

### Allocation Elimination

Replaced per-frame Vec allocations with reusable buffers.

| Optimization | Allocations/Frame | Impact |
|--------------|-------------------|--------|
| user_label_candidates_buf | 0 (was 1) | ~50 ns saved |
| Generation counter (no grid clear) | 0 (was 1024) | ~17,700 ns saved |

**Implementation**:
```rust
// Before: Allocates new Vec every frame
let mut candidates: Vec<(UserId, Vec2, f32, f32, f32)> = Vec::new();

// After: Reuses pre-allocated buffer
self.user_label_candidates_buf.clear();
// ... populate buffer ...
```

### Complexity Summary

| Component | Before | After | Verification |
|-----------|--------|-------|--------------|
| Grid reset | O(1024) | O(1) amortized | Generation counter |
| Beam sorting | O(n log n) | O(n) | select_nth_unstable |
| User label sorting | O(v log v) | O(v) | select_nth_unstable |
| File label sorting | O(f log f) | O(f) | select_nth_unstable |
| Buffer allocation | O(n) allocs | O(1) | Reusable buffers |

---

*Last updated: 2026-01-26*
