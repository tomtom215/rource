# Unsuccessful Optimizations

This document catalogs optimization techniques that were benchmarked but found to
perform the same or worse than existing implementations. These serve as valuable
documentation to prevent future re-investigation of already-tested approaches.

---

## Table of Contents

1. [Spatial Index Alternatives](#spatial-index-alternatives)
2. [Numerical Approximations](#numerical-approximations)
3. [Integration Methods](#integration-methods)
4. [Bloom Algorithm Alternatives](#bloom-algorithm-alternatives)

---

## Spatial Index Alternatives

### Morton-Ordered Linear Structure

**Phase**: 57
**Concept**: Replace pointer-based QuadTree with sorted Morton codes + binary search

**Implementation**:
```rust
pub fn morton_encode_2d(x: u16, y: u16) -> u32 {
    fn spread(mut n: u32) -> u32 {
        n = (n | (n << 8)) & 0x00FF00FF;
        n = (n | (n << 4)) & 0x0F0F0F0F;
        n = (n | (n << 2)) & 0x33333333;
        (n | (n << 1)) & 0x55555555
    }
    spread(x as u32) | (spread(y as u32) << 1)
}
```

**Claimed Benefits**:
- ~2x bandwidth reduction vs pointer chasing
- Better cache locality for spatial queries

**Benchmark Results**:

**Rebuild Performance** (where Morton wins):

| Entity Count | QuadTree  | Morton    | Speedup   |
|--------------|-----------|-----------|-----------|
| 500          | 22.8 us   | 7.7 us    | 3.0x      |
| 2,000        | 83.2 us   | 36.8 us   | 2.3x      |
| 10,000       | 422.6 us  | 195.8 us  | 2.2x      |

**Query Performance** (where Morton loses catastrophically):

| Entity Count | QuadTree  | Morton    | Comparison              |
|--------------|-----------|-----------|-------------------------|
| 500          | 35.7 ns   | 945 ns    | **QuadTree 26x faster** |
| 2,000        | 35.9 ns   | 3.5 us    | **QuadTree 97x faster** |

**Net Impact Analysis** (10,000 entities):
- Rebuild savings: (422.6 - 195.8) us / 5 = 45.4 us/frame (every 5 frames)
- Query cost per frame: 3.5 us - 0.036 us = 3.46 us
- With hover (3 queries per mouse event): 10.4 us additional

**Conclusion**: Morton is **NOT beneficial** for Rource's query-heavy workload.
The research claim of "20-50% on queries" is actually inverted—QuadTree queries
are 26-97x faster than Morton binary search + filtering.

**Why It Failed**: Morton encoding trades O(log n) tree traversal for O(log n)
binary search, but then requires O(k) filtering of results within the Morton code
range. For visibility queries returning small result sets, the filtering dominates.

---

## Numerical Approximations

### Fast Inverse Square Root (Quake III)

**Phase**: 58
**Concept**: Use bit manipulation for initial guess + Newton-Raphson refinement

```rust
fn fast_inv_sqrt(x: f32) -> f32 {
    let i = x.to_bits();
    let i = 0x5f3759df - (i >> 1);
    let y = f32::from_bits(i);
    y * (1.5 - 0.5 * x * y * y)  // Newton-Raphson iteration
}
```

**Benchmark Results**:

| Method              | Time (1000) | Throughput   | Speedup |
|---------------------|-------------|--------------|---------|
| 1.0/sqrt(x)         | 1.05 us     | 948 Melem/s  | 1.0x    |
| Quake 1-iteration   | 0.79 us     | 1.27 Gelem/s | 1.33x   |
| Quake 2-iteration   | 1.92 us     | 519 Melem/s  | **0.55x** |

**Conclusion**: One Newton-Raphson iteration is 1.33x faster with ~1-2% error,
but two iterations (for higher accuracy) is **slower than standard sqrt**.

**Why Not Implemented**: Modern CPUs have hardware sqrt (SSE2 `sqrtss`) taking
only ~10-15 cycles. The 1.33x speedup is marginal, and accuracy trade-off isn't
justified for visualization where precision matters for determinism.

---

### Octant-Based Length Approximation

**Phase**: 58
**Concept**: Use alpha-max-beta-min approximation to avoid sqrt

```rust
fn octant_length(x: f32, y: f32) -> f32 {
    let ax = x.abs();
    let ay = y.abs();
    let (max, min) = if ax > ay { (ax, ay) } else { (ay, ax) };
    0.96 * max + 0.397 * min  // ~4% max error
}
```

**Benchmark Results**:

| Method           | Time (1000) | Throughput   | Speedup     |
|------------------|-------------|--------------|-------------|
| sqrt(x^2 + y^2)  | 1.10 us     | 909 Melem/s  | 1.0x        |
| Octant basic     | 1.10 us     | 911 Melem/s  | **1.00x**   |
| Octant improved  | 2.15 us     | 464 Melem/s  | **0.51x**   |

**Conclusion**: **No benefit**. Modern hardware sqrt is as fast as the approximation.
The "improved" version with correction factor is 2x slower.

**Why It Failed**: This technique was valuable when sqrt was software-implemented
(hundreds of cycles). Modern SSE2 `sqrtss` takes ~10-15 cycles, eliminating the
advantage of approximation.

---

### Combined Force Calculation Approximations

**Phase**: 58
**Concept**: Use fast_inv_sqrt + octant_length together in force calculations

**Benchmark Results**:

| Method          | Time (1000) | Throughput   | Result      |
|-----------------|-------------|--------------|-------------|
| Standard        | 3.05 us     | 328 Melem/s  | 1.0x        |
| Fast inv_sqrt   | 3.96 us     | 253 Melem/s  | **0.77x**   |
| Octant length   | 3.19 us     | 311 Melem/s  | **0.95x**   |

**Conclusion**: Combined optimizations are **slower** than standard implementation.

**Why It Failed**: The overhead of additional operations (bit manipulation,
conditionals, correction factors) outweighs approximation savings when hardware
provides efficient exact computation.

---

## Integration Methods

### Verlet Integration

**Phase**: 58
**Concept**: Use Verlet integration for better energy conservation

```rust
// Verlet: position-based, implicit velocity
let new_pos = 2.0 * pos - prev_pos + acceleration * dt * dt;
let velocity = (new_pos - prev_pos) / (2.0 * dt);

// Velocity Verlet: explicit velocity tracking
let half_vel = velocity + 0.5 * acceleration * dt;
let new_pos = pos + half_vel * dt;
let new_accel = compute_acceleration(new_pos);
let new_vel = half_vel + 0.5 * new_accel * dt;
```

**Benchmark Results**:

| Method             | Time (1000) | Throughput   | Speedup     |
|--------------------|-------------|--------------|-------------|
| Semi-implicit Euler| 2.62 us     | 381 Melem/s  | 1.0x        |
| Verlet             | 2.60 us     | 384 Melem/s  | **1.01x**   |
| Velocity Verlet    | 2.86 us     | 349 Melem/s  | **0.92x**   |

**Conclusion**: **No performance benefit**. Verlet and Euler have virtually
identical performance. Velocity Verlet is slightly slower.

**Why Not Implemented**: Switching to Verlet would require structural changes
(storing previous positions) with no performance benefit. For visualization
(not physics simulation), Euler is sufficient.

---

## Bloom Algorithm Alternatives

### Transpose-Blur-Transpose

**Phase**: 43
**Concept**: Transpose image, horizontal blur (cache-friendly), transpose back

```rust
// Strategy: Transform vertical blur to horizontal
// 1. Transpose source image
// 2. Horizontal blur (sequential access)
// 3. Transpose result back
```

**Benchmark Results**: **15-24% regression**

**Why It Failed**: The overhead of two O(n) transpose passes exceeded the cache
benefit. Each transpose requires reading/writing every pixel, and for moderately
sized images (480x270 bloom), this dominates.

**Alternative Implemented**: Strip-based processing (8 columns together) achieved
6.6% improvement without transpose overhead.

---

## Key Insights

### Modern Hardware Changes the Equation

Many "classic" optimization techniques were developed when:
- sqrt was software-implemented (~100+ cycles)
- Division was extremely expensive
- Cache hierarchies were simpler
- SIMD wasn't available

Modern hardware provides:
- Hardware sqrt (SSE2 `sqrtss`): ~10-15 cycles
- Hardware division: ~15-20 cycles
- Multi-level caches with prefetching
- SIMD vectorization by compiler

### Approximation Overhead Can Exceed Savings

The overhead of:
- Bit manipulation
- Conditional branches
- Correction factor multiplications
- Register pressure from temporary values

Can exceed the cost of exact hardware-accelerated computation.

### Query Patterns Matter More Than Structure

Morton ordering shows excellent rebuild performance but catastrophic query
performance because:
- Rebuild is amortized (every 5 frames)
- Queries are per-frame (visibility) and per-event (hover)
- The filtering cost after binary search dominates

### Summary Table

| Optimization        | Phase | Expected    | Actual      | Reason               |
|---------------------|-------|-------------|-------------|----------------------|
| Morton spatial      | 57    | 20-50% faster | 26-97x slower | Query filtering cost |
| Quake inv_sqrt (2x) | 58    | Faster      | 0.55x       | HW sqrt is fast      |
| Octant length       | 58    | Faster      | Same/slower | HW sqrt is fast      |
| Combined approx     | 58    | Faster      | 0.77x       | Overhead exceeds gain|
| Verlet integration  | 58    | Faster      | Same        | No perf difference   |
| Transpose blur      | 43    | Faster      | 15-24% worse| Transpose overhead   |

---

*Last updated: 2026-01-25*
