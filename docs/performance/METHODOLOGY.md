# Benchmarking Methodology

This document describes the rigorous methodology used for all performance measurements in Rource. Following these standards ensures reproducible, statistically valid results.

---

## Table of Contents

1. [Statistical Rigor](#1-statistical-rigor)
2. [Benchmark Frameworks](#2-benchmark-frameworks)
3. [Environment Control](#3-environment-control)
4. [Reproducibility Protocol](#4-reproducibility-protocol)
5. [Reporting Standards](#5-reporting-standards)
6. [Regression Detection](#6-regression-detection)

---

## 1. Statistical Rigor

### 1.1 Sample Size Requirements

All benchmarks must meet minimum sample requirements:

| Benchmark Type | Minimum Samples | Warm-up Iterations |
|---------------|-----------------|-------------------|
| Micro (<1µs) | 1000 | 100 |
| Small (1µs-100µs) | 100 | 50 |
| Medium (100µs-10ms) | 50 | 10 |
| Large (>10ms) | 20 | 5 |

### 1.2 Confidence Intervals

All results reported with **95% confidence intervals**:

```
Result: 156.23 ns ± 2.14 ns (95% CI)
```

Criterion computes this automatically using bootstrap resampling with 100,000 resamples.

### 1.3 Effect Size Calculation

When comparing optimizations, report **Cohen's d** for effect size:

```
d = (μ_old - μ_new) / σ_pooled
```

| d Value | Interpretation |
|---------|---------------|
| < 0.2 | Negligible |
| 0.2 - 0.5 | Small |
| 0.5 - 0.8 | Medium |
| > 0.8 | Large |

**Minimum threshold for claiming improvement**: d > 0.5 (medium effect)

### 1.4 Outlier Detection

Criterion uses **IQR (Interquartile Range)** method:

```
Lower fence: Q1 - 1.5 × IQR
Upper fence: Q3 + 1.5 × IQR
```

Results outside fences are classified as:
- **Mild outliers**: 1.5-3× IQR from quartiles
- **Severe outliers**: >3× IQR from quartiles

Severe outliers (>5% of samples) indicate environmental instability.

---

## 2. Benchmark Frameworks

### 2.1 Criterion (Timing-Based)

Primary framework for performance benchmarks.

**Location**: `crates/*/benches/*.rs`

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

fn benchmark_operation(c: &mut Criterion) {
    let mut group = c.benchmark_group("operation");
    group.throughput(Throughput::Elements(1000));
    group.sample_size(100);

    let input = prepare_input();

    group.bench_function("baseline", |b| {
        b.iter(|| baseline_impl(black_box(&input)))
    });

    group.bench_function("optimized", |b| {
        b.iter(|| optimized_impl(black_box(&input)))
    });

    group.finish();
}
```

**Running**:
```bash
cargo bench --bench bench_name
```

### 2.2 IAI-CallGrind (Instruction-Based)

Deterministic benchmarks using Valgrind instruction counting.

**Location**: `crates/*/benches/iai_*.rs`

```rust
use iai_callgrind::{library_benchmark, library_benchmark_group, main};

#[library_benchmark]
fn bench_operation() -> usize {
    operation(input)
}

library_benchmark_group!(name = benchmarks; benchmarks = bench_operation);
main!(library_benchmark_groups = benchmarks);
```

**Running** (Linux only):
```bash
cargo bench --bench iai_bench_name
```

**Advantages**:
- Zero timing variance
- Deterministic results
- Ideal for CI regression detection
- Measures actual CPU instructions

### 2.3 DHAT (Allocation Profiling)

Heap allocation tracking for memory optimization.

```rust
#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    // ... code to profile ...
}
```

**Running**:
```bash
cargo run --profile dhat --features dhat-heap
```

---

## 3. Environment Control

### 3.1 Hardware Requirements

**Reference Hardware** (for normalized comparisons):
- CPU: 4+ cores, x86_64 or aarch64
- RAM: 8GB+ available
- Storage: SSD recommended

### 3.2 System Preparation

Before running benchmarks:

```bash
# 1. Close all other applications
# 2. Disable CPU frequency scaling (Linux)
sudo cpupower frequency-set --governor performance

# 3. Thermal warmup (10 minutes)
# Run the benchmark once without recording results

# 4. Disable turbo boost (optional, for consistency)
echo "1" | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

### 3.3 CI Environment

GitHub Actions runners:
- **ubuntu-latest**: 2-core x86_64, 7GB RAM
- **macos-latest**: Apple Silicon or Intel, 7GB RAM
- **windows-latest**: 2-core x86_64, 7GB RAM

**Note**: CI results may vary ±5% due to shared infrastructure. Use IAI-CallGrind for CI regression detection.

---

## 4. Reproducibility Protocol

### 4.1 Benchmark Script

All benchmarks can be reproduced using:

```bash
./scripts/benchmark-all.sh
```

### 4.2 Expected Results Verification

```bash
./scripts/benchmark-all.sh --verify-against docs/performance/EXPECTED_RESULTS.json
```

This compares results against known-good baselines and reports any regressions.

### 4.3 Result Archival

After significant optimizations:

```bash
# Generate new baseline
./scripts/benchmark-all.sh --save-baseline

# Results saved to:
# - docs/performance/EXPECTED_RESULTS.json
# - docs/performance/CHRONOLOGY.md (manual entry)
```

---

## 5. Reporting Standards

### 5.1 Required Metrics

Every benchmark report must include:

| Metric | Example | Purpose |
|--------|---------|---------|
| Mean | 156.23 ns | Central tendency |
| Std Dev | 4.31 ns | Dispersion |
| 95% CI | ±2.14 ns | Uncertainty bounds |
| Median | 155.00 ns | Robust central tendency |
| Min/Max | 148/189 ns | Range |
| Throughput | 6.4M ops/s | Comparative metric |

### 5.2 Comparison Format

When comparing before/after:

```
| Operation | Before | After | Change | Effect Size |
|-----------|--------|-------|--------|-------------|
| blend_rgba | 12.3 ns | 9.7 ns | -21% | d = 1.2 (Large) |
```

### 5.3 Visualization

Use ASCII charts for terminal/markdown compatibility:

```
Benchmark Results: Alpha Blending
─────────────────────────────────────────────────────
Before: ████████████████████████████████████ 12.3 ns
After:  ████████████████████████████ 9.7 ns (-21%)
─────────────────────────────────────────────────────
```

---

## 6. Regression Detection

### 6.1 Thresholds

| Severity | Threshold | Action |
|----------|-----------|--------|
| Info | >5% slower | Log for review |
| Warning | >10% slower | Alert on PR |
| Error | >20% slower | Block merge |

### 6.2 CI Integration

`.github/workflows/bench.yml` automatically:

1. Runs all benchmarks on PR
2. Compares against main branch baseline
3. Comments on PR if regression detected
4. Stores results on gh-pages for trend tracking

### 6.3 False Positive Handling

If a benchmark regresses in CI but not locally:

1. Check for timing variance (use IAI-CallGrind)
2. Verify no environmental differences
3. Run 3x in CI to confirm consistency
4. Document as flaky if inconsistent

---

## Appendix A: Quick Reference

### Running All Benchmarks

```bash
# Criterion (timing)
cargo bench --workspace

# IAI-CallGrind (instruction count, Linux only)
cargo bench --bench iai_scene --bench iai_vcs

# Specific benchmark
cargo bench --bench scene_perf -- "update_scene"

# With baseline comparison
cargo bench -- --baseline main
```

### Benchmark Files

| Crate | File | What it benchmarks |
|-------|------|-------------------|
| rource-math | `color_perf.rs` | Color conversion |
| rource-core | `scene_perf.rs` | Scene updates |
| rource-core | `easing_perf.rs` | Animation easing |
| rource-core | `iai_scene.rs` | Scene (instruction count) |
| rource-vcs | `vcs_parsing.rs` | Parser performance |
| rource-vcs | `iai_vcs.rs` | Parser (instruction count) |
| rource-render | `blend_perf.rs` | Alpha blending |
| rource-render | `bloom_perf.rs` | Bloom effect |
| rource-render | `visual_perf.rs` | Full render pipeline |

---

## Appendix B: Checklist

Before claiming a performance improvement:

- [ ] Ran on release build (`--release`)
- [ ] Ran at least 50 samples
- [ ] Reported 95% confidence interval
- [ ] Calculated effect size (d > 0.5)
- [ ] Verified on multiple runs
- [ ] Checked for measurement noise
- [ ] All tests still pass
- [ ] Updated CHRONOLOGY.md with results

---

*Document Version: 1.1*
*Last Updated: 2026-01-26*
*Based on: Criterion 0.8, IAI-CallGrind 0.16*
