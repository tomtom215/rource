# Load Testing Guide

**Version**: 1.0
**Last Updated**: 2026-01-27

This document describes the load testing infrastructure for Rource, including test methodology, success criteria, and CI integration.

---

## Overview

Load tests validate sustained operation under realistic workloads:

| Test | Duration | Commits | Purpose |
|------|----------|---------|---------|
| **Quick Sanity** | 1 minute | 1,000 | Fast CI gate |
| **Smoke Test** | 5 minutes | 10,000 | Weekly validation |
| **Full Load Test** | 30 minutes | 100,000 | Comprehensive stability |
| **Memory Churn** | Variable | 100,000+ | Leak detection |

---

## Success Criteria

All load tests must meet these criteria to pass:

| Criterion | Requirement | Rationale |
|-----------|-------------|-----------|
| **Duration** | Complete without crash | Basic stability |
| **Memory Stability** | < 5% growth after warm-up | No memory leaks |
| **Frame Stability** | P99 < 2x P50 | Consistent performance |
| **No Panics** | Zero panics or OOM | Production readiness |

### Memory Stability

Memory is measured using Resident Set Size (RSS):
- **Linux**: Parsed from `/proc/self/statm`
- **macOS**: Retrieved via `mach_task_basic_info`

Growth is calculated as:
```
growth_percent = ((final_rss - warmup_rss) / warmup_rss) * 100
```

The 5% threshold allows for:
- Internal buffer growth
- Cache expansion
- OS memory management overhead

### Frame Stability

Frame time percentiles measure consistency:
- **P50 (median)**: Typical frame time
- **P99**: Worst-case frame time (excluding outliers)

The P99/P50 ratio indicates "jitter":
- Ratio < 2x: Stable, predictable performance
- Ratio 2-3x: Acceptable variance
- Ratio > 3x: Unstable, investigate

---

## Running Load Tests

### Quick Sanity (1 minute)

```bash
cargo test -p rource-core --test load_tests load_test_quick_sanity -- --nocapture
```

This test runs automatically in the standard test suite.

### Smoke Test (5 minutes)

```bash
cargo test --release -p rource-core --test load_tests smoke -- --ignored --nocapture
```

Output:
```
========================================
Smoke Test: 5 Minutes, 10k Commits
========================================

Generating 10000 synthetic commits...
Scene initialized with 7000 files, 50 users
Warm-up baseline RSS: 45.2 MB

Starting 5-minute smoke test...

[ 16.7%]   30s | P50:  0.142ms | P99:  0.234ms | RSS:   45.8MB (+ 1.3%)
[ 33.3%]   60s | P50:  0.143ms | P99:  0.238ms | RSS:   45.9MB (+ 1.5%)
...

========================================
Smoke Test Results
========================================
Duration:    5.0 minutes
Frames:      18012
P50:         0.142 ms
P99:         0.241 ms
P99/P50:     1.70x
Mem Growth:  1.82%

Smoke test passed!
```

### Full Load Test (30 minutes)

```bash
cargo test --release -p rource-core --test load_tests load_test_30min -- --ignored --nocapture
```

Output:
```
========================================
Load Test: 30 Minutes, 100k Commits
========================================

Generating 100000 synthetic commits...
Parsed 100000 commits
Initializing scene...
Applying commits to scene...
Scene initialized with 60000 files, 50 users

Warm-up phase (60 frames)...
Warm-up baseline RSS: 125.4 MB

Starting 30-minute load test...

[  3.3%]   60s elapsed | P50:  0.312ms | P99:  0.521ms | RSS:  126.2MB (+ 0.6%)
[  6.7%]  120s elapsed | P50:  0.314ms | P99:  0.528ms | RSS:  126.8MB (+ 1.1%)
...
[100.0%] 1800s elapsed | P50:  0.318ms | P99:  0.542ms | RSS:  129.1MB (+ 2.9%)

========================================
Load Test Complete
========================================

Duration:        30.0 minutes
Total Frames:    108072
Final Entities:  60000 files, 50 users

Frame Times:
  P50:           0.318 ms
  P95:           0.468 ms
  P99:           0.542 ms
  P99.9:         0.891 ms
  P99/P50 Ratio: 1.70x

Memory:
  Warm-up RSS:   125.4 MB
  Final RSS:     129.1 MB
  Growth:        2.95%

========================================
Verification
========================================

 Duration >= 30 min:        PASS
 Memory growth < 5%:       PASS (2.95%)
 P99 < 2x P50:             PASS (1.70x)

 All success criteria met!
```

### Memory Churn Test

```bash
cargo test --release -p rource-core --test load_tests memory_churn -- --ignored --nocapture
```

This test specifically stresses memory allocation/deallocation patterns.

---

## CI Integration

Load tests run weekly via GitHub Actions (`.github/workflows/load-test.yml`):

### Schedule

- **Weekly**: Sundays at 2:00 AM UTC (smoke test)
- **Manual**: Dispatch with "smoke" or "full" option

### Triggering Manually

```bash
# Via GitHub CLI
gh workflow run load-test.yml -f duration=full

# Or via web UI
# Actions > Load Test > Run workflow > Select duration
```

### Artifacts

Each run produces a JSON report:
- `load_test_report.json` (full test)
- `load_test_smoke_report.json` (smoke test)

Reports include:
- Duration and frame count
- Frame time percentiles (P50, P95, P99, P99.9)
- Memory samples over time
- Entity counts over time
- Success criteria results

### Failure Handling

On failure, the workflow:
1. Uploads the report artifact for analysis
2. Creates a GitHub issue with label `load-test-failure`
3. Comments on existing issue if one is already open

---

## Report Format

Load test reports are JSON with this structure:

```json
{
  "test": "load_test",
  "duration_seconds": 1800.0,
  "total_frames": 108072,
  "frame_times_ms": {
    "average": 0.315,
    "p50": 0.318,
    "p95": 0.468,
    "p99": 0.542,
    "p999": 0.891
  },
  "fps": {
    "average": 60.0,
    "min_sustainable": 55.4
  },
  "memory": {
    "warmup_mb": 125.4,
    "final_mb": 129.1,
    "growth_percent": 2.95,
    "samples": 1800
  },
  "entities": {
    "final_files": 60000,
    "final_users": 50,
    "samples": 1800
  },
  "success_criteria": {
    "duration_30min": true,
    "memory_growth_under_5pct": true,
    "p99_under_2x_p50": true,
    "no_panics": true
  }
}
```

---

## Synthetic Data Generation

Load tests use synthetic commit data to ensure reproducibility:

### Characteristics

| Aspect | Value | Rationale |
|--------|-------|-----------|
| Authors | 50 | Realistic team size |
| Modules | 1000 | Deep directory structure |
| Files per module | 100 | Typical codebase density |
| Action mix | 60% M, 30% A, 10% D | Realistic change patterns |
| File types | .rs, .js, .ts, .py, .md | Varied extensions |
| Commit rate | 1 per hour | Chronological spread |

### Format

Synthetic logs use the custom format:
```
<timestamp>|<author>|<action>|<path>
```

Example:
```
1000000000|Author0|A|src/module0/file0.rs
1000003600|Author1|M|src/module0/file1.js
1000007200|Author2|A|src/module0/file2.ts
```

---

## Troubleshooting

### Test Takes Too Long

The 30-minute test is designed to take ~30 minutes. If it runs significantly longer:
1. Check CPU usage - may be thermal throttling
2. Check for background processes
3. Run in release mode (`--release`)

### Memory Growth Exceeds 5%

If memory growth fails the 5% threshold:
1. Download the report and review memory samples
2. Look for continuous growth vs. step increases
3. Run with DHAT profiling:
   ```bash
   cargo build --profile dhat --features dhat -p rource-core
   cargo test --profile dhat --features dhat -p rource-core --test load_tests
   ```
4. Review allocation sites in `dhat-heap.json`

### Frame Time Regression

If P99/P50 ratio exceeds 2x:
1. Check for garbage collection pauses
2. Look for cache misses or spatial index rebuilds
3. Profile with Tracy:
   ```bash
   cargo build --release --features tracy -p rource-core
   ```
4. Review recent changes to hot paths

### Test Panics

If the test panics:
1. Check `RUST_BACKTRACE=1` output
2. Review recent changes to Scene or physics code
3. Check for integer overflow or division by zero
4. Verify synthetic data generation

---

## Performance Baselines

### Reference Hardware

| Component | Specification |
|-----------|---------------|
| CPU | AMD Ryzen 9 5900X (12C/24T) |
| RAM | 32 GB DDR4-3600 |
| OS | Ubuntu 22.04 LTS |
| Rust | 1.93.0 |

### Expected Results (Reference Hardware)

| Test | Commits | P50 | P99 | Memory Growth |
|------|---------|-----|-----|---------------|
| Quick Sanity | 1,000 | < 0.5ms | < 1ms | < 2% |
| Smoke Test | 10,000 | < 0.5ms | < 1ms | < 3% |
| Full Load | 100,000 | < 1ms | < 2ms | < 5% |

### Scaling Characteristics

Frame time scales approximately linearly with entity count:
- 10k files: ~0.15ms P50
- 50k files: ~0.30ms P50
- 100k files: ~0.50ms P50

Memory scales sublinearly due to path interning:
- 10k commits: ~50MB
- 50k commits: ~100MB
- 100k commits: ~130MB

---

## Integration with Other Tests

Load tests complement other testing strategies:

| Test Type | Purpose | Frequency |
|-----------|---------|-----------|
| Unit Tests | Correctness | Every commit |
| Benchmarks | Performance regression | Every PR |
| Load Tests | Sustained stability | Weekly |
| Chaos Tests | Edge cases | Every commit |
| Mutation Tests | Test quality | Weekly |

---

## Future Enhancements

- [ ] Add GPU memory tracking for WebGL/wgpu
- [ ] Add WASM-specific load tests
- [ ] Add network latency simulation
- [ ] Add concurrent user simulation
- [ ] Add visual regression during load test

---

*Last Updated: 2026-01-27*
