# Future Work: Path to Expert+ Excellence

**Status**: Active Roadmap
**Created**: 2026-01-26
**Purpose**: Comprehensive roadmap to achieve verifiable Expert+ rating in all engineering categories

---

## Executive Summary

This document outlines the complete set of improvements required to achieve **quantifiably verifiable Expert+ status** across all professional engineering categories. Each task includes:

- **Success Criteria**: Measurable, testable requirements
- **Verification Method**: How to prove completion
- **Documentation Requirements**: What artifacts to produce
- **Industry Benchmark**: What "Expert+" looks like in practice

---

## Current Assessment vs Target

| Category | Current Rating | Target | Gap |
|----------|---------------|--------|-----|
| Technical Excellence | 9.5/10 (Expert) | Expert+ | Minor |
| Engineering Maturity | 9/10 (Expert) | Expert+ | Minor |
| Documentation Quality | 9.5/10 (Expert) | Expert+ | Minor |
| **Operational Readiness** | **7.5/10 (Senior+)** | **Expert+** | **Major** |
| **Security Posture** | **7/10 (Senior)** | **Expert+** | **Major** |
| **Testing Maturity** | **8/10 (Senior+)** | **Expert+** | **Moderate** |
| **CI/CD Excellence** | **8/10 (Senior+)** | **Expert+** | **Moderate** |
| **Accessibility** | **Not Rated** | **Expert+** | **Major** |

---

## Quick Reference: All Tasks

| ID | Task | Category | Priority | Complexity | Status |
|----|------|----------|----------|------------|--------|
| OP-1 | Production Telemetry Infrastructure | Operational | Critical | High | Pending |
| OP-2 | P50/P99 Latency Documentation | Operational | Critical | Medium | Pending |
| OP-3 | Load Testing Suite (100k commits, 30min) | Operational | Critical | High | Pending |
| OP-4 | Memory Stability Analysis | Operational | High | Medium | Pending |
| OP-5 | Error Rate Tracking | Operational | High | Medium | Pending |
| SEC-1 | Fuzzing Coverage Metrics & Dashboard | Security | Critical | Medium | Pending |
| SEC-2 | SBOM Generation | Security | High | Low | Done |
| SEC-3 | Supply Chain Security (SLSA) | Security | High | Medium | Pending |
| SEC-4 | Security Policy (SECURITY.md) | Security | Medium | Low | Done |
| TST-1 | Mutation Testing Suite | Testing | Critical | High | Pending |
| TST-2 | Property-Based Test Expansion | Testing | High | Medium | Pending |
| TST-3 | Visual Regression Testing | Testing | High | High | Pending |
| TST-4 | Cross-Browser Automated Testing | Testing | Medium | High | Pending |
| CI-1 | Performance Regression Gates | CI/CD | Critical | Medium | Pending |
| CI-2 | Benchmark History Dashboard | CI/CD | High | Medium | Pending |
| CI-3 | Automated Release Notes | CI/CD | Medium | Low | Done |
| CI-4 | Canary Deployments | CI/CD | Medium | Medium | Pending |
| DOC-1 | API Stability Policy (STABILITY.md) | Documentation | Critical | Low | Done |
| DOC-2 | Architecture Decision Records (ADRs) | Documentation | High | Medium | Pending |
| DOC-3 | Runbook/Playbook Documentation | Documentation | High | Medium | Pending |
| ACC-1 | Keyboard Navigation Implementation | Accessibility | Critical | High | Pending |
| ACC-2 | WCAG 2.1 AA Compliance Audit | Accessibility | Critical | High | Pending |
| ACC-3 | Screen Reader Compatibility | Accessibility | High | High | Pending |
| ACC-4 | Color Contrast Compliance | Accessibility | High | Medium | Pending |
| ACC-5 | Reduced Motion Support | Accessibility | Medium | Low | Done |

---

## Category 1: Operational Readiness (7.5/10 → Expert+)

### What Expert+ Looks Like
- Production systems with real-time telemetry dashboards
- P50/P99/P999 latency SLOs with documented historical data
- Load tested to 10x expected production load
- Memory leak detection with automated alerts
- Error budgets and incident response procedures

---

### OP-1: Production Telemetry Infrastructure

**Priority**: Critical
**Complexity**: High
**Estimated Effort**: 3-4 implementation sessions

#### Problem Statement
While `tracing` infrastructure exists, there's no evidence of production metrics collection.
Hot paths lack instrumentation. No dashboards exist for real-time monitoring.

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Tracing spans in hot paths | `update_layout()`, `render_frame()`, `apply_commit()` instrumented | Code review |
| Metrics collection | Frame time, entity count, memory usage exported | Prometheus endpoint test |
| Dashboard | Grafana/similar showing real-time metrics | Screenshot evidence |
| Historical data | 7 days of metrics retained | Query historical data |

#### Implementation

**Step 1: Add tracing spans to hot paths**
```rust
// crates/rource-core/src/scene/layout_methods.rs
#[tracing::instrument(skip(self), fields(entity_count = self.entity_count()))]
pub fn update_layout(&mut self, dt: f32) {
    let _span = tracing::info_span!("physics").entered();
    // ... existing code
}
```

**Step 2: Export metrics via `metrics` crate**
```rust
// rource-cli/src/telemetry.rs
use metrics::{counter, gauge, histogram};

pub fn record_frame(frame_time_ms: f64, entity_count: usize) {
    histogram!("rource.frame_time_ms").record(frame_time_ms);
    gauge!("rource.entity_count").set(entity_count as f64);
    counter!("rource.frames_total").increment(1);
}
```

**Step 3: Create Prometheus exporter (optional, for CLI)**
```rust
// Feature-gated: --features telemetry
metrics_exporter_prometheus::PrometheusBuilder::new()
    .with_http_listener(([127, 0, 0, 1], 9090))
    .install()?;
```

**Step 4: WASM metrics export via JavaScript**
```typescript
// Expose metrics to browser performance API
performance.measure('rource-frame', { detail: { frameTime, entityCount } });
```

#### Files to Create/Modify
- `crates/rource-core/src/telemetry.rs` (new)
- `crates/rource-core/src/scene/layout_methods.rs` (add spans)
- `crates/rource-render/src/lib.rs` (add spans)
- `rource-cli/src/telemetry.rs` (new)
- `rource-wasm/src/telemetry.rs` (new)
- `Cargo.toml` (add optional dependencies)

#### Documentation Requirements
- `docs/operations/TELEMETRY.md` - Setup guide
- `docs/operations/METRICS_REFERENCE.md` - All metrics documented
- README.md - Badge showing telemetry capability

#### Verification Command
```bash
# Start with telemetry enabled
ROURCE_TELEMETRY=true cargo run --release --features telemetry -- .

# In another terminal, verify metrics
curl -s http://localhost:9090/metrics | grep rource
# Expected: rource_frame_time_ms, rource_entity_count, etc.
```

---

### OP-2: P50/P99 Latency Documentation

**Priority**: Critical
**Complexity**: Medium
**Estimated Effort**: 1-2 sessions

#### Problem Statement
No documented latency percentiles from real-world usage. Benchmark data exists but
isn't presented as production SLO-style metrics.

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| P50/P95/P99 documented | Frame time percentiles for standard workloads | `docs/performance/SLO.md` |
| Multiple scenarios | Small (1k), Medium (10k), Large (100k) commits | Tables in documentation |
| Hardware baseline | Documented test hardware specs | Reproducibility section |
| Browser matrix | Chrome, Firefox, Safari, Edge | Cross-browser table |

#### Implementation

**Step 1: Create latency collection script**
```bash
#!/bin/bash
# scripts/collect-latency-metrics.sh

for commits in 1000 10000 100000; do
    echo "Testing with $commits commits..."
    cargo run --release -- \
        --headless \
        --max-commits $commits \
        --output /tmp/frames \
        --telemetry-output /tmp/latency-$commits.json \
        /path/to/large/repo
done
```

**Step 2: Calculate percentiles**
```python
# scripts/analyze-latency.py
import json
import numpy as np

def analyze(filename):
    with open(filename) as f:
        data = json.load(f)
    frame_times = [d['frame_time_ms'] for d in data['frames']]
    return {
        'p50': np.percentile(frame_times, 50),
        'p95': np.percentile(frame_times, 95),
        'p99': np.percentile(frame_times, 99),
        'p999': np.percentile(frame_times, 99.9),
    }
```

**Step 3: Document in SLO format**
```markdown
# docs/performance/SLO.md

## Frame Latency SLOs

| Scenario | P50 | P95 | P99 | P99.9 | Target FPS |
|----------|-----|-----|-----|-------|------------|
| Small (1k commits) | 2.1ms | 3.4ms | 5.2ms | 8.1ms | 60 FPS |
| Medium (10k commits) | 4.8ms | 8.2ms | 12.4ms | 18.3ms | 60 FPS |
| Large (100k commits) | 12.3ms | 18.7ms | 24.1ms | 35.2ms | 30 FPS |

**Test Hardware**: AMD Ryzen 9 5900X, 32GB RAM, RTX 3080
**Test Date**: 2026-01-XX
**Methodology**: 1000 frames per scenario, warm start
```

#### Documentation Requirements
- `docs/performance/SLO.md` (new)
- `docs/performance/LATENCY_METHODOLOGY.md` (new)
- `scripts/collect-latency-metrics.sh` (new)
- `scripts/analyze-latency.py` (new)

---

### OP-3: Load Testing Suite (100k Commits, 30 Minutes)

**Priority**: Critical
**Complexity**: High
**Estimated Effort**: 2-3 sessions

#### Problem Statement
No documented evidence of sustained load testing. Chaos tests exist but don't
cover long-running stability under realistic workloads.

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Duration | 30-minute continuous run | Timestamped logs |
| Scale | 100,000+ commits visualized | Commit count in logs |
| Memory stability | < 5% growth after warm-up | Memory graphs |
| Frame stability | P99 < 2x P50 after 30 min | Latency percentiles |
| No crashes | Zero panics or OOM | Exit code 0 |

#### Implementation

**Step 1: Create load test harness**
```rust
// tests/load_tests.rs
#[test]
#[ignore] // Run with: cargo test --release -- --ignored load_test_30min
fn load_test_30min_100k_commits() {
    let start = Instant::now();
    let duration = Duration::from_secs(30 * 60);

    let mut metrics = LoadTestMetrics::new();

    while start.elapsed() < duration {
        // Run update cycle
        scene.update(1.0 / 60.0);
        renderer.render(&scene);

        // Collect metrics every second
        if metrics.should_sample() {
            metrics.record(
                start.elapsed(),
                memory_usage(),
                last_frame_time(),
                scene.entity_count(),
            );
        }
    }

    // Generate report
    metrics.write_report("load_test_report.json");

    // Assertions
    assert!(metrics.memory_growth_percent() < 5.0);
    assert!(metrics.p99_frame_time() < 2.0 * metrics.p50_frame_time());
    assert_eq!(metrics.panic_count(), 0);
}
```

**Step 2: Memory tracking**
```rust
// crates/rource-core/src/diagnostics/memory.rs
pub fn memory_usage() -> MemoryStats {
    #[cfg(target_os = "linux")]
    {
        // Parse /proc/self/statm
    }
    #[cfg(target_arch = "wasm32")]
    {
        // Use performance.measureUserAgentSpecificMemory()
    }
}
```

**Step 3: CI integration (weekly)**
```yaml
# .github/workflows/load-test.yml
name: Load Test
on:
  schedule:
    - cron: '0 2 * * 0'  # Weekly Sunday 2 AM
  workflow_dispatch:

jobs:
  load-test:
    runs-on: ubuntu-latest
    timeout-minutes: 45
    steps:
      - uses: actions/checkout@v4
      - name: Run 30-minute load test
        run: cargo test --release -- --ignored load_test_30min
      - name: Upload results
        uses: actions/upload-artifact@v4
        with:
          name: load-test-results
          path: load_test_report.json
```

#### Documentation Requirements
- `docs/operations/LOAD_TESTING.md` - Methodology and results
- `docs/operations/LOAD_TEST_RESULTS.md` - Latest results with graphs
- `.github/workflows/load-test.yml` - CI workflow

---

### OP-4: Memory Stability Analysis

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1-2 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Heap profiling | dhat integration for allocation tracking | `--features heap-profile` |
| Leak detection | Valgrind/ASAN clean run | CI job |
| Memory budget | Documented per-entity memory cost | `MEMORY_BUDGET.md` |
| Growth analysis | Graph of memory vs time for 30min | Load test artifacts |

#### Implementation

**Step 1: Add dhat heap profiling**
```rust
// Already in Cargo.toml, ensure proper usage
#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();
    // ... rest of main
}
```

**Step 2: Document memory budget**
```markdown
# docs/performance/MEMORY_BUDGET.md

## Per-Entity Memory Costs

| Entity Type | Size (bytes) | Notes |
|-------------|--------------|-------|
| File | 128 | Position, color, state, path |
| Directory | 256 | Children HashSet, bounds |
| User | 192 | Position, color, avatar ref |
| Action (beam) | 64 | Source, target, alpha |

## Scaling Analysis

| Commits | Estimated Memory | Actual Memory | Overhead |
|---------|------------------|---------------|----------|
| 1,000 | 2.1 MB | 2.4 MB | +14% |
| 10,000 | 18.5 MB | 21.2 MB | +15% |
| 100,000 | 165 MB | 198 MB | +20% |
```

---

### OP-5: Error Rate Tracking

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1 session

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Error categorization | Parse errors, render errors, WebGL errors | Enum in code |
| Error counters | `metrics::counter!("rource.errors", "type" => ...)` | Prometheus query |
| Error budget | < 0.1% error rate target | SLO document |
| Alerting threshold | Document when to alert | Runbook |

---

## Category 2: Security Posture (7/10 → Expert+)

### What Expert+ Looks Like
- Quantified fuzzing coverage with edge statistics
- SBOM (Software Bill of Materials) for supply chain transparency
- SLSA Level 2+ build provenance
- Documented security policy and vulnerability disclosure process
- Regular dependency audits with automation

---

### SEC-1: Fuzzing Coverage Metrics & Dashboard

**Priority**: Critical
**Complexity**: Medium
**Estimated Effort**: 2 sessions

#### Problem Statement
`fuzz/` directory exists but there's no quantified coverage data. Cannot prove
security testing completeness.

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Coverage report | cargo-fuzz coverage output | `fuzz/coverage/` |
| Edge coverage % | Document % of branches hit | Coverage report |
| Corpus statistics | Number of inputs, unique crashes | `FUZZING.md` |
| CI integration | Weekly fuzzing run with report | GitHub Actions |
| README badge | "Fuzzed for X hours" | Badge in README |

#### Implementation

**Step 1: Generate coverage report**
```bash
#!/bin/bash
# scripts/fuzz-coverage.sh

cd fuzz
cargo +nightly fuzz coverage parse_git_log

# Generate HTML report
cargo cov -- show \
    target/x86_64-unknown-linux-gnu/coverage/parse_git_log/coverage.profdata \
    --format=html \
    --output-dir=coverage-report \
    --instr-profile=coverage.profdata

# Generate summary for README
cargo cov -- report \
    --instr-profile=coverage.profdata \
    --summary-only > coverage-summary.txt
```

**Step 2: Create fuzzing documentation**
```markdown
# docs/security/FUZZING.md

## Fuzzing Status

| Fuzz Target | Corpus Size | Coverage | Hours Run | Last Run |
|-------------|-------------|----------|-----------|----------|
| parse_git_log | 1,247 inputs | 78.3% | 168 hours | 2026-01-XX |
| parse_custom_log | 892 inputs | 82.1% | 96 hours | 2026-01-XX |
| parse_svn_log | 654 inputs | 74.9% | 72 hours | 2026-01-XX |

## Coverage Methodology

Coverage is measured using LLVM source-based coverage via `cargo-fuzz`.
Edge coverage represents the percentage of conditional branches executed.

## Running Fuzz Tests

\`\`\`bash
# Install cargo-fuzz
cargo install cargo-fuzz

# Run VCS parser fuzzing (continuous)
cargo +nightly fuzz run parse_git_log

# Run with timeout (CI)
cargo +nightly fuzz run parse_git_log -- -max_total_time=3600
\`\`\`
```

**Step 3: CI workflow**
```yaml
# .github/workflows/fuzz.yml
name: Fuzzing
on:
  schedule:
    - cron: '0 0 * * 0'  # Weekly
  workflow_dispatch:

jobs:
  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - run: cargo install cargo-fuzz
      - name: Fuzz VCS parsers (1 hour each)
        run: |
          cargo +nightly fuzz run parse_git_log -- -max_total_time=3600
          cargo +nightly fuzz run parse_custom_log -- -max_total_time=3600
      - name: Generate coverage
        run: ./scripts/fuzz-coverage.sh
      - name: Upload coverage
        uses: actions/upload-artifact@v4
        with:
          name: fuzz-coverage
          path: fuzz/coverage-report/
```

---

### SEC-2: SBOM Generation

**Priority**: High
**Complexity**: Low
**Estimated Effort**: 1 session
**Status**: ✅ **COMPLETED** (Pre-existing in release.yml)

#### Completion Notes

Already implemented in `.github/workflows/release.yml` (lines 54-81):
- Generates both SPDX and CycloneDX format SBOMs
- Uses `cargo-sbom` for generation
- SBOMs uploaded as release artifacts
- Integrated into the release workflow

Files:
- `.github/workflows/release.yml` - SBOM job with dual format output

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| SBOM format | CycloneDX or SPDX JSON | ✅ Both formats generated |
| CI generation | Generated on every release | ✅ Release workflow job |
| All dependencies | Direct + transitive | ✅ cargo-sbom includes all |
| Vulnerability scanning | SBOM fed to scanner | ⚠️ Not yet integrated (future enhancement) |

---

### SEC-3: Supply Chain Security (SLSA)

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1-2 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Build provenance | SLSA Level 2 attestation | Sigstore/in-toto |
| Reproducible builds | Same source → same binary | Hash comparison |
| Signed releases | GPG or Sigstore signatures | Verify signature |

#### Implementation

```yaml
# .github/workflows/release.yml additions
- name: Generate SLSA provenance
  uses: slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@v1.9.0
  with:
    base64-subjects: "${{ needs.build.outputs.hashes }}"
```

---

### SEC-4: Security Policy (SECURITY.md)

**Priority**: Medium
**Complexity**: Low
**Estimated Effort**: 0.5 session
**Status**: ✅ **COMPLETED** (2026-01-26)

#### Completion Notes

Created `/SECURITY.md` with:
- Supported versions table
- Vulnerability reporting via GitHub Security Advisories
- Response timeline (48h acknowledgment, 7-day critical fix)
- Security measures documentation (audits, fuzzing, minimal unsafe)
- WASM security considerations

#### Implementation

```markdown
# SECURITY.md

## Supported Versions

| Version | Supported |
|---------|-----------|
| 1.x.x | Yes |
| < 1.0 | No |

## Reporting a Vulnerability

Please report security vulnerabilities via GitHub Security Advisories:
https://github.com/tomtom215/rource/security/advisories/new

Do NOT report security vulnerabilities via public GitHub issues.

## Security Measures

- **Dependency Auditing**: Weekly `cargo audit` via CI
- **Fuzzing**: Continuous fuzzing of VCS parsers
- **Minimal Unsafe**: Single unsafe block with documented safety invariants
- **SBOM**: Software Bill of Materials published with each release

## Response Timeline

- Acknowledgment: 48 hours
- Initial assessment: 7 days
- Fix timeline: Based on severity (Critical: 7 days, High: 30 days)
```

---

## Category 3: Testing Maturity (8/10 → Expert+)

### What Expert+ Looks Like
- Mutation testing proving test effectiveness
- Property-based tests for all mathematical operations
- Visual regression tests for rendering
- Cross-browser automated testing
- Test coverage metrics with mutation score

---

### TST-1: Mutation Testing Suite

**Priority**: Critical
**Complexity**: High
**Estimated Effort**: 2-3 sessions

#### Problem Statement
2,076 tests exist but their effectiveness at catching bugs is unquantified.
Mutation testing reveals "test coverage quality" vs just "test coverage quantity".

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Mutation score | > 80% mutants killed | cargo-mutants output |
| Critical modules | 90%+ score for math, vcs | Per-crate scores |
| CI integration | Block PRs if score drops | CI job |
| Documentation | Explain mutation methodology | `TESTING.md` |

#### Implementation

**Step 1: Install and run cargo-mutants**
```bash
# Install
cargo install cargo-mutants

# Run on specific crates (math is critical)
cargo mutants -p rource-math -- --release

# Generate report
cargo mutants -p rource-math --json > mutation-report.json
```

**Step 2: CI integration**
```yaml
# .github/workflows/mutation.yml
name: Mutation Testing
on:
  pull_request:
    paths:
      - 'crates/rource-math/**'
      - 'crates/rource-vcs/**'

jobs:
  mutants:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: cargo install cargo-mutants
      - name: Run mutation tests (math)
        run: |
          cargo mutants -p rource-math -- --release
          SCORE=$(jq '.summary.mutation_score' mutation-outcomes.json)
          if (( $(echo "$SCORE < 0.80" | bc -l) )); then
            echo "Mutation score $SCORE below 80% threshold"
            exit 1
          fi
```

**Step 3: Documentation**
```markdown
# docs/testing/MUTATION_TESTING.md

## Mutation Testing Results

| Crate | Mutants | Killed | Survived | Score |
|-------|---------|--------|----------|-------|
| rource-math | 847 | 782 | 65 | 92.3% |
| rource-vcs | 423 | 361 | 62 | 85.3% |
| rource-core | 1,234 | 987 | 247 | 80.0% |

## Interpreting Results

- **Killed**: Mutant detected by tests (good)
- **Survived**: Mutant NOT detected (test gap)
- **Score**: % of mutants killed (higher = better)

## Improving Score

Survived mutants indicate test gaps. Each survivor represents
a potential bug that tests would miss.
```

---

### TST-2: Property-Based Test Expansion

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1-2 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Math coverage | All Vec2/Vec3/Vec4/Mat3/Mat4 operations | Test file review |
| Invariant tests | Associativity, commutativity, identity | Property tests |
| Round-trip tests | serialize/deserialize, encode/decode | Property tests |

#### Implementation

```rust
// crates/rource-math/tests/proptests.rs (expand existing)
proptest! {
    // Matrix multiplication associativity
    #[test]
    fn mat4_mul_associative(
        a in mat4_strategy(),
        b in mat4_strategy(),
        c in mat4_strategy()
    ) {
        let ab_c = (a * b) * c;
        let a_bc = a * (b * c);
        // Allow for floating-point tolerance
        prop_assert!(matrices_approx_equal(ab_c, a_bc, 1e-5));
    }

    // Color round-trip
    #[test]
    fn color_argb8_roundtrip(r in 0u8..=255, g in 0u8..=255, b in 0u8..=255, a in 0u8..=255) {
        let color = Color::from_rgba8(r, g, b, a);
        let packed = color.to_argb8();
        let unpacked = Color::from_argb8(packed);
        prop_assert_eq!(color.to_rgba8(), unpacked.to_rgba8());
    }
}
```

---

### TST-3: Visual Regression Testing

**Priority**: High
**Complexity**: High
**Estimated Effort**: 2-3 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Reference images | Golden images for key scenarios | `tests/visual/golden/` |
| Diff detection | Pixel-wise comparison with threshold | Test output |
| CI integration | Block PRs with visual regressions | CI job |
| Multiple backends | Software, WebGL2, wgpu | Per-backend goldens |

#### Implementation

```rust
// tests/visual_regression.rs
#[test]
fn visual_regression_directory_tree() {
    let scene = create_test_scene_with_commits(100);
    let frame = render_to_pixels(&scene, 800, 600);

    let golden_path = "tests/visual/golden/directory_tree_100.png";

    if env::var("UPDATE_GOLDEN").is_ok() {
        save_png(&frame, golden_path);
    } else {
        let golden = load_png(golden_path);
        let diff = pixel_diff(&frame, &golden);
        assert!(diff.mean_squared_error < 0.001,
            "Visual regression detected: MSE={}", diff.mean_squared_error);
    }
}
```

---

### TST-4: Cross-Browser Automated Testing

**Priority**: Medium
**Complexity**: High
**Estimated Effort**: 2-3 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Browser matrix | Chrome, Firefox, Safari, Edge | CI matrix |
| Automated tests | Playwright/Selenium test suite | Test files |
| Rendering verification | Screenshot comparison per browser | CI artifacts |
| Performance comparison | Frame time per browser | Benchmark data |

#### Implementation

```typescript
// tests/e2e/browser.spec.ts (Playwright)
import { test, expect } from '@playwright/test';

test.describe('Rource WASM', () => {
  test('renders visualization correctly', async ({ page }) => {
    await page.goto('/');
    await page.waitForSelector('canvas');

    // Wait for first render
    await page.waitForFunction(() =>
      (window as any).rource?.getFrameCount() > 10
    );

    // Screenshot comparison
    await expect(page).toHaveScreenshot('initial-render.png', {
      maxDiffPixelRatio: 0.01
    });
  });

  test('achieves 30+ FPS', async ({ page }) => {
    await page.goto('/');
    const fps = await page.evaluate(() =>
      (window as any).rource?.getCurrentFPS()
    );
    expect(fps).toBeGreaterThan(30);
  });
});
```

---

## Category 4: CI/CD Excellence (8/10 → Expert+)

### What Expert+ Looks Like
- Performance regression gates that block merges
- Historical benchmark dashboards
- Automated changelog generation
- Canary/staged deployments
- Feature flag infrastructure

---

### CI-1: Performance Regression Gates

**Priority**: Critical
**Complexity**: Medium
**Estimated Effort**: 1-2 sessions

#### Problem Statement
Benchmarks exist but don't block PRs. A PR could regress performance by 50%
and still merge.

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Threshold | Block if >5% regression | CI failure |
| Baseline | Compare against main branch | Benchmark diff |
| Report | PR comment with comparison | GitHub bot |
| Override | Allow with justification | Label bypass |

#### Implementation

**Option A: Using bencher.dev (recommended)**
```yaml
# .github/workflows/bench-pr.yml
name: Benchmark PR
on: pull_request

jobs:
  bench:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: bencherdev/bencher@main
      - name: Run benchmarks
        run: |
          bencher run \
            --project rource \
            --token ${{ secrets.BENCHER_API_TOKEN }} \
            --branch ${{ github.head_ref }} \
            --testbed ubuntu-latest \
            --adapter rust_criterion \
            --err \
            --github-actions ${{ secrets.GITHUB_TOKEN }} \
            cargo bench
```

**Option B: Using criterion-compare**
```yaml
- name: Benchmark comparison
  run: |
    git fetch origin main
    cargo bench --bench scene_perf -- --save-baseline pr
    git checkout origin/main
    cargo bench --bench scene_perf -- --save-baseline main
    git checkout -
    critcmp main pr --threshold 5
```

---

### CI-2: Benchmark History Dashboard

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1-2 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Historical data | 90 days of benchmark history | Data retention |
| Visualization | Graphs of key metrics over time | Dashboard URL |
| Trend detection | Alert on consistent degradation | Notification |
| Public access | Anyone can view trends | Public URL |

#### Implementation

```yaml
# Using GitHub Pages + criterion HTML reports
- name: Generate benchmark report
  run: cargo bench -- --noplot
- name: Deploy to Pages
  uses: peaceiris/actions-gh-pages@v3
  with:
    github_token: ${{ secrets.GITHUB_TOKEN }}
    publish_dir: ./target/criterion
    destination_dir: benchmarks/${{ github.sha }}
```

---

### CI-3: Automated Release Notes

**Priority**: Medium
**Complexity**: Low
**Estimated Effort**: 0.5 session
**Status**: ✅ **COMPLETED** (Pre-existing in release.yml)

#### Completion Notes

Already implemented with comprehensive git-cliff configuration:
- `/cliff.toml` - Full conventional commits configuration with:
  - Changelog header/body/footer templates
  - Commit type grouping (Features, Bug Fixes, Performance, etc.)
  - GitHub PR/username linking
  - Breaking change protection
- `.github/workflows/release.yml` - Changelog job using `orhun/git-cliff-action@v4`
- Changelog uploaded as release artifact and used for release body

Files:
- `/cliff.toml` - git-cliff configuration
- `.github/workflows/release.yml` - Changelog generation job (lines 27-52)

---

### CI-4: Canary Deployments

**Priority**: Medium
**Complexity**: Medium
**Estimated Effort**: 1 session

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Canary environment | preview.rource.dev | URL accessible |
| Automatic deploy | PRs deploy to canary | Preview comment |
| Smoke tests | Automated verification | Test pass |

---

## Category 5: Documentation Quality (9.5/10 → Expert+)

### What Expert+ Looks Like
- API stability guarantees with semver policy
- Architecture Decision Records (ADRs)
- Operational runbooks/playbooks
- Complete API reference with examples

---

### DOC-1: API Stability Policy (STABILITY.md)

**Priority**: Critical
**Complexity**: Low
**Estimated Effort**: 0.5 session
**Status**: ✅ **COMPLETED** (2026-01-26)

#### Completion Notes

Created `/STABILITY.md` with:
- 70+ WASM APIs categorized into Stable/Beta/Experimental tiers
- Semver policy with clear breaking change definitions
- Deprecation policy with 2 minor version notice for Stable APIs
- Migration guides for API consumers

#### Problem Statement
WASM API has no documented stability guarantees. Integrators don't know
if `rource.getRendererType()` will exist in the next version.

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Stability tiers | Stable, Beta, Experimental | Document exists |
| Semver policy | When to bump major/minor/patch | Document exists |
| Deprecation policy | How long deprecated APIs last | Document exists |
| API inventory | All public APIs categorized | API reference |

#### Implementation

```markdown
# STABILITY.md

## API Stability Tiers

### Stable (No breaking changes in minor versions)
These APIs follow semantic versioning strictly:

| API | Since | Notes |
|-----|-------|-------|
| `rource.loadGitLog(log)` | 1.0.0 | Core functionality |
| `rource.play()` / `rource.pause()` | 1.0.0 | Playback control |
| `rource.setZoom(level)` | 1.0.0 | Camera control |

### Beta (May change in minor versions)
These APIs are feature-complete but interface may evolve:

| API | Since | Notes |
|-----|-------|-------|
| `rource.setUseGPUCulling(bool)` | 1.2.0 | Performance tuning |
| `rource.exportScreenshot()` | 1.1.0 | May add options |

### Experimental (May change or be removed)
These APIs are for testing and may not be available in future versions:

| API | Since | Notes |
|-----|-------|-------|
| `rource.debugHitTest(x, y)` | 1.3.0 | Debugging only |

## Semver Policy

- **Major (X.0.0)**: Breaking changes to Stable APIs
- **Minor (0.X.0)**: New features, Beta API changes
- **Patch (0.0.X)**: Bug fixes only

## Deprecation Policy

1. Deprecated APIs are marked with `@deprecated` JSDoc
2. Deprecated APIs work for at least 2 minor versions
3. Deprecation warnings logged to console
4. Removal announced in release notes
```

---

### DOC-2: Architecture Decision Records (ADRs)

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1-2 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Key decisions documented | Backend selection, physics algo, etc. | ADR files |
| Template | Consistent ADR format | Template file |
| Index | List of all ADRs | `docs/adr/README.md` |

#### Implementation

```markdown
# docs/adr/0001-use-barnes-hut-for-force-layout.md

# ADR 0001: Use Barnes-Hut Algorithm for Force-Directed Layout

## Status
Accepted

## Context
Force-directed layout requires O(n²) pairwise force calculations by default.
For repositories with 10,000+ files, this becomes the bottleneck.

## Decision
Implement Barnes-Hut algorithm with adaptive theta parameter.

## Consequences
- **Positive**: O(n log n) complexity enables 100k+ entity visualization
- **Positive**: Adaptive theta balances accuracy vs speed
- **Negative**: More complex code than pairwise
- **Negative**: Approximation introduces small layout differences

## Alternatives Considered
1. **Pairwise (O(n²))**: Too slow for large repos
2. **Fruchterman-Reingold**: Still O(n²) per iteration
3. **GPU compute**: Platform-dependent, not always available
```

---

### DOC-3: Runbook/Playbook Documentation

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1 session

#### Implementation

```markdown
# docs/operations/RUNBOOK.md

## Incident Response Playbooks

### High Memory Usage

**Symptoms**: Browser tab using >2GB memory, OOM crashes

**Diagnosis**:
1. Check entity count: `rource.getEntityCount()`
2. Check for memory leaks: Enable heap profiling
3. Check commit count: Large repos (>100k commits)

**Mitigation**:
1. Reduce `--max-commits` to 50,000
2. Enable LOD: `rource.setUseLOD(true)`
3. Disable bloom: `rource.setBloomEnabled(false)`

### Low Frame Rate

**Symptoms**: <30 FPS, stuttering animation

**Diagnosis**:
1. Check renderer: `rource.getRendererType()`
2. Check GPU culling: `rource.isGPUCullingActive()`
3. Check entity count vs threshold

**Mitigation**:
1. Enable GPU culling: `rource.setUseGPUCulling(true)`
2. Lower culling threshold: `rource.setGPUCullingThreshold(5000)`
3. Switch to lower quality: `rource.setRenderQuality('low')`
```

---

## Category 6: Accessibility (Not Rated → Expert+)

### What Expert+ Looks Like
- WCAG 2.1 AA compliance
- Full keyboard navigation
- Screen reader compatibility
- High contrast mode
- Reduced motion support
- Documented accessibility statement

---

### ACC-1: Keyboard Navigation Implementation

**Priority**: Critical
**Complexity**: High
**Estimated Effort**: 2-3 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| All controls accessible | Play, pause, zoom, pan via keyboard | Manual test |
| Focus indicators | Visible focus state | Visual inspection |
| Keyboard shortcuts | Documented shortcuts | Help overlay |
| No keyboard traps | Tab cycles through all controls | Manual test |

#### Implementation

```typescript
// Keyboard shortcuts
const KEYBOARD_SHORTCUTS = {
  'Space': 'togglePlayPause',
  'ArrowLeft': 'rewind10Seconds',
  'ArrowRight': 'forward10Seconds',
  '+': 'zoomIn',
  '-': 'zoomOut',
  '0': 'resetZoom',
  'ArrowUp': 'panUp',
  'ArrowDown': 'panDown',
  'h': 'toggleHelp',
  'f': 'toggleFullscreen',
  'Escape': 'exitFullscreen',
};

// Focus management
canvas.setAttribute('tabindex', '0');
canvas.setAttribute('role', 'application');
canvas.setAttribute('aria-label', 'Git repository visualization');
```

---

### ACC-2: WCAG 2.1 AA Compliance Audit

**Priority**: Critical
**Complexity**: High
**Estimated Effort**: 2 sessions

#### Success Criteria

| Criterion | WCAG Requirement | Verification |
|-----------|------------------|--------------|
| 1.4.3 Contrast | 4.5:1 for text, 3:1 for graphics | Contrast checker |
| 2.1.1 Keyboard | All functionality via keyboard | Manual test |
| 2.4.7 Focus Visible | Visible focus indicator | Visual check |
| 2.5.5 Target Size | 44x44px minimum touch targets | Measurement |

#### Implementation

```markdown
# docs/accessibility/WCAG_COMPLIANCE.md

## WCAG 2.1 AA Compliance Status

| Criterion | Status | Notes |
|-----------|--------|-------|
| 1.1.1 Non-text Content | Partial | Canvas lacks alt text |
| 1.4.3 Contrast (Minimum) | Pass | All text >4.5:1 |
| 1.4.11 Non-text Contrast | Pass | UI elements >3:1 |
| 2.1.1 Keyboard | Pass | All controls accessible |
| 2.1.2 No Keyboard Trap | Pass | Escape exits all states |
| 2.4.7 Focus Visible | Pass | Custom focus ring |

## Known Limitations

- Canvas-based visualization cannot provide text alternatives
  for individual entities. Summary statistics are provided instead.
- Animation cannot be fully paused in play mode by design.
  Reduced motion mode slows but doesn't stop animation.
```

---

### ACC-3: Screen Reader Compatibility

**Priority**: High
**Complexity**: High
**Estimated Effort**: 2 sessions

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| ARIA labels | All controls labeled | Accessibility audit |
| Live regions | Status updates announced | Screen reader test |
| Skip links | Skip to main content | Keyboard test |
| Summary text | Visualization described | Screen reader test |

#### Implementation

```html
<!-- ARIA live region for status updates -->
<div id="status-announcer" aria-live="polite" aria-atomic="true" class="sr-only">
  <!-- JavaScript updates this with status messages -->
</div>

<!-- Control descriptions -->
<button aria-label="Play visualization" aria-pressed="false">
  <span class="icon">▶</span>
</button>

<!-- Canvas description -->
<canvas
  role="img"
  aria-label="Animated visualization of git repository history showing 1,234 files and 56 contributors"
></canvas>
```

```typescript
// Announce status changes to screen readers
function announceStatus(message: string) {
  const announcer = document.getElementById('status-announcer');
  announcer.textContent = message;
}

// Example usage
announceStatus('Visualization started. 1,234 files, 56 contributors.');
announceStatus('Now showing commits from March 2024.');
```

---

### ACC-4: Color Contrast Compliance

**Priority**: High
**Complexity**: Medium
**Estimated Effort**: 1 session

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Text contrast | >4.5:1 against background | Contrast checker |
| UI element contrast | >3:1 against background | Contrast checker |
| Color-blind safe | Not relying on color alone | Colorblind sim |
| High contrast mode | Optional high contrast theme | Toggle test |

#### Implementation

```rust
// crates/rource-render/src/theme.rs
pub struct AccessibleTheme {
    // WCAG AA compliant colors
    pub text_on_dark: Color,     // #FFFFFF on #1a1a2e = 12.6:1 ✓
    pub text_on_light: Color,    // #1a1a2e on #FFFFFF = 12.6:1 ✓
    pub focus_ring: Color,       // #4A90D9 (visible on both)
    pub error: Color,            // #D32F2F (not just red, has icon)
}

impl AccessibleTheme {
    pub fn high_contrast() -> Self {
        Self {
            text_on_dark: Color::WHITE,
            text_on_light: Color::BLACK,
            focus_ring: Color::from_hex("#FFFF00"), // Yellow focus
            error: Color::from_hex("#FF0000"),
        }
    }
}
```

---

### ACC-5: Reduced Motion Support

**Priority**: Medium
**Complexity**: Low
**Estimated Effort**: 0.5 session
**Status**: ✅ **COMPLETED** (2026-01-26)

#### Completion Notes

Implemented comprehensive reduced motion support:
- CSS: `@media (prefers-reduced-motion: reduce)` disables all CSS animations/transitions
- CSS: `.reduce-motion` class for manual override when user selects 'always'
- JS: `reduced-motion.js` feature module with:
  - System preference detection via `matchMedia`
  - Three-state preference: 'system' (default), 'always', 'never'
  - WASM integration: slows playback speed (10x) and disables bloom
  - Preference persistence via localStorage
  - Event dispatching for component reactions

Files created/modified:
- `rource-wasm/www/js/features/reduced-motion.js` (new)
- `rource-wasm/www/js/preferences.js` (added `reducedMotion` default)
- `rource-wasm/www/styles/features/accessibility.css` (added `.reduce-motion` class)
- `rource-wasm/www/js/main.js` (integration)
- `rource-wasm/www/index.html` (modulepreload)

#### Success Criteria

| Criterion | Requirement | Verification |
|-----------|-------------|--------------|
| Detect preference | `prefers-reduced-motion` | CSS/JS check |
| Respect preference | Reduce/disable animations | Visual check |
| Manual toggle | User can override | Settings UI |

---

## Implementation Workflow

For each task, follow this workflow:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    IMPLEMENTATION WORKFLOW                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. READ          - Review task requirements in this document           │
│  2. PLAN          - Break into sub-tasks if complex                     │
│  3. IMPLEMENT     - Write code, tests, documentation                    │
│  4. VERIFY        - Run tests, clippy, verify success criteria          │
│  5. DOCUMENT      - Update relevant docs, add to CHRONOLOGY if perf     │
│  6. COMMIT        - Clear message referencing task ID                   │
│  7. UPDATE        - Mark task complete in this document                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Commit Message Format

```
<type>(<task-id>): <description>

<body explaining what was done>

Closes: #<issue> (if applicable)
```

Examples:
```
feat(OP-1): add production telemetry infrastructure

- Added tracing spans to hot paths (update_layout, render_frame)
- Implemented Prometheus metrics exporter (feature-gated)
- Created TELEMETRY.md documentation
- Added metrics reference documentation

feat(SEC-1): add fuzzing coverage metrics

- Configured cargo-fuzz coverage reporting
- Added weekly fuzzing CI workflow
- Created FUZZING.md with corpus statistics
- Added "Fuzzed for X hours" README badge
```

---

## Priority Order

Recommended implementation sequence for maximum impact:

### Phase A: Foundation (Critical Items)
1. **CI-1**: Performance regression gates (blocks regressions)
2. **SEC-1**: Fuzzing coverage metrics (security proof)
3. **OP-1**: Production telemetry (observability)
4. **DOC-1**: API stability policy (consumer trust)

### Phase B: Operational Excellence
5. **OP-3**: Load testing suite (stability proof)
6. **TST-1**: Mutation testing (test quality proof)
7. **OP-2**: P50/P99 documentation (SLO evidence)
8. **CI-2**: Benchmark history dashboard (trend visibility)

### Phase C: Security & Testing
9. **SEC-2**: SBOM generation (supply chain)
10. **SEC-3**: SLSA provenance (build trust)
11. **TST-3**: Visual regression testing (rendering stability)
12. **TST-2**: Property-based test expansion (math correctness)

### Phase D: Accessibility & Polish
13. **ACC-1**: Keyboard navigation (core accessibility)
14. **ACC-2**: WCAG compliance audit (accessibility proof)
15. **ACC-4**: Color contrast compliance (visual accessibility)
16. **DOC-2**: Architecture Decision Records (design documentation)

### Phase E: Completeness
17. **ACC-3**: Screen reader compatibility (assistive tech)
18. **ACC-5**: Reduced motion support (motion sensitivity)
19. **TST-4**: Cross-browser testing (platform coverage)
20. **DOC-3**: Runbook documentation (operational maturity)
21. **OP-4**: Memory stability analysis (resource management)
22. **OP-5**: Error rate tracking (reliability metrics)
23. **CI-3**: Automated release notes (release process)
24. **CI-4**: Canary deployments (deployment safety)
25. **SEC-4**: Security policy (vulnerability handling)

---

## Verification Checklist

When all tasks are complete, verify Expert+ status:

### Operational Readiness (Expert+)
- [ ] Telemetry spans in hot paths, Prometheus export working
- [ ] P50/P99/P99.9 latency documented for 3+ scenarios
- [ ] 30-minute load test passing with <5% memory growth
- [ ] Memory budget documented per entity type
- [ ] Error categorization and rate tracking active

### Security Posture (Expert+)
- [ ] Fuzzing coverage >75% for VCS parsers
- [ ] SBOM generated with each release
- [ ] SLSA Level 2 attestation in place
- [ ] SECURITY.md with disclosure process

### Testing Maturity (Expert+)
- [ ] Mutation score >80% for critical crates
- [ ] Property tests for all math operations
- [ ] Visual regression tests for key scenarios
- [ ] Cross-browser tests for Chrome, Firefox, Safari

### CI/CD Excellence (Expert+)
- [ ] Performance regression gate blocking >5% regressions
- [ ] 90-day benchmark history visible
- [ ] Automated changelog generation
- [ ] Canary deployment for PRs

### Documentation Quality (Expert+)
- [ ] STABILITY.md with API tiers and semver policy
- [ ] 5+ Architecture Decision Records
- [ ] Operational runbook with playbooks
- [ ] Complete API reference with examples

### Accessibility (Expert+)
- [ ] Full keyboard navigation implemented
- [ ] WCAG 2.1 AA compliance documented
- [ ] Screen reader tested and working
- [ ] High contrast mode available
- [ ] Reduced motion support implemented

---

## Success Metrics

Upon completion, the project should achieve:

| Category | Target Rating | Verification |
|----------|---------------|--------------|
| Technical Excellence | 10/10 (Expert+) | Maintained existing standards |
| Engineering Maturity | 10/10 (Expert+) | ROI-based decisions documented |
| Documentation Quality | 10/10 (Expert+) | ADRs, stability policy, runbooks |
| Operational Readiness | 10/10 (Expert+) | Telemetry, SLOs, load tests |
| Security Posture | 10/10 (Expert+) | Fuzzing metrics, SBOM, SLSA |
| Testing Maturity | 10/10 (Expert+) | Mutation testing, visual regression |
| CI/CD Excellence | 10/10 (Expert+) | Regression gates, benchmarks |
| Accessibility | 10/10 (Expert+) | WCAG AA, keyboard, screen reader |

---

*Document created: 2026-01-26*
*Version: 1.0.0*
*Status: Active Roadmap*
