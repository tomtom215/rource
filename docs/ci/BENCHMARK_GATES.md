# Benchmark Regression Gates

**Status**: Active
**Task ID**: CI-1
**Implemented**: 2026-01-26

---

## Overview

This document describes the performance regression gates implemented in the CI pipeline. These gates automatically detect and block pull requests that introduce significant performance regressions.

## Regression Threshold

| Threshold | Value | Action |
|-----------|-------|--------|
| Acceptable | < 5% | PR can merge |
| Blocking | ≥ 5% | PR blocked until fixed or bypassed |

The 5% threshold was chosen based on:
- Statistical noise in criterion benchmarks (~2-3%)
- Acceptable variance margin (~2%)
- Detection of meaningful regressions (> 5% is noticeable)

## How It Works

### Workflow Trigger

The `bench-pr.yml` workflow triggers on pull requests to `main` when performance-sensitive files change:

```yaml
paths:
  - 'crates/**/*.rs'
  - 'rource-cli/**/*.rs'
  - 'rource-wasm/**/*.rs'
  - 'Cargo.toml'
  - 'Cargo.lock'
```

### Comparison Process

1. **PR Benchmarks**: Run all criterion benchmarks on the PR branch
2. **Main Benchmarks**: Run identical benchmarks on the `main` branch
3. **Comparison**: Use `critcmp` to compare results with 5% threshold
4. **Report**: Post detailed comparison as PR comment
5. **Gate**: Fail CI if any benchmark regresses ≥ 5%

### Benchmark Suites

The following benchmarks are included in the comparison:

| Crate | Benchmark | Critical Path |
|-------|-----------|---------------|
| rource-core | scene_perf | Scene update loop |
| rource-core | barnes_hut_theta | Physics simulation |
| rource-core | easing_perf | Animation curves |
| rource-math | color_perf | Color operations |
| rource-render | blend_perf | Alpha blending |
| rource-render | bloom_perf | Post-processing |
| rource-render | texture_batching | Draw call batching |
| rource-vcs | vcs_parsing | Log parsing |

## Bypassing the Gate

In some cases, a performance regression may be acceptable (e.g., adding necessary functionality). To bypass the gate:

### Step 1: Add the Bypass Label

Add the `allow-perf-regression` label to the PR.

### Step 2: Document Justification

Include justification in the PR description:

```markdown
## Performance Regression Justification

**Benchmarks affected**: `scene_update/apply_commit`
**Regression**: +8.2%
**Reason**: Added new feature X which requires additional processing per commit.
**Mitigation**: Future optimization planned in #123.
```

### Step 3: Get Review

Performance regression PRs require explicit approval from a maintainer.

## PR Comment Format

The workflow posts a comment with this structure:

```markdown
## Benchmark Comparison Results

Comparing PR branch `feature/xyz` against `main` (`abc1234`)

### ✅ No Significant Regressions
All benchmarks are within the 5% tolerance threshold.

### Detailed Comparison
```
group                  main                  pr
-----                  ----                  --
scene_update/idle      1.23 µs ± 0.02       1.21 µs ± 0.02  -1.6% (faster)
scene_update/commit    5.67 µs ± 0.15       5.82 µs ± 0.14  +2.6% (within tolerance)
```
```

## Creating the Bypass Label

Repository maintainers should create the label:

```bash
gh label create "allow-perf-regression" \
  --description "Bypass performance regression gate with justification" \
  --color "FBCA04"
```

## Workflow Files

| File | Purpose |
|------|---------|
| `.github/workflows/bench-pr.yml` | PR benchmark comparison (blocking) |
| `.github/workflows/bench.yml` | Main branch benchmark tracking (historical) |

## Local Testing

Before submitting a PR, run benchmarks locally:

```bash
# Run all benchmarks
cargo bench --workspace

# Run specific benchmark suite
cargo bench -p rource-core --bench scene_perf

# Compare against saved baseline
cargo bench --workspace -- --save-baseline my-baseline
# ... make changes ...
cargo bench --workspace -- --save-baseline after-changes
critcmp my-baseline after-changes --threshold 5
```

## Troubleshooting

### False Positives

Benchmark variance can occasionally cause false positives. If you believe the regression is noise:

1. Re-run the CI workflow (variance may resolve)
2. Check if the regression is consistent across multiple runs
3. Run benchmarks locally to verify

### Missing Baseline

If the comparison fails due to missing baseline:

1. Ensure `main` branch has recent benchmark data
2. Check that criterion is generating baseline files correctly
3. Verify the benchmark names match between branches

### Timeout Issues

The workflow has a 45-minute timeout. For large benchmark suites:

1. Consider running only critical benchmarks on PR
2. Use `--bench <specific>` to limit scope
3. Adjust timeout if consistently hitting limits

---

## Success Criteria Verification

| Criterion | Requirement | Status |
|-----------|-------------|--------|
| Threshold | Block if >5% regression | ✓ Implemented |
| Baseline | Compare against main branch | ✓ Implemented |
| Report | PR comment with comparison | ✓ Implemented |
| Override | Allow with justification (label) | ✓ Implemented |

---

*Last updated: 2026-01-26*
*Task: CI-1 Performance Regression Gates*
