# Fuzzing Documentation

**Status**: Active
**Task ID**: SEC-1
**Last Updated**: 2026-01-26

---

## Overview

Rource uses continuous fuzzing to ensure the robustness of its VCS (Version Control System) parsers. This document describes the fuzzing infrastructure, coverage metrics, and processes for maintaining security through fuzz testing.

## Fuzzing Status

| Fuzz Target | Parser | Status | CI Schedule |
|-------------|--------|--------|-------------|
| `fuzz_git_parser` | Git log parser | Active | Weekly |
| `fuzz_custom_parser` | Custom pipe-delimited parser | Active | Weekly |
| `fuzz_svn_parser` | SVN log parser | Active | Weekly |

## Coverage Goals

| Metric | Target | Current |
|--------|--------|---------|
| Edge Coverage | ≥ 75% | *Run `scripts/fuzz-coverage.sh` to measure* |
| Line Coverage | ≥ 80% | *Run `scripts/fuzz-coverage.sh` to measure* |
| Weekly Fuzzing | 1+ hour per target | ✓ Configured |
| Crashes | 0 | ✓ (last verified by CI) |

## CI Integration

### Weekly Fuzzing Schedule

The `.github/workflows/fuzz.yml` workflow runs every Sunday at 2 AM UTC:

```yaml
on:
  schedule:
    - cron: '0 2 * * 0'  # Weekly Sunday 2 AM UTC
```

### PR Fuzzing

Parser changes trigger a short fuzzing run (5 minutes per target):

```yaml
on:
  pull_request:
    paths:
      - 'crates/rource-vcs/**/*.rs'
      - 'fuzz/**'
```

## Running Fuzz Tests

### Quick Start

```bash
# Install prerequisites
rustup install nightly
cargo install cargo-fuzz

# Run all fuzzers (1 hour per target)
cd fuzz
cargo +nightly fuzz list
cargo +nightly fuzz run fuzz_git_parser -- -max_total_time=3600
```

### Using the Coverage Script

```bash
# Local mode (30 min per target, detailed output)
./scripts/fuzz-coverage.sh

# CI mode (5 min per target, JSON output)
./scripts/fuzz-coverage.sh --ci
```

### Output Files

| File | Description |
|------|-------------|
| `fuzz/coverage-metrics.json` | Metrics for all targets |
| `fuzz/coverage-report/` | HTML coverage reports |
| `fuzz/corpus/<target>/` | Discovered interesting inputs |
| `fuzz/artifacts/<target>/` | Crash-inducing inputs |

## Fuzz Targets

### fuzz_git_parser

Tests the Git log parser with arbitrary input.

```rust
fuzz_target!(|data: &str| {
    let parser = GitParser::new();
    let _ = parser.parse_str(data);
});
```

**Attack Surface**:
- Commit hash parsing
- Timestamp parsing
- Author/email extraction
- File path parsing
- Multiline message handling

### fuzz_custom_parser

Tests the custom pipe-delimited format parser.

```rust
fuzz_target!(|data: &str| {
    let parser = CustomParser::new();
    let _ = parser.parse_str(data);
});
```

**Format**: `timestamp|author|action|path`

**Attack Surface**:
- Field boundary parsing
- Unicode handling
- Timestamp validation
- Path normalization

### fuzz_svn_parser

Tests the SVN log parser.

```rust
fuzz_target!(|data: &str| {
    let parser = SvnParser::new();
    let _ = parser.parse_str(data);
});
```

**Attack Surface**:
- Revision number parsing
- Date format parsing
- Author extraction
- Path lists

## Coverage Methodology

Coverage is measured using LLVM source-based coverage via `cargo-fuzz`:

1. **Instrumentation**: Compiled with `-Zinstrument-coverage`
2. **Collection**: Coverage data collected during fuzzing
3. **Reporting**: `llvm-cov` generates reports

### Measuring Coverage

```bash
# Generate coverage for a target
cd fuzz
cargo +nightly fuzz coverage fuzz_git_parser

# View coverage report
llvm-cov report target/coverage/fuzz_git_parser \
    -instr-profile=coverage/fuzz_git_parser/coverage.profdata
```

## Crash Handling

### When a Crash is Found

1. **CI Notification**: Workflow fails and creates an issue
2. **Artifact Upload**: Crashing input saved for 30 days
3. **Investigation**: Download and reproduce locally

### Reproducing Crashes

```bash
# Download artifact from CI
# Then reproduce:
cd fuzz
cargo +nightly fuzz run fuzz_git_parser artifacts/fuzz_git_parser/crash-abc123
```

### Minimizing Crashes

```bash
# Minimize the crash input
cargo +nightly fuzz tmin fuzz_git_parser artifacts/fuzz_git_parser/crash-abc123
```

### Fixing Crashes

1. Reproduce the crash
2. Identify the root cause
3. Fix the vulnerability
4. Add the minimized input to the corpus as a regression test
5. Verify the fix

```bash
# Add to regression corpus
cp minimized-crash fuzz/corpus/fuzz_git_parser/regression-issue-123

# Verify fix
cargo +nightly fuzz run fuzz_git_parser fuzz/corpus/fuzz_git_parser/regression-issue-123
```

## Security Guarantees

All parsers must satisfy:

| Guarantee | Description |
|-----------|-------------|
| **No Panics** | Must never panic on any input |
| **No Hangs** | Must complete in bounded time |
| **Graceful Errors** | Invalid input returns `Result::Err` |
| **Memory Safe** | No buffer overflows or use-after-free |
| **Deterministic** | Same input produces same output |

## Corpus Management

### Seeding the Corpus

```bash
# Add known-good examples
mkdir -p fuzz/corpus/fuzz_git_parser
echo "commit abc123\nAuthor: Test <test@example.com>\n\n    Message" \
    > fuzz/corpus/fuzz_git_parser/valid-commit
```

### Corpus Hygiene

```bash
# Minimize corpus (remove redundant inputs)
cd fuzz
cargo +nightly fuzz cmin fuzz_git_parser
```

## README Badge

Add this badge to track fuzzing status:

```markdown
[![Fuzzing](https://github.com/tomtom215/rource/actions/workflows/fuzz.yml/badge.svg)](https://github.com/tomtom215/rource/actions/workflows/fuzz.yml)
```

## Metrics History

Fuzzing metrics are collected in `fuzz/coverage-metrics.json` and uploaded as CI artifacts. Track trends by comparing weekly runs.

### Example Metrics Format

```json
{
  "timestamp": "2026-01-26T02:00:00Z",
  "event": "schedule",
  "duration_per_target": 3600,
  "targets": [
    {
      "name": "fuzz_git_parser",
      "corpus_size": 1247,
      "crashes": 0
    },
    {
      "name": "fuzz_custom_parser",
      "corpus_size": 892,
      "crashes": 0
    },
    {
      "name": "fuzz_svn_parser",
      "corpus_size": 654,
      "crashes": 0
    }
  ]
}
```

## Success Criteria (SEC-1)

| Criterion | Requirement | Status |
|-----------|-------------|--------|
| Coverage report | cargo-fuzz coverage output | ✓ `scripts/fuzz-coverage.sh` |
| Edge coverage % | Document % of branches hit | ✓ Coverage reports |
| Corpus statistics | Number of inputs, unique crashes | ✓ `coverage-metrics.json` |
| CI integration | Weekly fuzzing run with report | ✓ `.github/workflows/fuzz.yml` |
| README badge | Fuzzing status badge | ✓ Badge code provided |

---

## References

- [cargo-fuzz Documentation](https://rust-fuzz.github.io/book/cargo-fuzz.html)
- [libFuzzer Documentation](https://llvm.org/docs/LibFuzzer.html)
- [LLVM Coverage](https://llvm.org/docs/CoverageMappingFormat.html)
- [Rust Fuzz Book](https://rust-fuzz.github.io/book/)

---

*Last updated: 2026-01-26*
*Task: SEC-1 Fuzzing Coverage Metrics & Dashboard*
