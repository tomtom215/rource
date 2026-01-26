# Fuzzing Infrastructure

This directory contains fuzz targets for Rource's VCS parsers using `cargo-fuzz` and libFuzzer.

## Prerequisites

1. Install nightly Rust:
   ```bash
   rustup install nightly
   ```

2. Install cargo-fuzz:
   ```bash
   cargo install cargo-fuzz
   ```

## Running Fuzzers

From the `fuzz/` directory:

```bash
# Fuzz the custom parser
cargo +nightly fuzz run fuzz_custom_parser

# Fuzz the Git parser
cargo +nightly fuzz run fuzz_git_parser

# Fuzz the SVN parser
cargo +nightly fuzz run fuzz_svn_parser
```

## Options

```bash
# Run for a specific duration (10 minutes)
cargo +nightly fuzz run fuzz_custom_parser -- -max_total_time=600

# Use multiple cores
cargo +nightly fuzz run fuzz_custom_parser -- -fork=4

# Run with specific seed corpus
cargo +nightly fuzz run fuzz_custom_parser corpus/custom_parser/

# List all fuzz targets
cargo +nightly fuzz list
```

## Coverage-Guided Fuzzing

cargo-fuzz uses coverage-guided fuzzing, which means it tracks code coverage and evolves inputs to maximize coverage. This helps find edge cases that traditional testing might miss.

## Crash Handling

When a crash is found:

1. The crashing input is saved to `fuzz/artifacts/<target>/`
2. Run the minimizer: `cargo +nightly fuzz tmin <target> <artifact>`
3. Analyze and fix the issue
4. Add the minimized input to the regression corpus

## Corpus Management

The fuzzer maintains a corpus of interesting inputs in `fuzz/corpus/<target>/`. These are inputs that triggered new code paths.

To seed the corpus with examples:

```bash
mkdir -p corpus/fuzz_custom_parser
echo "1234567890|John|A|src/main.rs" > corpus/fuzz_custom_parser/example1
```

## CI Integration

Add to your CI workflow:

```yaml
- name: Run fuzz tests (limited)
  run: |
    cargo install cargo-fuzz
    cd fuzz
    for target in $(cargo +nightly fuzz list 2>/dev/null); do
      cargo +nightly fuzz run $target -- -max_total_time=60
    done
```

## Fuzz Targets

| Target | Description |
|--------|-------------|
| `fuzz_custom_parser` | Custom pipe-delimited log format parser |
| `fuzz_git_parser` | Git log format parser |
| `fuzz_svn_parser` | SVN log format parser |

## Security

Fuzzing is a key part of our security strategy. All parsers must:

1. Never panic on any input
2. Never hang indefinitely
3. Handle malformed input gracefully
4. Return proper error types for invalid input

---

*Last Updated: 2026-01-26*
