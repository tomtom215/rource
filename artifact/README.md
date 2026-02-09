# Artifact: Triple-Verified (CPP 2027)

This artifact reproduces all verification results for:

> **Triple-Verified: Hybrid Formal Verification of a Production Rust Math
> Library using Verus, Coq, and Kani**

## Quick Start

```bash
docker build -t rource-artifact -f artifact/Dockerfile .
docker run --rm rource-artifact          # Full reproduction (~30 min)
docker run --rm rource-artifact --quick  # Quick subset (~10 min)
```

## Claims Verified

| Claim | Tool | Expected Result |
|-------|------|-----------------|
| 2900+ unit tests pass | `cargo test` | All pass, zero failures |
| Zero clippy warnings | `cargo clippy` | Zero warnings |
| 498 Verus proof functions | `/tmp/verus/verus` | Zero errors across 11 files |
| 1,366 R-based Coq theorems | `coqc` | Zero admits |
| 471 Z-based Coq theorems | `coqc` | Zero admits |
| 361 FP error bound theorems | `coqc` (Flocq 4.1.3) | Zero admits |
| 272 Kani harnesses | `cargo kani` | Zero failures (subset run) |

## Tool Versions

| Tool | Version | Purpose |
|------|---------|---------|
| Rust | 1.93 | MSRV, compilation |
| Coq | 8.18.0 | Interactive theorem prover |
| Flocq | 4.1.3 | IEEE 754 formalization |
| Verus | 0.2026.01.23+ | SMT-based Rust verification |
| Kani | 0.67.0 | Bounded model checking |

## Modes

| Mode | Command | Time | What it checks |
|------|---------|------|---------------|
| Full | `--` (default) | ~30 min | All 5 phases |
| Quick | `--quick` | ~10 min | Tests + Coq + Verus |
| Tests only | `--tests` | ~2 min | Rust tests + clippy + fmt |
| Coq only | `--coq` | ~2 min | All 46 Coq files |
| Verus only | `--verus` | ~1 min | All 11 Verus files |
| Kani only | `--kani` | ~20 min | Representative harnesses |

## Without Docker

```bash
# Prerequisites: Rust 1.93+, Coq 8.18, Flocq 4.1.3, Verus, Kani
./artifact/reproduce-all.sh
```

## Expected Output

```
================================================================
  Summary
================================================================
  PASS: 12
  FAIL: 0
  SKIP: 0

ARTIFACT EVALUATION: PASSED

All verification claims are reproducible from this clean build.
```

## File Structure

```
artifact/
├── Dockerfile          # Docker image for clean reproduction
├── reproduce-all.sh    # Main reproduction script
└── README.md           # This file
```
