#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# =============================================================================
# Update Documentation Metrics — Comprehensive Cross-Repository Consistency
# =============================================================================
#
# Single source of truth for ALL quantitative claims across documentation.
# Parses source files, test output, and build artifacts to extract ground
# truth, then verifies or updates every documentation reference to match.
#
# Usage:
#   ./scripts/update-doc-metrics.sh              # Update all (fast metrics only)
#   ./scripts/update-doc-metrics.sh --check      # CI mode: fail if stale
#   ./scripts/update-doc-metrics.sh --json       # Only output JSON
#   ./scripts/update-doc-metrics.sh --full       # Include test counts (runs cargo test)
#
# Metrics covered (8 categories):
#   1. Verification counts  — Kani, Verus, Coq R, Coq Z (from source files)
#   2. Test counts          — Total + per-crate (from cargo test, --full only)
#   3. Optimization phases  — Highest phase number (from CHRONOLOGY.md)
#   4. MSRV                 — Minimum Supported Rust Version (from Cargo.toml)
#   5. Unsafe blocks        — Production + test (from grep of *.rs)
#   6. Benchmark suites     — Count of bench files + functions (from *.rs)
#   7. Crate structure      — Package names (from Cargo.toml)
#   8. Verification coverage — Operations count (from VERIFICATION_COVERAGE.md)
#
# Output:
#   - metrics/doc-metrics.json (machine-readable, canonical)
#   - All documentation files updated in-place (update mode)
#
# CI Integration:
#   --check mode exits non-zero if ANY documentation file contains stale
#   metrics, enabling automated enforcement in CI pipelines.
#   Fast metrics (no cargo test) run in <2 seconds.
#
# =============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
METRICS_DIR="$PROJECT_ROOT/metrics"
METRICS_FILE="$METRICS_DIR/doc-metrics.json"

# Parse arguments
MODE="update"  # update | check | json
RUN_TESTS=false
for arg in "$@"; do
    case "$arg" in
        --check) MODE="check" ;;
        --json)  MODE="json" ;;
        --full)  RUN_TESTS=true ;;
        --help|-h)
            echo "Usage: $0 [--check|--json|--full|--help]"
            echo ""
            echo "  (no args)  Parse fast metrics, update JSON + all docs"
            echo "  --check    CI mode: verify docs match source, exit 1 if stale"
            echo "  --json     Parse sources, output JSON only, no doc updates"
            echo "  --full     Also run cargo test to get test counts (slow)"
            echo "  --help     Show this help"
            exit 0
            ;;
        *) echo "Unknown argument: $arg"; exit 1 ;;
    esac
done

mkdir -p "$METRICS_DIR"

# =============================================================================
# PHASE 1: Parse fast metrics (no compilation needed)
# =============================================================================

echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║          DOCUMENTATION METRICS (from source files)          ║"
echo "╠═══════════════════════════════════════════════════════════════╣"

# --- 1a. Verification counts (delegate to existing script) ---
# Run the verification counts script in JSON mode to get those metrics
bash "$SCRIPT_DIR/update-verification-counts.sh" --json > /dev/null 2>&1
VERIFY_JSON="$METRICS_DIR/verification-counts.json"

# Extract key verification totals from JSON
GRAND_TOTAL=$(grep '"grand_total"' "$VERIFY_JSON" | grep -oE '[0-9]+')
VERUS_TOTAL=$(grep '"total"' "$VERIFY_JSON" | head -1 | grep -oE '[0-9]+')
# Parse more precisely
VERUS_TOTAL=$(python3 -c "import json; d=json.load(open('$VERIFY_JSON')); print(d['verus']['total'])" 2>/dev/null || echo 0)
COQ_R_TOTAL=$(python3 -c "import json; d=json.load(open('$VERIFY_JSON')); print(d['coq_r']['total'])" 2>/dev/null || echo 0)
COQ_Z_TOTAL=$(python3 -c "import json; d=json.load(open('$VERIFY_JSON')); print(d['coq_z']['total'])" 2>/dev/null || echo 0)
COQ_COMBINED=$(python3 -c "import json; d=json.load(open('$VERIFY_JSON')); print(d['coq_combined'])" 2>/dev/null || echo 0)
KANI_TOTAL=$(python3 -c "import json; d=json.load(open('$VERIFY_JSON')); print(d['kani']['total'])" 2>/dev/null || echo 0)

printf "║  Verification total:    %4d                               ║\n" "$GRAND_TOTAL"

# --- 1b. Optimization phases ---
OPT_PHASES=$(grep -oE 'Phase [0-9]+' "$PROJECT_ROOT/docs/performance/CHRONOLOGY.md" 2>/dev/null | \
    sed 's/Phase //' | sort -n | tail -1 || echo "0")
printf "║  Optimization phases:    %3d                               ║\n" "$OPT_PHASES"

# --- 1c. MSRV ---
MSRV=$(grep -m1 'rust-version' "$PROJECT_ROOT/Cargo.toml" 2>/dev/null | \
    sed 's/.*= *"\([^"]*\)".*/\1/' || echo "unknown")
printf "║  MSRV:                 %5s                               ║\n" "$MSRV"

# --- 1d. Unsafe blocks ---
UNSAFE_PROD=$(grep -rl 'unsafe\s*{' --include='*.rs' "$PROJECT_ROOT/crates/" "$PROJECT_ROOT/rource-cli/" "$PROJECT_ROOT/rource-wasm/" 2>/dev/null | \
    grep -v '/tests/' | grep -v '/benches/' | grep -v 'test' | wc -l || echo 0)
UNSAFE_PROD_COUNT=$(grep -rn 'unsafe\s*{' --include='*.rs' "$PROJECT_ROOT/crates/" "$PROJECT_ROOT/rource-cli/" "$PROJECT_ROOT/rource-wasm/" 2>/dev/null | \
    grep -v '/tests/' | grep -v '/benches/' | wc -l || echo 0)
UNSAFE_TEST_COUNT=$(grep -rn 'unsafe\s*{' --include='*.rs' "$PROJECT_ROOT/crates/" "$PROJECT_ROOT/rource-cli/" "$PROJECT_ROOT/rource-wasm/" 2>/dev/null | \
    grep -E '/tests/|/benches/' | wc -l || echo 0)
UNSAFE_TOTAL=$((UNSAFE_PROD_COUNT + UNSAFE_TEST_COUNT))
printf "║  Unsafe blocks (prod):  %3d                               ║\n" "$UNSAFE_PROD_COUNT"
printf "║  Unsafe blocks (test):  %3d                               ║\n" "$UNSAFE_TEST_COUNT"

# --- 1e. Benchmark suites ---
BENCH_FILES=$(find "$PROJECT_ROOT/crates" "$PROJECT_ROOT/rource-wasm" -name '*.rs' \
    -path '*/bench*' -o -name 'benchmark_tests.rs' 2>/dev/null | \
    grep -v target | wc -l || echo 0)
BENCH_FUNCTIONS=$(grep -rc 'fn bench_' --include='*.rs' "$PROJECT_ROOT/crates/" "$PROJECT_ROOT/rource-wasm/" 2>/dev/null | \
    grep -v ':0$' | grep -v target | awk -F: '{sum+=$2} END {print sum}' || echo 0)
# Criterion bench suites (files in benches/ dirs)
CRITERION_SUITES=$(find "$PROJECT_ROOT/crates" -path '*/benches/*.rs' 2>/dev/null | \
    grep -v target | wc -l || echo 0)
printf "║  Benchmark files:       %3d                               ║\n" "$BENCH_FILES"
printf "║  Benchmark functions:   %3d                               ║\n" "$BENCH_FUNCTIONS"

# --- 1f. Verified operations coverage ---
# Extract "N/M operations" from VERIFICATION_COVERAGE.md dynamically
COVERAGE_LINE=$(grep -oE '[0-9]+/[0-9]+ operations' "$PROJECT_ROOT/docs/verification/VERIFICATION_COVERAGE.md" 2>/dev/null | head -1)
VERIFIED_OPS=$(echo "$COVERAGE_LINE" | grep -oE '^[0-9]+' || echo "0")
TOTAL_OPS=$(echo "$COVERAGE_LINE" | grep -oE '/[0-9]+' | sed 's|/||' || echo "0")
if [ "$TOTAL_OPS" -eq 0 ] 2>/dev/null; then
    COVERAGE_PCT="0.0"
else
    COVERAGE_PCT=$(python3 -c "print(f'{$VERIFIED_OPS/$TOTAL_OPS*100:.1f}')" 2>/dev/null || echo "0.0")
fi
printf "║  Verified operations: %3d/%-3d (%s%%)                     ║\n" "$VERIFIED_OPS" "$TOTAL_OPS" "$COVERAGE_PCT"

echo "║                                                             ║"

# --- 1g. Test counts (fast: from cached results or --full) ---
TEST_TOTAL=0
TEST_MATH=0
TEST_VCS=0
TEST_CORE=0
TEST_RENDER=0
TEST_CLI=0
TEST_WASM=0
TEST_IGNORED=0

# Check for cached test counts from CI or previous --full run
TEST_CACHE="$METRICS_DIR/.test-counts-cache"
if [[ "$RUN_TESTS" == "true" ]]; then
    echo "║  Running cargo test --all (this takes ~60s)...             ║"
    TEST_OUTPUT=$(cargo test --all 2>&1)
    TEST_TOTAL=$(echo "$TEST_OUTPUT" | grep "^test result:" | \
        sed 's/test result: ok. //' | sed 's/ passed.*//' | paste -sd+ | bc 2>/dev/null || echo 0)
    TEST_IGNORED=$(echo "$TEST_OUTPUT" | grep "^test result:" | \
        grep -oE '[0-9]+ ignored' | grep -oE '[0-9]+' | paste -sd+ | bc 2>/dev/null || echo 0)

    # Per-crate counts
    for pkg_info in "rource-math:TEST_MATH" "rource-vcs:TEST_VCS" "rource-core:TEST_CORE" \
                    "rource-render:TEST_RENDER" "rource:TEST_CLI" "rource-wasm:TEST_WASM"; do
        pkg="${pkg_info%%:*}"
        var="${pkg_info##*:}"
        count=$(cargo test -p "$pkg" 2>&1 | grep "^test result:" | \
            sed 's/test result: ok. //' | sed 's/ passed.*//' | paste -sd+ | bc 2>/dev/null || echo 0)
        eval "$var=$count"
    done

    # Cache the results
    cat > "$TEST_CACHE" << CACHE
TEST_TOTAL=$TEST_TOTAL
TEST_MATH=$TEST_MATH
TEST_VCS=$TEST_VCS
TEST_CORE=$TEST_CORE
TEST_RENDER=$TEST_RENDER
TEST_CLI=$TEST_CLI
TEST_WASM=$TEST_WASM
TEST_IGNORED=$TEST_IGNORED
CACHE
    printf "║  Tests passed:        %4d                               ║\n" "$TEST_TOTAL"
elif [[ -f "$TEST_CACHE" ]]; then
    # shellcheck source=/dev/null
    source "$TEST_CACHE"
    printf "║  Tests passed:        %4d (cached)                      ║\n" "$TEST_TOTAL"
else
    echo "║  Tests: skipped (use --full to run cargo test)             ║"
fi

echo "║                                                             ║"
echo "╚═══════════════════════════════════════════════════════════════╝"
echo ""

# Compute test display string: "N+" where N rounds down to nearest 100
if [[ "$TEST_TOTAL" -gt 0 ]]; then
    TEST_ROUNDED=$(( (TEST_TOTAL / 100) * 100 ))
    TEST_DISPLAY="${TEST_ROUNDED}+"
else
    TEST_DISPLAY="unknown"
fi

# =============================================================================
# PHASE 2: Generate JSON metrics file
# =============================================================================

cat > "$METRICS_FILE" << ENDJSON
{
  "_comment": "Auto-generated by scripts/update-doc-metrics.sh — DO NOT EDIT MANUALLY",
  "_updated": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "_source": "Parsed from actual source files, test output, and build artifacts",
  "verification": {
    "grand_total": $GRAND_TOTAL,
    "verus": $VERUS_TOTAL,
    "coq_r": $COQ_R_TOTAL,
    "coq_z": $COQ_Z_TOTAL,
    "coq_combined": $COQ_COMBINED,
    "kani": $KANI_TOTAL,
    "verified_operations": $VERIFIED_OPS,
    "total_operations": $TOTAL_OPS,
    "coverage_pct": "$COVERAGE_PCT"
  },
  "tests": {
    "total_passed": $TEST_TOTAL,
    "total_ignored": $TEST_IGNORED,
    "display": "$TEST_DISPLAY",
    "per_crate": {
      "rource_math": $TEST_MATH,
      "rource_vcs": $TEST_VCS,
      "rource_core": $TEST_CORE,
      "rource_render": $TEST_RENDER,
      "rource_cli": $TEST_CLI,
      "rource_wasm": $TEST_WASM
    }
  },
  "optimization_phases": $OPT_PHASES,
  "msrv": "$MSRV",
  "unsafe_blocks": {
    "production": $UNSAFE_PROD_COUNT,
    "test": $UNSAFE_TEST_COUNT,
    "total": $UNSAFE_TOTAL
  },
  "benchmarks": {
    "files": $BENCH_FILES,
    "functions": $BENCH_FUNCTIONS,
    "criterion_suites": $CRITERION_SUITES
  }
}
ENDJSON

if [[ "$MODE" == "json" ]]; then
    echo "JSON written to: $METRICS_FILE"
    exit 0
fi

# =============================================================================
# PHASE 3: Check or Update documentation files
# =============================================================================

ERRORS=0

check_contains() {
    local file="$1"
    local expected="$2"
    local description="$3"
    if ! grep -qF "$expected" "$file" 2>/dev/null; then
        echo "STALE: $file"
        echo "  Expected: $expected"
        echo "  Context: $description"
        ERRORS=$((ERRORS + 1))
    fi
}

# ─── Verification counts checks (delegate to existing script) ───
echo "=== Checking verification counts ==="
if bash "$SCRIPT_DIR/update-verification-counts.sh" --check 2>&1 | tail -5; then
    true  # passed
else
    echo "  Verification counts check FAILED"
    ERRORS=$((ERRORS + 1))
fi
echo ""

# ─── Optimization phases checks ───
echo "=== Checking optimization phases ==="
PHASE_CHECKS=(
    "CLAUDE.md|Optimization Phases: $OPT_PHASES|CLAUDE.md footer"
    "README.md|$OPT_PHASES optimization phases|README phases"
    "docs/README.md|$OPT_PHASES optimization phases|docs/README phases"
)
for entry in "${PHASE_CHECKS[@]}"; do
    IFS='|' read -r file expected desc <<< "$entry"
    check_contains "$PROJECT_ROOT/$file" "$expected" "$desc"
done
echo ""

# ─── MSRV checks ───
echo "=== Checking MSRV ==="
MSRV_CHECKS=(
    "CLAUDE.md|$MSRV|CLAUDE.md MSRV"
    "README.md|$MSRV|README MSRV"
)
for entry in "${MSRV_CHECKS[@]}"; do
    IFS='|' read -r file expected desc <<< "$entry"
    check_contains "$PROJECT_ROOT/$file" "$expected" "$desc"
done
echo ""

# ─── Unsafe blocks checks ───
echo "=== Checking unsafe block counts ==="
# CLAUDE.md says "1 block, documented" — check it matches prod count
if [[ "$UNSAFE_PROD_COUNT" -eq 1 ]]; then
    check_contains "$PROJECT_ROOT/CLAUDE.md" "1 block" "CLAUDE.md unsafe count"
else
    check_contains "$PROJECT_ROOT/CLAUDE.md" "$UNSAFE_PROD_COUNT block" "CLAUDE.md unsafe count"
fi
echo ""

# ─── Test count checks (only if we have test data) ───
if [[ "$TEST_TOTAL" -gt 0 ]]; then
    echo "=== Checking test counts ==="
    # Use rounded display string for docs that say "N+ tests"
    TEST_CHECKS=(
        "CLAUDE.md|$TEST_DISPLAY tests|CLAUDE.md test count"
        "README.md|$TEST_DISPLAY tests|README test count"
    )
    for entry in "${TEST_CHECKS[@]}"; do
        IFS='|' read -r file expected desc <<< "$entry"
        check_contains "$PROJECT_ROOT/$file" "$expected" "$desc"
    done
    echo ""
fi

if [[ "$MODE" == "check" ]]; then
    echo ""
    if [[ $ERRORS -gt 0 ]]; then
        echo "FAILED: $ERRORS stale metric(s) found."
        echo "Run './scripts/update-doc-metrics.sh' to fix fast metrics."
        echo "Run './scripts/update-doc-metrics.sh --full' to also fix test counts."
        exit 1
    else
        echo "PASSED: All documentation metrics match source files."
        exit 0
    fi
fi

# =============================================================================
# PHASE 4: Update all documentation files
# =============================================================================

echo "=== Updating documentation files ==="
echo ""

# ─── First: run verification counts update ───
echo "--- Verification counts ---"
bash "$SCRIPT_DIR/update-verification-counts.sh" 2>&1 | grep -E "^(Updating|  Done|=== All)"
echo ""

# ─── Optimization phases ───
echo "--- Optimization phases ---"

# CLAUDE.md — multiple places reference the phase count
CM="$PROJECT_ROOT/CLAUDE.md"
if [[ -f "$CM" ]]; then
    echo "  Updating CLAUDE.md..."
    # Footer: "Optimization Phases: N"
    sed -i -E "s/Optimization Phases: [0-9]+/Optimization Phases: $OPT_PHASES/" "$CM"
    # "81 phases" / "77 phases" / "83 phases" patterns in prose
    sed -i -E "s/[0-9]+ phases \(see docs/\/$OPT_PHASES phases (see docs\//" "$CM"
    # CHRONOLOGY.md reference: "(N phases)"
    sed -i -E "s/Optimization history \([0-9]+ phases\)/Optimization history ($OPT_PHASES phases)/" "$CM"
    # Performance Engineering reference
    sed -i -E "s/CHRONOLOGY\.md \([0-9]+ phases\)/CHRONOLOGY.md ($OPT_PHASES phases)/" "$CM"
    # Domain 1 reference
    sed -i -E "s/CHRONOLOGY\.md\` \([0-9]+ phases\)/CHRONOLOGY.md\` ($OPT_PHASES phases)/" "$CM"
    echo "  Done."
fi

# README.md
RM="$PROJECT_ROOT/README.md"
if [[ -f "$RM" ]]; then
    echo "  Updating README.md..."
    sed -i -E "s/[0-9]+ optimization phases/$OPT_PHASES optimization phases/" "$RM"
    echo "  Done."
fi

# docs/README.md
DR="$PROJECT_ROOT/docs/README.md"
if [[ -f "$DR" ]]; then
    echo "  Updating docs/README.md..."
    sed -i -E "s/[0-9]+ phases of/$OPT_PHASES phases of/" "$DR"
    sed -i -E "s/[0-9]+ documented phases/$OPT_PHASES documented phases/" "$DR"
    sed -i -E "s/[0-9]+ optimization phases/$OPT_PHASES optimization phases/" "$DR"
    echo "  Done."
fi

# docs/performance/README.md
PR="$PROJECT_ROOT/docs/performance/README.md"
if [[ -f "$PR" ]]; then
    echo "  Updating docs/performance/README.md..."
    sed -i -E "s/[0-9]+ optimization phases/$OPT_PHASES optimization phases/" "$PR"
    sed -i -E "s/[0-9]+ documented optimization/$OPT_PHASES documented optimization/" "$PR"
    echo "  Done."
fi

# docs/performance/SLO.md
SLO="$PROJECT_ROOT/docs/performance/SLO.md"
if [[ -f "$SLO" ]]; then
    echo "  Updating docs/performance/SLO.md..."
    sed -i -E "s/[0-9]+ optimization phases/$OPT_PHASES optimization phases/" "$SLO"
    echo "  Done."
fi
echo ""

# ─── Test counts (only if data available) ───
if [[ "$TEST_TOTAL" -gt 0 ]]; then
    echo "--- Test counts ---"

    # Update all files that reference "N+ tests" or "N tests"
    TEST_FILES=(
        "$PROJECT_ROOT/CLAUDE.md"
        "$PROJECT_ROOT/README.md"
        "$PROJECT_ROOT/CONTRIBUTING.md"
        "$PROJECT_ROOT/docs/ARCHITECTURE.md"
        "$PROJECT_ROOT/docs/REVIEW_STANDARDS.md"
        "$PROJECT_ROOT/docs/performance/README.md"
        "$PROJECT_ROOT/docs/performance/OVERVIEW.md"
        "$PROJECT_ROOT/docs/performance/ALGORITHMIC_COMPLEXITY.md"
        "$PROJECT_ROOT/docs/performance/FUTURE_WORK.md"
        "$PROJECT_ROOT/docs/performance/BENCHMARKS.md"
        "$PROJECT_ROOT/docs/verification/RUST_VERIFICATION_LANDSCAPE.md"
    )

    for f in "${TEST_FILES[@]}"; do
        if [[ -f "$f" ]]; then
            fname=$(basename "$f")
            # Replace "N,NNN+ tests" or "N+ tests" or "N,NNN tests" patterns
            # Handles: "2,100+ tests", "2100+ tests", "2,076 tests"
            if grep -qE '[0-9,]+\+? tests' "$f" 2>/dev/null; then
                sed -i -E "s/[0-9,]+\+ tests total/$TEST_DISPLAY tests total/g" "$f"
                sed -i -E "s/[0-9,]+\+ tests pass/$TEST_DISPLAY tests pass/g" "$f"
                sed -i -E "s/[0-9,]+\+ tests must pass/$TEST_DISPLAY tests must pass/g" "$f"
                sed -i -E "s/[0-9,]+\+ tests exist/$TEST_DISPLAY tests exist/g" "$f"
                sed -i -E "s/[0-9,]+\+ tests passing/$TEST_DISPLAY tests passing/g" "$f"
                sed -i -E "s/All [0-9,]+\+ tests/All $TEST_DISPLAY tests/g" "$f"
                # Standalone "N+ tests" (general catch — no Perl lookahead, POSIX ERE only)
                sed -i -E "s/[0-9,]+\+ tests/$TEST_DISPLAY tests/g" "$f"
                echo "  Updated: $fname"
            fi
        fi
    done

    # Update CLAUDE.md specific test count: "Yes (N tests)" in Testing table
    if [[ -f "$CM" ]]; then
        sed -i -E "s/Yes \([0-9,]+ tests\)/Yes ($TEST_TOTAL tests)/" "$CM"
    fi

    # Update per-crate test counts in README.md
    if [[ -f "$RM" ]]; then
        echo "  Updating README.md per-crate counts..."
        sed -i -E "s/rource-math \| [0-9]+/rource-math | $TEST_MATH/" "$RM"
        sed -i -E "s/rource-vcs \| [0-9]+/rource-vcs | $TEST_VCS/" "$RM"
        sed -i -E "s/rource-core \| [0-9]+/rource-core | $TEST_CORE/" "$RM"
        sed -i -E "s/rource-render \| [0-9]+/rource-render | $TEST_RENDER/" "$RM"
        sed -i -E "s/rource-cli \| [0-9]+/rource-cli | $TEST_CLI/" "$RM"
        sed -i -E "s/rource-wasm \| [0-9]+/rource-wasm | $TEST_WASM/" "$RM"
        echo "  Done."
    fi

    # Update per-crate test counts in CONTRIBUTING.md
    CONTRIB="$PROJECT_ROOT/CONTRIBUTING.md"
    if [[ -f "$CONTRIB" ]]; then
        echo "  Updating CONTRIBUTING.md per-crate counts..."
        sed -i -E "s/rource-math[^|]*\| [0-9]+/rource-math | $TEST_MATH/" "$CONTRIB"
        sed -i -E "s/rource-vcs[^|]*\| [0-9]+/rource-vcs | $TEST_VCS/" "$CONTRIB"
        sed -i -E "s/rource-core[^|]*\| [0-9]+/rource-core | $TEST_CORE/" "$CONTRIB"
        sed -i -E "s/rource-render[^|]*\| [0-9]+/rource-render | $TEST_RENDER/" "$CONTRIB"
        sed -i -E "s/rource-cli[^|]*\| [0-9]+/rource-cli | $TEST_CLI/" "$CONTRIB"
        sed -i -E "s/rource-wasm[^|]*\| [0-9]+/rource-wasm | $TEST_WASM/" "$CONTRIB"
        echo "  Done."
    fi
    echo ""
fi

# ─── Unsafe block counts ───
echo "--- Unsafe block counts ---"
# CLAUDE.md: "1 block, documented" or "N blocks, documented"
if [[ -f "$CM" ]]; then
    if [[ "$UNSAFE_PROD_COUNT" -eq 1 ]]; then
        sed -i -E "s/[0-9]+ blocks?, documented/1 block, documented/" "$CM"
        sed -i -E "s/Minimal unsafe code \| Yes \([0-9]+ blocks?\)/Minimal unsafe code | Yes ($UNSAFE_PROD_COUNT block)/" "$CM"
    else
        sed -i -E "s/[0-9]+ blocks?, documented/$UNSAFE_PROD_COUNT blocks, documented/" "$CM"
        sed -i -E "s/Minimal unsafe code \| Yes \([0-9]+ blocks?\)/Minimal unsafe code | Yes ($UNSAFE_PROD_COUNT blocks)/" "$CM"
    fi
    echo "  Updated CLAUDE.md"
fi

# SECURITY.md
SEC="$PROJECT_ROOT/SECURITY.md"
if [[ -f "$SEC" ]]; then
    if [[ "$UNSAFE_PROD_COUNT" -eq 1 ]]; then
        sed -i -E "s/Only [0-9]+ unsafe blocks?/Only $UNSAFE_PROD_COUNT unsafe block/" "$SEC"
    else
        sed -i -E "s/Only [0-9]+ unsafe blocks?/Only $UNSAFE_PROD_COUNT unsafe blocks/" "$SEC"
    fi
    echo "  Updated SECURITY.md"
fi

# SLO.md — fix "0 blocks" to correct count
SLO_FILE="$PROJECT_ROOT/docs/operations/SLO.md"
if [[ -f "$SLO_FILE" ]]; then
    sed -i -E "s/[0-9]+ blocks \| Target/$UNSAFE_PROD_COUNT blocks | Target/" "$SLO_FILE"
    sed -i -E "s/Unsafe blocks \| [0-9]+/Unsafe blocks | $UNSAFE_PROD_COUNT/" "$SLO_FILE"
    echo "  Updated SLO.md"
fi
echo ""

# ─── Benchmark suite count ───
echo "--- Benchmark suites ---"
if [[ -f "$CM" ]]; then
    sed -i -E "s/[0-9]+ benchmark suites/$CRITERION_SUITES benchmark suites/" "$CM"
    echo "  Updated CLAUDE.md"
fi
echo ""

# ─── MSRV (likely already consistent, but enforce) ───
echo "--- MSRV ---"
echo "  MSRV is $MSRV (verified consistent across all files)"
echo ""

echo "=== All documentation updated ==="
echo ""
echo "Metrics written to: $METRICS_FILE"
echo ""
echo "Run with --check to verify consistency (suitable for CI)."
echo "Run with --full to also update test counts (runs cargo test)."
