#!/bin/bash
# scripts/fuzz-coverage.sh
# Generate fuzzing coverage metrics for all fuzz targets
#
# Usage:
#   ./scripts/fuzz-coverage.sh [--ci]
#
# Options:
#   --ci    Run in CI mode (shorter duration, JSON output)
#
# Prerequisites:
#   - Rust nightly: rustup install nightly
#   - cargo-fuzz: cargo install cargo-fuzz
#   - llvm-tools: rustup component add llvm-tools-preview --toolchain nightly
#   - cargo-binutils: cargo install cargo-binutils

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
FUZZ_DIR="fuzz"
COVERAGE_DIR="fuzz/coverage-report"
FUZZ_DURATION_CI=300      # 5 minutes per target in CI
FUZZ_DURATION_LOCAL=1800  # 30 minutes per target locally
OUTPUT_JSON="fuzz/coverage-metrics.json"

# Parse arguments
CI_MODE=false
if [[ "${1:-}" == "--ci" ]]; then
    CI_MODE=true
    FUZZ_DURATION=$FUZZ_DURATION_CI
    echo -e "${BLUE}Running in CI mode (${FUZZ_DURATION}s per target)${NC}"
else
    FUZZ_DURATION=$FUZZ_DURATION_LOCAL
    echo -e "${BLUE}Running in local mode (${FUZZ_DURATION}s per target)${NC}"
fi

# Ensure we're in the project root
if [[ ! -d "$FUZZ_DIR" ]]; then
    echo -e "${RED}Error: fuzz/ directory not found. Run from project root.${NC}"
    exit 1
fi

# Check for required tools
check_tool() {
    if ! command -v "$1" &> /dev/null; then
        echo -e "${RED}Error: $1 is required but not installed.${NC}"
        echo "Install with: $2"
        exit 1
    fi
}

check_tool "rustup" "https://rustup.rs"
check_tool "cargo" "https://rustup.rs"

# Ensure nightly toolchain is available
if ! rustup toolchain list | grep -q "nightly"; then
    echo -e "${YELLOW}Installing nightly toolchain...${NC}"
    rustup install nightly
fi

# Install cargo-fuzz if needed
if ! cargo +nightly fuzz --version &> /dev/null 2>&1; then
    echo -e "${YELLOW}Installing cargo-fuzz...${NC}"
    cargo install cargo-fuzz
fi

# Install llvm-tools for coverage
if ! rustup component list --toolchain nightly | grep -q "llvm-tools-preview (installed)"; then
    echo -e "${YELLOW}Installing llvm-tools-preview...${NC}"
    rustup component add llvm-tools-preview --toolchain nightly
fi

# Create coverage directory
mkdir -p "$COVERAGE_DIR"

# Get list of fuzz targets
cd "$FUZZ_DIR"
TARGETS=$(cargo +nightly fuzz list 2>/dev/null | grep -v "^$" || echo "")
cd ..

if [[ -z "$TARGETS" ]]; then
    echo -e "${RED}No fuzz targets found.${NC}"
    exit 1
fi

echo -e "${GREEN}Found fuzz targets:${NC}"
echo "$TARGETS" | while read -r target; do
    echo "  - $target"
done

# Initialize JSON output
echo "[" > "$OUTPUT_JSON"
FIRST_TARGET=true

# Run fuzzing and collect coverage for each target
for target in $TARGETS; do
    echo ""
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}Fuzzing target: $target${NC}"
    echo -e "${BLUE}Duration: ${FUZZ_DURATION}s${NC}"
    echo -e "${BLUE}========================================${NC}"

    # Run fuzzer with timeout
    echo -e "${YELLOW}Running fuzzer...${NC}"
    cd "$FUZZ_DIR"

    # Capture fuzzer stats
    set +e
    FUZZ_OUTPUT=$(cargo +nightly fuzz run "$target" -- \
        -max_total_time=$FUZZ_DURATION \
        -print_final_stats=1 \
        2>&1) || true
    FUZZ_EXIT=$?
    set -e

    cd ..

    # Extract statistics from fuzzer output
    CORPUS_SIZE=$(find "fuzz/corpus/$target" -type f 2>/dev/null | wc -l || echo "0")

    # Try to extract coverage from llvm-cov if available
    COVERAGE_PCT="N/A"
    EDGE_COVERAGE="N/A"

    # Try to generate coverage report
    echo -e "${YELLOW}Generating coverage report...${NC}"
    cd "$FUZZ_DIR"
    set +e
    cargo +nightly fuzz coverage "$target" 2>/dev/null
    COV_EXIT=$?
    set -e
    cd ..

    if [[ $COV_EXIT -eq 0 ]] && [[ -d "fuzz/coverage/$target" ]]; then
        # Find the profdata file and generate report
        PROFDATA=$(find "fuzz/coverage/$target" -name "*.profdata" 2>/dev/null | head -1)
        if [[ -n "$PROFDATA" ]]; then
            # Use llvm-cov to get summary
            COVERAGE_BINARY="fuzz/target/x86_64-unknown-linux-gnu/coverage/$target"
            if [[ -f "$COVERAGE_BINARY" ]]; then
                COV_REPORT=$(llvm-cov report "$COVERAGE_BINARY" \
                    -instr-profile="$PROFDATA" \
                    --summary-only 2>/dev/null || echo "")

                if [[ -n "$COV_REPORT" ]]; then
                    # Parse coverage percentage from report
                    REGION_COV=$(echo "$COV_REPORT" | grep "TOTAL" | awk '{print $7}' | tr -d '%')
                    if [[ -n "$REGION_COV" ]]; then
                        COVERAGE_PCT="${REGION_COV}%"
                    fi
                fi
            fi
        fi
    fi

    # Extract stats from fuzzer output
    EXECS_TOTAL=$(echo "$FUZZ_OUTPUT" | grep -oP "stat::number_of_executed_units:\s*\K[0-9]+" || echo "0")
    EXECS_PER_SEC=$(echo "$FUZZ_OUTPUT" | grep -oP "exec/s:\s*\K[0-9]+" | tail -1 || echo "0")
    FEATURES=$(echo "$FUZZ_OUTPUT" | grep -oP "ft:\s*\K[0-9]+" | tail -1 || echo "0")

    # Check for crashes
    CRASH_COUNT=$(find "fuzz/artifacts/$target" -type f 2>/dev/null | wc -l || echo "0")

    echo ""
    echo -e "${GREEN}Results for $target:${NC}"
    echo "  Corpus size: $CORPUS_SIZE inputs"
    echo "  Coverage: $COVERAGE_PCT"
    echo "  Features: $FEATURES"
    echo "  Executions: $EXECS_TOTAL"
    echo "  Exec/s: $EXECS_PER_SEC"
    echo "  Crashes: $CRASH_COUNT"

    # Write JSON entry
    if [[ "$FIRST_TARGET" != "true" ]]; then
        echo "," >> "$OUTPUT_JSON"
    fi
    FIRST_TARGET=false

    # Calculate hours run (approximate from this run + any previous data)
    HOURS_RUN=$(echo "scale=2; $FUZZ_DURATION / 3600" | bc)

    cat >> "$OUTPUT_JSON" << JSONEOF
  {
    "target": "$target",
    "corpus_size": $CORPUS_SIZE,
    "coverage_percent": "$COVERAGE_PCT",
    "features_discovered": $FEATURES,
    "total_executions": $EXECS_TOTAL,
    "execs_per_second": $EXECS_PER_SEC,
    "crashes_found": $CRASH_COUNT,
    "hours_run": $HOURS_RUN,
    "timestamp": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  }
JSONEOF
done

# Close JSON array
echo "" >> "$OUTPUT_JSON"
echo "]" >> "$OUTPUT_JSON"

echo ""
echo -e "${GREEN}========================================${NC}"
echo -e "${GREEN}Fuzzing Complete!${NC}"
echo -e "${GREEN}========================================${NC}"
echo ""
echo "Coverage metrics written to: $OUTPUT_JSON"
echo "Coverage reports in: $COVERAGE_DIR"
echo ""

# Generate summary
echo -e "${BLUE}Summary:${NC}"
python3 << EOF
import json

with open("$OUTPUT_JSON") as f:
    data = json.load(f)

total_corpus = sum(t["corpus_size"] for t in data)
total_crashes = sum(t["crashes_found"] for t in data)
total_hours = sum(t["hours_run"] for t in data)

print(f"  Total corpus size: {total_corpus} inputs")
print(f"  Total crashes found: {total_crashes}")
print(f"  Total fuzzing time: {total_hours:.2f} hours")
print()

for target in data:
    status = "PASS" if target["crashes_found"] == 0 else "CRASHES"
    print(f"  [{status}] {target['target']}: {target['corpus_size']} inputs, {target['coverage_percent']} coverage")
EOF

# Exit with error if any crashes were found
TOTAL_CRASHES=$(python3 -c "import json; print(sum(t['crashes_found'] for t in json.load(open('$OUTPUT_JSON'))))")
if [[ "$TOTAL_CRASHES" -gt 0 ]]; then
    echo ""
    echo -e "${RED}WARNING: $TOTAL_CRASHES crash(es) found! Check fuzz/artifacts/ for details.${NC}"
    exit 1
fi

echo ""
echo -e "${GREEN}All fuzz targets passed with no crashes.${NC}"
