#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>
#
# benchmark-all.sh - Run all benchmarks and optionally verify against baseline
#
# Usage:
#   ./scripts/benchmark-all.sh                    # Run all benchmarks
#   ./scripts/benchmark-all.sh --save-baseline    # Save current results as baseline
#   ./scripts/benchmark-all.sh --verify-against FILE  # Compare against baseline
#   ./scripts/benchmark-all.sh --quick            # Run subset of benchmarks

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RESULTS_DIR="$PROJECT_ROOT/target/benchmark-results"
BASELINE_FILE="$PROJECT_ROOT/docs/performance/EXPECTED_RESULTS.json"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Parse arguments
SAVE_BASELINE=false
VERIFY_AGAINST=""
QUICK_MODE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --save-baseline)
            SAVE_BASELINE=true
            shift
            ;;
        --verify-against)
            VERIFY_AGAINST="$2"
            shift 2
            ;;
        --quick)
            QUICK_MODE=true
            shift
            ;;
        --help|-h)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --save-baseline       Save current results as baseline"
            echo "  --verify-against FILE Compare against baseline file"
            echo "  --quick               Run subset of benchmarks"
            echo "  --help, -h            Show this help message"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Create results directory
mkdir -p "$RESULTS_DIR"

echo -e "${BLUE}============================================${NC}"
echo -e "${BLUE}  Rource Benchmark Suite${NC}"
echo -e "${BLUE}============================================${NC}"
echo ""

# System info
echo -e "${YELLOW}System Information:${NC}"
echo "  Date: $(date -Iseconds)"
echo "  Hostname: $(hostname)"
echo "  OS: $(uname -s) $(uname -r)"
if command -v lscpu &> /dev/null; then
    echo "  CPU: $(lscpu | grep 'Model name' | cut -d: -f2 | xargs)"
    echo "  Cores: $(nproc)"
fi
echo "  Rust: $(rustc --version)"
echo ""

# Warmup
echo -e "${YELLOW}Warming up...${NC}"
cargo build --release --quiet 2>/dev/null || true
echo ""

# Run criterion benchmarks
echo -e "${BLUE}Running Criterion Benchmarks${NC}"
echo "========================================"

BENCH_OUTPUT="$RESULTS_DIR/criterion-output.txt"

if [ "$QUICK_MODE" = true ]; then
    echo -e "${YELLOW}Quick mode: running subset of benchmarks${NC}"
    cargo bench --workspace -- --quick --noplot 2>&1 | tee "$BENCH_OUTPUT"
else
    cargo bench --workspace -- --noplot 2>&1 | tee "$BENCH_OUTPUT"
fi

# Extract benchmark results to JSON
echo ""
echo -e "${YELLOW}Extracting results...${NC}"

RESULTS_JSON="$RESULTS_DIR/benchmark-results.json"

python3 << 'EOF' - "$BENCH_OUTPUT" "$RESULTS_JSON"
import json
import re
import sys

input_file = sys.argv[1]
output_file = sys.argv[2]

results = []

with open(input_file, 'r') as f:
    content = f.read()

# Parse Criterion benchmark output
# Format: "group/name/variant    time:   [lower bound  estimate  upper bound]"
pattern = r'([\w/]+)\s+time:\s+\[([0-9.]+)\s+(\w+)\s+([0-9.]+)\s+(\w+)\s+([0-9.]+)\s+(\w+)\]'

for match in re.finditer(pattern, content):
    name = match.group(1)
    lower = float(match.group(2))
    lower_unit = match.group(3)
    estimate = float(match.group(4))
    estimate_unit = match.group(5)
    upper = float(match.group(6))
    upper_unit = match.group(7)

    # Convert to nanoseconds
    def to_ns(value, unit):
        multipliers = {'ns': 1, 'µs': 1000, 'us': 1000, 'ms': 1000000, 's': 1000000000}
        return value * multipliers.get(unit, 1)

    results.append({
        'name': name,
        'lower_ns': to_ns(lower, lower_unit),
        'estimate_ns': to_ns(estimate, estimate_unit),
        'upper_ns': to_ns(upper, upper_unit),
        'unit': 'ns'
    })

with open(output_file, 'w') as f:
    json.dump({
        'benchmarks': results,
        'count': len(results)
    }, f, indent=2)

print(f"Extracted {len(results)} benchmark results to {output_file}")
EOF

# Verify against baseline if requested
if [ -n "$VERIFY_AGAINST" ]; then
    echo ""
    echo -e "${BLUE}Verifying Against Baseline${NC}"
    echo "========================================"

    python3 << 'EOF' - "$RESULTS_JSON" "$VERIFY_AGAINST"
import json
import sys

results_file = sys.argv[1]
baseline_file = sys.argv[2]

try:
    with open(results_file, 'r') as f:
        results = json.load(f)
except Exception as e:
    print(f"Error loading results: {e}")
    sys.exit(1)

try:
    with open(baseline_file, 'r') as f:
        baseline = json.load(f)
except Exception as e:
    print(f"Error loading baseline: {e}")
    sys.exit(1)

# Create lookup for baseline
baseline_lookup = {b['name']: b for b in baseline.get('benchmarks', [])}

regressions = []
improvements = []
new_benchmarks = []

for bench in results.get('benchmarks', []):
    name = bench['name']
    current = bench['estimate_ns']

    if name in baseline_lookup:
        expected = baseline_lookup[name]['estimate_ns']
        ratio = current / expected if expected > 0 else 1.0
        change_pct = (ratio - 1.0) * 100

        if ratio > 1.10:  # More than 10% slower
            regressions.append((name, expected, current, change_pct))
        elif ratio < 0.90:  # More than 10% faster
            improvements.append((name, expected, current, change_pct))
    else:
        new_benchmarks.append((name, current))

# Report
print(f"\nBaseline Comparison:")
print(f"  Total benchmarks: {len(results.get('benchmarks', []))}")
print(f"  Matched: {len(results.get('benchmarks', [])) - len(new_benchmarks)}")
print(f"  New: {len(new_benchmarks)}")
print()

if regressions:
    print(f"\033[91mREGRESSIONS ({len(regressions)}):\033[0m")
    for name, expected, current, pct in regressions:
        print(f"  {name}: {expected:.1f}ns -> {current:.1f}ns ({pct:+.1f}%)")
    print()

if improvements:
    print(f"\033[92mIMPROVEMENTS ({len(improvements)}):\033[0m")
    for name, expected, current, pct in improvements:
        print(f"  {name}: {expected:.1f}ns -> {current:.1f}ns ({pct:+.1f}%)")
    print()

if new_benchmarks:
    print(f"\033[93mNEW BENCHMARKS ({len(new_benchmarks)}):\033[0m")
    for name, value in new_benchmarks:
        print(f"  {name}: {value:.1f}ns")
    print()

if regressions:
    print("\033[91mWARNING: Performance regressions detected!\033[0m")
    sys.exit(1)
else:
    print("\033[92mNo regressions detected.\033[0m")
    sys.exit(0)
EOF
fi

# Save baseline if requested
if [ "$SAVE_BASELINE" = true ]; then
    echo ""
    echo -e "${YELLOW}Saving baseline...${NC}"
    cp "$RESULTS_JSON" "$BASELINE_FILE"
    echo -e "${GREEN}Baseline saved to: $BASELINE_FILE${NC}"
fi

# Summary
echo ""
echo -e "${BLUE}============================================${NC}"
echo -e "${BLUE}  Summary${NC}"
echo -e "${BLUE}============================================${NC}"
echo ""
echo "Results saved to: $RESULTS_DIR/"
echo ""
echo "Files:"
ls -la "$RESULTS_DIR/"
echo ""
echo -e "${GREEN}Benchmark run complete!${NC}"
