#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>
#
# run-profiler.sh - Run various profiling tools on Rource
#
# Usage:
#   ./scripts/run-profiler.sh [PROFILER] [OPTIONS]
#
# Profilers:
#   flamegraph   - CPU flamegraph (default)
#   samply       - Interactive CPU profiling
#   dhat         - Memory allocation tracking
#   cachegrind   - Cache miss analysis
#   callgrind    - Instruction profiling
#   iai          - Deterministic benchmarks
#   criterion    - Statistical benchmarks
#   hyperfine    - Command-line benchmarking
#   tracy        - Real-time tracing (requires Tracy GUI)
#
# Options:
#   --repo PATH  - Repository to visualize (default: .)
#   --stress     - Use Home Assistant Core for stress testing
#   --help       - Show this help

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

# Defaults
PROFILER="flamegraph"
REPO_PATH="."
OUTPUT_DIR="/tmp/rource-profile"
STRESS_TEST=false
HA_CORE_PATH="/tmp/ha-core"

show_help() {
    cat << 'EOF'
Rource Profiler Runner

USAGE:
    ./scripts/run-profiler.sh [PROFILER] [OPTIONS]

PROFILERS:
    flamegraph    CPU flamegraph using perf/dtrace (default)
    samply        Interactive CPU profiling (Firefox Profiler)
    dhat          Memory allocation tracking (produces dhat-heap.json)
    cachegrind    Cache miss analysis (Valgrind)
    callgrind     Instruction profiling (Valgrind)
    iai           Deterministic instruction-count benchmarks
    criterion     Statistical benchmarks with regression detection
    hyperfine     Command-line benchmarking
    tracy         Real-time tracing (connect with Tracy GUI)
    all           Run all non-interactive profilers

OPTIONS:
    --repo PATH   Repository to visualize (default: current directory)
    --stress      Use Home Assistant Core (~103K commits) for stress testing
    --help        Show this help message

EXAMPLES:
    # Quick CPU flamegraph
    ./scripts/run-profiler.sh flamegraph

    # Memory profiling with DHAT
    ./scripts/run-profiler.sh dhat

    # Stress test with Home Assistant Core
    ./scripts/run-profiler.sh flamegraph --stress

    # Run all benchmarks
    ./scripts/run-profiler.sh criterion

    # Interactive profiling
    ./scripts/run-profiler.sh samply

OUTPUT:
    Results are saved to /tmp/rource-profile/
    - flamegraph.svg   (flamegraph)
    - dhat-heap.json   (dhat)
    - cachegrind.out.* (cachegrind)
    - callgrind.out.*  (callgrind)
EOF
}

setup_stress_test() {
    echo -e "${CYAN}Setting up Home Assistant Core stress test...${NC}"

    if [[ ! -d "$HA_CORE_PATH" ]]; then
        echo -e "${YELLOW}Cloning Home Assistant Core (this may take a while)...${NC}"
        git clone --depth=1 https://github.com/home-assistant/core.git "$HA_CORE_PATH"
    fi

    # Generate git log if not present
    local log_file="$HA_CORE_PATH/ha-core.log"
    if [[ ! -f "$log_file" ]]; then
        echo -e "${YELLOW}Generating git log (this may take a while)...${NC}"
        cd "$HA_CORE_PATH"
        git fetch --unshallow 2>/dev/null || true
        git log --pretty=format:"%H|%an|%at" --numstat > "$log_file"
        cd - > /dev/null
    fi

    REPO_PATH="$HA_CORE_PATH"
    echo -e "${GREEN}Using Home Assistant Core: $REPO_PATH${NC}"
    echo -e "${GREEN}Log file: $log_file${NC}"
}

ensure_output_dir() {
    mkdir -p "$OUTPUT_DIR"
    echo -e "${CYAN}Output directory: $OUTPUT_DIR${NC}"
}

build_profiling() {
    echo -e "${CYAN}Building with profiling profile...${NC}"
    RUSTFLAGS="-C force-frame-pointers=yes" cargo build --profile profiling
}

build_dhat() {
    echo -e "${CYAN}Building with DHAT profiling...${NC}"
    cargo build --profile dhat --features dhat
}

build_tracy() {
    echo -e "${CYAN}Building with Tracy support...${NC}"
    cargo build --profile profiling --features tracy
}

run_flamegraph() {
    echo -e "${CYAN}Running flamegraph profiling...${NC}"
    build_profiling

    cargo flamegraph --profile profiling \
        --output "$OUTPUT_DIR/flamegraph.svg" \
        -- --headless --output "$OUTPUT_DIR/frames" --seconds-per-day 0.1 "$REPO_PATH"

    echo -e "${GREEN}Flamegraph saved to: $OUTPUT_DIR/flamegraph.svg${NC}"
}

run_samply() {
    echo -e "${CYAN}Running samply profiling...${NC}"
    build_profiling

    echo -e "${YELLOW}samply will open Firefox Profiler in your browser${NC}"
    samply record ./target/profiling/rource \
        --headless --output "$OUTPUT_DIR/frames" --seconds-per-day 0.1 "$REPO_PATH"
}

run_dhat() {
    echo -e "${CYAN}Running DHAT memory profiling...${NC}"
    build_dhat

    cd "$OUTPUT_DIR"
    ../target/dhat/rource --headless --output frames --seconds-per-day 0.1 "$REPO_PATH"
    cd - > /dev/null

    if [[ -f "$OUTPUT_DIR/dhat-heap.json" ]]; then
        echo -e "${GREEN}DHAT output: $OUTPUT_DIR/dhat-heap.json${NC}"
        echo -e "${CYAN}View results at: https://nnethercote.github.io/dh_view/dh_view.html${NC}"
    fi
}

run_cachegrind() {
    echo -e "${CYAN}Running Cachegrind cache analysis...${NC}"
    build_profiling

    valgrind --tool=cachegrind \
        --cachegrind-out-file="$OUTPUT_DIR/cachegrind.out" \
        ./target/profiling/rource \
        --headless --output "$OUTPUT_DIR/frames" --seconds-per-day 0.1 "$REPO_PATH"

    echo -e "${GREEN}Cachegrind output: $OUTPUT_DIR/cachegrind.out${NC}"
    echo -e "${CYAN}Annotate with: cg_annotate $OUTPUT_DIR/cachegrind.out${NC}"
}

run_callgrind() {
    echo -e "${CYAN}Running Callgrind instruction profiling...${NC}"
    build_profiling

    valgrind --tool=callgrind \
        --callgrind-out-file="$OUTPUT_DIR/callgrind.out" \
        ./target/profiling/rource \
        --headless --output "$OUTPUT_DIR/frames" --seconds-per-day 0.1 "$REPO_PATH"

    echo -e "${GREEN}Callgrind output: $OUTPUT_DIR/callgrind.out${NC}"
    echo -e "${CYAN}View with: kcachegrind $OUTPUT_DIR/callgrind.out${NC}"
}

run_iai() {
    echo -e "${CYAN}Running iai-callgrind benchmarks...${NC}"
    cargo bench --bench iai_scene 2>&1 | tee "$OUTPUT_DIR/iai-results.txt"
    echo -e "${GREEN}Results saved to: $OUTPUT_DIR/iai-results.txt${NC}"
}

run_criterion() {
    echo -e "${CYAN}Running Criterion benchmarks...${NC}"
    cargo bench --workspace -- --noplot 2>&1 | tee "$OUTPUT_DIR/criterion-results.txt"
    echo -e "${GREEN}Results saved to: $OUTPUT_DIR/criterion-results.txt${NC}"
}

run_hyperfine() {
    echo -e "${CYAN}Running hyperfine benchmarking...${NC}"
    cargo build --release

    hyperfine \
        --warmup 3 \
        --runs 10 \
        --export-json "$OUTPUT_DIR/hyperfine.json" \
        --export-markdown "$OUTPUT_DIR/hyperfine.md" \
        "./target/release/rource --headless --output $OUTPUT_DIR/frames --seconds-per-day 0.1 $REPO_PATH"

    echo -e "${GREEN}Results saved to: $OUTPUT_DIR/hyperfine.json${NC}"
    cat "$OUTPUT_DIR/hyperfine.md"
}

run_tracy() {
    echo -e "${CYAN}Building with Tracy support...${NC}"
    build_tracy

    echo -e "${YELLOW}Start Tracy capture application, then press Enter to run Rource...${NC}"
    read -r

    ./target/profiling/rource \
        --headless --output "$OUTPUT_DIR/frames" --seconds-per-day 0.1 "$REPO_PATH"
}

run_all() {
    echo -e "${CYAN}Running all non-interactive profilers...${NC}"

    run_flamegraph
    echo ""
    run_dhat
    echo ""
    run_cachegrind
    echo ""
    run_iai
    echo ""
    run_criterion
    echo ""
    run_hyperfine

    echo -e "\n${GREEN}All profiling complete!${NC}"
    echo -e "Results in: $OUTPUT_DIR"
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        flamegraph|samply|dhat|cachegrind|callgrind|iai|criterion|hyperfine|tracy|all)
            PROFILER="$1"
            shift
            ;;
        --repo)
            REPO_PATH="$2"
            shift 2
            ;;
        --stress)
            STRESS_TEST=true
            shift
            ;;
        --help|-h)
            show_help
            exit 0
            ;;
        *)
            echo -e "${RED}Unknown argument: $1${NC}"
            show_help
            exit 1
            ;;
    esac
done

# Setup
ensure_output_dir

if [[ "$STRESS_TEST" == true ]]; then
    setup_stress_test
fi

# Run selected profiler
case $PROFILER in
    flamegraph)
        run_flamegraph
        ;;
    samply)
        run_samply
        ;;
    dhat)
        run_dhat
        ;;
    cachegrind)
        run_cachegrind
        ;;
    callgrind)
        run_callgrind
        ;;
    iai)
        run_iai
        ;;
    criterion)
        run_criterion
        ;;
    hyperfine)
        run_hyperfine
        ;;
    tracy)
        run_tracy
        ;;
    all)
        run_all
        ;;
esac
