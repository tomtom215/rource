#!/bin/bash
# Rource vs Gource Benchmark - Common utilities
# This file contains shared functions and variables for all benchmark scripts

set -euo pipefail

# ==============================================================================
# Configuration
# ==============================================================================

BENCHMARK_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULTS_DIR="${BENCHMARK_DIR}/results"
LOGS_DIR="${BENCHMARK_DIR}/logs"
TOOLS_DIR="${BENCHMARK_DIR}/tools"
DOCS_DIR="${BENCHMARK_DIR}/docs"

# Tool paths
ROURCE_BIN="${BENCHMARK_DIR}/../target/release/rource"
GOURCE_BIN="/usr/local/bin/gource"

# Test repository
TEST_REPO="${BENCHMARK_DIR}/home-assistant-core"

# Benchmark parameters
BENCHMARK_RUNS=3              # Number of runs for each benchmark
WARMUP_RUNS=1                 # Warmup runs before measurement
FRAME_COUNT=300               # Number of frames for rendering tests
FRAMERATE=60                  # Framerate for exports
RESOLUTION_WIDTH=1280         # Default width
RESOLUTION_HEIGHT=720         # Default height
SECONDS_PER_DAY=0.1           # Speed of visualization

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ==============================================================================
# Utility Functions
# ==============================================================================

log_info() {
    echo -e "${BLUE}[INFO]${NC} $*"
}

log_success() {
    echo -e "${GREEN}[OK]${NC} $*"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $*"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $*" >&2
}

# Check if required tools exist
check_dependencies() {
    local missing=0

    if [[ ! -x "$ROURCE_BIN" ]]; then
        log_error "Rource binary not found at $ROURCE_BIN"
        log_info "Build with: cargo build --release"
        missing=1
    fi

    if [[ ! -x "$GOURCE_BIN" ]]; then
        log_error "Gource binary not found at $GOURCE_BIN"
        missing=1
    fi

    if [[ ! -d "$TEST_REPO/.git" ]]; then
        log_error "Test repository not found at $TEST_REPO"
        missing=1
    fi

    for cmd in time bc awk grep wc; do
        if ! command -v "$cmd" &> /dev/null; then
            log_error "Required command '$cmd' not found"
            missing=1
        fi
    done

    return $missing
}

# Create timestamp for this benchmark run
get_timestamp() {
    date +"%Y%m%d_%H%M%S"
}

# Create a results directory for this run
create_run_dir() {
    local name="$1"
    local timestamp
    timestamp=$(get_timestamp)
    local run_dir="${RESULTS_DIR}/${name}_${timestamp}"
    mkdir -p "$run_dir"
    echo "$run_dir"
}

# Get file size in bytes
get_file_size() {
    local file="$1"
    stat -c%s "$file" 2>/dev/null || echo 0
}

# Format bytes to human readable
format_bytes() {
    local bytes="$1"
    if (( bytes >= 1073741824 )); then
        echo "$(echo "scale=2; $bytes / 1073741824" | bc) GB"
    elif (( bytes >= 1048576 )); then
        echo "$(echo "scale=2; $bytes / 1048576" | bc) MB"
    elif (( bytes >= 1024 )); then
        echo "$(echo "scale=2; $bytes / 1024" | bc) KB"
    else
        echo "$bytes B"
    fi
}

# Calculate average from a file of numbers (one per line)
calculate_average() {
    local file="$1"
    awk '{ sum += $1; count++ } END { if (count > 0) print sum/count; else print 0 }' "$file"
}

# Calculate standard deviation
calculate_stddev() {
    local file="$1"
    awk '{
        sum += $1;
        sumsq += ($1)^2;
        count++
    } END {
        if (count > 1) {
            avg = sum/count;
            print sqrt(sumsq/count - avg^2)
        } else {
            print 0
        }
    }' "$file"
}

# Calculate min value
calculate_min() {
    local file="$1"
    sort -n "$file" | head -1
}

# Calculate max value
calculate_max() {
    local file="$1"
    sort -n "$file" | tail -1
}

# Run a command with timing and memory tracking
# Returns: time_seconds:peak_memory_kb
run_with_stats() {
    local output_file="$1"
    shift

    # Use /usr/bin/time for detailed stats
    /usr/bin/time -v "$@" 2>&1 | tee "$output_file"

    # Extract stats
    local wall_time
    local peak_memory
    wall_time=$(grep "Elapsed (wall clock) time" "$output_file" | sed 's/.*: //')
    peak_memory=$(grep "Maximum resident set size" "$output_file" | awk '{print $NF}')

    echo "${wall_time}:${peak_memory}"
}

# Convert time string (h:mm:ss or m:ss.ss) to seconds
time_to_seconds() {
    local time_str="$1"
    local seconds=0

    if [[ "$time_str" =~ ([0-9]+):([0-9]+):([0-9.]+) ]]; then
        # h:mm:ss format
        seconds=$(echo "${BASH_REMATCH[1]} * 3600 + ${BASH_REMATCH[2]} * 60 + ${BASH_REMATCH[3]}" | bc)
    elif [[ "$time_str" =~ ([0-9]+):([0-9.]+) ]]; then
        # m:ss format
        seconds=$(echo "${BASH_REMATCH[1]} * 60 + ${BASH_REMATCH[2]}" | bc)
    else
        seconds="$time_str"
    fi

    echo "$seconds"
}

# Generate git log in a format both tools can use
generate_git_log() {
    local repo="$1"
    local output="$2"

    log_info "Generating git log for $repo..."

    cd "$repo"
    git log --pretty=format:"%at|%an|%h" --reverse --name-status | \
    awk 'BEGIN { FS="|" }
    /^[0-9]+\|/ { timestamp=$1; author=$2; hash=$3; next }
    /^[AMD]\t/ {
        action=substr($0,1,1)
        file=substr($0,3)
        print timestamp "|" author "|" action "|" file
    }' > "$output"

    local count
    count=$(wc -l < "$output")
    log_success "Generated log with $count file changes"
}

# Generate Gource custom log format
generate_gource_log() {
    local repo="$1"
    local output="$2"

    log_info "Generating Gource-format log..."

    cd "$repo"
    gource --output-custom-log "$output" . 2>/dev/null

    local count
    count=$(wc -l < "$output")
    log_success "Generated Gource log with $count entries"
}

# Print a separator line
print_separator() {
    echo "============================================================"
}

# Print benchmark header
print_header() {
    local title="$1"
    echo
    print_separator
    echo " $title"
    print_separator
    echo
}

# Format result for display
format_result() {
    local name="$1"
    local rource_val="$2"
    local gource_val="$3"
    local unit="${4:-}"

    local diff
    if [[ -n "$rource_val" && -n "$gource_val" && "$gource_val" != "0" ]]; then
        diff=$(echo "scale=1; ($rource_val - $gource_val) / $gource_val * 100" | bc 2>/dev/null || echo "N/A")
        if [[ "$diff" != "N/A" ]]; then
            diff="${diff}%"
        fi
    else
        diff="N/A"
    fi

    printf "%-30s | %15s %s | %15s %s | %10s\n" "$name" "$rource_val" "$unit" "$gource_val" "$unit" "$diff"
}

# Export functions for subshells
export -f log_info log_success log_warn log_error
export -f get_file_size format_bytes
export -f calculate_average calculate_stddev calculate_min calculate_max
export -f time_to_seconds
