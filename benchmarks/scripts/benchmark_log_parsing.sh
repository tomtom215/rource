#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# Benchmark: Git Log Parsing Performance
# Measures how quickly each tool can parse git logs

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

print_header "Benchmark: Git Log Parsing Performance"

# Check dependencies
if ! check_dependencies; then
    log_error "Missing dependencies, aborting"
    exit 1
fi

# Create output directory
RUN_DIR=$(create_run_dir "log_parsing")
log_info "Results will be saved to: $RUN_DIR"

# Get repository stats
cd "$TEST_REPO"
TOTAL_COMMITS=$(git rev-list --count HEAD)
TOTAL_FILES=$(git log --pretty=format: --name-only --diff-filter=A | sort -u | wc -l)
log_info "Repository: Home Assistant Core"
log_info "Total commits: $TOTAL_COMMITS"
log_info "Total unique files ever added: $TOTAL_FILES"

# Generate git log file for testing
GIT_LOG_FILE="${RUN_DIR}/git.log"
log_info "Generating git log file..."
git log --pretty=format:"user:%an%n%at" --reverse --name-status > "$GIT_LOG_FILE"
GIT_LOG_SIZE=$(get_file_size "$GIT_LOG_FILE")
log_info "Git log size: $(format_bytes $GIT_LOG_SIZE)"

# Also generate custom format log
CUSTOM_LOG_FILE="${RUN_DIR}/custom.log"
log_info "Generating custom format log..."
git log --pretty=format:"%at|%an|%h" --reverse --name-status | \
awk 'BEGIN { FS="|" }
/^[0-9]+\|/ { timestamp=$1; author=$2; hash=$3; next }
/^[AMD]\t/ {
    action=substr($0,1,1)
    file=substr($0,3)
    print timestamp "|" author "|" action "|" file
}' > "$CUSTOM_LOG_FILE"
CUSTOM_LOG_SIZE=$(get_file_size "$CUSTOM_LOG_FILE")
CUSTOM_LOG_LINES=$(wc -l < "$CUSTOM_LOG_FILE")
log_info "Custom log size: $(format_bytes $CUSTOM_LOG_SIZE) ($CUSTOM_LOG_LINES lines)"

# ==============================================================================
# Benchmark: Rource log parsing
# ==============================================================================

log_info ""
log_info "Benchmarking Rource log parsing..."

ROURCE_TIMES_FILE="${RUN_DIR}/rource_times.txt"
ROURCE_MEMORY_FILE="${RUN_DIR}/rource_memory.txt"

# Warmup
for i in $(seq 1 $WARMUP_RUNS); do
    mkdir -p /tmp/rource_warmup
    "$ROURCE_BIN" --headless --output /tmp/rource_warmup --stop-at-time 0.1 -s 0.001 --custom-log "$CUSTOM_LOG_FILE" 2>/dev/null || true
    rm -rf /tmp/rource_warmup
done

# Actual runs - we measure log loading time by using headless with just 1 frame
for i in $(seq 1 $BENCHMARK_RUNS); do
    log_info "  Run $i/$BENCHMARK_RUNS..."

    STATS_FILE="${RUN_DIR}/rource_run_${i}.stats"

    # Ensure output directory exists
    mkdir -p /tmp/rource_bench

    /usr/bin/time -v "$ROURCE_BIN" \
        --headless \
        --output /tmp/rource_bench \
        --stop-at-time 0.1 \
        -s 0.001 \
        --custom-log "$CUSTOM_LOG_FILE" \
        2>&1 | tee "$STATS_FILE" || true

    rm -rf /tmp/rource_bench

    # Extract timing - handle m:ss.ss format from /usr/bin/time
    WALL_TIME=$(grep "Elapsed (wall clock) time" "$STATS_FILE" | sed 's/.*: //' || echo "0:00.00")
    # Convert to seconds - time_to_seconds handles h:mm:ss and m:ss formats
    SECONDS=$(time_to_seconds "$WALL_TIME" 2>/dev/null || echo "0")
    echo "$SECONDS" >> "$ROURCE_TIMES_FILE"

    # Extract memory
    PEAK_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}' || echo "0")
    echo "$PEAK_MEM" >> "$ROURCE_MEMORY_FILE"
done

ROURCE_AVG_TIME=$(calculate_average "$ROURCE_TIMES_FILE")
ROURCE_STDDEV_TIME=$(calculate_stddev "$ROURCE_TIMES_FILE")
ROURCE_AVG_MEM=$(calculate_average "$ROURCE_MEMORY_FILE")
ROURCE_AVG_MEM_MB=$(echo "scale=2; $ROURCE_AVG_MEM / 1024" | bc)

log_success "Rource: ${ROURCE_AVG_TIME}s (±${ROURCE_STDDEV_TIME}s), ${ROURCE_AVG_MEM_MB} MB"

# ==============================================================================
# Benchmark: Gource log parsing
# ==============================================================================

log_info ""
log_info "Benchmarking Gource log parsing..."

GOURCE_TIMES_FILE="${RUN_DIR}/gource_times.txt"
GOURCE_MEMORY_FILE="${RUN_DIR}/gource_memory.txt"

# Generate Gource native log format
GOURCE_LOG_FILE="${RUN_DIR}/gource.log"
cd "$TEST_REPO"
gource --output-custom-log "$GOURCE_LOG_FILE" . 2>/dev/null
GOURCE_LOG_SIZE=$(get_file_size "$GOURCE_LOG_FILE")
log_info "Gource log size: $(format_bytes $GOURCE_LOG_SIZE)"

# Warmup
for i in $(seq 1 $WARMUP_RUNS); do
    timeout 30 xvfb-run -a -s "-screen 0 ${RESOLUTION_WIDTH}x${RESOLUTION_HEIGHT}x24" \
        gource --log-format custom "$GOURCE_LOG_FILE" --stop-at-end -s 0.001 --output-framerate 60 -o - 2>/dev/null | head -c 10000 > /dev/null || true
done

# Gource doesn't have true headless mode, so we use xvfb-run
# We'll measure time to parse the log by running with minimal output
for i in $(seq 1 $BENCHMARK_RUNS); do
    log_info "  Run $i/$BENCHMARK_RUNS..."

    STATS_FILE="${RUN_DIR}/gource_run_${i}.stats"

    # Run Gource via xvfb with output to null - this will measure parse + minimal render
    /usr/bin/time -v timeout 60 xvfb-run -a -s "-screen 0 ${RESOLUTION_WIDTH}x${RESOLUTION_HEIGHT}x24" \
        gource \
        --log-format custom \
        "$GOURCE_LOG_FILE" \
        --stop-at-end \
        -s 0.001 \
        --output-framerate 60 \
        -o /dev/null \
        --viewport ${RESOLUTION_WIDTH}x${RESOLUTION_HEIGHT} \
        2>&1 | tee "$STATS_FILE" || true

    # Extract timing - handle m:ss.ss format from /usr/bin/time
    WALL_TIME=$(grep "Elapsed (wall clock) time" "$STATS_FILE" | sed 's/.*: //' || echo "0:00.00")
    SECONDS=$(time_to_seconds "$WALL_TIME" 2>/dev/null || echo "0")
    echo "$SECONDS" >> "$GOURCE_TIMES_FILE"

    # Extract memory
    PEAK_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}' || echo "0")
    echo "$PEAK_MEM" >> "$GOURCE_MEMORY_FILE"
done

GOURCE_AVG_TIME=$(calculate_average "$GOURCE_TIMES_FILE")
GOURCE_STDDEV_TIME=$(calculate_stddev "$GOURCE_TIMES_FILE")
GOURCE_AVG_MEM=$(calculate_average "$GOURCE_MEMORY_FILE")
GOURCE_AVG_MEM_MB=$(echo "scale=2; $GOURCE_AVG_MEM / 1024" | bc)

log_success "Gource: ${GOURCE_AVG_TIME}s (±${GOURCE_STDDEV_TIME}s), ${GOURCE_AVG_MEM_MB} MB"

# ==============================================================================
# Results Summary
# ==============================================================================

print_header "Results: Log Parsing Performance"

echo "Repository: Home Assistant Core"
echo "Commits: $TOTAL_COMMITS"
echo "File Changes: $CUSTOM_LOG_LINES"
echo ""

printf "%-20s | %-20s | %-20s | %-15s\n" "Metric" "Rource" "Gource" "Diff"
printf "%-20s-+-%-20s-+-%-20s-+-%-15s\n" "--------------------" "--------------------" "--------------------" "---------------"

SPEEDUP=$(echo "scale=2; $GOURCE_AVG_TIME / $ROURCE_AVG_TIME" | bc 2>/dev/null || echo "N/A")
MEM_RATIO=$(echo "scale=2; $GOURCE_AVG_MEM / $ROURCE_AVG_MEM" | bc 2>/dev/null || echo "N/A")

printf "%-20s | %15.3f s    | %15.3f s    | %s\n" "Parse Time (avg)" "$ROURCE_AVG_TIME" "$GOURCE_AVG_TIME" "${SPEEDUP}x faster"
printf "%-20s | %15.3f s    | %15.3f s    |\n" "Parse Time (stddev)" "$ROURCE_STDDEV_TIME" "$GOURCE_STDDEV_TIME"
printf "%-20s | %15.2f MB   | %15.2f MB   | %s\n" "Peak Memory" "$ROURCE_AVG_MEM_MB" "$GOURCE_AVG_MEM_MB" "${MEM_RATIO}x less"

# Save results to JSON
cat > "${RUN_DIR}/results.json" << EOF
{
  "benchmark": "log_parsing",
  "timestamp": "$(date -Iseconds)",
  "repository": {
    "name": "home-assistant/core",
    "commits": $TOTAL_COMMITS,
    "file_changes": $CUSTOM_LOG_LINES
  },
  "rource": {
    "avg_time_seconds": $ROURCE_AVG_TIME,
    "stddev_time_seconds": $ROURCE_STDDEV_TIME,
    "avg_memory_kb": $ROURCE_AVG_MEM,
    "runs": $BENCHMARK_RUNS
  },
  "gource": {
    "avg_time_seconds": $GOURCE_AVG_TIME,
    "stddev_time_seconds": $GOURCE_STDDEV_TIME,
    "avg_memory_kb": $GOURCE_AVG_MEM,
    "runs": $BENCHMARK_RUNS
  },
  "comparison": {
    "speedup": "$SPEEDUP",
    "memory_ratio": "$MEM_RATIO"
  }
}
EOF

log_success "Results saved to ${RUN_DIR}/results.json"
