#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# Benchmark: Memory Usage Analysis
# Detailed memory profiling for both tools

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

print_header "Benchmark: Memory Usage Analysis"

# Check dependencies
if ! check_dependencies; then
    log_error "Missing dependencies, aborting"
    exit 1
fi

# Create output directory
RUN_DIR=$(create_run_dir "memory")
log_info "Results will be saved to: $RUN_DIR"

# Generate logs
cd "$TEST_REPO"
TOTAL_COMMITS=$(git rev-list --count HEAD)

# Custom log for Rource
CUSTOM_LOG="${RUN_DIR}/custom.log"
log_info "Generating Rource-format log..."
git log --pretty=format:"%at|%an|%h" --reverse --name-status | \
awk 'BEGIN { FS="|" }
/^[0-9]+\|/ { timestamp=$1; author=$2; hash=$3; next }
/^[AMD]\t/ {
    action=substr($0,1,1)
    file=substr($0,3)
    print timestamp "|" author "|" action "|" file
}' > "$CUSTOM_LOG"

# Gource log
GOURCE_LOG="${RUN_DIR}/gource.log"
log_info "Generating Gource-format log..."
gource --output-custom-log "$GOURCE_LOG" . 2>/dev/null

LOG_LINES=$(wc -l < "$CUSTOM_LOG")
log_info "Total commits: $TOTAL_COMMITS"
log_info "Log entries: $LOG_LINES"

# ==============================================================================
# Test 1: Memory at load time (initial parse)
# ==============================================================================

print_header "Test 1: Memory at Initial Load"

# Rource
log_info "Testing Rource initial load memory..."
ROURCE_LOAD_STATS="${RUN_DIR}/rource_load_stats.txt"

/usr/bin/time -v "$ROURCE_BIN" \
    --headless \
    --output /tmp/rource_mem_test \
    --stop-at-time 0.1 \
    -s 0.001 \
    --custom-log "$CUSTOM_LOG" \
    2>&1 | tee "$ROURCE_LOAD_STATS" || true
rm -rf /tmp/rource_mem_test

ROURCE_LOAD_MEM=$(grep "Maximum resident set size" "$ROURCE_LOAD_STATS" | awk '{print $NF}')
ROURCE_LOAD_MEM_MB=$(echo "scale=2; $ROURCE_LOAD_MEM / 1024" | bc)

log_success "Rource initial load: ${ROURCE_LOAD_MEM_MB} MB"

# Gource
log_info "Testing Gource initial load memory..."
GOURCE_LOAD_STATS="${RUN_DIR}/gource_load_stats.txt"

/usr/bin/time -v xvfb-run -a -s "-screen 0 640x480x24" \
    gource \
    --log-format custom \
    "$GOURCE_LOG" \
    --stop-at-end \
    -s 0.001 \
    --output-framerate 60 \
    --viewport 640x480 \
    -o /dev/null \
    2>&1 | tee "$GOURCE_LOAD_STATS" || true

GOURCE_LOAD_MEM=$(grep "Maximum resident set size" "$GOURCE_LOAD_STATS" | awk '{print $NF}' || echo "0")
GOURCE_LOAD_MEM_MB=$(echo "scale=2; $GOURCE_LOAD_MEM / 1024" | bc)

log_success "Gource initial load: ${GOURCE_LOAD_MEM_MB} MB"

# ==============================================================================
# Test 2: Memory during rendering (different resolutions)
# ==============================================================================

print_header "Test 2: Memory vs Resolution"

declare -a RESOLUTIONS=("640x480" "1280x720" "1920x1080" "2560x1440")

ROURCE_RES_MEMS=()
GOURCE_RES_MEMS=()

for res in "${RESOLUTIONS[@]}"; do
    WIDTH=$(echo "$res" | cut -d'x' -f1)
    HEIGHT=$(echo "$res" | cut -d'x' -f2)

    log_info "Testing ${res}..."

    # Rource
    STATS_FILE="${RUN_DIR}/rource_${res}.stats"
    /usr/bin/time -v "$ROURCE_BIN" \
        --headless \
        --output /tmp/rource_res_test \
        --stop-at-time 0.5 \
        --width "$WIDTH" \
        --height "$HEIGHT" \
        -s 0.001 \
        --custom-log "$CUSTOM_LOG" \
        2>&1 | tee "$STATS_FILE" || true
    rm -rf /tmp/rource_res_test

    ROURCE_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}')
    ROURCE_MEM_MB=$(echo "scale=2; $ROURCE_MEM / 1024" | bc)
    ROURCE_RES_MEMS+=("$ROURCE_MEM_MB")

    # Gource
    STATS_FILE="${RUN_DIR}/gource_${res}.stats"
    /usr/bin/time -v xvfb-run -a -s "-screen 0 ${WIDTH}x${HEIGHT}x24" \
        timeout 60 gource \
        --log-format custom \
        "$GOURCE_LOG" \
        --stop-at-end \
        -s 0.05 \
        --output-framerate 30 \
        --viewport ${WIDTH}x${HEIGHT} \
        -o /dev/null \
        2>&1 | tee "$STATS_FILE" || true

    GOURCE_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}' || echo "0")
    GOURCE_MEM_MB=$(echo "scale=2; $GOURCE_MEM / 1024" | bc)
    GOURCE_RES_MEMS+=("$GOURCE_MEM_MB")

    log_info "  Rource: ${ROURCE_MEM_MB} MB | Gource: ${GOURCE_MEM_MB} MB"
done

# ==============================================================================
# Test 3: Memory growth over time (frame count)
# ==============================================================================

print_header "Test 3: Memory vs Frame Count"

declare -a FRAME_COUNTS=(10 50 100 200 500)

ROURCE_FRAME_MEMS=()
GOURCE_FRAME_MEMS=()

for frames in "${FRAME_COUNTS[@]}"; do
    log_info "Testing $frames frames..."

    # Rource - convert frames to time (frames/60fps)
    STOP_TIME=$(echo "scale=2; $frames / 60" | bc)
    STATS_FILE="${RUN_DIR}/rource_frames_${frames}.stats"
    /usr/bin/time -v "$ROURCE_BIN" \
        --headless \
        --output /tmp/rource_frame_test \
        --stop-at-time "$STOP_TIME" \
        --width 1280 \
        --height 720 \
        -s 0.001 \
        --custom-log "$CUSTOM_LOG" \
        2>&1 | tee "$STATS_FILE" || true
    rm -rf /tmp/rource_frame_test

    ROURCE_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}')
    ROURCE_MEM_MB=$(echo "scale=2; $ROURCE_MEM / 1024" | bc)
    ROURCE_FRAME_MEMS+=("$ROURCE_MEM_MB")

    # Gource (estimate frame count via time)
    # At s=0.1 and 60fps, ~6 seconds = 360 frames
    SPD=$(echo "scale=4; $frames / 60 / 10" | bc)  # rough approximation
    if (( $(echo "$SPD < 0.01" | bc -l) )); then SPD=0.01; fi

    STATS_FILE="${RUN_DIR}/gource_frames_${frames}.stats"
    /usr/bin/time -v xvfb-run -a -s "-screen 0 1280x720x24" \
        timeout 120 gource \
        --log-format custom \
        "$GOURCE_LOG" \
        --stop-at-end \
        -s "$SPD" \
        --output-framerate 60 \
        --viewport 1280x720 \
        -o /dev/null \
        2>&1 | tee "$STATS_FILE" || true

    GOURCE_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}' || echo "0")
    GOURCE_MEM_MB=$(echo "scale=2; $GOURCE_MEM / 1024" | bc)
    GOURCE_FRAME_MEMS+=("$GOURCE_MEM_MB")

    log_info "  Rource: ${ROURCE_MEM_MB} MB | Gource: ${GOURCE_MEM_MB} MB"
done

# ==============================================================================
# Results Summary
# ==============================================================================

print_header "Memory Usage Summary"

echo "Repository: Home Assistant Core ($TOTAL_COMMITS commits)"
echo ""

echo "=== Initial Load Memory ==="
printf "%-15s | %15s | %15s | %15s\n" "Tool" "Memory (MB)" "Per Commit (KB)" "Per Entry (B)"
printf "%-15s-+-%-15s-+-%-15s-+-%-15s\n" "---------------" "---------------" "---------------" "---------------"

ROURCE_PER_COMMIT=$(echo "scale=2; $ROURCE_LOAD_MEM_MB * 1024 / $TOTAL_COMMITS" | bc)
ROURCE_PER_ENTRY=$(echo "scale=2; $ROURCE_LOAD_MEM_MB * 1024 * 1024 / $LOG_LINES" | bc)
GOURCE_PER_COMMIT=$(echo "scale=2; $GOURCE_LOAD_MEM_MB * 1024 / $TOTAL_COMMITS" | bc)
GOURCE_PER_ENTRY=$(echo "scale=2; $GOURCE_LOAD_MEM_MB * 1024 * 1024 / $LOG_LINES" | bc)

printf "%-15s | %15s | %15s | %15s\n" "Rource" "$ROURCE_LOAD_MEM_MB" "$ROURCE_PER_COMMIT" "$ROURCE_PER_ENTRY"
printf "%-15s | %15s | %15s | %15s\n" "Gource" "$GOURCE_LOAD_MEM_MB" "$GOURCE_PER_COMMIT" "$GOURCE_PER_ENTRY"

echo ""
echo "=== Memory by Resolution ==="
printf "%-15s | %15s | %15s\n" "Resolution" "Rource (MB)" "Gource (MB)"
printf "%-15s-+-%-15s-+-%-15s\n" "---------------" "---------------" "---------------"

for i in "${!RESOLUTIONS[@]}"; do
    printf "%-15s | %15s | %15s\n" "${RESOLUTIONS[$i]}" "${ROURCE_RES_MEMS[$i]}" "${GOURCE_RES_MEMS[$i]}"
done

echo ""
echo "=== Memory by Frame Count ==="
printf "%-15s | %15s | %15s\n" "Frames" "Rource (MB)" "Gource (MB)"
printf "%-15s-+-%-15s-+-%-15s\n" "---------------" "---------------" "---------------"

for i in "${!FRAME_COUNTS[@]}"; do
    printf "%-15s | %15s | %15s\n" "${FRAME_COUNTS[$i]}" "${ROURCE_FRAME_MEMS[$i]}" "${GOURCE_FRAME_MEMS[$i]}"
done

# Save results to JSON
cat > "${RUN_DIR}/results.json" << EOF
{
  "benchmark": "memory",
  "timestamp": "$(date -Iseconds)",
  "repository": {
    "name": "home-assistant/core",
    "commits": $TOTAL_COMMITS,
    "log_entries": $LOG_LINES
  },
  "initial_load": {
    "rource_mb": $ROURCE_LOAD_MEM_MB,
    "gource_mb": $GOURCE_LOAD_MEM_MB,
    "rource_per_commit_kb": $ROURCE_PER_COMMIT,
    "gource_per_commit_kb": $GOURCE_PER_COMMIT
  },
  "by_resolution": {
$(for i in "${!RESOLUTIONS[@]}"; do
    echo "    \"${RESOLUTIONS[$i]}\": { \"rource\": ${ROURCE_RES_MEMS[$i]}, \"gource\": ${GOURCE_RES_MEMS[$i]} }$(if [[ $i -lt $((${#RESOLUTIONS[@]}-1)) ]]; then echo ","; fi)"
done)
  },
  "by_frames": {
$(for i in "${!FRAME_COUNTS[@]}"; do
    echo "    \"${FRAME_COUNTS[$i]}\": { \"rource\": ${ROURCE_FRAME_MEMS[$i]}, \"gource\": ${GOURCE_FRAME_MEMS[$i]} }$(if [[ $i -lt $((${#FRAME_COUNTS[@]}-1)) ]]; then echo ","; fi)"
done)
  }
}
EOF

log_success "Results saved to ${RUN_DIR}/results.json"
