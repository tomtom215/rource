#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# Benchmark: Rendering Performance
# Measures frame generation and export speed

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

print_header "Benchmark: Rendering Performance"

# Check dependencies
if ! check_dependencies; then
    log_error "Missing dependencies, aborting"
    exit 1
fi

# Check for Xvfb (needed for Gource headless)
if ! command -v xvfb-run &> /dev/null; then
    log_error "xvfb-run not found. Install with: apt-get install xvfb"
    exit 1
fi

# Create output directory
RUN_DIR=$(create_run_dir "rendering")
log_info "Results will be saved to: $RUN_DIR"

# Parameters
RENDER_FRAMES=${FRAME_COUNT:-300}
RENDER_FPS=${FRAMERATE:-60}
RENDER_WIDTH=${RESOLUTION_WIDTH:-1280}
RENDER_HEIGHT=${RESOLUTION_HEIGHT:-720}
RENDER_SPD=${SECONDS_PER_DAY:-0.1}

log_info "Render parameters:"
log_info "  Resolution: ${RENDER_WIDTH}x${RENDER_HEIGHT}"
log_info "  Frames: ${RENDER_FRAMES}"
log_info "  FPS: ${RENDER_FPS}"
log_info "  Seconds per day: ${RENDER_SPD}"

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
log_info "Log entries: $LOG_LINES"

# ==============================================================================
# Benchmark: Rource PPM Export
# ==============================================================================

print_header "Rource: Headless PPM Export"

ROURCE_TIMES="${RUN_DIR}/rource_export_times.txt"
ROURCE_FPS_FILE="${RUN_DIR}/rource_fps.txt"
ROURCE_MEMORY="${RUN_DIR}/rource_memory.txt"

for run in $(seq 1 $BENCHMARK_RUNS); do
    log_info "Run $run/$BENCHMARK_RUNS..."

    OUTPUT_DIR="${RUN_DIR}/rource_frames_${run}"
    STATS_FILE="${RUN_DIR}/rource_stats_${run}.txt"

    rm -rf "$OUTPUT_DIR"
    mkdir -p "$OUTPUT_DIR"

    START_TIME=$(date +%s.%N)

    # Calculate stop time: FRAMES / FPS = seconds
    STOP_TIME=$(echo "scale=2; $RENDER_FRAMES / $RENDER_FPS" | bc)

    /usr/bin/time -v "$ROURCE_BIN" \
        --headless \
        --output "$OUTPUT_DIR" \
        --stop-at-time "$STOP_TIME" \
        --width "$RENDER_WIDTH" \
        --height "$RENDER_HEIGHT" \
        --seconds-per-day "$RENDER_SPD" \
        --framerate "$RENDER_FPS" \
        --no-bloom \
        --custom-log "$CUSTOM_LOG" \
        2>&1 | tee "$STATS_FILE"

    END_TIME=$(date +%s.%N)

    # Calculate metrics
    ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)
    echo "$ELAPSED" >> "$ROURCE_TIMES"

    ACTUAL_FRAMES=$(ls "$OUTPUT_DIR"/*.ppm 2>/dev/null | wc -l)
    FPS=$(echo "scale=2; $ACTUAL_FRAMES / $ELAPSED" | bc)
    echo "$FPS" >> "$ROURCE_FPS_FILE"

    PEAK_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}' || echo "0")
    echo "$PEAK_MEM" >> "$ROURCE_MEMORY"

    # Calculate output size
    OUTPUT_SIZE=$(du -sb "$OUTPUT_DIR" | cut -f1)

    log_info "  Frames: $ACTUAL_FRAMES"
    log_info "  Time: ${ELAPSED}s"
    log_info "  FPS: $FPS"
    log_info "  Peak memory: $(echo "scale=2; $PEAK_MEM / 1024" | bc) MB"
    log_info "  Output size: $(format_bytes $OUTPUT_SIZE)"

    # Keep only the last run's frames to save space
    if [[ $run -lt $BENCHMARK_RUNS ]]; then
        rm -rf "$OUTPUT_DIR"
    fi
done

ROURCE_AVG_TIME=$(calculate_average "$ROURCE_TIMES")
ROURCE_AVG_FPS=$(calculate_average "$ROURCE_FPS_FILE")
ROURCE_AVG_MEM=$(calculate_average "$ROURCE_MEMORY")

# ==============================================================================
# Benchmark: Gource PPM Export
# ==============================================================================

print_header "Gource: Headless PPM Export (via xvfb)"

GOURCE_TIMES="${RUN_DIR}/gource_export_times.txt"
GOURCE_FPS_FILE="${RUN_DIR}/gource_fps.txt"
GOURCE_MEMORY="${RUN_DIR}/gource_memory.txt"

for run in $(seq 1 $BENCHMARK_RUNS); do
    log_info "Run $run/$BENCHMARK_RUNS..."

    OUTPUT_DIR="${RUN_DIR}/gource_frames_${run}"
    OUTPUT_PPM="${OUTPUT_DIR}/output.ppm"
    STATS_FILE="${RUN_DIR}/gource_stats_${run}.txt"

    rm -rf "$OUTPUT_DIR"
    mkdir -p "$OUTPUT_DIR"

    START_TIME=$(date +%s.%N)

    # Gource outputs all frames to a single PPM stream
    # We use a subshell to split into individual frames
    /usr/bin/time -v xvfb-run -a -s "-screen 0 ${RENDER_WIDTH}x${RENDER_HEIGHT}x24" \
        gource \
        --log-format custom \
        "$GOURCE_LOG" \
        --stop-at-end \
        -s "$RENDER_SPD" \
        --output-framerate "$RENDER_FPS" \
        --viewport ${RENDER_WIDTH}x${RENDER_HEIGHT} \
        --disable-progress \
        --disable-input \
        --auto-skip-seconds 0.1 \
        --no-vsync \
        --disable-bloom \
        -o - 2>"$STATS_FILE" | \
    head -c $((RENDER_WIDTH * RENDER_HEIGHT * 3 * RENDER_FRAMES + 1000 * RENDER_FRAMES)) > "$OUTPUT_PPM" || true

    END_TIME=$(date +%s.%N)

    # Calculate metrics
    ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)
    echo "$ELAPSED" >> "$GOURCE_TIMES"

    # Count frames in PPM stream (each frame has a P6 header)
    ACTUAL_FRAMES=$(grep -c "^P6$" "$OUTPUT_PPM" 2>/dev/null || echo 0)
    if [[ $ACTUAL_FRAMES -eq 0 ]]; then
        # Fallback: estimate from file size
        FILE_SIZE=$(stat -c%s "$OUTPUT_PPM" 2>/dev/null || echo 0)
        FRAME_SIZE=$((RENDER_WIDTH * RENDER_HEIGHT * 3 + 50))
        ACTUAL_FRAMES=$((FILE_SIZE / FRAME_SIZE))
    fi

    FPS=$(echo "scale=2; $ACTUAL_FRAMES / $ELAPSED" | bc 2>/dev/null || echo "0")
    echo "$FPS" >> "$GOURCE_FPS_FILE"

    PEAK_MEM=$(grep "Maximum resident set size" "$STATS_FILE" | awk '{print $NF}' || echo "0")
    echo "$PEAK_MEM" >> "$GOURCE_MEMORY"

    OUTPUT_SIZE=$(get_file_size "$OUTPUT_PPM")

    log_info "  Frames: $ACTUAL_FRAMES"
    log_info "  Time: ${ELAPSED}s"
    log_info "  FPS: $FPS"
    log_info "  Peak memory: $(echo "scale=2; $PEAK_MEM / 1024" | bc) MB"
    log_info "  Output size: $(format_bytes $OUTPUT_SIZE)"

    # Cleanup to save space
    if [[ $run -lt $BENCHMARK_RUNS ]]; then
        rm -rf "$OUTPUT_DIR"
    fi
done

GOURCE_AVG_TIME=$(calculate_average "$GOURCE_TIMES")
GOURCE_AVG_FPS=$(calculate_average "$GOURCE_FPS_FILE")
GOURCE_AVG_MEM=$(calculate_average "$GOURCE_MEMORY")

# ==============================================================================
# Results Summary
# ==============================================================================

print_header "Results: Rendering Performance"

echo "Repository: Home Assistant Core"
echo "Resolution: ${RENDER_WIDTH}x${RENDER_HEIGHT}"
echo "Target Frames: ${RENDER_FRAMES}"
echo ""

printf "%-25s | %-18s | %-18s | %-15s\n" "Metric" "Rource" "Gource" "Comparison"
printf "%-25s-+-%-18s-+-%-18s-+-%-15s\n" "-------------------------" "------------------" "------------------" "---------------"

TIME_SPEEDUP=$(echo "scale=2; $GOURCE_AVG_TIME / $ROURCE_AVG_TIME" | bc 2>/dev/null || echo "N/A")
FPS_RATIO=$(echo "scale=2; $ROURCE_AVG_FPS / $GOURCE_AVG_FPS" | bc 2>/dev/null || echo "N/A")
MEM_RATIO=$(echo "scale=2; $GOURCE_AVG_MEM / $ROURCE_AVG_MEM" | bc 2>/dev/null || echo "N/A")

ROURCE_MEM_MB=$(echo "scale=2; $ROURCE_AVG_MEM / 1024" | bc)
GOURCE_MEM_MB=$(echo "scale=2; $GOURCE_AVG_MEM / 1024" | bc)

printf "%-25s | %14.2f s   | %14.2f s   | %sx faster\n" "Export Time (avg)" "$ROURCE_AVG_TIME" "$GOURCE_AVG_TIME" "$TIME_SPEEDUP"
printf "%-25s | %14.2f fps | %14.2f fps | %sx higher\n" "Render FPS (avg)" "$ROURCE_AVG_FPS" "$GOURCE_AVG_FPS" "$FPS_RATIO"
printf "%-25s | %14.2f MB  | %14.2f MB  | %sx less\n" "Peak Memory (avg)" "$ROURCE_MEM_MB" "$GOURCE_MEM_MB" "$MEM_RATIO"

# Save results to JSON
cat > "${RUN_DIR}/results.json" << EOF
{
  "benchmark": "rendering",
  "timestamp": "$(date -Iseconds)",
  "parameters": {
    "resolution": "${RENDER_WIDTH}x${RENDER_HEIGHT}",
    "target_frames": $RENDER_FRAMES,
    "framerate": $RENDER_FPS,
    "seconds_per_day": $RENDER_SPD,
    "runs": $BENCHMARK_RUNS
  },
  "repository": {
    "name": "home-assistant/core",
    "commits": $TOTAL_COMMITS,
    "log_entries": $LOG_LINES
  },
  "rource": {
    "avg_export_time_seconds": $ROURCE_AVG_TIME,
    "avg_render_fps": $ROURCE_AVG_FPS,
    "avg_memory_kb": $ROURCE_AVG_MEM
  },
  "gource": {
    "avg_export_time_seconds": $GOURCE_AVG_TIME,
    "avg_render_fps": $GOURCE_AVG_FPS,
    "avg_memory_kb": $GOURCE_AVG_MEM
  },
  "comparison": {
    "time_speedup": "$TIME_SPEEDUP",
    "fps_ratio": "$FPS_RATIO",
    "memory_ratio": "$MEM_RATIO"
  }
}
EOF

log_success "Results saved to ${RUN_DIR}/results.json"
