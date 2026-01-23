#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# Rource vs Gource: Complete Benchmark Suite
# Run all benchmarks and generate comprehensive report

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

# ==============================================================================
# Banner
# ==============================================================================

cat << 'EOF'
╔══════════════════════════════════════════════════════════════════╗
║                                                                  ║
║   ██████╗  ██████╗ ██╗   ██╗██████╗  ██████╗███████╗            ║
║   ██╔══██╗██╔═══██╗██║   ██║██╔══██╗██╔════╝██╔════╝            ║
║   ██████╔╝██║   ██║██║   ██║██████╔╝██║     █████╗              ║
║   ██╔══██╗██║   ██║██║   ██║██╔══██╗██║     ██╔══╝              ║
║   ██║  ██║╚██████╔╝╚██████╔╝██║  ██║╚██████╗███████╗            ║
║   ╚═╝  ╚═╝ ╚═════╝  ╚═════╝ ╚═╝  ╚═╝ ╚═════╝╚══════╝            ║
║                                                                  ║
║       Benchmark Suite: Rource vs Gource                          ║
║       Test Repository: Home Assistant Core                       ║
║                                                                  ║
╚══════════════════════════════════════════════════════════════════╝
EOF

# ==============================================================================
# Configuration
# ==============================================================================

TIMESTAMP=$(get_timestamp)
REPORT_DIR="${RESULTS_DIR}/complete_${TIMESTAMP}"
mkdir -p "$REPORT_DIR"

log_info "Benchmark run: $TIMESTAMP"
log_info "Report directory: $REPORT_DIR"
echo

# ==============================================================================
# Pre-flight Checks
# ==============================================================================

print_header "Pre-flight Checks"

log_info "Checking Rource..."
if [[ -x "$ROURCE_BIN" ]]; then
    ROURCE_VERSION=$("$ROURCE_BIN" --version 2>&1 | head -1 || echo "unknown")
    log_success "Rource: $ROURCE_VERSION"
else
    log_error "Rource binary not found at $ROURCE_BIN"
    exit 1
fi

log_info "Checking Gource..."
if command -v gource &> /dev/null; then
    GOURCE_VERSION=$(gource --help 2>&1 | head -1)
    log_success "Gource: $GOURCE_VERSION"
else
    log_error "Gource not found"
    exit 1
fi

log_info "Checking test repository..."
if [[ -d "$TEST_REPO/.git" ]]; then
    cd "$TEST_REPO"
    REPO_COMMITS=$(git rev-list --count HEAD)
    REPO_BRANCH=$(git branch --show-current)
    log_success "Repository: home-assistant/core"
    log_success "  Commits: $REPO_COMMITS"
    log_success "  Branch: $REPO_BRANCH"
else
    log_error "Test repository not found at $TEST_REPO"
    exit 1
fi

log_info "Checking xvfb..."
if command -v xvfb-run &> /dev/null; then
    log_success "xvfb-run: available"
else
    log_error "xvfb-run not found (needed for headless Gource)"
    exit 1
fi

# ==============================================================================
# System Information
# ==============================================================================

print_header "System Information"

CPU_INFO=$(lscpu | grep "Model name" | cut -d: -f2 | xargs || echo "unknown")
CPU_CORES=$(nproc)
MEMORY_TOTAL=$(free -h | grep Mem | awk '{print $2}')
OS_INFO=$(uname -srm)

echo "CPU: $CPU_INFO"
echo "Cores: $CPU_CORES"
echo "Memory: $MEMORY_TOTAL"
echo "OS: $OS_INFO"
echo

cat > "${REPORT_DIR}/system_info.json" << EOF
{
  "cpu": "$CPU_INFO",
  "cores": $CPU_CORES,
  "memory": "$MEMORY_TOTAL",
  "os": "$OS_INFO",
  "rource_version": "$ROURCE_VERSION",
  "gource_version": "$GOURCE_VERSION"
}
EOF

# ==============================================================================
# Run Benchmarks
# ==============================================================================

BENCHMARK_SCRIPTS=(
    "benchmark_log_parsing.sh"
    "benchmark_memory.sh"
    "benchmark_rendering.sh"
)

declare -A BENCHMARK_RESULTS

for script in "${BENCHMARK_SCRIPTS[@]}"; do
    SCRIPT_PATH="${SCRIPT_DIR}/${script}"
    SCRIPT_NAME="${script%.sh}"

    if [[ -x "$SCRIPT_PATH" ]]; then
        print_header "Running: $SCRIPT_NAME"

        LOG_FILE="${REPORT_DIR}/${SCRIPT_NAME}.log"

        if bash "$SCRIPT_PATH" 2>&1 | tee "$LOG_FILE"; then
            log_success "$SCRIPT_NAME completed"
            BENCHMARK_RESULTS["$SCRIPT_NAME"]="success"
        else
            log_error "$SCRIPT_NAME failed"
            BENCHMARK_RESULTS["$SCRIPT_NAME"]="failed"
        fi
    else
        log_warn "Script not found: $script"
        BENCHMARK_RESULTS["$SCRIPT_NAME"]="skipped"
    fi
done

# ==============================================================================
# Collect Results
# ==============================================================================

print_header "Collecting Results"

# Find the most recent result directories
LOG_PARSING_DIR=$(ls -td "${RESULTS_DIR}"/log_parsing_* 2>/dev/null | head -1)
MEMORY_DIR=$(ls -td "${RESULTS_DIR}"/memory_* 2>/dev/null | head -1)
RENDERING_DIR=$(ls -td "${RESULTS_DIR}"/rendering_* 2>/dev/null | head -1)

# Copy results to report directory
if [[ -d "$LOG_PARSING_DIR" ]]; then
    cp "${LOG_PARSING_DIR}/results.json" "${REPORT_DIR}/log_parsing_results.json" 2>/dev/null || true
fi
if [[ -d "$MEMORY_DIR" ]]; then
    cp "${MEMORY_DIR}/results.json" "${REPORT_DIR}/memory_results.json" 2>/dev/null || true
fi
if [[ -d "$RENDERING_DIR" ]]; then
    cp "${RENDERING_DIR}/results.json" "${REPORT_DIR}/rendering_results.json" 2>/dev/null || true
fi

# ==============================================================================
# Generate Summary Report
# ==============================================================================

print_header "Generating Summary Report"

REPORT_FILE="${REPORT_DIR}/BENCHMARK_REPORT.md"

cat > "$REPORT_FILE" << 'EOF'
# Rource vs Gource Benchmark Report

## Overview

This report compares the performance of **Rource** (Rust implementation) against **Gource** (original C++ implementation) using the Home Assistant Core repository as the test case.

### Test Repository
- **Repository**: [home-assistant/core](https://github.com/home-assistant/core)
EOF

echo "- **Commits**: $REPO_COMMITS" >> "$REPORT_FILE"
echo "- **Benchmark Date**: $(date '+%Y-%m-%d %H:%M:%S')" >> "$REPORT_FILE"

cat >> "$REPORT_FILE" << 'EOF'

### System Information
EOF

echo "- **CPU**: $CPU_INFO" >> "$REPORT_FILE"
echo "- **Cores**: $CPU_CORES" >> "$REPORT_FILE"
echo "- **Memory**: $MEMORY_TOTAL" >> "$REPORT_FILE"
echo "- **OS**: $OS_INFO" >> "$REPORT_FILE"
echo "" >> "$REPORT_FILE"

# Add version info
echo "### Tool Versions" >> "$REPORT_FILE"
echo "- **Rource**: $ROURCE_VERSION" >> "$REPORT_FILE"
echo "- **Gource**: $GOURCE_VERSION" >> "$REPORT_FILE"
echo "" >> "$REPORT_FILE"

# Parse and add log parsing results
if [[ -f "${REPORT_DIR}/log_parsing_results.json" ]]; then
    cat >> "$REPORT_FILE" << 'EOF'
## Log Parsing Performance

Time to parse and load the git history:

| Metric | Rource | Gource | Comparison |
|--------|--------|--------|------------|
EOF

    # Extract values using basic tools since jq might not be available
    ROURCE_TIME=$(grep -o '"avg_time_seconds": [0-9.]*' "${REPORT_DIR}/log_parsing_results.json" | head -1 | cut -d: -f2 | tr -d ' ')
    GOURCE_TIME=$(grep -o '"avg_time_seconds": [0-9.]*' "${REPORT_DIR}/log_parsing_results.json" | tail -1 | cut -d: -f2 | tr -d ' ')
    ROURCE_MEM=$(grep -o '"avg_memory_kb": [0-9]*' "${REPORT_DIR}/log_parsing_results.json" | head -1 | cut -d: -f2 | tr -d ' ')
    GOURCE_MEM=$(grep -o '"avg_memory_kb": [0-9]*' "${REPORT_DIR}/log_parsing_results.json" | tail -1 | cut -d: -f2 | tr -d ' ')

    SPEEDUP=$(grep -o '"speedup": "[^"]*"' "${REPORT_DIR}/log_parsing_results.json" | cut -d'"' -f4)

    ROURCE_MEM_MB=$(echo "scale=2; $ROURCE_MEM / 1024" | bc 2>/dev/null || echo "N/A")
    GOURCE_MEM_MB=$(echo "scale=2; $GOURCE_MEM / 1024" | bc 2>/dev/null || echo "N/A")

    echo "| Parse Time | ${ROURCE_TIME}s | ${GOURCE_TIME}s | ${SPEEDUP}x faster |" >> "$REPORT_FILE"
    echo "| Memory | ${ROURCE_MEM_MB} MB | ${GOURCE_MEM_MB} MB | - |" >> "$REPORT_FILE"
    echo "" >> "$REPORT_FILE"
fi

# Parse and add rendering results
if [[ -f "${REPORT_DIR}/rendering_results.json" ]]; then
    cat >> "$REPORT_FILE" << 'EOF'
## Rendering Performance

Headless PPM frame export performance:

| Metric | Rource | Gource | Comparison |
|--------|--------|--------|------------|
EOF

    ROURCE_EXPORT=$(grep -o '"avg_export_time_seconds": [0-9.]*' "${REPORT_DIR}/rendering_results.json" | head -1 | cut -d: -f2 | tr -d ' ')
    GOURCE_EXPORT=$(grep -o '"avg_export_time_seconds": [0-9.]*' "${REPORT_DIR}/rendering_results.json" | tail -1 | cut -d: -f2 | tr -d ' ')
    ROURCE_FPS=$(grep -o '"avg_render_fps": [0-9.]*' "${REPORT_DIR}/rendering_results.json" | head -1 | cut -d: -f2 | tr -d ' ')
    GOURCE_FPS=$(grep -o '"avg_render_fps": [0-9.]*' "${REPORT_DIR}/rendering_results.json" | tail -1 | cut -d: -f2 | tr -d ' ')

    TIME_SPEEDUP=$(grep -o '"time_speedup": "[^"]*"' "${REPORT_DIR}/rendering_results.json" | cut -d'"' -f4)
    FPS_RATIO=$(grep -o '"fps_ratio": "[^"]*"' "${REPORT_DIR}/rendering_results.json" | cut -d'"' -f4)

    echo "| Export Time | ${ROURCE_EXPORT}s | ${GOURCE_EXPORT}s | ${TIME_SPEEDUP}x faster |" >> "$REPORT_FILE"
    echo "| Render FPS | ${ROURCE_FPS} | ${GOURCE_FPS} | ${FPS_RATIO}x higher |" >> "$REPORT_FILE"
    echo "" >> "$REPORT_FILE"
fi

# Parse and add memory results
if [[ -f "${REPORT_DIR}/memory_results.json" ]]; then
    cat >> "$REPORT_FILE" << 'EOF'
## Memory Usage

Memory consumption analysis:

| Test | Rource | Gource |
|------|--------|--------|
EOF

    ROURCE_LOAD_MEM=$(grep -o '"rource_mb": [0-9.]*' "${REPORT_DIR}/memory_results.json" | head -1 | cut -d: -f2 | tr -d ' ')
    GOURCE_LOAD_MEM=$(grep -o '"gource_mb": [0-9.]*' "${REPORT_DIR}/memory_results.json" | head -1 | cut -d: -f2 | tr -d ' ')

    echo "| Initial Load | ${ROURCE_LOAD_MEM} MB | ${GOURCE_LOAD_MEM} MB |" >> "$REPORT_FILE"
    echo "" >> "$REPORT_FILE"
fi

# Add methodology
cat >> "$REPORT_FILE" << 'EOF'
## Methodology

### Test Parameters
- **Benchmark Runs**: 3 (average reported)
- **Warmup Runs**: 1 (discarded)
- **Resolution**: 1280x720
- **Frame Count**: 300 frames
- **Framerate**: 60 FPS

### Measurement Tools
- `/usr/bin/time -v` for timing and memory measurement
- Peak RSS (Maximum Resident Set Size) for memory
- Wall clock time for duration

### Notes
- Rource uses a pure software renderer (CPU-only)
- Gource uses OpenGL (GPU-accelerated when available)
- Gource tests run via `xvfb-run` for headless operation
- Both tools configured with bloom disabled for fair comparison

## Conclusion

EOF

echo "Benchmark completed at $(date '+%Y-%m-%d %H:%M:%S')" >> "$REPORT_FILE"

log_success "Report generated: $REPORT_FILE"

# ==============================================================================
# Final Summary
# ==============================================================================

print_header "Benchmark Complete"

echo "Results directory: $REPORT_DIR"
echo ""
echo "Generated files:"
ls -la "$REPORT_DIR"
echo ""

log_success "All benchmarks completed!"
echo ""
echo "View the full report:"
echo "  cat ${REPORT_FILE}"
