#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# Benchmark: Binary Size and Dependencies Comparison
# Compares the size and dependency footprint of both tools

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

print_header "Benchmark: Binary Size and Dependencies"

# Create output directory
RUN_DIR=$(create_run_dir "binary")
log_info "Results will be saved to: $RUN_DIR"

# ==============================================================================
# Binary Sizes
# ==============================================================================

print_header "Binary Sizes"

ROURCE_SIZE=$(get_file_size "$ROURCE_BIN")
GOURCE_SIZE=$(get_file_size "$GOURCE_BIN")

echo "Rource binary: $(format_bytes $ROURCE_SIZE)"
echo "Gource binary: $(format_bytes $GOURCE_SIZE)"
echo ""

# Check stripped sizes
ROURCE_STRIPPED="/tmp/rource_stripped"
GOURCE_STRIPPED="/tmp/gource_stripped"

cp "$ROURCE_BIN" "$ROURCE_STRIPPED"
cp "$GOURCE_BIN" "$GOURCE_STRIPPED"

strip "$ROURCE_STRIPPED" 2>/dev/null || true
strip "$GOURCE_STRIPPED" 2>/dev/null || true

ROURCE_STRIPPED_SIZE=$(get_file_size "$ROURCE_STRIPPED")
GOURCE_STRIPPED_SIZE=$(get_file_size "$GOURCE_STRIPPED")

echo "Rource (stripped): $(format_bytes $ROURCE_STRIPPED_SIZE)"
echo "Gource (stripped): $(format_bytes $GOURCE_STRIPPED_SIZE)"

rm -f "$ROURCE_STRIPPED" "$GOURCE_STRIPPED"

# ==============================================================================
# Shared Library Dependencies
# ==============================================================================

print_header "Library Dependencies"

echo "=== Rource Dependencies ===" > "${RUN_DIR}/rource_deps.txt"
ldd "$ROURCE_BIN" >> "${RUN_DIR}/rource_deps.txt" 2>/dev/null || echo "Static binary" >> "${RUN_DIR}/rource_deps.txt"

echo "=== Gource Dependencies ===" > "${RUN_DIR}/gource_deps.txt"
ldd "$GOURCE_BIN" >> "${RUN_DIR}/gource_deps.txt" 2>/dev/null || echo "Static binary" >> "${RUN_DIR}/gource_deps.txt"

ROURCE_DEP_COUNT=$(ldd "$ROURCE_BIN" 2>/dev/null | wc -l || echo "0")
GOURCE_DEP_COUNT=$(ldd "$GOURCE_BIN" 2>/dev/null | wc -l || echo "0")

echo "Rource shared libraries: $ROURCE_DEP_COUNT"
cat "${RUN_DIR}/rource_deps.txt" | grep "=>" | head -20
echo ""
echo "Gource shared libraries: $GOURCE_DEP_COUNT"
cat "${RUN_DIR}/gource_deps.txt" | grep "=>" | head -20
echo ""

# ==============================================================================
# Resource Files
# ==============================================================================

print_header "Resource Files"

# Gource resource directory
GOURCE_RESOURCE_DIR="/usr/local/share/gource"
if [[ -d "$GOURCE_RESOURCE_DIR" ]]; then
    GOURCE_RESOURCE_SIZE=$(du -sb "$GOURCE_RESOURCE_DIR" | cut -f1)
    echo "Gource resource directory: $(format_bytes $GOURCE_RESOURCE_SIZE)"
    ls -la "$GOURCE_RESOURCE_DIR" 2>/dev/null || true
else
    GOURCE_RESOURCE_SIZE=0
    echo "Gource resource directory: not found"
fi

# Rource doesn't need external resources (fonts embedded)
ROURCE_RESOURCE_SIZE=0
echo "Rource resource directory: N/A (fonts embedded)"

# ==============================================================================
# Total Footprint
# ==============================================================================

print_header "Total Disk Footprint"

ROURCE_TOTAL=$((ROURCE_SIZE + ROURCE_RESOURCE_SIZE))
GOURCE_TOTAL=$((GOURCE_SIZE + GOURCE_RESOURCE_SIZE))

echo "Rource total: $(format_bytes $ROURCE_TOTAL)"
echo "  Binary: $(format_bytes $ROURCE_SIZE)"
echo "  Resources: $(format_bytes $ROURCE_RESOURCE_SIZE)"
echo ""
echo "Gource total: $(format_bytes $GOURCE_TOTAL)"
echo "  Binary: $(format_bytes $GOURCE_SIZE)"
echo "  Resources: $(format_bytes $GOURCE_RESOURCE_SIZE)"

# ==============================================================================
# WASM Build (if available)
# ==============================================================================

print_header "WASM Build Sizes (Rource only)"

WASM_DIR="${BENCHMARK_DIR}/../rource-wasm/pkg"
if [[ -d "$WASM_DIR" ]]; then
    WASM_BG_FILE=$(ls "${WASM_DIR}"/*.wasm 2>/dev/null | head -1)
    if [[ -f "$WASM_BG_FILE" ]]; then
        WASM_SIZE=$(get_file_size "$WASM_BG_FILE")
        echo "WASM file: $(format_bytes $WASM_SIZE)"

        # Check gzipped size
        WASM_GZ_SIZE=$(gzip -c "$WASM_BG_FILE" | wc -c)
        echo "WASM (gzipped): $(format_bytes $WASM_GZ_SIZE)"
    fi

    JS_FILE=$(ls "${WASM_DIR}"/*.js 2>/dev/null | head -1)
    if [[ -f "$JS_FILE" ]]; then
        JS_SIZE=$(get_file_size "$JS_FILE")
        echo "JS bindings: $(format_bytes $JS_SIZE)"
    fi
else
    echo "WASM build not found. Build with: wasm-pack build rource-wasm"
    WASM_SIZE=0
    WASM_GZ_SIZE=0
fi

# ==============================================================================
# Results Summary
# ==============================================================================

print_header "Summary: Binary Comparison"

printf "%-30s | %-15s | %-15s\n" "Metric" "Rource" "Gource"
printf "%-30s-+-%-15s-+-%-15s\n" "------------------------------" "---------------" "---------------"
printf "%-30s | %15s | %15s\n" "Binary Size" "$(format_bytes $ROURCE_SIZE)" "$(format_bytes $GOURCE_SIZE)"
printf "%-30s | %15s | %15s\n" "Binary Size (stripped)" "$(format_bytes $ROURCE_STRIPPED_SIZE)" "$(format_bytes $GOURCE_STRIPPED_SIZE)"
printf "%-30s | %15s | %15s\n" "Shared Libraries" "$ROURCE_DEP_COUNT" "$GOURCE_DEP_COUNT"
printf "%-30s | %15s | %15s\n" "Resource Files" "$(format_bytes $ROURCE_RESOURCE_SIZE)" "$(format_bytes $GOURCE_RESOURCE_SIZE)"
printf "%-30s | %15s | %15s\n" "Total Footprint" "$(format_bytes $ROURCE_TOTAL)" "$(format_bytes $GOURCE_TOTAL)"
echo ""
printf "%-30s | %15s | %15s\n" "WASM Support" "Yes" "No"
if [[ ${WASM_GZ_SIZE:-0} -gt 0 ]]; then
    printf "%-30s | %15s | %15s\n" "WASM Size (gzip)" "$(format_bytes $WASM_GZ_SIZE)" "N/A"
fi

# Save results
cat > "${RUN_DIR}/results.json" << EOF
{
  "benchmark": "binary",
  "timestamp": "$(date -Iseconds)",
  "rource": {
    "binary_size": $ROURCE_SIZE,
    "binary_stripped": $ROURCE_STRIPPED_SIZE,
    "shared_libs": $ROURCE_DEP_COUNT,
    "resource_size": $ROURCE_RESOURCE_SIZE,
    "total_footprint": $ROURCE_TOTAL,
    "wasm_size": ${WASM_SIZE:-0},
    "wasm_gzip": ${WASM_GZ_SIZE:-0}
  },
  "gource": {
    "binary_size": $GOURCE_SIZE,
    "binary_stripped": $GOURCE_STRIPPED_SIZE,
    "shared_libs": $GOURCE_DEP_COUNT,
    "resource_size": $GOURCE_RESOURCE_SIZE,
    "total_footprint": $GOURCE_TOTAL
  }
}
EOF

log_success "Results saved to ${RUN_DIR}/results.json"
