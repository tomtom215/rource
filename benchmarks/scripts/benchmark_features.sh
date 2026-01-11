#!/bin/bash
# Benchmark: Feature Parity Comparison
# Documents which features are supported by Rource vs Gource

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/common.sh"

print_header "Feature Parity Comparison: Rource vs Gource"

# Create output directory
RUN_DIR=$(create_run_dir "features")
log_info "Results will be saved to: $RUN_DIR"

# ==============================================================================
# Extract CLI Options
# ==============================================================================

print_header "CLI Options Analysis"

# Get Rource help
"$ROURCE_BIN" --help > "${RUN_DIR}/rource_help.txt" 2>&1 || true

# Get Gource help
gource --help > "${RUN_DIR}/gource_help.txt" 2>&1 || true

# Count options
ROURCE_OPTIONS=$(grep -c "^\s*-" "${RUN_DIR}/rource_help.txt" 2>/dev/null || echo "0")
GOURCE_OPTIONS=$(grep -c "^\s*-" "${RUN_DIR}/gource_help.txt" 2>/dev/null || echo "0")

echo "Rource CLI options: $ROURCE_OPTIONS"
echo "Gource CLI options: $GOURCE_OPTIONS"
echo ""

# ==============================================================================
# Feature Matrix
# ==============================================================================

print_header "Feature Matrix"

# Define feature categories and check support
declare -A FEATURES

check_feature() {
    local feature="$1"
    local rource_pattern="$2"
    local gource_pattern="$3"

    local rource_support="No"
    local gource_support="No"

    if grep -qi "$rource_pattern" "${RUN_DIR}/rource_help.txt" 2>/dev/null; then
        rource_support="Yes"
    fi

    if grep -qi "$gource_pattern" "${RUN_DIR}/gource_help.txt" 2>/dev/null; then
        gource_support="Yes"
    fi

    printf "| %-35s | %-8s | %-8s |\n" "$feature" "$rource_support" "$gource_support"
}

echo "### Input/Output Features"
printf "| %-35s | %-8s | %-8s |\n" "Feature" "Rource" "Gource"
printf "| %-35s | %-8s | %-8s |\n" "-----------------------------------" "--------" "--------"
check_feature "Git log parsing" "log" "log"
check_feature "Custom log format" "log" "custom"
check_feature "SVN log support" "svn" "svn"
check_feature "CVS log support" "cvs" "cvs"
check_feature "Mercurial log support" "hg" "hg"
check_feature "Bazaar log support" "bzr" "bzr"
check_feature "PPM frame output" "output" "output-ppm"
check_feature "Headless mode" "headless" "output-ppm"
echo ""

echo "### Display Features"
printf "| %-35s | %-8s | %-8s |\n" "Feature" "Rource" "Gource"
printf "| %-35s | %-8s | %-8s |\n" "-----------------------------------" "--------" "--------"
check_feature "Fullscreen mode" "fullscreen" "fullscreen"
check_feature "Window mode" "width\|height" "viewport"
check_feature "Multi-monitor support" "screen" "screen"
check_feature "Title display" "title" "title"
check_feature "Date display" "date" "date"
check_feature "User labels" "user" "user"
check_feature "File labels" "file" "filename"
check_feature "Directory labels" "dir" "dir"
check_feature "Bloom effect" "bloom" "bloom"
check_feature "Shadows" "shadow" "shadow"
check_feature "Elasticity" "elasticity" "elasticity"
echo ""

echo "### Camera Features"
printf "| %-35s | %-8s | %-8s |\n" "Feature" "Rource" "Gource"
printf "| %-35s | %-8s | %-8s |\n" "-----------------------------------" "--------" "--------"
check_feature "Auto camera mode" "camera" "camera"
check_feature "Camera padding" "padding" "padding"
check_feature "Follow users" "follow" "follow"
check_feature "Highlight users" "highlight" "highlight"
echo ""

echo "### Filter Features"
printf "| %-35s | %-8s | %-8s |\n" "Feature" "Rource" "Gource"
printf "| %-35s | %-8s | %-8s |\n" "-----------------------------------" "--------" "--------"
check_feature "File filter (regex)" "file-filter" "file-filter"
check_feature "File include (regex)" "file-include" "file-include"
check_feature "User filter (regex)" "user-filter" "user-filter"
check_feature "User include (regex)" "user-include" "user-include"
check_feature "Hide files" "hide.*file" "hide.*file"
check_feature "Hide users" "hide.*user" "hide.*user"
check_feature "Hide dirnames" "hide.*dir" "hide.*dirname"
check_feature "Hide filenames" "hide.*file" "hide.*filename"
check_feature "Hide root" "hide.*root" "hide.*root"
echo ""

echo "### Playback Features"
printf "| %-35s | %-8s | %-8s |\n" "Feature" "Rource" "Gource"
printf "| %-35s | %-8s | %-8s |\n" "-----------------------------------" "--------" "--------"
check_feature "Seconds per day" "seconds-per-day" "seconds-per-day"
check_feature "Auto skip seconds" "auto-skip" "auto-skip"
check_feature "Start date" "start-date" "start-date"
check_feature "Stop date" "stop-date" "stop-date"
check_feature "Start position" "start-position" "start-position"
check_feature "Stop position" "stop-position" "stop-position"
check_feature "Stop at end" "stop-at-end" "stop-at-end"
check_feature "Loop mode" "loop" "loop"
echo ""

echo "### Appearance Features"
printf "| %-35s | %-8s | %-8s |\n" "Feature" "Rource" "Gource"
printf "| %-35s | %-8s | %-8s |\n" "-----------------------------------" "--------" "--------"
check_feature "Background color" "background" "background"
check_feature "Font color" "font-colour" "font-colour"
check_feature "Font size" "font-size" "font-size"
check_feature "Font file" "font-file" "font-file"
check_feature "Logo image" "logo" "logo"
check_feature "Background image" "background-image" "background-image"
check_feature "User images" "user-image-dir" "user-image-dir"
check_feature "Default user image" "default-user-image" "default-user-image"
check_feature "File extension colors" "file-extensions" "file-extensions"
echo ""

# ==============================================================================
# Platform Support
# ==============================================================================

print_header "Platform Support"

printf "| %-25s | %-15s | %-15s |\n" "Platform" "Rource" "Gource"
printf "| %-25s | %-15s | %-15s |\n" "-------------------------" "---------------" "---------------"
printf "| %-25s | %-15s | %-15s |\n" "Linux (native)" "Yes" "Yes"
printf "| %-25s | %-15s | %-15s |\n" "macOS (native)" "Yes" "Yes"
printf "| %-25s | %-15s | %-15s |\n" "Windows (native)" "Yes" "Yes"
printf "| %-25s | %-15s | %-15s |\n" "WebAssembly (browser)" "Yes" "No"
printf "| %-25s | %-15s | %-15s |\n" "Headless (no GPU)" "Yes" "Partial*"
printf "| %-25s | %-15s | %-15s |\n" "ARM support" "Yes" "Yes"
printf "| %-25s | %-15s | %-15s |\n" "RISC-V support" "Yes**" "Limited"
echo ""
echo "* Gource requires X11/OpenGL even for headless output"
echo "** Rource's software renderer works on any CPU architecture"
echo ""

# ==============================================================================
# Rendering Backends
# ==============================================================================

print_header "Rendering Backends"

printf "| %-25s | %-15s | %-15s |\n" "Backend" "Rource" "Gource"
printf "| %-25s | %-15s | %-15s |\n" "-------------------------" "---------------" "---------------"
printf "| %-25s | %-15s | %-15s |\n" "Software (CPU)" "Yes (default)" "No"
printf "| %-25s | %-15s | %-15s |\n" "OpenGL" "No" "Yes (required)"
printf "| %-25s | %-15s | %-15s |\n" "WebGL2" "Yes (WASM)" "No"
printf "| %-25s | %-15s | %-15s |\n" "Vulkan" "No" "No"
printf "| %-25s | %-15s | %-15s |\n" "Metal" "No" "No"
echo ""

# ==============================================================================
# Unique Features
# ==============================================================================

print_header "Unique Features by Tool"

echo "### Rource-only Features"
echo "- Pure software renderer (no GPU required)"
echo "- WebAssembly support (runs in browsers)"
echo "- Memory-efficient compact storage for large repos"
echo "- Streaming log parser (constant memory usage)"
echo "- True headless mode (no X11 required)"
echo "- Single binary distribution (fonts embedded)"
echo ""

echo "### Gource-only Features"
echo "- GPU-accelerated rendering (OpenGL)"
echo "- User avatar images (gravatar support)"
echo "- Caption files"
echo "- Multiple VCS formats (CVS, Hg, Bazaar)"
echo "- Mouse interaction (pick users)"
echo "- Customizable sprites"
echo ""

# ==============================================================================
# Save Results
# ==============================================================================

cat > "${RUN_DIR}/results.json" << EOF
{
  "benchmark": "features",
  "timestamp": "$(date -Iseconds)",
  "cli_options": {
    "rource": $ROURCE_OPTIONS,
    "gource": $GOURCE_OPTIONS
  },
  "platforms": {
    "rource": ["linux", "macos", "windows", "wasm"],
    "gource": ["linux", "macos", "windows"]
  },
  "renderers": {
    "rource": ["software", "webgl2"],
    "gource": ["opengl"]
  },
  "unique_features": {
    "rource": [
      "software_renderer",
      "wasm_support",
      "compact_storage",
      "streaming_parser",
      "true_headless",
      "embedded_fonts"
    ],
    "gource": [
      "gpu_acceleration",
      "user_avatars",
      "caption_files",
      "multiple_vcs",
      "mouse_interaction",
      "custom_sprites"
    ]
  }
}
EOF

log_success "Feature comparison saved to ${RUN_DIR}/results.json"
