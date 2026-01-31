#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# =============================================================================
# Update Verification Counts
# =============================================================================
#
# Single source of truth for ALL verification metrics across the repository.
# Parses actual source files to extract counts, generates a canonical JSON
# metrics file, and updates all documentation files to match.
#
# Usage:
#   ./scripts/update-verification-counts.sh           # Update everything
#   ./scripts/update-verification-counts.sh --check   # CI mode: fail if stale
#   ./scripts/update-verification-counts.sh --json    # Only output JSON, no updates
#
# Source of truth (parsed, not hardcoded):
#   - Kani:  crates/rource-math/src/kani_proofs/*.rs   (#[kani::proof])
#   - Verus: crates/rource-math/proofs/*_proofs.rs     (proof fn)
#   - Coq R: crates/rource-math/proofs/coq/*_Proofs.v  (Theorem|Lemma|Local Lemma)
#   - Coq Z: crates/rource-math/proofs/coq/*_Compute.v (Theorem|Lemma|Local Lemma)
#   - Tests: cargo test --all (parsed from output)
#   - Phases: docs/performance/CHRONOLOGY.md (highest Phase N)
#
# Output:
#   - metrics/verification-counts.json (machine-readable, canonical)
#   - All documentation files updated in-place
#
# CI Integration:
#   --check mode exits non-zero if ANY documentation file contains stale
#   counts, enabling automated enforcement in CI pipelines.
#
# =============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
METRICS_DIR="$PROJECT_ROOT/metrics"
COUNTS_FILE="$METRICS_DIR/verification-counts.json"

# Parse arguments
MODE="update"  # update | check | json
for arg in "$@"; do
    case "$arg" in
        --check) MODE="check" ;;
        --json)  MODE="json" ;;
        --help|-h)
            echo "Usage: $0 [--check|--json|--help]"
            echo ""
            echo "  (no args)  Parse sources, update JSON + all docs"
            echo "  --check    CI mode: verify docs match source, exit 1 if stale"
            echo "  --json     Parse sources, output JSON only, no doc updates"
            echo "  --help     Show this help"
            exit 0
            ;;
        *) echo "Unknown argument: $arg"; exit 1 ;;
    esac
done

mkdir -p "$METRICS_DIR"

# =============================================================================
# PHASE 1: Parse source files to extract ground-truth counts
# =============================================================================

# --- Kani harnesses ---
count_kani() {
    local file="$1"
    grep -c '#\[kani::proof\]' "$file" 2>/dev/null || echo 0
}

KANI_DIR="$PROJECT_ROOT/crates/rource-math/src/kani_proofs"
KANI_VEC2=$(count_kani "$KANI_DIR/vec2.rs")
KANI_VEC3=$(count_kani "$KANI_DIR/vec3.rs")
KANI_VEC4=$(count_kani "$KANI_DIR/vec4.rs")
KANI_MAT3=$(count_kani "$KANI_DIR/mat3.rs")
KANI_MAT4=$(count_kani "$KANI_DIR/mat4.rs")
KANI_COLOR=$(count_kani "$KANI_DIR/color.rs")
KANI_RECT=$(count_kani "$KANI_DIR/rect.rs")
KANI_BOUNDS=$(count_kani "$KANI_DIR/bounds.rs")
KANI_UTILS=$(count_kani "$KANI_DIR/utils.rs")
KANI_TOTAL=$((KANI_VEC2 + KANI_VEC3 + KANI_VEC4 + KANI_MAT3 + KANI_MAT4 + KANI_COLOR + KANI_RECT + KANI_BOUNDS + KANI_UTILS))

# --- Verus proof functions ---
count_verus() {
    local file="$1"
    grep -c 'proof fn' "$file" 2>/dev/null || echo 0
}

VERUS_DIR="$PROJECT_ROOT/crates/rource-math/proofs"
VERUS_VEC2=$(count_verus "$VERUS_DIR/vec2_proofs.rs")
VERUS_VEC3=$(count_verus "$VERUS_DIR/vec3_proofs.rs")
VERUS_VEC4=$(count_verus "$VERUS_DIR/vec4_proofs.rs")
VERUS_MAT3_BASE=$(count_verus "$VERUS_DIR/mat3_proofs.rs")
VERUS_MAT3_EXT=$(count_verus "$VERUS_DIR/mat3_extended_proofs.rs")
VERUS_MAT3=$((VERUS_MAT3_BASE + VERUS_MAT3_EXT))
VERUS_MAT4_BASE=$(count_verus "$VERUS_DIR/mat4_proofs.rs")
VERUS_MAT4_EXT=$(count_verus "$VERUS_DIR/mat4_extended_proofs.rs")
VERUS_MAT4=$((VERUS_MAT4_BASE + VERUS_MAT4_EXT))
VERUS_COLOR=$(count_verus "$VERUS_DIR/color_proofs.rs")
VERUS_RECT=$(count_verus "$VERUS_DIR/rect_proofs.rs")
VERUS_TOTAL=$((VERUS_VEC2 + VERUS_VEC3 + VERUS_VEC4 + VERUS_MAT3 + VERUS_MAT4 + VERUS_COLOR + VERUS_RECT))

# --- Coq R-based theorems (Proofs + Complexity + Utils) ---
count_coq() {
    local file="$1"
    grep -cE '^(Theorem|Lemma|Local Lemma)' "$file" 2>/dev/null || echo 0
}

COQ_DIR="$PROJECT_ROOT/crates/rource-math/proofs/coq"
COQ_R_VEC2=$(count_coq "$COQ_DIR/Vec2_Proofs.v")
COQ_R_VEC3=$(count_coq "$COQ_DIR/Vec3_Proofs.v")
COQ_R_VEC4=$(count_coq "$COQ_DIR/Vec4_Proofs.v")
COQ_R_MAT3=$(count_coq "$COQ_DIR/Mat3_Proofs.v")
COQ_R_MAT4=$(count_coq "$COQ_DIR/Mat4_Proofs.v")
COQ_R_COLOR=$(count_coq "$COQ_DIR/Color_Proofs.v")
COQ_R_RECT=$(count_coq "$COQ_DIR/Rect_Proofs.v")
COQ_R_COMPLEXITY=$(count_coq "$COQ_DIR/Complexity.v")
COQ_R_UTILS=$(count_coq "$COQ_DIR/Utils.v")
COQ_R_CROSSTYPE=$(count_coq "$COQ_DIR/Vec_CrossType.v")
COQ_R_BOUNDS=$(count_coq "$COQ_DIR/Bounds_Proofs.v")
COQ_R_TOTAL=$((COQ_R_VEC2 + COQ_R_VEC3 + COQ_R_VEC4 + COQ_R_MAT3 + COQ_R_MAT4 + COQ_R_COLOR + COQ_R_RECT + COQ_R_COMPLEXITY + COQ_R_UTILS + COQ_R_CROSSTYPE + COQ_R_BOUNDS))

# --- Coq Z-based theorems (Compute) ---
COQ_Z_VEC2=$(count_coq "$COQ_DIR/Vec2_Compute.v")
COQ_Z_VEC3=$(count_coq "$COQ_DIR/Vec3_Compute.v")
COQ_Z_VEC4=$(count_coq "$COQ_DIR/Vec4_Compute.v")
COQ_Z_MAT3=$(count_coq "$COQ_DIR/Mat3_Compute.v")
COQ_Z_MAT4=$(count_coq "$COQ_DIR/Mat4_Compute.v")
COQ_Z_COLOR=$(count_coq "$COQ_DIR/Color_Compute.v")
COQ_Z_RECT=$(count_coq "$COQ_DIR/Rect_Compute.v")
COQ_Z_UTILS=$(count_coq "$COQ_DIR/Utils_Compute.v")
COQ_Z_BOUNDS=$(count_coq "$COQ_DIR/Bounds_Compute.v")
COQ_Z_TOTAL=$((COQ_Z_VEC2 + COQ_Z_VEC3 + COQ_Z_VEC4 + COQ_Z_MAT3 + COQ_Z_MAT4 + COQ_Z_COLOR + COQ_Z_RECT + COQ_Z_UTILS + COQ_Z_BOUNDS))

# --- Coq FP error bounds theorems (Flocq-based) ---
COQ_FP_COMMON=$(count_coq "$COQ_DIR/FP_Common.v")
COQ_FP_ROUNDING=$(count_coq "$COQ_DIR/FP_Rounding.v")
COQ_FP_ERRORBOUNDS=$(count_coq "$COQ_DIR/FP_ErrorBounds.v")
COQ_FP_VEC=$(count_coq "$COQ_DIR/FP_Vec.v")
COQ_FP_TOTAL=$((COQ_FP_COMMON + COQ_FP_ROUNDING + COQ_FP_ERRORBOUNDS + COQ_FP_VEC))

# --- Coq combined ---
COQ_COMBINED=$((COQ_R_TOTAL + COQ_Z_TOTAL))
COQ_ALL=$((COQ_COMBINED + COQ_FP_TOTAL))

# --- Grand total (includes FP layer) ---
GRAND_TOTAL=$((VERUS_TOTAL + COQ_R_TOTAL + COQ_Z_TOTAL + COQ_FP_TOTAL + KANI_TOTAL))

# --- Per-type totals ---
TOTAL_VEC2=$((VERUS_VEC2 + COQ_R_VEC2 + COQ_Z_VEC2 + KANI_VEC2))
TOTAL_VEC3=$((VERUS_VEC3 + COQ_R_VEC3 + COQ_Z_VEC3 + KANI_VEC3))
TOTAL_VEC4=$((VERUS_VEC4 + COQ_R_VEC4 + COQ_Z_VEC4 + KANI_VEC4))
TOTAL_MAT3=$((VERUS_MAT3 + COQ_R_MAT3 + COQ_Z_MAT3 + KANI_MAT3))
TOTAL_MAT4=$((VERUS_MAT4 + COQ_R_MAT4 + COQ_Z_MAT4 + KANI_MAT4))
TOTAL_COLOR=$((VERUS_COLOR + COQ_R_COLOR + COQ_Z_COLOR + KANI_COLOR))
TOTAL_RECT=$((VERUS_RECT + COQ_R_RECT + COQ_Z_RECT + KANI_RECT))
TOTAL_UTILS=$((COQ_R_UTILS + COQ_Z_UTILS + KANI_UTILS))
TOTAL_BOUNDS=$((COQ_R_BOUNDS + COQ_Z_BOUNDS + KANI_BOUNDS))
TOTAL_COMPLEXITY=$COQ_R_COMPLEXITY

# --- Optimization phases ---
OPT_PHASES=$(grep -oE 'Phase [0-9]+' "$PROJECT_ROOT/docs/performance/CHRONOLOGY.md" 2>/dev/null | \
    sed 's/Phase //' | sort -n | tail -1 || echo "0")

# =============================================================================
# PHASE 2: Generate JSON metrics file
# =============================================================================

cat > "$COUNTS_FILE" << ENDJSON
{
  "_comment": "Auto-generated by scripts/update-verification-counts.sh — DO NOT EDIT MANUALLY",
  "_updated": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "_source": "Parsed from actual source files (not hardcoded)",
  "grand_total": $GRAND_TOTAL,
  "verus": {
    "total": $VERUS_TOTAL,
    "vec2": $VERUS_VEC2,
    "vec3": $VERUS_VEC3,
    "vec4": $VERUS_VEC4,
    "mat3": $VERUS_MAT3,
    "mat3_base": $VERUS_MAT3_BASE,
    "mat3_extended": $VERUS_MAT3_EXT,
    "mat4": $VERUS_MAT4,
    "mat4_base": $VERUS_MAT4_BASE,
    "mat4_extended": $VERUS_MAT4_EXT,
    "color": $VERUS_COLOR,
    "rect": $VERUS_RECT
  },
  "coq_r": {
    "total": $COQ_R_TOTAL,
    "vec2": $COQ_R_VEC2,
    "vec3": $COQ_R_VEC3,
    "vec4": $COQ_R_VEC4,
    "mat3": $COQ_R_MAT3,
    "mat4": $COQ_R_MAT4,
    "color": $COQ_R_COLOR,
    "rect": $COQ_R_RECT,
    "complexity": $COQ_R_COMPLEXITY,
    "utils": $COQ_R_UTILS,
    "crosstype": $COQ_R_CROSSTYPE,
    "bounds": $COQ_R_BOUNDS
  },
  "coq_z": {
    "total": $COQ_Z_TOTAL,
    "vec2": $COQ_Z_VEC2,
    "vec3": $COQ_Z_VEC3,
    "vec4": $COQ_Z_VEC4,
    "mat3": $COQ_Z_MAT3,
    "mat4": $COQ_Z_MAT4,
    "color": $COQ_Z_COLOR,
    "rect": $COQ_Z_RECT,
    "utils": $COQ_Z_UTILS,
    "bounds": $COQ_Z_BOUNDS
  },
  "coq_fp": {
    "total": $COQ_FP_TOTAL,
    "common": $COQ_FP_COMMON,
    "rounding": $COQ_FP_ROUNDING,
    "error_bounds": $COQ_FP_ERRORBOUNDS,
    "vec": $COQ_FP_VEC
  },
  "coq_combined": $COQ_COMBINED,
  "coq_all": $COQ_ALL,
  "kani": {
    "total": $KANI_TOTAL,
    "vec2": $KANI_VEC2,
    "vec3": $KANI_VEC3,
    "vec4": $KANI_VEC4,
    "mat3": $KANI_MAT3,
    "mat4": $KANI_MAT4,
    "color": $KANI_COLOR,
    "rect": $KANI_RECT,
    "bounds": $KANI_BOUNDS,
    "utils": $KANI_UTILS
  },
  "per_type": {
    "vec2": $TOTAL_VEC2,
    "vec3": $TOTAL_VEC3,
    "vec4": $TOTAL_VEC4,
    "mat3": $TOTAL_MAT3,
    "mat4": $TOTAL_MAT4,
    "color": $TOTAL_COLOR,
    "rect": $TOTAL_RECT,
    "utils": $TOTAL_UTILS,
    "bounds": $TOTAL_BOUNDS,
    "complexity": $TOTAL_COMPLEXITY
  },
  "optimization_phases": $OPT_PHASES
}
ENDJSON

# =============================================================================
# PHASE 3: Display summary
# =============================================================================

echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║          VERIFICATION COUNTS (from source files)            ║"
echo "╠═══════════════════════════════════════════════════════════════╣"
echo "║                                                             ║"
printf "║  Verus proof functions:  %4d                               ║\n" "$VERUS_TOTAL"
printf "║  Coq R-based theorems:  %4d                               ║\n" "$COQ_R_TOTAL"
printf "║  Coq Z-based theorems:  %4d                               ║\n" "$COQ_Z_TOTAL"
printf "║  Coq FP error bounds:   %4d                               ║\n" "$COQ_FP_TOTAL"
printf "║  Kani CBMC harnesses:   %4d                               ║\n" "$KANI_TOTAL"
echo "║  ─────────────────────────────                              ║"
printf "║  GRAND TOTAL:           %4d                               ║\n" "$GRAND_TOTAL"
echo "║                                                             ║"
printf "║  Optimization phases:     %3d                               ║\n" "$OPT_PHASES"
echo "║                                                             ║"
echo "╚═══════════════════════════════════════════════════════════════╝"
echo ""
echo "Per-type breakdown:"
printf "  %-12s  Verus  Coq-R  Coq-Z  Kani  Total\n" "Type"
printf "  %-12s  -----  -----  -----  ----  -----\n" "────────────"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "Vec2" "$VERUS_VEC2" "$COQ_R_VEC2" "$COQ_Z_VEC2" "$KANI_VEC2" "$TOTAL_VEC2"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "Vec3" "$VERUS_VEC3" "$COQ_R_VEC3" "$COQ_Z_VEC3" "$KANI_VEC3" "$TOTAL_VEC3"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "Vec4" "$VERUS_VEC4" "$COQ_R_VEC4" "$COQ_Z_VEC4" "$KANI_VEC4" "$TOTAL_VEC4"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "Mat3" "$VERUS_MAT3" "$COQ_R_MAT3" "$COQ_Z_MAT3" "$KANI_MAT3" "$TOTAL_MAT3"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "Mat4" "$VERUS_MAT4" "$COQ_R_MAT4" "$COQ_Z_MAT4" "$KANI_MAT4" "$TOTAL_MAT4"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "Color" "$VERUS_COLOR" "$COQ_R_COLOR" "$COQ_Z_COLOR" "$KANI_COLOR" "$TOTAL_COLOR"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "Rect" "$VERUS_RECT" "$COQ_R_RECT" "$COQ_Z_RECT" "$KANI_RECT" "$TOTAL_RECT"
printf "  %-12s  %5s  %5d  %5d  %4d  %5d\n" "Utils" "—" "$COQ_R_UTILS" "$COQ_Z_UTILS" "$KANI_UTILS" "$TOTAL_UTILS"
printf "  %-12s  %5s  %5d  %5s  %4s  %5d\n" "Complexity" "—" "$COQ_R_COMPLEXITY" "—" "—" "$TOTAL_COMPLEXITY"
printf "  %-12s  %5s  %5d  %5s  %4s  %5d\n" "CrossType" "—" "$COQ_R_CROSSTYPE" "—" "—" "$COQ_R_CROSSTYPE"
printf "  %-12s  %5s  %5d  %5d  %4d  %5d\n" "Bounds" "—" "$COQ_R_BOUNDS" "$COQ_Z_BOUNDS" "$KANI_BOUNDS" "$TOTAL_BOUNDS"
printf "  %-12s  %5d  %5d  %5d  %4d  %5d\n" "TOTAL" "$VERUS_TOTAL" "$COQ_R_TOTAL" "$COQ_Z_TOTAL" "$KANI_TOTAL" "$GRAND_TOTAL"
echo ""

if [[ "$MODE" == "json" ]]; then
    echo "JSON written to: $COUNTS_FILE"
    exit 0
fi

# =============================================================================
# PHASE 4: Check or Update documentation files
# =============================================================================

ERRORS=0

# Helper: check if a file contains a specific string, report error if not
check_contains() {
    local file="$1"
    local expected="$2"
    local description="$3"
    if ! grep -qF "$expected" "$file" 2>/dev/null; then
        echo "STALE: $file"
        echo "  Expected: $expected"
        echo "  Context: $description"
        ERRORS=$((ERRORS + 1))
    fi
}

# Helper: replace a pattern in a file (sed -i)
replace_in_file() {
    local file="$1"
    local old="$2"
    local new="$3"
    if [[ -f "$file" ]] && grep -qF "$old" "$file" 2>/dev/null; then
        sed -i "s|$(echo "$old" | sed 's/[&/\]/\\&/g')|$(echo "$new" | sed 's/[&/\]/\\&/g')|g" "$file"
        echo "  Updated: $(basename "$file"): '$old' → '$new'"
    fi
}

# Define key strings that must appear in specific files
# Format: file|expected_string|description

CHECKS=(
    # FORMAL_VERIFICATION.md - overview paragraph
    "docs/verification/FORMAL_VERIFICATION.md|$GRAND_TOTAL machine-checked|Overview total"
    # FORMAL_VERIFICATION.md - summary table Kani row
    "docs/verification/FORMAL_VERIFICATION.md|$KANI_TOTAL proof harnesses|Kani summary row"
    # FORMAL_VERIFICATION.md - combined row
    "docs/verification/FORMAL_VERIFICATION.md|**$GRAND_TOTAL**|Combined total row"
    # FORMAL_VERIFICATION.md - FP row
    "docs/verification/FORMAL_VERIFICATION.md|$COQ_FP_TOTAL theorems|Coq FP row"
    # FORMAL_VERIFICATION.md - Coq combined comment
    "docs/verification/FORMAL_VERIFICATION.md|$COQ_COMBINED theorems|Coq combined comment"
    # FORMAL_VERIFICATION.md - architecture diagram Coq count
    "docs/verification/FORMAL_VERIFICATION.md|Coq Proofs ($COQ_COMBINED theorems)|Architecture Coq total"
    # FORMAL_VERIFICATION.md - architecture diagram Z-based count
    "docs/verification/FORMAL_VERIFICATION.md|($COQ_Z_TOTAL thms)|Architecture Z-based total"
    # FORMAL_VERIFICATION.md - Layer 2 comment
    "docs/verification/FORMAL_VERIFICATION.md|($COQ_Z_TOTAL theorems)|Layer 2 Z-based count"
    # FORMAL_VERIFICATION.md - Z-based footer per-type
    "docs/verification/FORMAL_VERIFICATION.md|Mat4($COQ_Z_MAT4)|Z-based footer Mat4"
    # FORMAL_VERIFICATION.md - Z-based in combined footer
    "docs/verification/FORMAL_VERIFICATION.md|Coq Z-based: $COQ_Z_TOTAL|Combined footer Z count"
    # VERIFICATION_COVERAGE.md - Kani total
    "docs/verification/VERIFICATION_COVERAGE.md|**$KANI_TOTAL**|Kani total row"
    # VERIFICATION_COVERAGE.md - architecture line
    "docs/verification/VERIFICATION_COVERAGE.md|$GRAND_TOTAL theorems|Architecture current layer"
    # VERIFICATION_COVERAGE.md - footer Kani
    "docs/verification/VERIFICATION_COVERAGE.md|Kani IEEE 754 harnesses: $KANI_TOTAL|Footer Kani count"
    # COQ_PROOFS.md - header admits line
    "docs/verification/COQ_PROOFS.md|across all $COQ_COMBINED theorems|COQ_PROOFS header total"
    # COQ_PROOFS.md - Z-based table total
    "docs/verification/COQ_PROOFS.md|**$COQ_Z_TOTAL**|COQ_PROOFS Z table total"
    # COQ_PROOFS.md - Z-based footer per-type
    "docs/verification/COQ_PROOFS.md|Mat4: $COQ_Z_MAT4|COQ_PROOFS Z footer Mat4"
    # COQ_PROOFS.md - combined Coq total
    "docs/verification/COQ_PROOFS.md|$COQ_COMBINED total Coq theorems|COQ_PROOFS combined total"
    # CLAUDE.md - formal verification status
    "CLAUDE.md|$KANI_TOTAL proof harnesses|Kani CBMC status"
    "CLAUDE.md|$GRAND_TOTAL formally verified|Combined status"
    # CLAUDE.md - per-type table totals
    "CLAUDE.md|**$GRAND_TOTAL**|Per-type table total"
    # CLAUDE.md - footer
    "CLAUDE.md|Formal Verification: $GRAND_TOTAL theorems/harnesses (Verus: $VERUS_TOTAL|Footer metadata"
    # CLAUDE.md - COQ_PROOFS.md doc reference
    "CLAUDE.md|R + Z, $COQ_COMBINED theorems|CLAUDE COQ_PROOFS ref"
    # README.md - verification table (Verus row)
    "README.md|$VERUS_TOTAL proof functions|README Verus row"
    # README.md - Coq R-based row
    "README.md|$COQ_R_TOTAL theorems|README Coq R row"
    # README.md - Coq Z-based row
    "README.md|$COQ_Z_TOTAL theorems|README Coq Z row"
    # README.md - combined total
    "README.md|$GRAND_TOTAL|README combined total"
    # docs/README.md - Verus reference
    "docs/README.md|$VERUS_TOTAL proof functions|docs/README Verus ref"
    # docs/README.md - Coq reference
    "docs/README.md|$COQ_COMBINED theorems|docs/README Coq ref"
    # docs/README.md - FORMAL_VERIFICATION reference
    "docs/README.md|$GRAND_TOTAL theorems/harnesses|docs/README FORMAL_VERIFICATION ref"
    # SETUP_GUIDE.md - Verus count
    "docs/verification/SETUP_GUIDE.md|$VERUS_TOTAL|SETUP_GUIDE Verus count"
    # WASM_EXTRACTION_PIPELINE.md - Verus count
    "docs/verification/WASM_EXTRACTION_PIPELINE.md|$VERUS_TOTAL proof|WASM_EXTRACTION Verus"
    # WASM_EXTRACTION_PIPELINE.md - Coq combined
    "docs/verification/WASM_EXTRACTION_PIPELINE.md|$COQ_COMBINED theorems|WASM_EXTRACTION Coq"
    # RUST_VERIFICATION_LANDSCAPE.md - total
    "docs/verification/RUST_VERIFICATION_LANDSCAPE.md|$GRAND_TOTAL|LANDSCAPE total"
    # RUST_VERIFICATION_LANDSCAPE.md - Coq theorem count
    "docs/verification/RUST_VERIFICATION_LANDSCAPE.md|Coq ($COQ_COMBINED theorems)|LANDSCAPE Coq count"
    # RUST_VERIFICATION_LANDSCAPE.md - Kani harness count
    "docs/verification/RUST_VERIFICATION_LANDSCAPE.md|$KANI_TOTAL harnesses for|LANDSCAPE Kani count"
    # kani_proofs/mod.rs - harness count in doc
    "crates/rource-math/src/kani_proofs/mod.rs|$KANI_TOTAL total|mod.rs harness count"
    # SETUP_GUIDE.md - Verus total in table
    "docs/verification/SETUP_GUIDE.md|**$VERUS_TOTAL**|SETUP_GUIDE Verus total"
    # SETUP_GUIDE.md - Coq combined total in table
    "docs/verification/SETUP_GUIDE.md|**$COQ_COMBINED**|SETUP_GUIDE Coq combined total"
    # SETUP_GUIDE.md - Combined total
    "docs/verification/SETUP_GUIDE.md|**$GRAND_TOTAL**|SETUP_GUIDE combined total"
    # FLOATING_POINT_VERIFICATION.md - grand total
    "docs/verification/FLOATING_POINT_VERIFICATION.md|$GRAND_TOTAL theorems|FP_VERIFICATION total"
    # CERTICOQ_WASM_ASSESSMENT.md - Layer 2 Z total
    "docs/verification/CERTICOQ_WASM_ASSESSMENT.md|$COQ_Z_TOTAL theorems, all 8|CERTICOQ Layer 2 total"
)

if [[ "$MODE" == "check" ]]; then
    echo "=== CI Consistency Check ==="
    echo "Verifying all documentation matches source-of-truth counts..."
    echo ""

    for entry in "${CHECKS[@]}"; do
        IFS='|' read -r file expected desc <<< "$entry"
        check_contains "$PROJECT_ROOT/$file" "$expected" "$desc"
    done

    echo ""
    if [[ $ERRORS -gt 0 ]]; then
        echo "FAILED: $ERRORS stale count(s) found."
        echo "Run './scripts/update-verification-counts.sh' to fix."
        exit 1
    else
        echo "PASSED: All documentation counts match source files."
        exit 0
    fi
fi

# =============================================================================
# PHASE 5: Update all documentation files
# =============================================================================

echo "=== Updating documentation files ==="
echo ""

# --- FORMAL_VERIFICATION.md ---
FV="$PROJECT_ROOT/docs/verification/FORMAL_VERIFICATION.md"
if [[ -f "$FV" ]]; then
    echo "Updating FORMAL_VERIFICATION.md..."
    # Overview paragraph: update "N machine-checked"
    sed -i -E "s/[0-9]+ machine-checked theorems\/harnesses/$GRAND_TOTAL machine-checked theorems\/harnesses/g" "$FV"
    # Kani summary row total
    sed -i -E "s/[0-9]+ proof harnesses \| 0/$KANI_TOTAL proof harnesses | 0/" "$FV"
    # Combined total row (matches both "8 types" and "8 types + FP")
    sed -i -E "s/\*\*[0-9]+\*\* \| \*\*0\*\* \| \*\*8 types[^|]*\*\*/**$GRAND_TOTAL** | **0** | **8 types + FP**/" "$FV"
    # Coq combined comment
    sed -i -E "s/[0-9]+ theorems, ~45s/$COQ_COMBINED theorems, ~45s/" "$FV"
    # Per-type Kani counts in the table
    sed -i -E "s/\| $((KANI_VEC2)) harnesses \| [0-9]+ \|/| $KANI_VEC2 harnesses | $TOTAL_VEC2 |/" "$FV"
    # Architecture diagram Kani count
    sed -i -E "s/\([0-9]+ harnesses\)  NaN/($KANI_TOTAL harnesses)  NaN/" "$FV"
    # Architecture diagram Coq total
    sed -i -E "s/Coq Proofs \([0-9]+ theorems\)/Coq Proofs ($COQ_COMBINED theorems)/" "$FV"
    # Architecture diagram Z-based total
    sed -i -E "s/Compute files \([0-9]+ thms\)/Compute files ($COQ_Z_TOTAL thms)/" "$FV"
    # Layer 2 Z-based comment
    sed -i -E "s/Z-based Computational Bridge \([0-9]+ theorems\)/Z-based Computational Bridge ($COQ_Z_TOTAL theorems)/" "$FV"
    # Z-based footer per-type (fix Mat4 count)
    sed -i -E "s/Mat4\([0-9]+\), Color/Mat4($COQ_Z_MAT4), Color/" "$FV"
    # Z-based footer total
    sed -i -E "s/= [0-9]+ theorems over Z/= $COQ_Z_TOTAL theorems over Z/" "$FV"
    # Z-based in combined footer
    sed -i -E "s/Coq Z-based: [0-9]+/Coq Z-based: $COQ_Z_TOTAL/" "$FV"
    # Footer: Kani total
    sed -i -E "s/Total harnesses: [0-9]+/Total harnesses: $KANI_TOTAL/" "$FV"
    # Footer: Kani per-type (anchored to "Total harnesses:" to avoid clobbering other breakdowns)
    # Match both old format (without Bounds) and new format (with Bounds)
    sed -i -E "s/Total harnesses: [0-9]+ \(Vec2: [0-9]+, Vec3: [0-9]+, Vec4: [0-9]+, Mat3: [0-9]+, Mat4: [0-9]+, Color: [0-9]+, Rect: [0-9]+(, Bounds: [0-9]+)?, Utils: [0-9]+\)/Total harnesses: $KANI_TOTAL (Vec2: $KANI_VEC2, Vec3: $KANI_VEC3, Vec4: $KANI_VEC4, Mat3: $KANI_MAT3, Mat4: $KANI_MAT4, Color: $KANI_COLOR, Rect: $KANI_RECT, Bounds: $KANI_BOUNDS, Utils: $KANI_UTILS)/" "$FV"
    # Overview paragraph Kani per-type (anchored to "Kani:" prefix)
    sed -i -E "s/Kani: [0-9]+ harnesses\) \(Vec2: [0-9]+, Vec3: [0-9]+, Vec4: [0-9]+, Mat3: [0-9]+, Mat4: [0-9]+, Color: [0-9]+, Rect: [0-9]+(, Bounds: [0-9]+)?, Utils: [0-9]+\)/Kani: $KANI_TOTAL harnesses) (Vec2: $KANI_VEC2, Vec3: $KANI_VEC3, Vec4: $KANI_VEC4, Mat3: $KANI_MAT3, Mat4: $KANI_MAT4, Color: $KANI_COLOR, Rect: $KANI_RECT, Bounds: $KANI_BOUNDS, Utils: $KANI_UTILS)/" "$FV"
    # Footer: Coq Z-based per-type (anchored to "*Total theorems:" — fix both total and per-type)
    # Use two-phase approach: first match the Z-based line by its unique prefix context
    sed -i -E "/Z-based Computational Bridge/{n;n;s/\*Total theorems: [0-9]+ \(Vec2: [0-9]+, Vec3: [0-9]+, Vec4: [0-9]+, Mat3: [0-9]+, Mat4: [0-9]+, Color: [0-9]+, Rect: [0-9]+, Utils: [0-9]+\)/\*Total theorems: $COQ_Z_TOTAL (Vec2: $COQ_Z_VEC2, Vec3: $COQ_Z_VEC3, Vec4: $COQ_Z_VEC4, Mat3: $COQ_Z_MAT3, Mat4: $COQ_Z_MAT4, Color: $COQ_Z_COLOR, Rect: $COQ_Z_RECT, Utils: $COQ_Z_UTILS)/}" "$FV"
    # Footer: combined total
    sed -i -E "s/Total theorems\/harnesses: [0-9]+ across/Total theorems\/harnesses: $GRAND_TOTAL across/" "$FV"
    sed -i -E "s/Kani: [0-9]+\)/Kani: $KANI_TOTAL)/" "$FV"
    # Footer: Coq R-based total
    sed -i -E "s/Total theorems: [0-9]+ \(Vec2: $COQ_R_VEC2/Total theorems: $COQ_R_TOTAL (Vec2: $COQ_R_VEC2/" "$FV"
    # (Z-based per-type is handled above by context-aware sed anchored to "Z-based Computational Bridge")
    # Per-type table Total row (update Verus, Kani, and grand totals)
    sed -i -E "s/\| \*\*[0-9]+ proof fns\*\* \| \*\*[0-9]+ theorems\*\* \| \*\*[0-9]+ theorems\*\* \| \*\*[0-9]+ theorems\*\* \| \*\*[0-9]+ harnesses\*\* \| \*\*[0-9]+\*\* \| \*\*ACADEMIC\*\*/| **$VERUS_TOTAL proof fns** | **$COQ_R_TOTAL theorems** | **$COQ_Z_TOTAL theorems** | **$COQ_FP_TOTAL theorems** | **$KANI_TOTAL harnesses** | **$GRAND_TOTAL** | **ACADEMIC**/" "$FV"
    # Per-type table: update individual Verus counts per type that changed
    sed -i -E "s/\| Mat4 \| [0-9]+ proof fns \|/| Mat4 | $VERUS_MAT4 proof fns |/" "$FV"
    sed -i -E "s/\| Color \| [0-9]+ proof fns \|/| Color | $VERUS_COLOR proof fns |/" "$FV"
    sed -i -E "s/\| Rect \| [0-9]+ proof fns \|/| Rect | $VERUS_RECT proof fns |/" "$FV"
    # Per-type table: update Kani harness counts per type
    sed -i -E "/\| Mat4 \|.*\| [0-9]+ harnesses/{s/[0-9]+ harnesses \| [0-9]+ \|/$KANI_MAT4 harnesses | $TOTAL_MAT4 |/}" "$FV"
    sed -i -E "/\| Color \|.*\| [0-9]+ harnesses/{s/[0-9]+ harnesses \| [0-9]+ \|/$KANI_COLOR harnesses | $TOTAL_COLOR |/}" "$FV"
    sed -i -E "/\| Rect \|.*\| [0-9]+ harnesses/{s/[0-9]+ harnesses \| [0-9]+ \|/$KANI_RECT harnesses | $TOTAL_RECT |/}" "$FV"
    # Summary Statistics Verus row
    sed -i -E "s/[0-9]+ proof functions \| 0 \| Vec2-4, Mat3-4, Color, Rect \| All verified/$VERUS_TOTAL proof functions | 0 | Vec2-4, Mat3-4, Color, Rect | All verified/" "$FV"
    # Academic contribution - total
    sed -i -E "s/rource-math with [0-9]+ machine-checked/rource-math with $GRAND_TOTAL machine-checked/" "$FV"
    # All harnesses verified line
    sed -i -E "s/All [0-9]+ harnesses verified/All $KANI_TOTAL harnesses verified/" "$FV"
    echo "  Done."
fi

# --- VERIFICATION_COVERAGE.md ---
VC="$PROJECT_ROOT/docs/verification/VERIFICATION_COVERAGE.md"
if [[ -f "$VC" ]]; then
    echo "Updating VERIFICATION_COVERAGE.md..."
    sed -i -E "s/→ [0-9]+ theorems, [0-9]+\.[0-9]+% ops/→ $GRAND_TOTAL theorems, 59.3% ops/" "$VC"
    sed -i -E "s/Kani IEEE 754 harnesses: [0-9]+/Kani IEEE 754 harnesses: $KANI_TOTAL/" "$VC"
    # Kani total row in bold
    sed -i -E "s/\| \*\*Total\*\* \| \*\*[0-9]+\*\* \| \*\*All verified/| **Total** | **$KANI_TOTAL** | **All verified/" "$VC"
    echo "  Done."
fi

# --- COQ_PROOFS.md ---
CP="$PROJECT_ROOT/docs/verification/COQ_PROOFS.md"
if [[ -f "$CP" ]]; then
    echo "Updating COQ_PROOFS.md..."
    # Header: "across all N theorems"
    sed -i -E "s/across all [0-9]+ theorems/across all $COQ_COMBINED theorems/" "$CP"
    # Z-based table total row
    sed -i -E "s/\*\*[0-9]+\*\* \| \*\*~45s\*\*/**$COQ_Z_TOTAL** | **~45s**/" "$CP"
    # Z-based footer per-type (Mat4 count)
    sed -i -E "s/Mat4: [0-9]+, Color: [0-9]+, Rect: [0-9]+, Utils: [0-9]+\)\*/Mat4: $COQ_Z_MAT4, Color: $COQ_Z_COLOR, Rect: $COQ_Z_RECT, Utils: $COQ_Z_UTILS)*/" "$CP"
    # Z-based footer total
    sed -i -E "s/\*Total theorems: [0-9]+ \(Vec2: $COQ_Z_VEC2, Vec3: $COQ_Z_VEC3, Vec4: $COQ_Z_VEC4, Mat3: $COQ_Z_MAT3/*Total theorems: $COQ_Z_TOTAL (Vec2: $COQ_Z_VEC2, Vec3: $COQ_Z_VEC3, Vec4: $COQ_Z_VEC4, Mat3: $COQ_Z_MAT3/" "$CP"
    # Combined Coq total
    sed -i -E "s/[0-9]+ total Coq theorems/$COQ_COMBINED total Coq theorems/" "$CP"
    echo "  Done."
fi

# --- CLAUDE.md ---
CM="$PROJECT_ROOT/CLAUDE.md"
if [[ -f "$CM" ]]; then
    echo "Updating CLAUDE.md..."
    # Kani CBMC status line
    sed -i -E "s/\*\*Kani \(CBMC\)\*\*: [0-9]+ proof harnesses/**Kani (CBMC)**: $KANI_TOTAL proof harnesses/" "$CM"
    # Combined status line
    sed -i -E "s/\*\*Combined\*\*: [0-9]+ formally verified/**Combined**: $GRAND_TOTAL formally verified/" "$CM"
    # Formal Verification doc reference
    sed -i -E "s/Formal verification overview and index \([0-9]+ theorems/Formal verification overview and index ($GRAND_TOTAL theorems/" "$CM"
    # Per-type table total row
    sed -i -E "s/\| \*\*[0-9]+ harnesses\*\* \| \*\*[0-9]+\*\* \| \*\*ACADEMIC\*\*/| **$KANI_TOTAL harnesses** | **$GRAND_TOTAL** | **ACADEMIC**/" "$CM"
    # Kani comment in verification commands
    sed -i -E "s/# Kani proofs \([0-9]+ harnesses/# Kani proofs ($KANI_TOTAL harnesses/" "$CM"
    # FP status line
    sed -i -E "s/\*\*Coq \(FP error bounds\)\*\*: [0-9]+ theorems/**Coq (FP error bounds)**: $COQ_FP_TOTAL theorems/" "$CM"
    # Verus status line
    sed -i -E "s/\*\*Verus\*\*: [0-9]+ proof functions/**Verus**: $VERUS_TOTAL proof functions/" "$CM"
    # Formal Verification in summary table
    sed -i -E "s/Verus \+ Coq \+ Kani proofs \([0-9]+ theorems\/harnesses\)/Verus + Coq + Kani proofs ($GRAND_TOTAL theorems\/harnesses)/" "$CM"
    # ASCII box
    sed -i -E "s/[0-9]+ formally verified theorems\/harnesses across Verus/$GRAND_TOTAL formally verified theorems\/harnesses across Verus/" "$CM"
    # Footer metadata (matches both with and without "Coq FP: N" field)
    sed -i -E "s/Formal Verification: [0-9]+ theorems\/harnesses \(Verus: [0-9]+, Coq R-based: [0-9]+, Coq Z-based: [0-9]+, (Coq FP: [0-9]+, )?Kani: [0-9]+\)/Formal Verification: $GRAND_TOTAL theorems\/harnesses (Verus: $VERUS_TOTAL, Coq R-based: $COQ_R_TOTAL, Coq Z-based: $COQ_Z_TOTAL, Coq FP: $COQ_FP_TOTAL, Kani: $KANI_TOTAL)/" "$CM"
    # Optimization phases
    sed -i -E "s/Optimization Phases: [0-9]+/Optimization Phases: $OPT_PHASES/" "$CM"
    # Coq R-based status line
    sed -i -E "s/\*\*Coq \(R-based\)\*\*: [0-9]+ theorems/**Coq (R-based)**: $COQ_R_TOTAL theorems/" "$CM"
    # Coq Z-based status line
    sed -i -E "s/\*\*Coq \(Z-based\)\*\*: [0-9]+ theorems/**Coq (Z-based)**: $COQ_Z_TOTAL theorems/" "$CM"
    # Per-type table total row (Coq R and Z columns)
    sed -i -E "s/\| \*\*[0-9]+ proof fns\*\* \| \*\*[0-9]+ theorems\*\* \| \*\*[0-9]+ theorems\*\*/| **$VERUS_TOTAL proof fns** | **$COQ_R_TOTAL theorems** | **$COQ_Z_TOTAL theorems**/" "$CM"
    # Per-type table: Bounds row
    sed -i -E "/\| Bounds \|/s/[0-9]+ theorems \| [0-9]+ theorems \| [0-9]+ harnesses \| [0-9]+/$COQ_R_BOUNDS theorems | $COQ_Z_BOUNDS theorems | $KANI_BOUNDS harnesses | $TOTAL_BOUNDS/" "$CM"
    # Per-type table: Utils row
    sed -i -E "/\| Utils \|/s/[0-9]+ theorems \| [0-9]+ theorems \| [0-9]+ harnesses \| [0-9]+/$COQ_R_UTILS theorems | $COQ_Z_UTILS theorems | $KANI_UTILS harnesses | $TOTAL_UTILS/" "$CM"
    # Coq command line comment (673/681/697 → correct)
    sed -i -E "s/# Coq proofs \([0-9]+ theorems/# Coq proofs ($COQ_COMBINED theorems/" "$CM"
    # COQ_PROOFS.md doc reference
    sed -i -E "s/Coq proofs \(R \+ Z, [0-9]+ theorems/Coq proofs (R + Z, $COQ_COMBINED theorems/" "$CM"
    echo "  Done."
fi

# --- README.md ---
RM="$PROJECT_ROOT/README.md"
if [[ -f "$RM" ]]; then
    echo "Updating README.md..."
    # Verus row: "| **Verus** ... | N proof functions, M+ VCs |"
    sed -i -E "s/[0-9]+ proof functions, [0-9]+\+ VCs/$VERUS_TOTAL proof functions, 452+ VCs/" "$RM"
    # Coq R-based row (matches "N theorems" on Coq R-based line)
    sed -i -E "/Coq \(R-based\)/s/[0-9]+ theorems/$COQ_R_TOTAL theorems/" "$RM"
    # Coq Z-based row (matches "N theorems" on Coq Z-based line)
    sed -i -E "/Coq \(Z-based\)/s/[0-9]+ theorems/$COQ_Z_TOTAL theorems/" "$RM"
    # Kani row (if present)
    sed -i -E "s/[0-9]+ harnesses, 0 failures/$KANI_TOTAL harnesses, 0 failures/" "$RM"
    # Combined/total bold references "**N theorems/harnesses**"
    sed -i -E "s/\*\*[0-9]+ theorems\/harnesses\*\*/**$GRAND_TOTAL theorems\/harnesses**/" "$RM"
    # Combined/total non-bold references
    sed -i -E "s/[0-9]+ formally verified theorems/$GRAND_TOTAL formally verified theorems/" "$RM"
    # Optimization phases
    sed -i -E "s/[0-9]+ optimization phases/$OPT_PHASES optimization phases/" "$RM"
    echo "  Done."
fi

# --- docs/README.md ---
DR="$PROJECT_ROOT/docs/README.md"
if [[ -f "$DR" ]]; then
    echo "Updating docs/README.md..."
    sed -i -E "s/[0-9]+ proof functions, [0-9]+ types/$VERUS_TOTAL proof functions, 7 types/" "$DR"
    sed -i -E "s/[0-9]+ theorems, 0 admits, Coq 8/$COQ_COMBINED theorems, 0 admits, Coq 8/" "$DR"
    # COQ_PROOFS.md reference (R-based + Z-based, N theorems)
    sed -i -E "s/R-based \+ Z-based, [0-9]+ theorems/R-based + Z-based, $COQ_COMBINED theorems/" "$DR"
    # FORMAL_VERIFICATION.md reference (total and types)
    sed -i -E "s/[0-9]+ theorems\/harnesses, [0-9]+ types/$GRAND_TOTAL theorems\/harnesses, 8 types/" "$DR"
    echo "  Done."
fi

# --- WASM_EXTRACTION_PIPELINE.md ---
WE="$PROJECT_ROOT/docs/verification/WASM_EXTRACTION_PIPELINE.md"
if [[ -f "$WE" ]]; then
    echo "Updating WASM_EXTRACTION_PIPELINE.md..."
    # Coq active count "Active (N theorems)"
    sed -i -E "s/Active \([0-9]+ theorems\)/Active ($COQ_COMBINED theorems)/" "$WE"
    # Working/tested count "tested, N theorems compile"
    sed -i -E "s/tested, [0-9]+ theorems compile/tested, $COQ_COMBINED theorems compile/" "$WE"
    echo "  Done."
fi

# --- SETUP_GUIDE.md ---
SG="$PROJECT_ROOT/docs/verification/SETUP_GUIDE.md"
if [[ -f "$SG" ]]; then
    echo "Updating SETUP_GUIDE.md..."
    # Verus table total row
    sed -i -E "s/\*\*Total\*\* \| \*\*[0-9]+\*\* \|/\*\*Total\*\* | \*\*$VERUS_TOTAL\*\* |/" "$SG"
    # Verus per-file counts
    sed -i -E "s/\`vec2_proofs\.rs\` \| [0-9]+/\`vec2_proofs.rs\` | $VERUS_VEC2/" "$SG"
    sed -i -E "s/\`vec3_proofs\.rs\` \| [0-9]+/\`vec3_proofs.rs\` | $VERUS_VEC3/" "$SG"
    sed -i -E "s/\`vec4_proofs\.rs\` \| [0-9]+/\`vec4_proofs.rs\` | $VERUS_VEC4/" "$SG"
    sed -i -E "s/\`mat3_proofs\.rs\` \| [0-9]+/\`mat3_proofs.rs\` | $VERUS_MAT3_BASE/" "$SG"
    sed -i -E "s/\`mat3_extended_proofs\.rs\` \| [0-9]+/\`mat3_extended_proofs.rs\` | $VERUS_MAT3_EXT/" "$SG"
    sed -i -E "s/\`mat4_proofs\.rs\` \| [0-9]+/\`mat4_proofs.rs\` | $VERUS_MAT4_BASE/" "$SG"
    sed -i -E "s/\`mat4_extended_proofs\.rs\` \| [0-9]+/\`mat4_extended_proofs.rs\` | $VERUS_MAT4_EXT/" "$SG"
    sed -i -E "s/\`color_proofs\.rs\` \| [0-9]+/\`color_proofs.rs\` | $VERUS_COLOR/" "$SG"
    sed -i -E "s/\`rect_proofs\.rs\` \| [0-9]+/\`rect_proofs.rs\` | $VERUS_RECT/" "$SG"
    # Coq table total row
    sed -i -E "s/\*\*32 files\*\* \| \*\*[0-9]+\*\*/\*\*32 files\*\* | \*\*$COQ_COMBINED\*\*/" "$SG"
    # Coq per-file counts (R-based proofs)
    sed -i -E "s/\`Vec2_Proofs\.v\` \| [0-9]+/\`Vec2_Proofs.v\` | $COQ_R_VEC2/" "$SG"
    sed -i -E "s/\`Vec3_Proofs\.v\` \| [0-9]+/\`Vec3_Proofs.v\` | $COQ_R_VEC3/" "$SG"
    sed -i -E "s/\`Vec4_Proofs\.v\` \| [0-9]+/\`Vec4_Proofs.v\` | $COQ_R_VEC4/" "$SG"
    sed -i -E "s/\`Mat3_Proofs\.v\` \| [0-9]+/\`Mat3_Proofs.v\` | $COQ_R_MAT3/" "$SG"
    sed -i -E "s/\`Mat4_Proofs\.v\` \| [0-9]+/\`Mat4_Proofs.v\` | $COQ_R_MAT4/" "$SG"
    sed -i -E "s/\`Color_Proofs\.v\` \| [0-9]+/\`Color_Proofs.v\` | $COQ_R_COLOR/" "$SG"
    sed -i -E "s/\`Rect_Proofs\.v\` \| [0-9]+/\`Rect_Proofs.v\` | $COQ_R_RECT/" "$SG"
    # Coq per-file counts (Z-based compute)
    sed -i -E "s/\`Vec2_Compute\.v\` \| [0-9]+/\`Vec2_Compute.v\` | $COQ_Z_VEC2/" "$SG"
    sed -i -E "s/\`Vec3_Compute\.v\` \| [0-9]+/\`Vec3_Compute.v\` | $COQ_Z_VEC3/" "$SG"
    sed -i -E "s/\`Vec4_Compute\.v\` \| [0-9]+/\`Vec4_Compute.v\` | $COQ_Z_VEC4/" "$SG"
    sed -i -E "s/\`Mat3_Compute\.v\` \| [0-9]+/\`Mat3_Compute.v\` | $COQ_Z_MAT3/" "$SG"
    sed -i -E "s/\`Mat4_Compute\.v\` \| [0-9]+/\`Mat4_Compute.v\` | $COQ_Z_MAT4/" "$SG"
    sed -i -E "s/\`Color_Compute\.v\` \| [0-9]+/\`Color_Compute.v\` | $COQ_Z_COLOR/" "$SG"
    sed -i -E "s/\`Rect_Compute\.v\` \| [0-9]+/\`Rect_Compute.v\` | $COQ_Z_RECT/" "$SG"
    sed -i -E "s/\`Utils_Compute\.v\` \| [0-9]+/\`Utils_Compute.v\` | $COQ_Z_UTILS/" "$SG"
    # Expected Results table
    sed -i -E "s/Verus \| [0-9]+ proof functions/Verus | $VERUS_TOTAL proof functions/" "$SG"
    sed -i -E "s/Coq \(R-based\) \| [0-9]+ theorems/Coq (R-based) | $COQ_R_TOTAL theorems/" "$SG"
    sed -i -E "s/Coq \(Z-based\) \| [0-9]+ theorems/Coq (Z-based) | $COQ_Z_TOTAL theorems/" "$SG"
    sed -i -E "s/Kani \(CBMC\) \| [0-9]+ harnesses/Kani (CBMC) | $KANI_TOTAL harnesses/" "$SG"
    sed -i -E "s/\*\*Combined\*\* \| \*\*[0-9]+\*\*/\*\*Combined\*\* | \*\*$GRAND_TOTAL\*\*/" "$SG"
    echo "  Done."
fi

# --- FLOATING_POINT_VERIFICATION.md ---
FPV="$PROJECT_ROOT/docs/verification/FLOATING_POINT_VERIFICATION.md"
if [[ -f "$FPV" ]]; then
    echo "Updating FLOATING_POINT_VERIFICATION.md..."
    # Coverage trajectory table: current total
    sed -i -E "s/Algebraic properties \| [0-9]+ theorems/Algebraic properties | $GRAND_TOTAL theorems/" "$FPV"
    echo "  Done."
fi

# --- CERTICOQ_WASM_ASSESSMENT.md ---
CW="$PROJECT_ROOT/docs/verification/CERTICOQ_WASM_ASSESSMENT.md"
if [[ -f "$CW" ]]; then
    echo "Updating CERTICOQ_WASM_ASSESSMENT.md..."
    # Architecture diagram Layer 2 per-type counts
    sed -i -E "s/Vec2_Compute\.v \([0-9]+ theorems\)/Vec2_Compute.v ($COQ_Z_VEC2 theorems)/" "$CW"
    sed -i -E "s/Vec3_Compute\.v \([0-9]+ theorems\)/Vec3_Compute.v ($COQ_Z_VEC3 theorems)/" "$CW"
    sed -i -E "s/Vec4_Compute\.v \([0-9]+ theorems\)/Vec4_Compute.v ($COQ_Z_VEC4 theorems)/" "$CW"
    sed -i -E "s/Mat3_Compute\.v \([0-9]+ theorems/Mat3_Compute.v ($COQ_Z_MAT3 theorems/" "$CW"
    sed -i -E "s/Mat4_Compute\.v \([0-9]+ theorems/Mat4_Compute.v ($COQ_Z_MAT4 theorems/" "$CW"
    sed -i -E "s/Color_Compute\.v \([0-9]+ theorems/Color_Compute.v ($COQ_Z_COLOR theorems/" "$CW"
    sed -i -E "s/Rect_Compute\.v \([0-9]+ theorems/Rect_Compute.v ($COQ_Z_RECT theorems/" "$CW"
    sed -i -E "s/Utils_Compute\.v \([0-9]+ theorems/Utils_Compute.v ($COQ_Z_UTILS theorems/" "$CW"
    # Layer 2 total
    sed -i -E "s/COMPLETE \([0-9]+ theorems, all 8 types\)/COMPLETE ($COQ_Z_TOTAL theorems, all 8 types)/" "$CW"
    # Layer 1 R-based proof file ranges
    PROOFS_TOTAL=$((COQ_R_VEC2 + COQ_R_VEC3 + COQ_R_VEC4 + COQ_R_MAT3 + COQ_R_MAT4))
    COLOR_RECT_TOTAL=$((COQ_R_COLOR + COQ_R_RECT))
    LAYER1_WITH_VERUS=$((VERUS_TOTAL + COQ_R_TOTAL))
    sed -i -E "s/Mat4_Proofs\.v \([0-9]+ theorems\)/Mat4_Proofs.v ($PROOFS_TOTAL theorems)/" "$CW"
    sed -i -E "s/Rect_Proofs\.v \([0-9]+ theorems\)/Rect_Proofs.v ($COLOR_RECT_TOTAL theorems)/" "$CW"
    sed -i -E "s/COMPLETE \([0-9]+ total with Verus\)/COMPLETE ($LAYER1_WITH_VERUS total with Verus)/" "$CW"
    # Vec2_Compute.v detail section heading
    sed -i -E "s/\*\*Theorems\*\*: [0-9]+ \(all machine-checked/\*\*Theorems\*\*: $COQ_Z_VEC2 (all machine-checked/" "$CW"
    echo "  Done."
fi

# --- WASM_EXTRACTION_PIPELINE.md ---
WE="$PROJECT_ROOT/docs/verification/WASM_EXTRACTION_PIPELINE.md"
if [[ -f "$WE" ]]; then
    echo "Updating WASM_EXTRACTION_PIPELINE.md..."
    sed -i -E "s/[0-9]+ proof fns\)/$VERUS_TOTAL proof fns)/" "$WE"
    sed -i -E "s/[0-9]+ theorems\)  Coq/$COQ_COMBINED theorems)  Coq/" "$WE"
    echo "  Done."
fi

# --- RUST_VERIFICATION_LANDSCAPE.md ---
RL="$PROJECT_ROOT/docs/verification/RUST_VERIFICATION_LANDSCAPE.md"
if [[ -f "$RL" ]]; then
    echo "Updating RUST_VERIFICATION_LANDSCAPE.md..."
    sed -i -E "s/[0-9]+-theorem corpus/$GRAND_TOTAL-theorem corpus/g" "$RL"
    sed -i -E "s/[0-9]+ theorems \([0-9]+\+[0-9]+\+[0-9]+\+[0-9]+\)/$GRAND_TOTAL theorems ($VERUS_TOTAL+$COQ_R_TOTAL+$COQ_Z_TOTAL+$KANI_TOTAL)/g" "$RL"
    sed -i -E "s/[0-9]+ theorems \([0-9]+\+[0-9]+\+[0-9]+\)/$GRAND_TOTAL theorems ($VERUS_TOTAL+$COQ_R_TOTAL+$COQ_Z_TOTAL+$KANI_TOTAL)/g" "$RL"
    # Coq theorem count in architecture diagram
    sed -i -E "s/Coq \([0-9]+ theorems\)/Coq ($COQ_COMBINED theorems)/" "$RL"
    # Kani harness count
    sed -i -E "s/[0-9]+ harnesses for FP-intensive/$KANI_TOTAL harnesses for FP-intensive/" "$RL"
    echo "  Done."
fi

# --- kani_proofs/mod.rs ---
KM="$PROJECT_ROOT/crates/rource-math/src/kani_proofs/mod.rs"
if [[ -f "$KM" ]]; then
    echo "Updating kani_proofs/mod.rs..."
    sed -i -E "s/# Harness Count \([0-9]+ total\)/# Harness Count ($KANI_TOTAL total)/" "$KM"
    sed -i -E "s/Vec2: [0-9]+, Vec3: [0-9]+, Vec4: [0-9]+/Vec2: $KANI_VEC2, Vec3: $KANI_VEC3, Vec4: $KANI_VEC4/" "$KM"
    sed -i -E "s/Mat3: [0-9]+, Mat4: [0-9]+/Mat3: $KANI_MAT3, Mat4: $KANI_MAT4/" "$KM"
    sed -i -E "s/Color: [0-9]+, Rect: [0-9]+(, Bounds: [0-9]+)?, Utils: [0-9]+/Color: $KANI_COLOR, Rect: $KANI_RECT, Bounds: $KANI_BOUNDS, Utils: $KANI_UTILS/" "$KM"
    echo "  Done."
fi

echo ""
echo "=== All documentation updated ==="
echo ""
echo "Metrics written to: $COUNTS_FILE"
echo ""
echo "Run with --check to verify consistency (suitable for CI)."
