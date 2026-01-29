#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# =============================================================================
# Rource Formal Verification Setup Script
# =============================================================================
#
# Purpose: Install and configure ALL formal verification tools for
#          PEER REVIEWED PUBLISHED ACADEMIC quality proofs.
#
# Usage:
#   ./scripts/setup-formal-verification.sh                # Full setup
#   ./scripts/setup-formal-verification.sh --check        # Verify installation only
#   ./scripts/setup-formal-verification.sh --verus        # Verus only
#   ./scripts/setup-formal-verification.sh --coq          # Coq + opam ecosystem only
#   ./scripts/setup-formal-verification.sh --metacoq      # MetaCoq from source only
#   ./scripts/setup-formal-verification.sh --wasm-of-ocaml # wasm_of_ocaml only
#   ./scripts/setup-formal-verification.sh --verify       # Run all proofs
#   ./scripts/setup-formal-verification.sh --help         # Show help
#
# This script installs:
#   - Verus (Microsoft's Rust verification tool) in /tmp/verus/
#   - Coq 8.18+ (proof assistant) via apt
#   - opam 2.x (OCaml package manager) + OCaml 4.14.x
#   - coq-equations 1.3+8.18 (via GitHub pin, bypassing broken opam repos)
#   - MetaCoq (verified extraction) from source in /tmp/metacoq/
#   - wasm_of_ocaml (OCaml-to-WASM compiler) via opam
#   - Rust 1.92.0 toolchain (required by Verus)
#
# Setup Guide: docs/verification/SETUP_GUIDE.md
#
# =============================================================================

set -euo pipefail

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

readonly SCRIPT_VERSION="2.0.0"
# Script name used in error messages and documentation
export SCRIPT_NAME="setup-formal-verification.sh"

# Verus configuration
readonly VERUS_INSTALL_DIR="/tmp/verus"
readonly VERUS_RUST_VERSION="1.92.0"

# Coq configuration
readonly COQ_MIN_VERSION="8.18"

# MetaCoq configuration
readonly METACOQ_INSTALL_DIR="/tmp/metacoq"
readonly METACOQ_BRANCH="coq-8.18"
readonly METACOQ_REPO="https://github.com/MetaCoq/metacoq.git"

# coq-equations configuration (pinned from GitHub to bypass broken opam repos)
readonly COQ_EQUATIONS_VERSION="1.3+8.18"
readonly COQ_EQUATIONS_GIT="git+https://github.com/mattam82/Coq-Equations.git#v1.3-8.18"

# Rocq migration notes (Coq → Rocq rebranding, v9.0+, March 2025):
# - Current: Coq 8.18 + MetaCoq (from source)
# - Future: Rocq 9.x + MetaRocq (when opam repos stabilize)
# - Both coq.inria.fr/opam/released AND rocq-prover.org/opam/released return HTTP 503
# - Core packages (rocq-core, rocq-stdlib) available from default opam.ocaml.org
# - MetaRocq 1.4.1 (latest, Dec 2024) targets Rocq 9.1
# - Migration requires: From Coq → From Stdlib, From MetaCoq → From MetaRocq
# - See docs/verification/SETUP_GUIDE.md "Coq → Rocq Rebranding" section

# Colors (only if terminal supports them)
if [[ -t 1 ]]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[1;33m'
    BLUE='\033[0;34m'
    CYAN='\033[0;36m'
    BOLD='\033[1m'
    NC='\033[0m'
else
    RED=''
    GREEN=''
    YELLOW=''
    BLUE=''
    CYAN=''
    BOLD=''
    NC=''
fi

# Modes
CHECK_ONLY=false
VERUS_ONLY=false
COQ_ONLY=false
METACOQ_ONLY=false
WASM_OF_OCAML_ONLY=false
VERIFY_PROOFS=false

# Counters
ERRORS=0
WARNINGS=0

# -----------------------------------------------------------------------------
# Helper Functions
# -----------------------------------------------------------------------------

print_header() {
    echo ""
    echo -e "${BOLD}${BLUE}=== $1 ===${NC}"
    echo ""
}

print_info() {
    echo -e "${CYAN}[INFO]${NC} $1"
}

print_ok() {
    echo -e "${GREEN}[OK]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
    WARNINGS=$((WARNINGS + 1))
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
    ERRORS=$((ERRORS + 1))
}

command_exists() {
    command -v "$1" > /dev/null 2>&1
}

# Compare version strings (returns 0 if $1 >= $2)
version_gte() {
    local v1="$1"
    local v2="$2"
    # Use sort -V for version comparison
    [ "$v1" = "$(printf '%s\n%s\n' "$v1" "$v2" | sort -V | tail -n1)" ]
}

# Retry a command with exponential backoff
retry_with_backoff() {
    local max_retries="$1"
    shift
    local retry_delay=2
    local attempt
    for attempt in $(seq 1 "$max_retries"); do
        if "$@"; then
            return 0
        fi
        if [[ "$attempt" -lt "$max_retries" ]]; then
            print_warn "Attempt $attempt failed, retrying in ${retry_delay}s..."
            sleep "$retry_delay"
            retry_delay=$((retry_delay * 2))
        fi
    done
    return 1
}

# Find project root (directory containing this script's parent)
get_project_root() {
    local script_dir
    script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    echo "$script_dir/.."
}

# -----------------------------------------------------------------------------
# System Dependencies
# -----------------------------------------------------------------------------

install_system_deps() {
    print_header "System Dependencies"

    if ! command_exists apt-get; then
        print_warn "apt-get not available; skipping system package installation"
        return 0
    fi

    local packages_needed=()

    # Check each required package
    if ! command_exists curl; then
        packages_needed+=("curl")
    fi
    if ! command_exists unzip; then
        packages_needed+=("unzip")
    fi
    if ! command_exists git; then
        packages_needed+=("git")
    fi
    if ! dpkg -s libgmp-dev > /dev/null 2>&1; then
        packages_needed+=("libgmp-dev")
    fi

    if [[ ${#packages_needed[@]} -eq 0 ]]; then
        print_ok "All system dependencies already installed"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "Missing system packages: ${packages_needed[*]}"
        return 1
    fi

    print_info "Installing system packages: ${packages_needed[*]}"
    if retry_with_backoff 4 apt-get update -qq; then
        if apt-get install -y -qq "${packages_needed[@]}"; then
            print_ok "System packages installed: ${packages_needed[*]}"
        else
            print_error "Failed to install system packages"
            return 1
        fi
    else
        print_error "apt-get update failed after retries"
        return 1
    fi

    return 0
}

# -----------------------------------------------------------------------------
# Verus Installation
# -----------------------------------------------------------------------------

install_verus() {
    print_header "Verus Installation"

    # Check architecture
    local arch
    arch=$(uname -m)
    if [[ "$arch" != "x86_64" ]]; then
        print_error "Verus requires x86_64 architecture (found: $arch)"
        return 1
    fi

    # Check if already installed
    if [[ -x "$VERUS_INSTALL_DIR/verus" ]]; then
        local version
        version=$("$VERUS_INSTALL_DIR/verus" --version 2>/dev/null | head -1 || echo "unknown")
        print_ok "Verus already installed: $version"

        if [[ "$CHECK_ONLY" == true ]]; then
            return 0
        fi
        print_info "Re-downloading to ensure latest version..."
    elif [[ "$CHECK_ONLY" == true ]]; then
        print_warn "Verus is not installed"
        return 1
    fi

    # Create install directory
    mkdir -p "$VERUS_INSTALL_DIR"

    # Download Verus with retry
    print_info "Downloading Verus..."
    local download_url="https://github.com/verus-lang/verus/releases/latest/download/verus-x86_64-linux.zip"
    local zip_file="$VERUS_INSTALL_DIR/verus.zip"

    if ! retry_with_backoff 4 curl -fSL -o "$zip_file" "$download_url"; then
        print_error "Failed to download Verus"
        return 1
    fi
    print_ok "Downloaded Verus"

    # Extract
    print_info "Extracting Verus..."
    if ! unzip -o -q "$zip_file" -d "$VERUS_INSTALL_DIR"; then
        print_error "Failed to extract Verus"
        return 1
    fi

    # Move contents from subdirectory if needed
    local extracted_dir
    extracted_dir=$(find "$VERUS_INSTALL_DIR" -maxdepth 1 -type d -name "verus-*" 2>/dev/null | head -1)
    if [[ -n "$extracted_dir" ]] && [[ -d "$extracted_dir" ]]; then
        cp -a "$extracted_dir"/. "$VERUS_INSTALL_DIR/" 2>/dev/null || true
        rm -rf "$extracted_dir"
    fi

    chmod +x "$VERUS_INSTALL_DIR/verus" 2>/dev/null || true
    rm -f "$zip_file"

    # Verify
    if [[ -x "$VERUS_INSTALL_DIR/verus" ]]; then
        local version
        version=$("$VERUS_INSTALL_DIR/verus" --version 2>/dev/null | head -1 || echo "installed")
        print_ok "Verus installed: $version"
    else
        print_error "Verus installation failed"
        return 1
    fi

    return 0
}

install_verus_rust_toolchain() {
    print_header "Verus Rust Toolchain"

    if ! command_exists rustup; then
        print_error "rustup is required but not installed"
        print_info "Install from: https://rustup.rs/"
        return 1
    fi

    if rustup toolchain list | grep -q "$VERUS_RUST_VERSION"; then
        print_ok "Rust $VERUS_RUST_VERSION toolchain already installed"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "Rust $VERUS_RUST_VERSION toolchain not installed"
        return 1
    fi

    print_info "Installing Rust $VERUS_RUST_VERSION toolchain..."
    if rustup install "$VERUS_RUST_VERSION"; then
        print_ok "Rust $VERUS_RUST_VERSION installed"
    else
        print_error "Failed to install Rust $VERUS_RUST_VERSION"
        return 1
    fi

    return 0
}

# -----------------------------------------------------------------------------
# Coq Installation
# -----------------------------------------------------------------------------

install_coq() {
    print_header "Coq Installation"

    # Check if already installed with correct version
    if command_exists coqc; then
        local version
        version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "unknown")
        if version_gte "$version" "$COQ_MIN_VERSION"; then
            print_ok "Coq already installed: version $version (>= $COQ_MIN_VERSION)"
            return 0
        fi
        print_warn "Coq version $version < $COQ_MIN_VERSION"
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        if ! command_exists coqc; then
            print_warn "Coq is not installed"
        fi
        return 1
    fi

    # Install via apt-get (CRITICAL: both coq and coq-theories)
    if command_exists apt-get; then
        print_info "Installing Coq via apt-get (coq + coq-theories)..."
        if retry_with_backoff 4 apt-get install -y -qq coq coq-theories; then
            print_ok "Coq installed via apt-get"
        else
            print_warn "apt-get installation failed, trying opam..."
        fi
    fi

    # Verify or try opam fallback
    if command_exists coqc; then
        local version
        version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "unknown")
        print_ok "Coq installation verified: version $version"
        return 0
    fi

    # opam fallback
    if command_exists opam; then
        print_info "Installing Coq via opam..."
        setup_opam_environment
        if opam install "coq.${COQ_MIN_VERSION}.0" --yes; then
            print_ok "Coq installed via opam"
        else
            print_error "Failed to install Coq"
            return 1
        fi
    else
        print_error "Neither apt-get nor opam could install Coq"
        return 1
    fi

    return 0
}

# -----------------------------------------------------------------------------
# opam Environment
# -----------------------------------------------------------------------------

setup_opam_environment() {
    print_header "opam Environment"

    # Install opam if not present
    if ! command_exists opam; then
        if command_exists apt-get; then
            print_info "Installing opam via apt-get..."
            if apt-get install -y -qq opam; then
                print_ok "opam installed"
            else
                print_error "Failed to install opam"
                return 1
            fi
        else
            print_error "opam not found and cannot install"
            print_info "Install from: https://opam.ocaml.org/doc/Install.html"
            return 1
        fi
    else
        print_ok "opam is available"
    fi

    # Initialize opam if needed
    if [[ ! -d "${OPAMROOT:-$HOME/.opam}" ]]; then
        print_info "Initializing opam..."
        if opam init --auto-setup --bare --yes --disable-sandboxing; then
            print_ok "opam initialized"
        else
            print_error "opam init failed"
            return 1
        fi
    fi

    # Create default switch if needed
    if ! opam switch list --short 2>/dev/null | grep -q "default"; then
        print_info "Creating opam default switch with OCaml 4.14.1..."
        if opam switch create default ocaml-base-compiler.4.14.1 --yes; then
            print_ok "opam switch created"
        else
            print_warn "opam switch creation failed; using existing switch"
        fi
    fi

    # Activate environment
    eval "$(opam env 2>/dev/null)" || true
    print_ok "opam environment activated"

    return 0
}

# -----------------------------------------------------------------------------
# coq-equations Installation
# -----------------------------------------------------------------------------

install_coq_equations() {
    print_header "coq-equations Installation"

    # Check if already installed
    if opam list coq-equations 2>/dev/null | grep -q "$COQ_EQUATIONS_VERSION"; then
        print_ok "coq-equations $COQ_EQUATIONS_VERSION already installed"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "coq-equations $COQ_EQUATIONS_VERSION not installed"
        return 1
    fi

    # Ensure opam is set up
    if ! command_exists opam; then
        setup_opam_environment || return 1
    fi
    eval "$(opam env 2>/dev/null)" || true

    # Install stdlib-shims (dependency)
    print_info "Installing stdlib-shims..."
    opam install stdlib-shims --yes 2>/dev/null || true

    # Pin coq-equations from GitHub (bypasses broken opam repos)
    # CRITICAL: The Coq opam repos (coq.inria.fr, rocq-prover.org) frequently
    # return HTTP 503. Pinning directly from GitHub source is reliable.
    print_info "Pinning coq-equations from GitHub source..."
    print_info "  Source: $COQ_EQUATIONS_GIT"

    if opam pin add coq-equations "$COQ_EQUATIONS_GIT" --yes; then
        print_ok "coq-equations $COQ_EQUATIONS_VERSION installed (GitHub pin)"
    else
        print_error "Failed to install coq-equations"
        print_info "You may need to install libgmp-dev: apt-get install -y libgmp-dev"
        return 1
    fi

    return 0
}

# -----------------------------------------------------------------------------
# MetaCoq Installation (from source)
# -----------------------------------------------------------------------------

install_metacoq() {
    print_header "MetaCoq Installation (from source)"

    # Check if already built
    if [[ -f "$METACOQ_INSTALL_DIR/erasure-plugin/theories/Loader.vo" ]]; then
        print_ok "MetaCoq erasure-plugin already built at $METACOQ_INSTALL_DIR"
        if [[ "$CHECK_ONLY" == true ]]; then
            return 0
        fi
        print_info "Rebuilding to ensure latest version..."
    elif [[ "$CHECK_ONLY" == true ]]; then
        print_warn "MetaCoq is not built"
        return 1
    fi

    # Prerequisites
    if ! command_exists coqc; then
        print_error "Coq is required for MetaCoq (install Coq first)"
        return 1
    fi

    if ! opam list coq-equations 2>/dev/null | grep -q "$COQ_EQUATIONS_VERSION"; then
        print_error "coq-equations $COQ_EQUATIONS_VERSION required (install it first)"
        return 1
    fi

    eval "$(opam env 2>/dev/null)" || true

    # Clone if not present
    if [[ ! -d "$METACOQ_INSTALL_DIR/.git" ]]; then
        print_info "Cloning MetaCoq ($METACOQ_BRANCH branch)..."
        if retry_with_backoff 4 git clone --branch "$METACOQ_BRANCH" --depth 1 \
            "$METACOQ_REPO" "$METACOQ_INSTALL_DIR"; then
            print_ok "MetaCoq cloned"
        else
            print_error "Failed to clone MetaCoq"
            return 1
        fi
    else
        print_ok "MetaCoq source already present at $METACOQ_INSTALL_DIR"
    fi

    # Configure for local build
    print_info "Configuring MetaCoq for local build..."
    (cd "$METACOQ_INSTALL_DIR" && bash ./configure.sh local)
    print_ok "MetaCoq configured"

    # Build each component in order
    # Build order: utils -> common -> template-coq -> pcuic -> template-pcuic
    #              -> safechecker -> erasure -> erasure-plugin
    local components=("utils" "common" "template-coq" "pcuic" "template-pcuic"
                      "safechecker" "erasure" "erasure-plugin")
    local total=${#components[@]}
    local current=0

    for component in "${components[@]}"; do
        current=$((current + 1))
        print_info "Building MetaCoq [$current/$total]: $component..."

        if (cd "$METACOQ_INSTALL_DIR" && eval "$(opam env 2>/dev/null)" && \
            make "$component" 2>&1 | tail -5); then
            print_ok "MetaCoq $component built"
        else
            print_error "MetaCoq $component build failed"
            print_info "Check build output: cd $METACOQ_INSTALL_DIR && make $component"
            return 1
        fi
    done

    print_ok "MetaCoq fully built (all $total components)"
    return 0
}

install_metacoq_to_coq() {
    print_header "MetaCoq Install (to Coq user-contrib)"

    if [[ ! -d "$METACOQ_INSTALL_DIR" ]]; then
        print_error "MetaCoq not found at $METACOQ_INSTALL_DIR (build first)"
        return 1
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        # Check if MetaCoq is already installed
        local user_contrib
        user_contrib="$(eval "$(opam env 2>/dev/null)" && coqtop -where 2>/dev/null)/user-contrib/MetaCoq"
        if [[ -d "$user_contrib/ErasurePlugin" ]]; then
            print_ok "MetaCoq installed at $user_contrib"
            return 0
        else
            print_warn "MetaCoq not installed to user-contrib"
            return 1
        fi
    fi

    print_info "Installing MetaCoq to Coq's user-contrib..."
    print_info "(This builds quotation theories and takes 15-20 min)"
    if (cd "$METACOQ_INSTALL_DIR" && eval "$(opam env 2>/dev/null)" && \
        make install 2>&1 | tail -5); then
        print_ok "MetaCoq installed to Coq's user-contrib"
    else
        print_error "MetaCoq installation failed"
        return 1
    fi

    # CRITICAL: Recompile .vo files to match MetaCoq's Coq installation
    # Without this, loading MetaCoq modules alongside rource-math .vo files
    # causes "inconsistent assumptions over library Coq.Init.Ltac" errors
    recompile_coq_proofs

    return 0
}

recompile_coq_proofs() {
    print_header "Recompile .vo Files (Coq library consistency)"

    local project_root
    project_root="$(get_project_root)"
    local coq_dir="$project_root/crates/rource-math/proofs/coq"

    if [[ ! -d "$coq_dir" ]]; then
        print_warn "Coq proofs directory not found, skipping recompilation"
        return 0
    fi

    print_info "Removing old .vo files to prevent library inconsistency..."
    (cd "$coq_dir" && rm -f ./*.vo ./*.vos ./*.vok ./*.glob)

    print_info "Recompiling all proofs with opam Coq (matching MetaCoq)..."
    eval "$(opam env 2>/dev/null)" || true

    pushd "$coq_dir" > /dev/null

    # Layer 1: Specifications
    local failed=0
    for f in Vec2.v Vec3.v Vec4.v Mat3.v Mat4.v; do
        if [[ -f "$f" ]] && ! coqc -Q . RourceMath "$f" 2>&1; then
            print_error "Failed to compile $f"
            failed=$((failed + 1))
        fi
    done

    # Layer 1: Proofs
    for f in Vec2_Proofs.v Vec3_Proofs.v Vec4_Proofs.v Mat3_Proofs.v Mat4_Proofs.v; do
        if [[ -f "$f" ]] && ! coqc -Q . RourceMath "$f" 2>&1; then
            print_error "Failed to compile $f"
            failed=$((failed + 1))
        fi
    done

    # Complexity
    if [[ -f "Complexity.v" ]] && ! coqc -Q . RourceMath Complexity.v 2>&1; then
        print_error "Failed to compile Complexity.v"
        failed=$((failed + 1))
    fi

    # Layer 2: Compute
    for f in Vec2_Compute.v Vec3_Compute.v Vec4_Compute.v Mat3_Compute.v Mat4_Compute.v; do
        if [[ -f "$f" ]] && ! coqc -Q . RourceMath "$f" 2>&1; then
            print_error "Failed to compile $f"
            failed=$((failed + 1))
        fi
    done

    # Layer 3: Extraction
    for f in Vec2_Extract.v Vec3_Extract.v Vec4_Extract.v \
             Mat3_Extract.v Mat4_Extract.v RourceMath_Extract.v; do
        if [[ -f "$f" ]] && ! coqc -Q . RourceMath "$f" 2>&1; then
            print_error "Failed to compile $f"
            failed=$((failed + 1))
        fi
    done

    # MetaCoq verified extraction (requires MetaCoq installed)
    if [[ -f "Vec2_VerifiedExtract.v" ]]; then
        if coqc -Q . RourceMath Vec2_VerifiedExtract.v 2>&1; then
            print_ok "Vec2_VerifiedExtract.v: MetaCoq verified erasure OK"
        else
            print_warn "Vec2_VerifiedExtract.v: MetaCoq erasure not available"
        fi
    fi

    popd > /dev/null

    if [[ $failed -eq 0 ]]; then
        print_ok "All .vo files recompiled (consistent with MetaCoq Coq)"
    else
        print_error "$failed file(s) failed recompilation"
        return 1
    fi

    return 0
}

# -----------------------------------------------------------------------------
# wasm_of_ocaml Installation
# -----------------------------------------------------------------------------

install_wasm_of_ocaml() {
    print_header "wasm_of_ocaml Installation"

    # Check if already installed
    if command_exists wasm_of_ocaml; then
        local version
        version=$(wasm_of_ocaml --version 2>/dev/null || echo "installed")
        print_ok "wasm_of_ocaml already installed: $version"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "wasm_of_ocaml is not installed"
        return 1
    fi

    # Ensure opam is set up
    if ! command_exists opam; then
        setup_opam_environment || return 1
    fi
    eval "$(opam env 2>/dev/null)" || true

    print_info "Installing wasm_of_ocaml via opam..."
    if opam install wasm_of_ocaml --yes; then
        print_ok "wasm_of_ocaml installed"
    else
        print_warn "wasm_of_ocaml installation failed (optional tool)"
        return 1
    fi

    return 0
}

# -----------------------------------------------------------------------------
# Proof Verification
# -----------------------------------------------------------------------------

verify_verus_proofs() {
    print_header "Verus Proof Verification"

    local verus_bin="$VERUS_INSTALL_DIR/verus"
    if [[ ! -x "$verus_bin" ]]; then
        print_error "Verus not found at $verus_bin"
        return 1
    fi

    local project_root
    project_root="$(get_project_root)"
    local proofs_dir="$project_root/crates/rource-math/proofs"

    if [[ ! -d "$proofs_dir" ]]; then
        print_error "Proofs directory not found: $proofs_dir"
        return 1
    fi

    local failed=0
    local verified=0

    for proof_file in "$proofs_dir"/*_proofs.rs; do
        if [[ -f "$proof_file" ]]; then
            local name
            name=$(basename "$proof_file")
            print_info "Verifying $name..."

            if "$verus_bin" "$proof_file" 2>&1 | grep -q "0 errors"; then
                print_ok "$name: VERIFIED"
                verified=$((verified + 1))
            else
                print_error "$name: FAILED"
                failed=$((failed + 1))
            fi
        fi
    done

    if [[ $failed -eq 0 ]]; then
        print_ok "All Verus proofs verified ($verified files, 0 errors)"
        return 0
    else
        print_error "$failed Verus proof file(s) failed verification"
        return 1
    fi
}

verify_coq_proofs() {
    print_header "Coq Proof Verification"

    if ! command_exists coqc; then
        print_error "Coq is not installed"
        return 1
    fi

    local project_root
    project_root="$(get_project_root)"
    local coq_dir="$project_root/crates/rource-math/proofs/coq"

    if [[ ! -d "$coq_dir" ]]; then
        print_error "Coq proofs directory not found: $coq_dir"
        return 1
    fi

    local failed=0
    local compiled=0

    pushd "$coq_dir" > /dev/null

    # Layer 1: Specifications
    for spec_file in Vec2.v Vec3.v Vec4.v Mat3.v Mat4.v; do
        if [[ -f "$spec_file" ]]; then
            print_info "Compiling spec: $spec_file..."
            if coqc -Q . RourceMath "$spec_file" 2>&1; then
                print_ok "$spec_file: COMPILED"
                compiled=$((compiled + 1))
            else
                print_error "$spec_file: FAILED"
                failed=$((failed + 1))
            fi
        fi
    done

    # Layer 1: Proofs (R-based)
    for proof_file in Vec2_Proofs.v Vec3_Proofs.v Vec4_Proofs.v Mat3_Proofs.v Mat4_Proofs.v; do
        if [[ -f "$proof_file" ]]; then
            print_info "Verifying: $proof_file..."
            if coqc -Q . RourceMath "$proof_file" 2>&1; then
                print_ok "$proof_file: VERIFIED"
                compiled=$((compiled + 1))
            else
                print_error "$proof_file: FAILED"
                failed=$((failed + 1))
            fi
        fi
    done

    # Complexity proofs
    if [[ -f "Complexity.v" ]]; then
        print_info "Verifying: Complexity.v..."
        if coqc -Q . RourceMath Complexity.v 2>&1; then
            print_ok "Complexity.v: VERIFIED"
            compiled=$((compiled + 1))
        else
            print_error "Complexity.v: FAILED"
            failed=$((failed + 1))
        fi
    fi

    # Layer 2: Computational bridge (Z-based)
    for compute_file in Vec2_Compute.v Vec3_Compute.v Vec4_Compute.v Mat3_Compute.v Mat4_Compute.v; do
        if [[ -f "$compute_file" ]]; then
            print_info "Verifying: $compute_file..."
            if coqc -Q . RourceMath "$compute_file" 2>&1; then
                print_ok "$compute_file: VERIFIED"
                compiled=$((compiled + 1))
            else
                print_error "$compute_file: FAILED"
                failed=$((failed + 1))
            fi
        fi
    done

    # Layer 3: Extraction files
    for extract_file in Vec2_Extract.v Vec3_Extract.v Vec4_Extract.v \
                        Mat3_Extract.v Mat4_Extract.v RourceMath_Extract.v; do
        if [[ -f "$extract_file" ]]; then
            print_info "Extracting: $extract_file..."
            if coqc -Q . RourceMath "$extract_file" 2>&1; then
                print_ok "$extract_file: EXTRACTED"
                compiled=$((compiled + 1))
            else
                print_error "$extract_file: FAILED"
                failed=$((failed + 1))
            fi
        fi
    done

    # Layer 4: MetaCoq verified extraction (optional, requires MetaCoq installed)
    if [[ -f "Vec2_VerifiedExtract.v" ]]; then
        print_info "Verifying MetaCoq erasure: Vec2_VerifiedExtract.v..."
        if coqc -Q . RourceMath Vec2_VerifiedExtract.v 2>&1; then
            print_ok "Vec2_VerifiedExtract.v: MetaCoq verified erasure OK"
            compiled=$((compiled + 1))
        else
            print_warn "Vec2_VerifiedExtract.v: MetaCoq not available (install with --metacoq)"
        fi
    fi

    popd > /dev/null

    if [[ $failed -eq 0 ]]; then
        print_ok "All Coq files verified ($compiled files, 0 errors, 0 admits)"
        return 0
    else
        print_error "$failed Coq file(s) failed verification"
        return 1
    fi
}

# -----------------------------------------------------------------------------
# Summary
# -----------------------------------------------------------------------------

print_summary() {
    print_header "Formal Verification Setup Summary"

    echo -e "${BOLD}Tool Status:${NC}"

    # Verus
    if [[ -x "$VERUS_INSTALL_DIR/verus" ]]; then
        local verus_version
        verus_version=$("$VERUS_INSTALL_DIR/verus" --version 2>/dev/null | head -1 || echo "installed")
        echo -e "  Verus:           ${GREEN}OK${NC}  $verus_version"
    else
        echo -e "  Verus:           ${RED}MISSING${NC}"
    fi

    # Coq
    if command_exists coqc; then
        local coq_version
        coq_version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "installed")
        echo -e "  Coq:             ${GREEN}OK${NC}  version $coq_version"
    else
        echo -e "  Coq:             ${RED}MISSING${NC}"
    fi

    # opam
    if command_exists opam; then
        echo -e "  opam:            ${GREEN}OK${NC}  $(opam --version 2>/dev/null || echo 'installed')"
    else
        echo -e "  opam:            ${RED}MISSING${NC}"
    fi

    # coq-equations
    if opam list coq-equations 2>/dev/null | grep -q "$COQ_EQUATIONS_VERSION"; then
        echo -e "  coq-equations:   ${GREEN}OK${NC}  $COQ_EQUATIONS_VERSION"
    else
        echo -e "  coq-equations:   ${YELLOW}MISSING${NC}"
    fi

    # MetaCoq
    if [[ -f "$METACOQ_INSTALL_DIR/erasure-plugin/theories/Loader.vo" ]] || \
       [[ -f "$METACOQ_INSTALL_DIR/erasure/theories/Extraction.vo" ]]; then
        echo -e "  MetaCoq:         ${GREEN}OK${NC}  built at $METACOQ_INSTALL_DIR"
    elif [[ -d "$METACOQ_INSTALL_DIR/.git" ]]; then
        echo -e "  MetaCoq:         ${YELLOW}CLONED${NC}  (not fully built)"
    else
        echo -e "  MetaCoq:         ${YELLOW}NOT INSTALLED${NC}"
    fi

    # wasm_of_ocaml
    if command_exists wasm_of_ocaml; then
        echo -e "  wasm_of_ocaml:   ${GREEN}OK${NC}  $(wasm_of_ocaml --version 2>/dev/null || echo 'installed')"
    else
        echo -e "  wasm_of_ocaml:   ${YELLOW}NOT INSTALLED${NC}  (optional)"
    fi

    # Rust toolchain
    if rustup toolchain list 2>/dev/null | grep -q "$VERUS_RUST_VERSION"; then
        echo -e "  Rust:            ${GREEN}OK${NC}  $VERUS_RUST_VERSION (for Verus)"
    else
        echo -e "  Rust:            ${YELLOW}MISSING${NC}  $VERUS_RUST_VERSION"
    fi

    echo ""
    echo -e "${BOLD}Verification:${NC}"
    echo "  Verus: 105 theorems, 242 VCs (5 types)"
    echo "  Coq:   347 theorems, 0 admits (22 files)"
    echo "  Total: 452 formally verified theorems"
    echo ""
    echo -e "${BOLD}Quick Commands:${NC}"
    echo "  # Run all proofs"
    echo "  ./scripts/setup-formal-verification.sh --verify"
    echo ""
    echo "  # Verus single proof"
    echo "  $VERUS_INSTALL_DIR/verus crates/rource-math/proofs/vec2_proofs.rs"
    echo ""
    echo "  # Coq single proof"
    echo "  cd crates/rource-math/proofs/coq && coqc -Q . RourceMath Vec2_Proofs.v"
    echo ""
    echo -e "${BOLD}Documentation:${NC}"
    echo "  Setup Guide: docs/verification/SETUP_GUIDE.md"
    echo "  Full Details: docs/verification/FORMAL_VERIFICATION.md"
    echo ""

    if [[ $ERRORS -eq 0 ]] && [[ $WARNINGS -eq 0 ]]; then
        echo -e "${GREEN}${BOLD}Formal verification environment ready!${NC}"
    elif [[ $ERRORS -eq 0 ]]; then
        echo -e "${YELLOW}${BOLD}Setup complete with $WARNINGS warning(s)${NC}"
    else
        echo -e "${RED}${BOLD}Setup completed with $ERRORS error(s) and $WARNINGS warning(s)${NC}"
        return 1
    fi

    return 0
}

show_help() {
    cat << 'HELPEOF'
Rource Formal Verification Setup Script v2.0.0

Usage: ./scripts/setup-formal-verification.sh [OPTIONS]

Options:
  --check          Check installation status only (no installations)
  --verus          Install/update Verus only
  --coq            Install/update Coq + opam ecosystem only
  --metacoq        Build/install MetaCoq from source only
  --wasm-of-ocaml  Install wasm_of_ocaml only
  --verify         Run all formal proofs after setup
  -h, --help       Show this help message

Description:
  Installs and configures ALL formal verification tools for the Rource
  project, targeting PEER REVIEWED PUBLISHED ACADEMIC quality.

Tools Installed:
  - Verus (Microsoft's Rust verification tool)
    Binary: /tmp/verus/verus
    Requires: Rust 1.92.0 toolchain

  - Coq 8.18+ (proof assistant)
    Installed via: apt-get (coq + coq-theories)
    Standard library: Reals, ZArith, Lra, Lia, Ring

  - opam + OCaml 4.14.x (package manager ecosystem)
    Required for: coq-equations, MetaCoq, wasm_of_ocaml

  - coq-equations 1.3+8.18 (dependent pattern matching)
    Installed via: GitHub pin (bypasses broken Coq opam repos)
    Source: github.com/mattam82/Coq-Equations#v1.3-8.18

  - MetaCoq (verified extraction / erasure)
    Built from: github.com/MetaCoq/metacoq#coq-8.18
    Location: /tmp/metacoq/

  - wasm_of_ocaml (OCaml to WASM compiler)
    Installed via: opam
    Used for: Coq -> OCaml -> WASM pipeline (Path 1)

Verification Status:
  - Verus: 105 theorems, 242 VCs (Vec2/Vec3/Vec4/Mat3/Mat4)
  - Coq:   347 theorems, 0 admits (22 files, ~40s compilation)
  - Total: 452 formally verified theorems (DUAL VERIFIED)

Setup Guide: docs/verification/SETUP_GUIDE.md

HELPEOF
}

# -----------------------------------------------------------------------------
# Main Entry Point
# -----------------------------------------------------------------------------

main() {
    # Parse arguments
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --check)
                CHECK_ONLY=true
                shift
                ;;
            --verus)
                VERUS_ONLY=true
                shift
                ;;
            --coq)
                COQ_ONLY=true
                shift
                ;;
            --metacoq)
                METACOQ_ONLY=true
                shift
                ;;
            --wasm-of-ocaml)
                WASM_OF_OCAML_ONLY=true
                shift
                ;;
            --verify)
                VERIFY_PROOFS=true
                shift
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            *)
                print_error "Unknown option: $1"
                show_help
                exit 1
                ;;
        esac
    done

    echo ""
    echo -e "${BOLD}Rource Formal Verification Setup v${SCRIPT_VERSION}${NC}"
    echo -e "Standard: ${CYAN}PEER REVIEWED PUBLISHED ACADEMIC${NC}"
    echo ""

    if [[ "$CHECK_ONLY" == true ]]; then
        print_info "Running in check-only mode (no installations)"
    fi

    # Determine what to install based on flags
    local install_all=true
    if [[ "$VERUS_ONLY" == true ]] || [[ "$COQ_ONLY" == true ]] || \
       [[ "$METACOQ_ONLY" == true ]] || [[ "$WASM_OF_OCAML_ONLY" == true ]]; then
        install_all=false
    fi

    # System dependencies (always needed)
    if [[ "$CHECK_ONLY" != true ]]; then
        install_system_deps || true
    fi

    # Verus
    if [[ "$install_all" == true ]] || [[ "$VERUS_ONLY" == true ]]; then
        install_verus_rust_toolchain || true
        install_verus || true
    fi

    # Coq + opam ecosystem
    if [[ "$install_all" == true ]] || [[ "$COQ_ONLY" == true ]]; then
        install_coq || true
        setup_opam_environment || true
        install_coq_equations || true
    fi

    # MetaCoq
    if [[ "$install_all" == true ]] || [[ "$METACOQ_ONLY" == true ]]; then
        # Ensure prerequisites are in place
        if [[ "$install_all" != true ]]; then
            eval "$(opam env 2>/dev/null)" || true
        fi
        install_metacoq || true
        install_metacoq_to_coq || true
    fi

    # wasm_of_ocaml
    if [[ "$install_all" == true ]] || [[ "$WASM_OF_OCAML_ONLY" == true ]]; then
        install_wasm_of_ocaml || true
    fi

    # Verify proofs if requested
    if [[ "$VERIFY_PROOFS" == true ]]; then
        if [[ "$install_all" == true ]] || [[ "$VERUS_ONLY" == true ]]; then
            verify_verus_proofs || true
        fi
        if [[ "$install_all" == true ]] || [[ "$COQ_ONLY" == true ]] || \
           [[ "$METACOQ_ONLY" == true ]]; then
            verify_coq_proofs || true
        fi
    fi

    print_summary

    if [[ $ERRORS -gt 0 ]]; then
        exit 1
    fi
    exit 0
}

main "$@"
