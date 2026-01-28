#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# =============================================================================
# Rource Formal Verification Setup Script
# =============================================================================
#
# Purpose: Install and configure formal verification tools (Verus + Coq) for
#          PEER REVIEWED PUBLISHED ACADEMIC quality proofs.
#
# Usage:
#   ./scripts/setup-formal-verification.sh           # Full setup
#   ./scripts/setup-formal-verification.sh --check   # Verify installation only
#   ./scripts/setup-formal-verification.sh --verus   # Verus only
#   ./scripts/setup-formal-verification.sh --coq     # Coq only
#   ./scripts/setup-formal-verification.sh --verify  # Run all proofs
#   ./scripts/setup-formal-verification.sh --help    # Show help
#
# Requirements:
#   - Linux x86_64 (Verus binary requirement)
#   - curl, unzip (for Verus download)
#   - apt/apt-get OR opam (for Coq installation)
#
# This script installs:
#   - Verus (Microsoft's Rust verification tool) in /tmp/verus/
#   - Coq 8.18+ (proof assistant) via apt or opam
#   - Rust 1.92.0 toolchain (required by Verus)
#
# =============================================================================

set -euo pipefail

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

readonly SCRIPT_VERSION="1.0.0"
readonly SCRIPT_NAME="setup-formal-verification.sh"

# Verus configuration
readonly VERUS_VERSION="latest"
readonly VERUS_INSTALL_DIR="/tmp/verus"
readonly VERUS_RUST_VERSION="1.92.0"

# Coq configuration
readonly COQ_MIN_VERSION="8.18"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# Modes
CHECK_ONLY=false
VERUS_ONLY=false
COQ_ONLY=false
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
    ((WARNINGS++)) || true
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
    ((ERRORS++)) || true
}

command_exists() {
    command -v "$1" &> /dev/null
}

# Compare version strings (returns 0 if $1 >= $2)
version_gte() {
    local v1="$1"
    local v2="$2"

    # Use sort -V for version comparison
    [ "$v1" = "$(echo -e "$v1\n$v2" | sort -V | tail -n1)" ]
}

# -----------------------------------------------------------------------------
# Verus Installation
# -----------------------------------------------------------------------------

check_verus_prerequisites() {
    print_header "Verus Prerequisites"

    # Check architecture
    local arch
    arch=$(uname -m)
    if [[ "$arch" != "x86_64" ]]; then
        print_error "Verus requires x86_64 architecture (found: $arch)"
        return 1
    fi
    print_ok "Architecture: $arch"

    # Check OS
    local os
    os=$(uname -s)
    if [[ "$os" != "Linux" ]]; then
        print_warn "Verus binary releases are for Linux; may need to build from source on $os"
    else
        print_ok "Operating system: $os"
    fi

    # Check required tools
    for tool in curl unzip; do
        if command_exists "$tool"; then
            print_ok "$tool is available"
        else
            print_error "$tool is required but not installed"
            return 1
        fi
    done

    # Check rustup
    if command_exists rustup; then
        print_ok "rustup is available"
    else
        print_error "rustup is required but not installed"
        print_info "Install from: https://rustup.rs/"
        return 1
    fi

    return 0
}

install_verus() {
    print_header "Verus Installation"

    # Check if already installed
    if [[ -x "$VERUS_INSTALL_DIR/verus" ]]; then
        local version
        version=$("$VERUS_INSTALL_DIR/verus" --version 2>/dev/null | head -1 || echo "unknown")
        print_ok "Verus is already installed: $version"

        if [[ "$CHECK_ONLY" == true ]]; then
            return 0
        fi

        print_info "Re-downloading to ensure latest version..."
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "Verus is not installed"
        return 1
    fi

    # Create install directory
    mkdir -p "$VERUS_INSTALL_DIR"

    # Download Verus
    print_info "Downloading Verus..."
    local download_url="https://github.com/verus-lang/verus/releases/latest/download/verus-x86_64-linux.zip"
    local zip_file="$VERUS_INSTALL_DIR/verus.zip"

    if ! curl -L -o "$zip_file" "$download_url" 2>/dev/null; then
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

    # Find the extracted directory and move contents up
    local extracted_dir
    extracted_dir=$(find "$VERUS_INSTALL_DIR" -maxdepth 1 -type d -name "verus-*" | head -1)
    if [[ -n "$extracted_dir" ]] && [[ -d "$extracted_dir" ]]; then
        mv "$extracted_dir"/* "$VERUS_INSTALL_DIR/" 2>/dev/null || true
        rmdir "$extracted_dir" 2>/dev/null || true
    fi

    # Make executable
    chmod +x "$VERUS_INSTALL_DIR/verus" 2>/dev/null || true

    # Cleanup
    rm -f "$zip_file"

    # Verify installation
    if [[ -x "$VERUS_INSTALL_DIR/verus" ]]; then
        local version
        version=$("$VERUS_INSTALL_DIR/verus" --version 2>/dev/null | head -1 || echo "installed")
        print_ok "Verus installed successfully: $version"
    else
        print_error "Verus installation failed"
        return 1
    fi

    return 0
}

install_verus_rust_toolchain() {
    print_header "Verus Rust Toolchain"

    # Check if toolchain is installed
    if rustup toolchain list | grep -q "$VERUS_RUST_VERSION"; then
        print_ok "Rust $VERUS_RUST_VERSION toolchain is installed"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "Rust $VERUS_RUST_VERSION toolchain is not installed"
        return 1
    fi

    print_info "Installing Rust $VERUS_RUST_VERSION toolchain (required by Verus)..."
    if rustup install "$VERUS_RUST_VERSION"; then
        print_ok "Rust $VERUS_RUST_VERSION installed successfully"
    else
        print_error "Failed to install Rust $VERUS_RUST_VERSION"
        return 1
    fi

    return 0
}

# -----------------------------------------------------------------------------
# Coq Installation
# -----------------------------------------------------------------------------

check_coq_prerequisites() {
    print_header "Coq Prerequisites"

    # Check for package manager
    if command_exists apt-get; then
        print_ok "apt-get is available"
        return 0
    elif command_exists opam; then
        print_ok "opam is available"
        return 0
    else
        print_error "Neither apt-get nor opam found"
        print_info "Install opam from: https://opam.ocaml.org/doc/Install.html"
        return 1
    fi
}

install_coq() {
    print_header "Coq Installation"

    # Check if already installed
    if command_exists coqc; then
        local version
        version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "unknown")
        print_ok "Coq is already installed: version $version"

        if version_gte "$version" "$COQ_MIN_VERSION"; then
            print_ok "Coq version $version >= $COQ_MIN_VERSION"
            return 0
        else
            print_warn "Coq version $version < $COQ_MIN_VERSION (upgrade recommended)"
        fi
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        if ! command_exists coqc; then
            print_warn "Coq is not installed"
            return 1
        fi
        return 0
    fi

    # Try apt-get first (simpler)
    if command_exists apt-get; then
        print_info "Installing Coq via apt-get..."
        if sudo apt-get update && sudo apt-get install -y coq; then
            print_ok "Coq installed via apt-get"
        else
            print_warn "apt-get installation failed, trying opam..."
        fi
    fi

    # Verify installation
    if command_exists coqc; then
        local version
        version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "unknown")
        print_ok "Coq installed: version $version"
        return 0
    fi

    # Try opam as fallback
    if command_exists opam; then
        print_info "Installing Coq via opam..."

        # Initialize opam if needed
        if [[ ! -d "$HOME/.opam" ]]; then
            print_info "Initializing opam..."
            opam init --auto-setup --bare --yes || true
        fi

        # Create switch for Coq
        local switch_name="coq-${COQ_MIN_VERSION}"
        if ! opam switch list 2>/dev/null | grep -q "$switch_name"; then
            print_info "Creating opam switch: $switch_name"
            opam switch create "$switch_name" ocaml-base-compiler.4.14.1 --yes || true
        fi

        eval "$(opam env --switch=$switch_name 2>/dev/null)" || true

        # Install Coq
        if opam install coq --yes; then
            print_ok "Coq installed via opam"
        else
            print_error "Failed to install Coq via opam"
            return 1
        fi
    fi

    # Final verification
    if command_exists coqc; then
        local version
        version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "unknown")
        print_ok "Coq installation verified: version $version"
        return 0
    else
        print_error "Coq installation failed"
        return 1
    fi
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

    # Find project root
    local script_dir
    script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    local project_root="$script_dir/.."
    local proofs_dir="$project_root/crates/rource-math/proofs"

    if [[ ! -d "$proofs_dir" ]]; then
        print_error "Proofs directory not found: $proofs_dir"
        return 1
    fi

    local failed=0

    for proof_file in "$proofs_dir"/*_proofs.rs; do
        if [[ -f "$proof_file" ]]; then
            local name
            name=$(basename "$proof_file")
            print_info "Verifying $name..."

            if "$verus_bin" "$proof_file" 2>&1 | grep -q "0 errors"; then
                print_ok "$name: VERIFIED"
            else
                print_error "$name: FAILED"
                ((failed++)) || true
            fi
        fi
    done

    if [[ $failed -eq 0 ]]; then
        print_ok "All Verus proofs verified successfully"
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

    # Find project root
    local script_dir
    script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    local project_root="$script_dir/.."
    local coq_dir="$project_root/crates/rource-math/proofs/coq"

    if [[ ! -d "$coq_dir" ]]; then
        print_error "Coq proofs directory not found: $coq_dir"
        return 1
    fi

    local failed=0

    # Change to Coq directory
    pushd "$coq_dir" > /dev/null

    # Compile specifications first
    for spec_file in Vec2.v Vec3.v Vec4.v; do
        if [[ -f "$spec_file" ]]; then
            print_info "Compiling $spec_file..."
            if coqc -Q . RourceMath "$spec_file" 2>&1; then
                print_ok "$spec_file: COMPILED"
            else
                print_error "$spec_file: FAILED"
                ((failed++)) || true
            fi
        fi
    done

    # Compile proofs
    for proof_file in Vec2_Proofs.v Vec3_Proofs.v Vec4_Proofs.v; do
        if [[ -f "$proof_file" ]]; then
            print_info "Verifying $proof_file..."
            if coqc -Q . RourceMath "$proof_file" 2>&1; then
                print_ok "$proof_file: VERIFIED"
            else
                print_error "$proof_file: FAILED"
                ((failed++)) || true
            fi
        fi
    done

    popd > /dev/null

    if [[ $failed -eq 0 ]]; then
        print_ok "All Coq proofs verified successfully"
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

    # Verus status
    if [[ -x "$VERUS_INSTALL_DIR/verus" ]]; then
        local verus_version
        verus_version=$("$VERUS_INSTALL_DIR/verus" --version 2>/dev/null | head -1 || echo "installed")
        echo -e "  Verus:  ${GREEN}✓${NC} $verus_version"
        echo -e "          Path: $VERUS_INSTALL_DIR/verus"
    else
        echo -e "  Verus:  ${RED}✗${NC} Not installed"
    fi

    # Coq status
    if command_exists coqc; then
        local coq_version
        coq_version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "installed")
        echo -e "  Coq:    ${GREEN}✓${NC} version $coq_version"
    else
        echo -e "  Coq:    ${RED}✗${NC} Not installed"
    fi

    # Rust toolchain status
    if rustup toolchain list 2>/dev/null | grep -q "$VERUS_RUST_VERSION"; then
        echo -e "  Rust:   ${GREEN}✓${NC} $VERUS_RUST_VERSION (for Verus)"
    else
        echo -e "  Rust:   ${YELLOW}!${NC} $VERUS_RUST_VERSION not installed"
    fi

    echo ""
    echo -e "${BOLD}Verification Commands:${NC}"
    echo "  # Verus proofs"
    echo "  $VERUS_INSTALL_DIR/verus crates/rource-math/proofs/vec2_proofs.rs"
    echo ""
    echo "  # Coq proofs"
    echo "  cd crates/rource-math/proofs/coq"
    echo "  coqc -Q . RourceMath Vec2.v Vec3.v Vec4.v"
    echo "  coqc -Q . RourceMath Vec2_Proofs.v Vec3_Proofs.v Vec4_Proofs.v"
    echo ""

    if [[ $ERRORS -eq 0 ]] && [[ $WARNINGS -eq 0 ]]; then
        echo -e "${GREEN}${BOLD}Formal verification environment ready!${NC}"
    elif [[ $ERRORS -eq 0 ]]; then
        echo -e "${YELLOW}${BOLD}Setup complete with $WARNINGS warning(s)${NC}"
    else
        echo -e "${RED}${BOLD}Setup failed with $ERRORS error(s)${NC}"
        return 1
    fi

    return 0
}

show_help() {
    cat << EOF
Rource Formal Verification Setup Script v${SCRIPT_VERSION}

Usage: ./scripts/setup-formal-verification.sh [OPTIONS]

Options:
  --check       Check installation status only (no installations)
  --verus       Install/update Verus only
  --coq         Install/update Coq only
  --verify      Run all formal proofs after setup
  -h, --help    Show this help message

Description:
  This script installs and configures formal verification tools for the
  Rource project, targeting PEER REVIEWED PUBLISHED ACADEMIC quality.

Tools Installed:
  - Verus (Microsoft's Rust verification tool)
    - Downloads binary to: $VERUS_INSTALL_DIR/
    - Requires Rust $VERUS_RUST_VERSION toolchain

  - Coq $COQ_MIN_VERSION+ (proof assistant)
    - Installed via apt-get or opam
    - Used for dual verification of Vec2/Vec3/Vec4

Verification Status:
  - Verus: 105 theorems, 242 VCs across Vec2/Vec3/Vec4/Mat3/Mat4
  - Coq: 90+ theorems across Vec2/Vec3/Vec4
  - Combined: 195+ formally verified theorems

Requirements:
  - Linux x86_64 (for Verus binary)
  - curl, unzip (for Verus download)
  - apt-get or opam (for Coq installation)
  - rustup (for Rust toolchain management)

EOF
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

    if [[ "$CHECK_ONLY" == true ]]; then
        print_info "Running in check-only mode (no installations)"
    fi

    # Verus setup
    if [[ "$COQ_ONLY" != true ]]; then
        check_verus_prerequisites || true
        install_verus_rust_toolchain || true
        install_verus || true
    fi

    # Coq setup
    if [[ "$VERUS_ONLY" != true ]]; then
        check_coq_prerequisites || true
        install_coq || true
    fi

    # Verify proofs if requested
    if [[ "$VERIFY_PROOFS" == true ]]; then
        if [[ "$COQ_ONLY" != true ]]; then
            verify_verus_proofs || true
        fi
        if [[ "$VERUS_ONLY" != true ]]; then
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
