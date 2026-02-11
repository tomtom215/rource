#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# =============================================================================
# Rource Development Session Setup Script
# =============================================================================
#
# Purpose: Verify and configure the development environment for Rource
#
# Usage:
#   source scripts/session-setup.sh        # Interactive setup
#   source scripts/session-setup.sh -q     # Quiet mode (minimal output)
#   source scripts/session-setup.sh -v     # Verbose mode (debug output)
#   source scripts/session-setup.sh -c     # Check only (no installations)
#   source scripts/session-setup.sh -h     # Show help
#
# This script should be sourced (not executed) to properly set environment
# variables in the current shell.
#
# =============================================================================

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------

# Minimum Rust version required (must match Cargo.toml rust-version)
readonly REQUIRED_RUST_VERSION="1.82"

# Script metadata
readonly SCRIPT_VERSION="2.0.0"
# Script name used in error messages and documentation
export SCRIPT_NAME="session-setup.sh"

# -----------------------------------------------------------------------------
# Global Variables
# -----------------------------------------------------------------------------

QUIET_MODE=false
VERBOSE_MODE=false
CHECK_ONLY=false
SETUP_ERRORS=0
SETUP_WARNINGS=0

# -----------------------------------------------------------------------------
# Helper Functions
# -----------------------------------------------------------------------------

# Colors for output (disabled if not a terminal)
setup_colors() {
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
}

# Print functions
print_header() {
    [[ "$QUIET_MODE" == true ]] && return
    echo ""
    echo -e "${BOLD}${BLUE}=== $1 ===${NC}"
    echo ""
}

print_info() {
    [[ "$QUIET_MODE" == true ]] && return
    echo -e "${CYAN}[INFO]${NC} $1"
}

print_ok() {
    [[ "$QUIET_MODE" == true ]] && return
    echo -e "${GREEN}[OK]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
    ((SETUP_WARNINGS++))
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
    ((SETUP_ERRORS++))
}

print_debug() {
    [[ "$VERBOSE_MODE" != true ]] && return
    echo -e "${BLUE}[DEBUG]${NC} $1"
}

# Check if a command exists
command_exists() {
    command -v "$1" &> /dev/null
}

# Compare version strings (returns 0 if $1 >= $2)
version_gte() {
    local v1="$1"
    local v2="$2"

    # Split versions into arrays
    IFS='.' read -ra V1_PARTS <<< "$v1"
    IFS='.' read -ra V2_PARTS <<< "$v2"

    # Compare each part
    for i in 0 1 2; do
        local p1="${V1_PARTS[$i]:-0}"
        local p2="${V2_PARTS[$i]:-0}"

        # Remove any non-numeric suffixes (e.g., "82" from "1.82.0-beta")
        p1="${p1%%[^0-9]*}"
        p2="${p2%%[^0-9]*}"

        if (( p1 > p2 )); then
            return 0
        elif (( p1 < p2 )); then
            return 1
        fi
    done

    return 0
}

# Install a cargo tool if not present
install_cargo_tool() {
    local tool="$1"
    local package="${2:-$1}"

    if command_exists "$tool"; then
        local version
        version=$("$tool" --version 2>/dev/null | head -1 | awk '{print $2}')
        print_ok "$tool is installed (version: ${version:-unknown})"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "$tool is not installed"
        return 1
    fi

    print_info "Installing $tool..."
    if cargo install "$package" 2>/dev/null; then
        print_ok "$tool installed successfully"
        return 0
    else
        print_error "Failed to install $tool"
        return 1
    fi
}

# Add a rustup component if not present
add_rustup_component() {
    local component="$1"

    if rustup component list --installed 2>/dev/null | grep -q "^${component}"; then
        print_ok "$component is installed"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "$component is not installed"
        return 1
    fi

    print_info "Installing $component..."
    if rustup component add "$component" 2>/dev/null; then
        print_ok "$component installed successfully"
        return 0
    else
        print_error "Failed to install $component"
        return 1
    fi
}

# -----------------------------------------------------------------------------
# Check Functions
# -----------------------------------------------------------------------------

check_project_directory() {
    print_header "Project Directory"

    # Check if we're in the project root or can find it
    local project_root=""

    if [[ -f "Cargo.toml" ]] && grep -q 'name = "rource"' Cargo.toml 2>/dev/null; then
        project_root="$(pwd)"
    elif [[ -f "../Cargo.toml" ]] && grep -q 'name = "rource"' ../Cargo.toml 2>/dev/null; then
        project_root="$(cd .. && pwd)"
    else
        # Try to find it relative to script location
        local script_dir
        script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" 2>/dev/null && pwd)"
        if [[ -n "$script_dir" ]] && [[ -f "$script_dir/../Cargo.toml" ]]; then
            project_root="$(cd "$script_dir/.." && pwd)"
        fi
    fi

    if [[ -z "$project_root" ]]; then
        print_error "Cannot find Rource project root"
        print_info "Please run this script from the project directory"
        return 1
    fi

    print_ok "Project root: $project_root"
    export ROURCE_PROJECT_ROOT="$project_root"

    # Verify key directories exist
    local required_dirs=("crates" "rource-cli" "rource-wasm" "scripts")
    for dir in "${required_dirs[@]}"; do
        if [[ -d "$project_root/$dir" ]]; then
            print_debug "Found directory: $dir"
        else
            print_error "Missing directory: $dir"
            return 1
        fi
    done

    print_ok "Project structure verified"
    return 0
}

check_rust_toolchain() {
    print_header "Rust Toolchain"

    # Check rustup
    if ! command_exists rustup; then
        if [[ "$CHECK_ONLY" == true ]]; then
            print_error "rustup is not installed"
            print_info "Install from: https://rustup.rs/"
            return 1
        fi

        print_info "Installing Rust via rustup..."
        if curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable; then
            # shellcheck source=/dev/null
            source "$HOME/.cargo/env"
            print_ok "Rust installed successfully"
        else
            print_error "Failed to install Rust"
            return 1
        fi
    else
        print_ok "rustup is installed"
    fi

    # Check rustc
    if ! command_exists rustc; then
        print_error "rustc not found (rustup may not be configured correctly)"
        return 1
    fi

    # Check Rust version
    local rust_version
    rust_version=$(rustc --version | awk '{print $2}')

    if version_gte "$rust_version" "$REQUIRED_RUST_VERSION"; then
        print_ok "Rust version: $rust_version (>= $REQUIRED_RUST_VERSION required)"
    else
        print_error "Rust version $rust_version is too old (>= $REQUIRED_RUST_VERSION required)"

        if [[ "$CHECK_ONLY" != true ]]; then
            print_info "Updating Rust..."
            if rustup update stable; then
                rust_version=$(rustc --version | awk '{print $2}')
                if version_gte "$rust_version" "$REQUIRED_RUST_VERSION"; then
                    print_ok "Rust updated to $rust_version"
                else
                    print_error "Still using old Rust version after update"
                    return 1
                fi
            else
                print_error "Failed to update Rust"
                return 1
            fi
        else
            return 1
        fi
    fi

    # Check cargo
    if command_exists cargo; then
        local cargo_version
        cargo_version=$(cargo --version | awk '{print $2}')
        print_ok "Cargo version: $cargo_version"
    else
        print_error "cargo not found"
        return 1
    fi

    return 0
}

check_wasm_target() {
    print_header "WASM Target"

    if rustup target list --installed 2>/dev/null | grep -q "wasm32-unknown-unknown"; then
        print_ok "wasm32-unknown-unknown target is installed"
        return 0
    fi

    if [[ "$CHECK_ONLY" == true ]]; then
        print_warn "wasm32-unknown-unknown target is not installed"
        return 1
    fi

    print_info "Installing wasm32-unknown-unknown target..."
    if rustup target add wasm32-unknown-unknown; then
        print_ok "WASM target installed successfully"
        return 0
    else
        print_error "Failed to install WASM target"
        return 1
    fi
}

check_rust_components() {
    print_header "Rust Components"

    add_rustup_component "clippy"
    add_rustup_component "rustfmt"
    add_rustup_component "rust-src"  # Useful for IDE integration

    return 0
}

check_cargo_tools() {
    print_header "Cargo Tools"

    # Required tools
    install_cargo_tool "wasm-pack" "wasm-pack"

    # Development tools
    install_cargo_tool "cargo-watch" "cargo-watch"

    # Security/audit tools
    install_cargo_tool "cargo-audit" "cargo-audit"
    install_cargo_tool "cargo-deny" "cargo-deny"

    # EXPERT+ Coverage tools (REQUIRED for verifiable quality)
    install_cargo_tool "cargo-tarpaulin" "cargo-tarpaulin"

    # Coverage tool (alternative)
    if command_exists cargo-llvm-cov; then
        print_ok "cargo-llvm-cov is installed"
    else
        print_info "cargo-llvm-cov not found (optional - alternative coverage tool)"
        print_info "  Install with: cargo install cargo-llvm-cov"
    fi

    return 0
}

check_optional_tools() {
    print_header "Optional Tools"

    # wasm-opt (from binaryen)
    if command_exists wasm-opt; then
        local wasm_opt_version
        wasm_opt_version=$(wasm-opt --version 2>/dev/null | head -1)
        print_ok "wasm-opt is installed ($wasm_opt_version)"
    else
        print_info "wasm-opt not found (optional - provides WASM optimization)"
        print_info "  Install with: apt-get install binaryen  OR  brew install binaryen"
    fi

    # ffmpeg (for video export)
    if command_exists ffmpeg; then
        local ffmpeg_version
        ffmpeg_version=$(ffmpeg -version 2>/dev/null | head -1 | awk '{print $3}')
        print_ok "ffmpeg is installed (version: $ffmpeg_version)"
    else
        print_info "ffmpeg not found (optional - for video export)"
        print_info "  Install with: apt-get install ffmpeg  OR  brew install ffmpeg"
    fi

    # Python 3 (for PPM inspection scripts)
    if command_exists python3; then
        local python_version
        python_version=$(python3 --version 2>/dev/null | awk '{print $2}')
        print_ok "Python 3 is installed (version: $python_version)"
    else
        print_info "Python 3 not found (optional - for PPM inspection scripts)"
    fi

    # git (essential for VCS operations)
    if command_exists git; then
        local git_version
        git_version=$(git --version | awk '{print $3}')
        print_ok "git is installed (version: $git_version)"
    else
        print_warn "git not found (required for repository visualization)"
    fi

    # Formal verification tools (for PEER REVIEWED PUBLISHED ACADEMIC standard)
    if command_exists coqc; then
        local coq_version
        coq_version=$(coqc --version 2>/dev/null | grep -oP 'version \K[0-9.]+' | head -1 || echo "installed")
        print_ok "Coq is installed (version: $coq_version)"
    else
        print_info "Coq not found (for formal verification)"
        print_info "  Install with: ./scripts/setup-formal-verification.sh --coq"
    fi

    if [[ -x "/tmp/verus/verus" ]]; then
        local verus_version
        verus_version=$(/tmp/verus/verus --version 2>/dev/null | head -1 || echo "installed")
        print_ok "Verus is installed ($verus_version)"
    else
        print_info "Verus not found (for formal verification)"
        print_info "  Install with: ./scripts/setup-formal-verification.sh --verus"
    fi

    # Visual Feedback Loop (VFL) tools
    if command_exists node; then
        local node_version
        node_version=$(node --version 2>/dev/null)
        print_ok "Node.js is installed ($node_version) — required for VFL"
    else
        print_info "Node.js not found (required for VFL screenshot capture)"
        print_info "  Install with: apt-get install nodejs  OR  brew install node"
    fi

    if command_exists npx; then
        print_ok "npx is available — required for VFL dev server"
    else
        print_info "npx not found (required for VFL dev server)"
    fi

    # Check VFL test scaffolding
    if [[ -f "${ROURCE_PROJECT_ROOT:-$PWD}/tests/visual/capture-chrome.js" ]]; then
        print_ok "VFL capture script found (tests/visual/capture-chrome.js)"
    else
        print_info "VFL capture script not found (tests/visual/capture-chrome.js)"
    fi

    if [[ -f "${ROURCE_PROJECT_ROOT:-$PWD}/tests/visual/package.json" ]]; then
        if [[ -d "${ROURCE_PROJECT_ROOT:-$PWD}/tests/visual/node_modules" ]]; then
            print_ok "VFL Playwright dependencies installed"
        else
            print_info "VFL Playwright dependencies not installed"
            print_info "  Run: cd tests/visual && npm install && npx playwright install chromium"
        fi
    fi

    return 0
}

check_build() {
    print_header "Build Verification"

    if [[ -z "$ROURCE_PROJECT_ROOT" ]]; then
        print_error "Project root not set"
        return 1
    fi

    cd "$ROURCE_PROJECT_ROOT" || return 1

    # Check if Cargo.lock exists
    if [[ -f "Cargo.lock" ]]; then
        print_ok "Cargo.lock exists"
    else
        print_info "Cargo.lock not found (will be created on first build)"
    fi

    # Quick build check (just parse, don't compile)
    print_info "Verifying Cargo.toml..."
    if cargo metadata --format-version 1 &>/dev/null; then
        print_ok "Cargo.toml is valid"
    else
        print_error "Cargo.toml has errors"
        return 1
    fi

    # Check if previous build exists
    if [[ -d "target/release" ]]; then
        print_ok "Release build directory exists"
    else
        print_info "No previous release build (run 'cargo build --release')"
    fi

    return 0
}

setup_environment() {
    print_header "Environment Setup"

    # Set helpful environment variables
    export RUST_BACKTRACE="${RUST_BACKTRACE:-1}"
    print_ok "RUST_BACKTRACE=$RUST_BACKTRACE"

    export CARGO_TERM_COLOR="${CARGO_TERM_COLOR:-always}"
    print_ok "CARGO_TERM_COLOR=$CARGO_TERM_COLOR"

    # Add cargo bin to PATH if not already present
    if [[ -d "$HOME/.cargo/bin" ]]; then
        if [[ ":$PATH:" != *":$HOME/.cargo/bin:"* ]]; then
            export PATH="$HOME/.cargo/bin:$PATH"
            print_ok "Added $HOME/.cargo/bin to PATH"
        else
            print_debug "$HOME/.cargo/bin already in PATH"
        fi
    fi

    return 0
}

print_summary() {
    print_header "Setup Summary"

    if [[ $SETUP_ERRORS -eq 0 ]] && [[ $SETUP_WARNINGS -eq 0 ]]; then
        echo -e "${GREEN}${BOLD}All checks passed!${NC}"
    elif [[ $SETUP_ERRORS -eq 0 ]]; then
        echo -e "${YELLOW}${BOLD}Setup complete with $SETUP_WARNINGS warning(s)${NC}"
    else
        echo -e "${RED}${BOLD}Setup failed with $SETUP_ERRORS error(s) and $SETUP_WARNINGS warning(s)${NC}"
    fi

    echo ""
    echo -e "${BOLD}Quick Commands:${NC}"
    echo "  cargo build --release    Build optimized native binary"
    echo "  cargo test               Run all tests"
    echo "  cargo clippy             Run linter"
    echo "  cargo fmt                Format code"
    echo "  ./scripts/build-wasm.sh  Build WASM version"
    echo ""
    echo -e "${BOLD}EXPERT+ Verification (REQUIRED):${NC}"
    echo "  cargo doc --no-deps --all-features                 Doc coverage (must be 0 warnings)"
    echo "  cargo tarpaulin -p rource-math -p rource-vcs \\    Line coverage analysis"
    echo "    -p rource-core -p rource-render --out Stdout"
    echo "  cargo clippy --all -- -D warnings                  Zero warnings required"
    echo "  cargo test --all                                   All tests must pass"
    echo ""
    echo -e "${BOLD}Formal Verification (PEER REVIEWED PUBLISHED ACADEMIC):${NC}"
    echo "  ./scripts/setup-formal-verification.sh --verify    Run all Verus + Coq proofs"
    echo "  # 237+ theorems total (105 Verus + 132+ Coq), zero admits"
    echo ""
    echo -e "${BOLD}Visual Feedback Loop (VFL):${NC}"
    echo "  npx serve rource-wasm/www -l 8787 &    Start dev server"
    echo "  node tests/visual/capture-chrome.js     Capture 16 screenshots"
    echo "  cd tests/visual && npx playwright test  Run Playwright VFL suite"
    echo ""
    echo -e "${BOLD}Project Paths:${NC}"
    echo "  Project Root: ${ROURCE_PROJECT_ROOT:-<not set>}"
    echo "  CLI Binary:   target/release/rource"
    echo "  WASM Demo:    rource-wasm/www/"
    echo ""

    if [[ $SETUP_ERRORS -gt 0 ]]; then
        return 1
    fi
    return 0
}

show_help() {
    cat << EOF
Rource Development Session Setup Script v${SCRIPT_VERSION}

Usage: source scripts/session-setup.sh [OPTIONS]

Options:
  -q, --quiet     Quiet mode (minimal output)
  -v, --verbose   Verbose mode (debug output)
  -c, --check     Check only (no installations)
  -h, --help      Show this help message

Description:
  This script verifies and configures the development environment for Rource.
  It checks for required tools, installs missing components, and sets up
  environment variables.

Requirements:
  - Rust ${REQUIRED_RUST_VERSION} or later
  - wasm-pack (for WASM builds)
  - wasm32-unknown-unknown target
  - cargo-tarpaulin (for EXPERT+ coverage verification)

EXPERT+ Verification Tools (REQUIRED):
  - cargo-tarpaulin - Line coverage analysis
  - cargo doc --all-features - Documentation coverage

Formal Verification Tools (PEER REVIEWED PUBLISHED ACADEMIC):
  - Verus - Rust formal verification (Microsoft)
  - Coq 8.18+ - Proof assistant for dual verification
  - Install: ./scripts/setup-formal-verification.sh

Optional Tools:
  - wasm-opt (from binaryen) - WASM optimization
  - ffmpeg - Video export
  - Python 3 - PPM inspection scripts
  - cargo-llvm-cov - Alternative coverage reports

Environment Variables Set:
  RUST_BACKTRACE     Enables backtraces (default: 1)
  CARGO_TERM_COLOR   Enables colored output (default: always)
  ROURCE_PROJECT_ROOT Project root directory

EOF
}

# -----------------------------------------------------------------------------
# Main Entry Point
# -----------------------------------------------------------------------------

main() {
    # Parse arguments
    while [[ $# -gt 0 ]]; do
        case "$1" in
            -q|--quiet)
                QUIET_MODE=true
                shift
                ;;
            -v|--verbose)
                VERBOSE_MODE=true
                shift
                ;;
            -c|--check)
                CHECK_ONLY=true
                shift
                ;;
            -h|--help)
                show_help
                return 0
                ;;
            *)
                print_error "Unknown option: $1"
                show_help
                return 1
                ;;
        esac
    done

    setup_colors

    [[ "$QUIET_MODE" != true ]] && echo ""
    [[ "$QUIET_MODE" != true ]] && echo -e "${BOLD}Rource Development Environment Setup v${SCRIPT_VERSION}${NC}"
    [[ "$CHECK_ONLY" == true ]] && print_info "Running in check-only mode (no installations)"

    # Run all checks
    check_project_directory || true
    check_rust_toolchain || true
    check_wasm_target || true
    check_rust_components || true
    check_cargo_tools || true
    check_optional_tools || true
    check_build || true
    setup_environment || true

    print_summary
    return $?
}

# Run main function with all arguments
# Note: We don't use 'set -e' because this script is meant to be sourced,
# and we want to continue checking even if some checks fail
main "$@"
