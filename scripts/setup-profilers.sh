#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>
#
# setup-profilers.sh - Install and configure profiling tools for Rource
#
# This script installs a comprehensive suite of profiling tools for finding
# performance bottlenecks at the microsecond/nanosecond level.
#
# Usage:
#   source scripts/setup-profilers.sh          # Install all tools
#   source scripts/setup-profilers.sh --check  # Check what's installed
#   source scripts/setup-profilers.sh --help   # Show help
#
# Profiler Categories:
#   CPU:         perf, cargo-flamegraph, samply, hotspot
#   Memory:      DHAT (via dhat crate), jemalloc-pprof, heaptrack
#   Cache:       Cachegrind, Callgrind (via Valgrind)
#   Instruction: iai-callgrind (deterministic CI benchmarks)
#   Tracing:     Tracy (real-time profiler)
#   WASM:        Chrome DevTools, wasmtime profiling
#   Causal:      Coz (identifies optimization opportunities)

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Detect OS
OS="unknown"
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    OS="linux"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    OS="macos"
fi

print_header() {
    echo -e "\n${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${CYAN}  $1${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}\n"
}

print_status() {
    local status=$1
    local name=$2
    local desc=$3

    if [[ "$status" == "installed" ]]; then
        echo -e "  ${GREEN}[OK]${NC} ${name} - ${desc}"
    elif [[ "$status" == "missing" ]]; then
        echo -e "  ${RED}✗${NC} ${name} - ${desc}"
    elif [[ "$status" == "optional" ]]; then
        echo -e "  ${YELLOW}○${NC} ${name} - ${desc} (optional)"
    else
        echo -e "  ${BLUE}?${NC} ${name} - ${desc}"
    fi
}

check_command() {
    command -v "$1" &> /dev/null
}

install_cargo_tools() {
    print_header "Installing Cargo-based Profiling Tools"

    # cargo-flamegraph - CPU flamegraph generation
    if ! check_command "flamegraph"; then
        echo -e "${YELLOW}Installing cargo-flamegraph...${NC}"
        cargo install flamegraph
    fi
    print_status "installed" "cargo-flamegraph" "CPU flamegraph generation"

    # samply - Interactive CPU profiler with Firefox Profiler UI
    if ! check_command "samply"; then
        echo -e "${YELLOW}Installing samply...${NC}"
        cargo install samply
    fi
    print_status "installed" "samply" "Interactive CPU profiling (Firefox Profiler UI)"

    # cargo-llvm-cov - Code coverage
    if ! check_command "cargo-llvm-cov"; then
        echo -e "${YELLOW}Installing cargo-llvm-cov...${NC}"
        cargo install cargo-llvm-cov
    fi
    print_status "installed" "cargo-llvm-cov" "LLVM-based code coverage"

    # iai-callgrind-runner - Required for iai-callgrind benchmarks
    if ! check_command "iai-callgrind-runner"; then
        echo -e "${YELLOW}Installing iai-callgrind-runner...${NC}"
        cargo install iai-callgrind-runner
    fi
    print_status "installed" "iai-callgrind-runner" "iai-callgrind benchmark runner"

    # hyperfine - Command-line benchmarking
    if ! check_command "hyperfine"; then
        echo -e "${YELLOW}Installing hyperfine...${NC}"
        cargo install hyperfine
    fi
    print_status "installed" "hyperfine" "Command-line benchmarking tool"
}

install_system_tools_linux() {
    print_header "Installing System Profiling Tools (Linux)"

    local packages_to_install=()

    # Check and collect packages
    if ! check_command "perf"; then
        packages_to_install+=("linux-tools-common" "linux-tools-$(uname -r)" 2>/dev/null || packages_to_install+=("linux-tools-generic"))
    fi
    print_status "$(check_command perf && echo installed || echo missing)" "perf" "Linux performance counters"

    if ! check_command "valgrind"; then
        packages_to_install+=("valgrind")
    fi
    print_status "$(check_command valgrind && echo installed || echo missing)" "valgrind" "Cachegrind, Callgrind, DHAT"

    if ! check_command "heaptrack"; then
        packages_to_install+=("heaptrack")
    fi
    print_status "$(check_command heaptrack && echo installed || echo missing)" "heaptrack" "Heap memory profiler"

    if ! check_command "hotspot"; then
        packages_to_install+=("hotspot")
    fi
    print_status "$(check_command hotspot && echo installed || echo missing)" "hotspot" "perf data visualizer GUI"

    # Install missing packages
    if [[ ${#packages_to_install[@]} -gt 0 ]]; then
        echo -e "\n${YELLOW}Installing system packages: ${packages_to_install[*]}${NC}"
        if check_command apt-get; then
            sudo apt-get update
            sudo apt-get install -y "${packages_to_install[@]}" || true
        elif check_command dnf; then
            sudo dnf install -y "${packages_to_install[@]}" || true
        elif check_command pacman; then
            sudo pacman -S --noconfirm "${packages_to_install[@]}" || true
        fi
    fi
}

install_system_tools_macos() {
    print_header "Installing System Profiling Tools (macOS)"

    # macOS uses different tools
    print_status "installed" "Instruments" "Xcode profiling (built-in)"
    print_status "installed" "sample" "CPU sampling (built-in)"
    print_status "installed" "leaks" "Memory leak detection (built-in)"

    # Homebrew packages
    if check_command brew; then
        if ! brew list valgrind &>/dev/null 2>&1; then
            echo -e "${YELLOW}Note: Valgrind not available on modern macOS. Using alternatives.${NC}"
        fi

        if ! check_command hyperfine; then
            brew install hyperfine
        fi
    else
        echo -e "${YELLOW}Homebrew not installed. Some tools may be unavailable.${NC}"
    fi
}

install_tracy() {
    print_header "Tracy Real-Time Profiler Setup"

    echo -e "${BLUE}Tracy requires building from source or downloading pre-built binaries.${NC}"
    echo -e "${BLUE}The tracing-tracy crate is already configured in Cargo.toml.${NC}"
    echo ""
    echo -e "To use Tracy:"
    echo -e "  1. Download Tracy from: ${CYAN}https://github.com/wolfpld/tracy/releases${NC}"
    echo -e "  2. Build with: ${CYAN}cargo build --profile profiling --features tracy${NC}"
    echo -e "  3. Run Tracy capture and then your application"
    echo ""
    print_status "optional" "Tracy" "Real-time nanosecond profiler"
}

install_wasm_tools() {
    print_header "WASM Profiling Tools"

    echo -e "${BLUE}WASM profiling is primarily done via browser DevTools:${NC}"
    echo ""
    echo -e "  ${GREEN}Chrome DevTools:${NC}"
    echo -e "    - Performance tab for CPU profiling"
    echo -e "    - Memory tab for heap snapshots"
    echo -e "    - Lighthouse for overall performance audits"
    echo ""
    echo -e "  ${GREEN}Firefox DevTools:${NC}"
    echo -e "    - Profiler for CPU sampling"
    echo -e "    - Memory tool for allocation tracking"
    echo ""
    echo -e "  ${GREEN}wasmtime profiling (for standalone WASM):${NC}"
    if check_command wasmtime; then
        echo -e "    wasmtime is installed"
        echo -e "    Use: ${CYAN}wasmtime run --profile=perfmap your.wasm${NC}"
    else
        echo -e "    ${YELLOW}wasmtime not installed${NC}"
        echo -e "    Install via: ${CYAN}curl https://wasmtime.dev/install.sh -sSf | bash${NC}"
    fi

    print_status "installed" "Browser DevTools" "Primary WASM profiling method"
}

setup_perf_permissions() {
    print_header "Configuring perf Permissions (Linux)"

    if [[ "$OS" != "linux" ]]; then
        echo -e "${YELLOW}Skipping: Not on Linux${NC}"
        return
    fi

    # Check current perf_event_paranoid setting
    local paranoid=$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo "unknown")
    echo -e "Current perf_event_paranoid: ${CYAN}$paranoid${NC}"

    if [[ "$paranoid" == "unknown" ]]; then
        echo -e "${YELLOW}Could not read perf_event_paranoid${NC}"
        return
    fi

    if [[ "$paranoid" -gt 1 ]]; then
        echo -e "${YELLOW}perf may require elevated permissions.${NC}"
        echo -e "To enable user-space profiling without sudo, run:"
        echo -e "  ${CYAN}sudo sysctl -w kernel.perf_event_paranoid=1${NC}"
        echo -e ""
        echo -e "To make this permanent, add to /etc/sysctl.conf:"
        echo -e "  ${CYAN}kernel.perf_event_paranoid=1${NC}"
    else
        echo -e "${GREEN}perf is configured for user-space profiling${NC}"
    fi
}

print_usage_guide() {
    print_header "Profiling Quick Reference"

    cat << 'EOF'
┌─────────────────────────────────────────────────────────────────────────────┐
│                         PROFILING TOOL QUICK REFERENCE                       │
├──────────────────┬──────────────┬────────────┬──────────────────────────────┤
│ Tool             │ Type         │ Overhead   │ Best For                     │
├──────────────────┼──────────────┼────────────┼──────────────────────────────┤
│ perf             │ CPU          │ Low        │ General CPU profiling        │
│ cargo-flamegraph │ CPU          │ Low        │ Quick flamegraph generation  │
│ samply           │ CPU          │ Low        │ Interactive analysis         │
│ Tracy            │ Multi        │ Low        │ Real-time nanosec tracing    │
│ DHAT             │ Memory       │ Medium     │ Allocation tracking          │
│ jemalloc-pprof   │ Memory       │ Very Low   │ Continuous memory profiling  │
│ Cachegrind       │ Cache        │ High       │ Cache miss analysis          │
│ iai-callgrind    │ Instructions │ Medium     │ Deterministic CI benchmarks  │
│ Coz              │ CPU          │ Low        │ Causal/actionable profiling  │
│ Chrome DevTools  │ WASM CPU     │ Low        │ Browser WASM profiling       │
└──────────────────┴──────────────┴────────────┴──────────────────────────────┘

COMMON COMMANDS:

  # CPU Flamegraph (requires perf on Linux, dtrace on macOS)
  cargo flamegraph --profile profiling -- --headless --output /tmp/frames .

  # Interactive CPU profiling with samply
  samply record ./target/profiling/rource --headless --output /tmp/frames .

  # Memory profiling with DHAT
  cargo build --profile dhat --features dhat
  ./target/dhat/rource --headless --output /tmp/frames .
  # Check dhat-heap.json for results

  # Valgrind Cachegrind (cache analysis)
  valgrind --tool=cachegrind ./target/profiling/rource --headless --output /tmp/frames .

  # iai-callgrind benchmarks (deterministic)
  cargo bench --bench iai_scene

  # Tracy real-time profiling
  cargo build --profile profiling --features tracy
  # Start Tracy capture, then run the binary

  # Hyperfine benchmarking
  hyperfine --warmup 3 './target/release/rource --headless --output /tmp/frames .'

  # WASM profiling (in browser)
  # 1. Build with debug info: ./scripts/build-wasm.sh --debug
  # 2. Open Chrome DevTools > Performance tab
  # 3. Record while using the demo

For comprehensive documentation, see: docs/PROFILING.md
EOF
}

check_all() {
    print_header "Profiling Tools Status"

    echo -e "${BLUE}Cargo Tools:${NC}"
    print_status "$(check_command flamegraph && echo installed || echo missing)" "cargo-flamegraph" "CPU flamegraphs"
    print_status "$(check_command samply && echo installed || echo missing)" "samply" "Interactive profiling"
    print_status "$(check_command cargo-llvm-cov && echo installed || echo missing)" "cargo-llvm-cov" "Code coverage"
    print_status "$(check_command iai-callgrind-runner && echo installed || echo missing)" "iai-callgrind-runner" "Deterministic benchmarks"
    print_status "$(check_command hyperfine && echo installed || echo missing)" "hyperfine" "CLI benchmarking"

    echo -e "\n${BLUE}System Tools:${NC}"
    if [[ "$OS" == "linux" ]]; then
        print_status "$(check_command perf && echo installed || echo missing)" "perf" "Linux perf"
        print_status "$(check_command valgrind && echo installed || echo missing)" "valgrind" "Valgrind suite"
        print_status "$(check_command heaptrack && echo installed || echo missing)" "heaptrack" "Heap profiling"
        print_status "$(check_command hotspot && echo installed || echo missing)" "hotspot" "perf GUI"
    elif [[ "$OS" == "macos" ]]; then
        print_status "installed" "Instruments" "Xcode profiling"
        print_status "installed" "sample" "CPU sampling"
    fi

    echo -e "\n${BLUE}WASM Tools:${NC}"
    print_status "$(check_command wasmtime && echo installed || echo missing)" "wasmtime" "WASM runtime"
    print_status "installed" "Browser DevTools" "Primary WASM method"
}

show_help() {
    cat << EOF
Rource Profiler Setup Script

USAGE:
    source scripts/setup-profilers.sh [OPTIONS]

OPTIONS:
    --check     Check which profiling tools are installed
    --help      Show this help message
    (no args)   Install all available profiling tools

PROFILERS INSTALLED:
    CPU:         perf, cargo-flamegraph, samply, hotspot
    Memory:      DHAT, jemalloc-pprof, heaptrack
    Cache:       Cachegrind, Callgrind (via Valgrind)
    Instruction: iai-callgrind
    Tracing:     Tracy
    WASM:        Browser DevTools, wasmtime

For detailed usage documentation, see docs/PROFILING.md
EOF
}

main() {
    local check_only=false

    for arg in "$@"; do
        case $arg in
            --check)
                check_only=true
                ;;
            --help|-h)
                show_help
                return 0
                ;;
        esac
    done

    if [[ "$check_only" == true ]]; then
        check_all
        return 0
    fi

    echo -e "${CYAN}"
    echo "╔═══════════════════════════════════════════════════════════════════════════╗"
    echo "║                    ROURCE PROFILER SETUP                                   ║"
    echo "║                                                                            ║"
    echo "║  Installing tools to find every wasted CPU cycle and byte allocation      ║"
    echo "╚═══════════════════════════════════════════════════════════════════════════╝"
    echo -e "${NC}"

    install_cargo_tools

    if [[ "$OS" == "linux" ]]; then
        install_system_tools_linux
        setup_perf_permissions
    elif [[ "$OS" == "macos" ]]; then
        install_system_tools_macos
    fi

    install_tracy
    install_wasm_tools
    print_usage_guide

    echo -e "\n${GREEN}Profiler setup complete!${NC}"
    echo -e "Run ${CYAN}source scripts/setup-profilers.sh --check${NC} to verify installation."
}

# Only run main if script is being executed (not sourced for functions)
if [[ "${BASH_SOURCE[0]}" == "${0}" ]] || [[ -z "${BASH_SOURCE[0]:-}" ]]; then
    main "$@"
fi
