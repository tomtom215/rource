#!/bin/bash
# Rource Development Session Setup Script
# Run with: source scripts/session-setup.sh

set -e

echo "=== Rource Development Environment Setup ==="
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

check_installed() {
    if command -v "$1" &> /dev/null; then
        echo -e "${GREEN}[OK]${NC} $1 is installed"
        return 0
    else
        echo -e "${RED}[MISSING]${NC} $1 is not installed"
        return 1
    fi
}

# Check Rust toolchain
echo "Checking Rust toolchain..."
if check_installed rustc; then
    RUST_VERSION=$(rustc --version | awk '{print $2}')
    echo "    Version: $RUST_VERSION"
else
    echo -e "${YELLOW}Installing Rust via rustup...${NC}"
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source "$HOME/.cargo/env"
fi

if check_installed cargo; then
    CARGO_VERSION=$(cargo --version | awk '{print $2}')
    echo "    Version: $CARGO_VERSION"
fi

# Check rustup
if ! check_installed rustup; then
    echo -e "${RED}Error: rustup is required but not installed${NC}"
    echo "Please install rustup from https://rustup.rs/"
    return 1 2>/dev/null || exit 1
fi

# Check WASM target
echo ""
echo "Checking WASM target..."
if rustup target list --installed | grep -q "wasm32-unknown-unknown"; then
    echo -e "${GREEN}[OK]${NC} wasm32-unknown-unknown target is installed"
else
    echo -e "${YELLOW}Installing wasm32-unknown-unknown target...${NC}"
    rustup target add wasm32-unknown-unknown
fi

# Check wasm-pack
echo ""
echo "Checking wasm-pack..."
if check_installed wasm-pack; then
    WASM_PACK_VERSION=$(wasm-pack --version | awk '{print $2}')
    echo "    Version: $WASM_PACK_VERSION"
else
    echo -e "${YELLOW}Installing wasm-pack...${NC}"
    cargo install wasm-pack
fi

# Check clippy
echo ""
echo "Checking Rust components..."
if rustup component list --installed | grep -q "clippy"; then
    echo -e "${GREEN}[OK]${NC} clippy is installed"
else
    echo -e "${YELLOW}Installing clippy...${NC}"
    rustup component add clippy
fi

# Check rustfmt
if rustup component list --installed | grep -q "rustfmt"; then
    echo -e "${GREEN}[OK]${NC} rustfmt is installed"
else
    echo -e "${YELLOW}Installing rustfmt...${NC}"
    rustup component add rustfmt
fi

# Check optional tools
echo ""
echo "Checking optional tools..."
if check_installed wasm-opt; then
    echo "    (wasm-opt provides additional WASM optimization)"
else
    echo -e "${YELLOW}[INFO]${NC} wasm-opt not found (optional - install via binaryen)"
fi

if check_installed cargo-watch; then
    echo "    (cargo-watch enables auto-rebuild on file changes)"
else
    echo -e "${YELLOW}[INFO]${NC} cargo-watch not found (optional - install with: cargo install cargo-watch)"
fi

# Summary
echo ""
echo "=== Setup Complete ==="
echo ""
echo "You're ready to develop Rource!"
echo ""
echo "Quick commands:"
echo "  cargo build           - Build debug version"
echo "  cargo build --release - Build release version"
echo "  cargo test            - Run tests"
echo "  cargo clippy          - Run linter"
echo "  cargo fmt             - Format code"
echo "  wasm-pack build       - Build WASM version"
echo ""
