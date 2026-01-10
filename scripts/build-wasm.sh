#!/bin/bash
# Build WASM module for Rource

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
WASM_DIR="$PROJECT_ROOT/rource-wasm"

echo "=== Building Rource WASM ==="
echo ""

# Check for wasm-pack
if ! command -v wasm-pack &> /dev/null; then
    echo "Error: wasm-pack not found. Install with: cargo install wasm-pack"
    exit 1
fi

cd "$WASM_DIR"

# Build with wasm-pack
echo "Building WASM with wasm-pack..."
wasm-pack build --target web --release

# Copy to www directory
echo "Copying package to www directory..."
cp -r pkg www/

# Optimize with wasm-opt if available
if command -v wasm-opt &> /dev/null; then
    echo "Optimizing with wasm-opt..."
    wasm-opt -Oz -o www/pkg/rource_wasm_bg_opt.wasm www/pkg/rource_wasm_bg.wasm
    mv www/pkg/rource_wasm_bg_opt.wasm www/pkg/rource_wasm_bg.wasm
    echo "WASM optimized"
else
    echo "Note: wasm-opt not found (optional - install via binaryen for smaller output)"
fi

# Print output sizes
echo ""
echo "=== Build Complete ==="
echo ""
echo "Output files in: $WASM_DIR/www/pkg/"
ls -lh www/pkg/*.wasm www/pkg/*.js 2>/dev/null || true

# Print gzip size estimate
if command -v gzip &> /dev/null; then
    echo ""
    echo "Gzip sizes:"
    for f in www/pkg/*.wasm; do
        if [ -f "$f" ]; then
            gzip_size=$(gzip -c "$f" | wc -c)
            echo "  $(basename "$f"): $(numfmt --to=iec $gzip_size 2>/dev/null || echo "$gzip_size bytes")"
        fi
    done
fi

echo ""
echo "To serve the demo:"
echo "  cd $WASM_DIR/www && python3 -m http.server 8080"
echo "  Then open http://localhost:8080"
