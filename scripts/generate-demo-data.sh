#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>
#
# Generates extended demo data by cloning real repositories from GitHub.
# Output goes to rource-wasm/www/demo-data/ as fetch-on-demand .log files.
#
# These files provide ~5,000 file-change entries per repo (capped) from
# real commit history, giving a much richer visualization than the small
# embedded constants in static-logs.js.
#
# The demo-data/ directory is included in the GitHub Pages deployment but
# can be excluded from self-hosted WASM builds to reduce download size.
#
# Usage:
#   ./scripts/generate-demo-data.sh
#
# Output:
#   rource-wasm/www/demo-data/{owner}-{repo}.log  (one per repo)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
OUTPUT_DIR="$PROJECT_ROOT/rource-wasm/www/demo-data"
TEMP_DIR="$(mktemp -d)"

# Max file-change entries per repo (keeps files under ~500 KB each)
MAX_ENTRIES=5000

# Clone depth (number of commits to fetch)
CLONE_DEPTH=500

# Repos to generate logs for
REPOS=(
    "facebook/react"
    "vuejs/vue"
    "sveltejs/svelte"
    "denoland/deno"
    "rust-lang/rust"
    "microsoft/vscode"
    "golang/go"
    "torvalds/linux"
)

cleanup() {
    rm -rf "$TEMP_DIR"
}
trap cleanup EXIT

mkdir -p "$OUTPUT_DIR"

echo "Generating extended demo data for ${#REPOS[@]} repositories..."
echo "Output directory: $OUTPUT_DIR"
echo "Clone depth: $CLONE_DEPTH commits, max $MAX_ENTRIES entries per repo"
echo ""

for repo in "${REPOS[@]}"; do
    owner=$(echo "$repo" | cut -d'/' -f1)
    name=$(echo "$repo" | cut -d'/' -f2)
    filename="${owner}-${name}.log"
    output_file="$OUTPUT_DIR/$filename"
    temp_file="$TEMP_DIR/${name}_full.log"

    echo "Processing $repo..."

    # Clone with shallow history
    repo_dir="$TEMP_DIR/$name"
    if ! git clone --depth "$CLONE_DEPTH" --single-branch "https://github.com/$repo.git" "$repo_dir" 2>/dev/null; then
        echo "  WARNING: Failed to clone $repo, skipping"
        continue
    fi

    cd "$repo_dir"

    # Extract full log in Rource custom format
    git log --reverse --pretty=format:'%at|%an' --name-status | \
    awk -F'|' '
        /^[0-9]+\|/ { timestamp=$1; author=$2; next }
        /^A\t/ { print timestamp"|"author"|A|"substr($0, 3); next }
        /^M\t/ { print timestamp"|"author"|M|"substr($0, 3); next }
        /^D\t/ { print timestamp"|"author"|D|"substr($0, 3); next }
        /^R[0-9]*\t/ {
            split(substr($0, index($0, "\t")+1), files, "\t")
            print timestamp"|"author"|D|"files[1]
            print timestamp"|"author"|A|"files[2]
            next
        }
    ' > "$temp_file" || true

    total=$(wc -l < "$temp_file" | tr -d ' ')

    if [ "$total" -le "$MAX_ENTRIES" ]; then
        mv "$temp_file" "$output_file"
    else
        # Keep the most recent entries (tail)
        tail -n "$MAX_ENTRIES" "$temp_file" > "$output_file"
        rm -f "$temp_file"
    fi

    count=$(wc -l < "$output_file" | tr -d ' ')
    authors=$(cut -d'|' -f2 "$output_file" | sort -u | wc -l | tr -d ' ')
    files=$(cut -d'|' -f4 "$output_file" | sort -u | wc -l | tr -d ' ')
    size=$(du -h "$output_file" | cut -f1)

    echo "  $filename: $count/$total entries, $authors authors, $files files ($size)"

    # Clean up clone to save disk space
    rm -rf "$repo_dir"

    cd "$PROJECT_ROOT"
done

echo ""
echo "Done! Generated demo data:"
ls -lh "$OUTPUT_DIR"/*.log
echo ""
echo "Total size:"
du -sh "$OUTPUT_DIR"
