#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>
#
# Generates static log files for popular repositories.
# These logs are used for zero-API-call demo visualization.
#
# Usage: ./scripts/generate-static-logs.sh
#
# Output: rource-wasm/www/static/logs/*.log

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
OUTPUT_DIR="$PROJECT_ROOT/rource-wasm/www/static/logs"
TEMP_DIR="$(mktemp -d)"

# Popular repos to generate logs for
REPOS=(
    "facebook/react"
    "vuejs/vue"
    "sveltejs/svelte"
    "denoland/deno"
    "rust-lang/rust"
    "microsoft/vscode"
    "torvalds/linux"
    "golang/go"
)

# Maximum commits to include (keeps file sizes reasonable)
MAX_COMMITS=500

cleanup() {
    rm -rf "$TEMP_DIR"
}
trap cleanup EXIT

mkdir -p "$OUTPUT_DIR"

echo "Generating static logs for ${#REPOS[@]} repositories..."
echo "Output directory: $OUTPUT_DIR"
echo ""

for repo in "${REPOS[@]}"; do
    owner=$(echo "$repo" | cut -d'/' -f1)
    name=$(echo "$repo" | cut -d'/' -f2)
    filename="${owner}-${name}.log"
    output_file="$OUTPUT_DIR/$filename"

    echo "Processing $repo..."

    # Clone with shallow history
    repo_dir="$TEMP_DIR/$name"
    if ! git clone --depth "$MAX_COMMITS" --single-branch "https://github.com/$repo.git" "$repo_dir" 2>/dev/null; then
        echo "  WARNING: Failed to clone $repo, skipping"
        continue
    fi

    cd "$repo_dir"

    # Generate log in Rource custom format: timestamp|author|action|filepath
    # Using --name-status to get file changes
    git log --reverse --format="%at|%an" --name-status HEAD~"$MAX_COMMITS"..HEAD 2>/dev/null | \
    awk '
    BEGIN { FS="|"; OFS="|" }
    /^[0-9]+\|/ {
        timestamp = $1
        author = $2
        gsub(/\|/, "_", author)  # Sanitize pipes in author names
        next
    }
    /^[AMDRT]\t/ {
        action = substr($0, 1, 1)
        filepath = substr($0, 3)
        gsub(/\|/, "_", filepath)  # Sanitize pipes in filenames
        # Handle renames (R100\told\tnew format)
        if (action == "R") {
            split(filepath, parts, "\t")
            filepath = parts[2]  # Use new filename
            action = "M"
        }
        if (timestamp && author && filepath) {
            print timestamp, author, action, filepath
        }
    }
    ' > "$output_file" || true

    # Count entries
    count=$(wc -l < "$output_file" | tr -d ' ')
    size=$(du -h "$output_file" | cut -f1)

    echo "  Generated $filename: $count entries ($size)"

    cd "$PROJECT_ROOT"
done

echo ""
echo "Done! Generated logs:"
ls -lh "$OUTPUT_DIR"/*.log 2>/dev/null || echo "No logs generated"

# Generate manifest file for JavaScript consumption
MANIFEST_FILE="$OUTPUT_DIR/manifest.json"
echo "Generating manifest..."

cat > "$MANIFEST_FILE" << 'HEADER'
{
  "generated": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "repos": [
HEADER

first=true
for repo in "${REPOS[@]}"; do
    owner=$(echo "$repo" | cut -d'/' -f1)
    name=$(echo "$repo" | cut -d'/' -f2)
    filename="${owner}-${name}.log"
    filepath="$OUTPUT_DIR/$filename"

    if [[ -f "$filepath" ]]; then
        count=$(wc -l < "$filepath" | tr -d ' ')

        if [[ "$first" == "true" ]]; then
            first=false
        else
            echo "," >> "$MANIFEST_FILE"
        fi

        echo -n "    {\"owner\": \"$owner\", \"repo\": \"$name\", \"file\": \"$filename\", \"entries\": $count}" >> "$MANIFEST_FILE"
    fi
done

cat >> "$MANIFEST_FILE" << 'FOOTER'

  ]
}
FOOTER

echo "Manifest written to: $MANIFEST_FILE"
