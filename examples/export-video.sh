#!/bin/bash
# Export repository history to MP4 video
#
# Usage: ./export-video.sh /path/to/repo output.mp4
#
# Requirements: rource, ffmpeg

set -e

REPO_PATH="${1:-.}"
OUTPUT_FILE="${2:-output.mp4}"
TEMP_DIR=$(mktemp -d)
FRAMERATE=60
SECONDS_PER_DAY=2.0

echo "Exporting repository: $REPO_PATH"
echo "Output file: $OUTPUT_FILE"
echo "Temporary frames: $TEMP_DIR"

# Export frames
echo "Generating frames..."
rource \
    --headless \
    --output "$TEMP_DIR" \
    --framerate "$FRAMERATE" \
    --seconds-per-day "$SECONDS_PER_DAY" \
    --no-bloom \
    "$REPO_PATH"

# Count frames
FRAME_COUNT=$(ls -1 "$TEMP_DIR"/*.ppm 2>/dev/null | wc -l)
echo "Generated $FRAME_COUNT frames"

if [ "$FRAME_COUNT" -eq 0 ]; then
    echo "Error: No frames generated"
    rm -rf "$TEMP_DIR"
    exit 1
fi

# Convert to video
echo "Encoding video..."
ffmpeg -y \
    -framerate "$FRAMERATE" \
    -i "$TEMP_DIR/frame_%08d.ppm" \
    -c:v libx264 \
    -preset medium \
    -crf 23 \
    -pix_fmt yuv420p \
    "$OUTPUT_FILE"

# Cleanup
echo "Cleaning up..."
rm -rf "$TEMP_DIR"

echo "Done! Video saved to: $OUTPUT_FILE"
