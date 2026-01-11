#!/bin/bash
# ==============================================================================
# update-wasm-cache.sh - Update WASM demo cached commit data
# ==============================================================================
#
# This script generates the cached Rource commit history for the WASM demo.
# It extracts all commits from the repository and embeds them in index.html
# so the demo can display the project's own history without API rate limits.
#
# Usage:
#   ./scripts/update-wasm-cache.sh
#
# The script updates:
#   - ROURCE_CACHED_DATA constant in rource-wasm/www/index.html
#   - "Last updated" comment with current date
#
# Run this before releases or when significant commits have been added.
# ==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
HTML_FILE="$PROJECT_ROOT/rource-wasm/www/index.html"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() { echo -e "${GREEN}[INFO]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

# Verify we're in a git repository
if ! git rev-parse --git-dir > /dev/null 2>&1; then
    log_error "Not in a git repository"
    exit 1
fi

# Verify index.html exists
if [[ ! -f "$HTML_FILE" ]]; then
    log_error "HTML file not found: $HTML_FILE"
    exit 1
fi

log_info "Generating commit log from git history..."

# Generate the Gource custom log format
# Format: timestamp|author|action|file
# - timestamp: Unix epoch seconds
# - author: Commit author name
# - action: A (add), M (modify), D (delete)
# - file: File path
TEMP_LOG=$(mktemp)
trap "rm -f $TEMP_LOG" EXIT

cd "$PROJECT_ROOT"

# Get commit log in Gource format
git log --reverse --pretty=format:'%at|%an' --name-status | \
awk -F'|' '
    /^[0-9]+\|/ { timestamp=$1; author=$2; next }
    /^A\t/ { print timestamp"|"author"|A|"substr($0, 3); next }
    /^M\t/ { print timestamp"|"author"|M|"substr($0, 3); next }
    /^D\t/ { print timestamp"|"author"|D|"substr($0, 3); next }
    /^R[0-9]*\t/ {
        # Rename: show as delete old + add new
        split(substr($0, index($0, "\t")+1), files, "\t")
        print timestamp"|"author"|D|"files[1]
        print timestamp"|"author"|A|"files[2]
        next
    }
' > "$TEMP_LOG"

# Count entries
COMMIT_COUNT=$(wc -l < "$TEMP_LOG" | tr -d ' ')
FILE_COUNT=$(cut -d'|' -f4 "$TEMP_LOG" | sort -u | wc -l | tr -d ' ')
AUTHOR_COUNT=$(cut -d'|' -f2 "$TEMP_LOG" | sort -u | wc -l | tr -d ' ')

log_info "Found $COMMIT_COUNT file changes, $FILE_COUNT unique files, $AUTHOR_COUNT authors"

# Get current date for the comment
CURRENT_DATE=$(date +%Y-%m-%d)

# Create the replacement JavaScript constant
# Using Python for reliable multiline string handling
export HTML_FILE CURRENT_DATE TEMP_LOG
python3 << 'PYTHON_SCRIPT'
import sys
import re
import os

html_file = os.environ.get('HTML_FILE')
current_date = os.environ.get('CURRENT_DATE')
temp_log = os.environ.get('TEMP_LOG')

# Read the log content from temp file
with open(temp_log, 'r', encoding='utf-8') as f:
    log_content = f.read().rstrip()

# Read the HTML file
with open(html_file, 'r', encoding='utf-8') as f:
    content = f.read()

# Pattern to match the cached data constant - simpler approach
# Match from "const ROURCE_CACHED_DATA = `" to the closing "`;"
pattern = re.compile(
    r'(// Last updated: )\d{4}-\d{2}-\d{2}(\s+// =+\s+const ROURCE_CACHED_DATA = `).*?(\`;)',
    re.DOTALL
)

# Build replacement
replacement = f'\\g<1>{current_date}\\g<2>{log_content}\\g<3>'

new_content, count = pattern.subn(replacement, content)

if count == 0:
    print("ERROR: Could not find ROURCE_CACHED_DATA pattern in HTML file", file=sys.stderr)
    # Debug: show what we're looking for
    if '// Last updated:' in content:
        print("Found '// Last updated:' marker", file=sys.stderr)
    if 'ROURCE_CACHED_DATA' in content:
        print("Found 'ROURCE_CACHED_DATA' marker", file=sys.stderr)
    sys.exit(1)

# Write back
with open(html_file, 'w', encoding='utf-8') as f:
    f.write(new_content)

print(f"SUCCESS: Updated ROURCE_CACHED_DATA with {len(log_content.splitlines())} entries")
PYTHON_SCRIPT

if [[ $? -eq 0 ]]; then
    log_info "Successfully updated $HTML_FILE"
    log_info "Cache date: $CURRENT_DATE"
    log_info "File changes: $COMMIT_COUNT"
    log_info "Unique files: $FILE_COUNT"
    log_info "Authors: $AUTHOR_COUNT"
else
    log_error "Failed to update HTML file"
    exit 1
fi
