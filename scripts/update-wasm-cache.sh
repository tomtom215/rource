#!/bin/bash
# ==============================================================================
# update-wasm-cache.sh - Update WASM demo cached commit data
# ==============================================================================
#
# This script generates the cached Rource commit history for the WASM demo.
# It extracts all commits from the repository and embeds them in cached-data.js
# so the demo can display the project's own history without API rate limits.
#
# Usage:
#   ./scripts/update-wasm-cache.sh
#
# The script updates:
#   - ROURCE_CACHED_DATA constant in rource-wasm/www/js/cached-data.js
#   - "Last updated" comment with current date
#
# Run this before releases or when significant commits have been added.
# ==============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CACHE_FILE="$PROJECT_ROOT/rource-wasm/www/js/cached-data.js"

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

# Verify cached-data.js exists
if [[ ! -f "$CACHE_FILE" ]]; then
    log_error "Cache file not found: $CACHE_FILE"
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
FILE_CHANGE_COUNT=$(wc -l < "$TEMP_LOG" | tr -d ' ')
FILE_COUNT=$(cut -d'|' -f4 "$TEMP_LOG" | sort -u | wc -l | tr -d ' ')
AUTHOR_COUNT=$(cut -d'|' -f2 "$TEMP_LOG" | sort -u | wc -l | tr -d ' ')

# Get actual git commit count (includes merge commits without file changes)
GIT_COMMIT_COUNT=$(git rev-list --count HEAD)

log_info "Found $GIT_COMMIT_COUNT git commits, $FILE_CHANGE_COUNT file changes, $FILE_COUNT unique files, $AUTHOR_COUNT authors"

# Get current date for the comment
CURRENT_DATE=$(date +%Y-%m-%d)

# Create the replacement JavaScript constant
# Using Python for reliable multiline string handling
export CACHE_FILE CURRENT_DATE TEMP_LOG GIT_COMMIT_COUNT
python3 << 'PYTHON_SCRIPT'
import sys
import re
import os

cache_file = os.environ.get('CACHE_FILE')
current_date = os.environ.get('CURRENT_DATE')
temp_log = os.environ.get('TEMP_LOG')
git_commit_count = os.environ.get('GIT_COMMIT_COUNT', '0')

# Read the log content from temp file
with open(temp_log, 'r', encoding='utf-8') as f:
    log_content = f.read().rstrip()

# Read the cache file
with open(cache_file, 'r', encoding='utf-8') as f:
    content = f.read()

# Pattern to match the Last updated date in the header comment
date_pattern = re.compile(r'(\* Last updated: )\d{4}-\d{2}-\d{2}')
content = date_pattern.sub(f'\\g<1>{current_date}', content)

# Update TOTAL_GIT_COMMITS constant (the actual git commit count)
commits_pattern = re.compile(r'export const TOTAL_GIT_COMMITS = \d+;')
content = commits_pattern.sub(f'export const TOTAL_GIT_COMMITS = {git_commit_count};', content)

# Pattern to match the ROURCE_CACHED_DATA export constant
# Matches: export const ROURCE_CACHED_DATA = `...`;
data_pattern = re.compile(
    r'(export const ROURCE_CACHED_DATA = `).*?(`;)',
    re.DOTALL
)

new_content, count = data_pattern.subn(f'\\g<1>{log_content}\\g<2>', content)

if count == 0:
    print("ERROR: Could not find ROURCE_CACHED_DATA pattern in cache file", file=sys.stderr)
    if 'ROURCE_CACHED_DATA' in content:
        print("Found 'ROURCE_CACHED_DATA' marker but pattern didn't match", file=sys.stderr)
    sys.exit(1)

# Write back
with open(cache_file, 'w', encoding='utf-8') as f:
    f.write(new_content)

print(f"SUCCESS: Updated ROURCE_CACHED_DATA with {len(log_content.splitlines())} entries")
print(f"Total git commits: {git_commit_count}")
PYTHON_SCRIPT

if [[ $? -eq 0 ]]; then
    log_info "Successfully updated $CACHE_FILE"
    log_info "Cache date: $CURRENT_DATE"
    log_info "Git commits: $GIT_COMMIT_COUNT"
    log_info "File changes: $FILE_CHANGE_COUNT"
    log_info "Unique files: $FILE_COUNT"
    log_info "Authors: $AUTHOR_COUNT"
else
    log_error "Failed to update cache file"
    exit 1
fi
