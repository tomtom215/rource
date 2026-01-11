#!/bin/bash
# Quick preview of repository history
#
# Fast playback with reduced quality for quick review
#
# Usage: ./quick-preview.sh /path/to/repo

REPO_PATH="${1:-.}"

rource \
    --seconds-per-day 0.5 \
    --no-bloom \
    --hide-filenames \
    --max-files 500 \
    "$REPO_PATH"
