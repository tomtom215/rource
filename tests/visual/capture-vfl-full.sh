#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# Comprehensive VFL (Visual Feedback Loop) capture script.
# Uses Chromium headless_shell with TMPDIR workaround for sandboxed environments.
#
# Captures: 4 viewports x 2 views x 2 themes = 16 core screenshots
# Plus additional viewports for edge-case coverage = 24+ total screenshots
#
# Usage: ./capture-vfl-full.sh [--port PORT]
# Prereq: HTTP server running on the specified port (default 8787)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCREENSHOTS_DIR="${SCRIPT_DIR}/screenshots"
CHROME_TMP="${SCRIPT_DIR}/.chrome-tmp"
HEADLESS_SHELL="/root/.cache/ms-playwright/chromium_headless_shell-1194/chrome-linux/headless_shell"
PORT="${1:-8787}"
BASE_URL="http://localhost:${PORT}"

# Viewports: standard 4 + 4 additional edge-case viewports
VIEWPORTS=(
    "mobile-375:375:667"
    "mobile-390:390:844"
    "tablet-768:768:1024"
    "tablet-1024:1024:768"
    "desktop-1200:1200:800"
    "desktop-1440:1440:900"
    "wide-1920:1920:1080"
    "ultrawide-2560:2560:1080"
)

# Views
VIEWS=(
    "dashboard:/"
    "viz:/?view=viz"
)

# Themes
THEMES=(
    "dark:"
    "light:theme=light"
)

mkdir -p "${SCREENSHOTS_DIR}" "${CHROME_TMP}"

captured=0
failed=0
total=0

for vp_entry in "${VIEWPORTS[@]}"; do
    IFS=':' read -r vp_name vp_w vp_h <<< "${vp_entry}"
    for view_entry in "${VIEWS[@]}"; do
        IFS=':' read -r view_name view_path <<< "${view_entry}"
        for theme_entry in "${THEMES[@]}"; do
            IFS=':' read -r theme_name theme_param <<< "${theme_entry}"
            total=$((total + 1))

            screenshot_name="${view_name}-${theme_name}-${vp_name}"
            out_file="${SCREENSHOTS_DIR}/${screenshot_name}.png"

            # Build URL
            url="${BASE_URL}${view_path}"
            if [ -n "${theme_param}" ]; then
                if [[ "${url}" == *"?"* ]]; then
                    url="${url}&${theme_param}"
                else
                    url="${url}?${theme_param}"
                fi
            fi

            printf "  [%2d/%2d] %-50s " "${total}" "$((${#VIEWPORTS[@]} * ${#VIEWS[@]} * ${#THEMES[@]}))" "${screenshot_name}"

            if TMPDIR="${CHROME_TMP}" "${HEADLESS_SHELL}" \
                --no-sandbox \
                --disable-gpu \
                --disable-dev-shm-usage \
                --disable-software-rasterizer \
                "--window-size=${vp_w},${vp_h}" \
                "--screenshot=${out_file}" \
                "${url}" >/dev/null 2>&1; then

                if [ -f "${out_file}" ]; then
                    size=$(stat -c%s "${out_file}" 2>/dev/null || stat -f%z "${out_file}" 2>/dev/null)
                    printf "OK (%s KB)\n" "$(echo "scale=1; ${size}/1024" | bc)"
                    captured=$((captured + 1))
                else
                    printf "FAIL (no output)\n"
                    failed=$((failed + 1))
                fi
            else
                printf "FAIL (chrome error)\n"
                failed=$((failed + 1))
            fi
        done
    done
done

echo ""
echo "VFL Capture Complete: ${captured} captured, ${failed} failed out of ${total} total"
echo "Screenshots directory: ${SCREENSHOTS_DIR}/"
echo ""

# Summary of unique theme checks
if command -v md5sum >/dev/null 2>&1; then
    echo "Theme differentiation check (dark vs light same viewport must differ):"
    for vp_entry in "${VIEWPORTS[@]}"; do
        IFS=':' read -r vp_name _ _ <<< "${vp_entry}"
        for view_entry in "${VIEWS[@]}"; do
            IFS=':' read -r view_name _ <<< "${view_entry}"
            dark_file="${SCREENSHOTS_DIR}/${view_name}-dark-${vp_name}.png"
            light_file="${SCREENSHOTS_DIR}/${view_name}-light-${vp_name}.png"
            if [ -f "${dark_file}" ] && [ -f "${light_file}" ]; then
                dark_md5=$(md5sum "${dark_file}" | cut -d' ' -f1)
                light_md5=$(md5sum "${light_file}" | cut -d' ' -f1)
                if [ "${dark_md5}" = "${light_md5}" ]; then
                    printf "  WARN: %s dark=light (identical!) - theme may not apply\n" "${view_name}-${vp_name}"
                else
                    printf "  OK:   %s dark!=light (themes differentiated)\n" "${view_name}-${vp_name}"
                fi
            fi
        done
    done
fi

# Clean up temp dir
rm -rf "${CHROME_TMP}"
