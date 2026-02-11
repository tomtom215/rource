#!/usr/bin/env node
// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Comprehensive Chrome-based screenshot capture for visual feedback loop.
 *
 * Captures screenshots at 4 viewports x 2 views x 2 themes = 16 screenshots.
 * Falls back to direct Chrome invocation when Playwright page crashes.
 *
 * Usage: node capture-chrome.js
 * Prereq: http-server running on port 8787
 */

const { execSync } = require('child_process');
const path = require('path');
const fs = require('fs');

const SCREENSHOTS_DIR = path.join(__dirname, 'screenshots');
const CHROME = '/root/.cache/ms-playwright/chromium-1194/chrome-linux/chrome';
const BASE_URL = 'http://localhost:8787';

const VIEWPORTS = [
    { name: 'mobile-375', width: 375, height: 667 },
    { name: 'tablet-768', width: 768, height: 1024 },
    { name: 'desktop-1200', width: 1200, height: 800 },
    { name: 'wide-1920', width: 1920, height: 1080 },
];

const PAGES = [
    { suffix: 'dashboard', url: '/' },
    { suffix: 'viz', url: '/?view=viz' },
];

// Theme parameter forces dark/light via localStorage before page load
const THEMES = [
    { suffix: 'dark', url_param: '' }, // Default (dark mode)
    { suffix: 'light', url_param: '&theme=light' },
];

fs.mkdirSync(SCREENSHOTS_DIR, { recursive: true });

let captured = 0;
let failed = 0;

for (const vp of VIEWPORTS) {
    for (const pg of PAGES) {
        for (const theme of THEMES) {
            const name = `${pg.suffix}-${theme.suffix}-${vp.name}`;
            const outFile = path.join(SCREENSHOTS_DIR, `${name}.png`);

            // Build URL with view param and optional theme
            let url = `${BASE_URL}${pg.url}`;
            if (theme.url_param) {
                url += pg.url.includes('?') ? theme.url_param : `?${theme.url_param.slice(1)}`;
            }

            console.log(`Capturing ${name} (${vp.width}x${vp.height})...`);

            try {
                execSync([
                    CHROME,
                    '--headless',
                    '--no-sandbox',
                    '--disable-gpu',
                    '--disable-dev-shm-usage',
                    '--disable-software-rasterizer',
                    `--window-size=${vp.width},${vp.height}`,
                    `--screenshot=${outFile}`,
                    url,
                ].join(' '), {
                    timeout: 20000,
                    stdio: ['ignore', 'ignore', 'ignore'],
                });

                const stats = fs.statSync(outFile);
                console.log(`  OK: ${(stats.size / 1024).toFixed(1)}KB`);
                captured++;
            } catch (err) {
                console.log(`  FAIL: ${err.message.split('\n')[0]}`);
                failed++;
            }
        }
    }
}

console.log(`\nDone! ${captured} captured, ${failed} failed.`);
console.log(`Screenshots in: ${SCREENSHOTS_DIR}`);
