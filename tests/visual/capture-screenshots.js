#!/usr/bin/env node
// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource Visual Feedback Loop — Screenshot Capture Script
 *
 * Captures screenshots at multiple viewports for visual auditing.
 * Uses Playwright directly (not @playwright/test) for maximum compatibility.
 *
 * Usage: node capture-screenshots.js [--port 8787]
 *
 * Prerequisites:
 *   1. WASM binary must be built (www/pkg/rource_wasm_bg.wasm)
 *   2. HTTP server must be running: http-server ../../rource-wasm/www -p 8787
 */

const { chromium } = require('playwright');
const path = require('path');
const fs = require('fs');

const SCREENSHOTS_DIR = path.join(__dirname, 'screenshots');
const PORT = parseInt(process.argv.find((a, i) => process.argv[i - 1] === '--port') || '8787', 10);
const BASE_URL = `http://localhost:${PORT}`;

const VIEWPORTS = [
    { name: 'mobile-375', width: 375, height: 667, deviceScaleFactor: 2, isMobile: true, hasTouch: true },
    { name: 'tablet-768', width: 768, height: 1024, deviceScaleFactor: 2 },
    { name: 'desktop-1200', width: 1200, height: 800 },
    { name: 'wide-1920', width: 1920, height: 1080 },
];

async function waitForAppReady(page) {
    // Wait for loading overlay to be hidden
    await page.waitForFunction(() => {
        const overlay = document.getElementById('loading-overlay');
        return overlay && overlay.classList.contains('hidden');
    }, { timeout: 30000 });
    await page.waitForTimeout(500);
}

async function waitForDashboardData(page) {
    // Wait for summary cards to populate (not "--")
    await page.waitForFunction(() => {
        const el = document.getElementById('acard-commits-value');
        return el && el.textContent && el.textContent.trim() !== '--';
    }, { timeout: 30000 });
    await page.waitForTimeout(1000);
}

async function captureScreenshot(page, name) {
    const filePath = path.join(SCREENSHOTS_DIR, `${name}.png`);
    await page.screenshot({ path: filePath, fullPage: true });
    console.log(`  Captured: ${name}.png`);
    return filePath;
}

async function main() {
    // Ensure screenshots directory exists
    fs.mkdirSync(SCREENSHOTS_DIR, { recursive: true });

    console.log(`Connecting to ${BASE_URL}...`);

    const browser = await chromium.launch({
        headless: true,
        args: ['--no-sandbox', '--disable-setuid-sandbox', '--disable-gpu', '--disable-dev-shm-usage'],
    });

    try {
        for (const vp of VIEWPORTS) {
            console.log(`\n=== Viewport: ${vp.name} (${vp.width}x${vp.height}) ===`);

            const context = await browser.newContext({
                viewport: { width: vp.width, height: vp.height },
                deviceScaleFactor: vp.deviceScaleFactor || 1,
                isMobile: vp.isMobile || false,
                hasTouch: vp.hasTouch || false,
            });
            const page = await context.newPage();

            // Suppress console errors (WASM/WebGL noise)
            page.on('pageerror', () => {});

            try {
                // 1. Dashboard default state (after data loads)
                console.log('  Loading page...');
                await page.goto(BASE_URL, { waitUntil: 'load', timeout: 30000 });
                await waitForAppReady(page);
                await waitForDashboardData(page);
                await captureScreenshot(page, `dashboard-default-${vp.name}`);

                // 2. Click each tab
                for (const tab of ['risk', 'team', 'temporal', 'quality']) {
                    const tabBtn = page.locator(`#analytics-dashboard [data-tab="${tab}"]`);
                    if (await tabBtn.isVisible()) {
                        await tabBtn.click();
                        await page.waitForTimeout(300);
                        await captureScreenshot(page, `tab-${tab}-${vp.name}`);
                    }
                }

                // 3. Switch to viz view
                const vizBtn = page.locator('#btn-switch-to-viz');
                if (await vizBtn.isVisible() && await vizBtn.isEnabled()) {
                    await vizBtn.click();
                    await page.waitForTimeout(1500);
                    await captureScreenshot(page, `viz-view-${vp.name}`);

                    // 4. Back to analytics
                    const backBtn = page.locator('#btn-back-to-analytics');
                    if (await backBtn.isVisible()) {
                        await backBtn.click();
                        await page.waitForTimeout(500);
                        await captureScreenshot(page, `back-to-analytics-${vp.name}`);
                    }
                }

            } catch (err) {
                console.error(`  Error on ${vp.name}: ${err.message}`);
                // Try to capture error state
                try {
                    await captureScreenshot(page, `error-${vp.name}`);
                } catch { /* ignore */ }
            }

            await context.close();
        }

        console.log('\nScreenshot capture complete!');
        console.log(`Screenshots saved to: ${SCREENSHOTS_DIR}/`);

    } finally {
        await browser.close();
    }
}

main().catch(err => {
    console.error('Fatal error:', err);
    process.exit(1);
});
