// @ts-check
const { test, expect } = require('@playwright/test');
const path = require('path');

/**
 * Rource Visual Feedback Loop — Screenshot Test Suite
 *
 * Captures screenshots of the analytics dashboard and visualization view
 * at multiple viewport sizes. Screenshots are saved to ./screenshots/ for
 * manual review and iterative visual defect fixing.
 *
 * Viewports tested:
 *   - mobile-375: iPhone SE (375x667, 2x DPR, touch)
 *   - tablet-768: iPad Mini (768x1024, 2x DPR)
 *   - desktop-1200: Standard desktop (1200x800)
 *   - wide-1920: Wide desktop (1920x1080)
 */

const SCREENSHOTS_DIR = path.join(__dirname, 'screenshots');

/**
 * Waits for the Rource app to finish loading.
 * The loading overlay hides when WASM init completes.
 */
async function waitForAppReady(page) {
    // Wait for the loading overlay to become hidden (has class 'hidden')
    await page.waitForFunction(() => {
        const overlay = document.getElementById('loading-overlay');
        return overlay && overlay.classList.contains('hidden');
    }, { timeout: 30000 });

    // Small delay for any post-init rendering
    await page.waitForTimeout(500);
}

/**
 * Waits for dashboard data to populate (summary cards show numbers, not "--")
 */
async function waitForDashboardData(page) {
    await page.waitForFunction(() => {
        const el = document.getElementById('acard-commits-value');
        return el && el.textContent && el.textContent !== '--';
    }, { timeout: 20000 });

    // Wait for tab content to render
    await page.waitForTimeout(500);
}

test.describe('Analytics Dashboard', () => {

    test('default landing — dashboard with data', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `dashboard-default-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });

    test('hotspots tab', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        // Hotspots is the default tab — just capture
        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `tab-hotspots-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });

    test('risk tab', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        await page.click('[data-tab="risk"]');
        await page.waitForTimeout(300);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `tab-risk-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });

    test('team tab', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        await page.click('[data-tab="team"]');
        await page.waitForTimeout(300);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `tab-team-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });

    test('temporal tab', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        await page.click('[data-tab="temporal"]');
        await page.waitForTimeout(300);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `tab-temporal-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });

    test('quality tab', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        await page.click('[data-tab="quality"]');
        await page.waitForTimeout(300);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `tab-quality-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });
});

test.describe('View Transitions', () => {

    test('visualize button transition', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        // Click Visualize
        await page.click('#btn-switch-to-viz');
        await page.waitForTimeout(1000);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `viz-view-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });

    test('back to analytics', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        // Switch to viz
        await page.click('#btn-switch-to-viz');
        await page.waitForTimeout(500);

        // Switch back to analytics
        await page.click('#btn-back-to-analytics');
        await page.waitForTimeout(500);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `back-to-analytics-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });
});

test.describe('URL Parameters', () => {

    test('direct viz view via URL', async ({ page }, testInfo) => {
        await page.goto('/?view=viz');
        await waitForAppReady(page);
        await page.waitForTimeout(2000);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `url-viz-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });
});

test.describe('Accessibility', () => {

    test('keyboard tab navigation', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        // Focus the first tab
        await page.click('[data-tab="hotspots"]');

        // Arrow right to risk tab
        await page.keyboard.press('ArrowRight');
        await page.waitForTimeout(200);

        // Arrow right to team tab
        await page.keyboard.press('ArrowRight');
        await page.waitForTimeout(200);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `a11y-keyboard-nav-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });

    test('focus indicators visible', async ({ page }, testInfo) => {
        await page.goto('/');
        await waitForAppReady(page);
        await waitForDashboardData(page);

        // Tab to the visualize button
        await page.keyboard.press('Tab');
        await page.keyboard.press('Tab');
        await page.waitForTimeout(200);

        await page.screenshot({
            path: path.join(SCREENSHOTS_DIR, `a11y-focus-${testInfo.project.name}.png`),
            fullPage: true,
        });
    });
});
