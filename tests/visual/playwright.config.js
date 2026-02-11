// @ts-check
const { defineConfig, devices } = require('@playwright/test');

/**
 * Playwright configuration for Rource visual feedback loop.
 * Captures screenshots at multiple viewports to audit visual quality.
 */
module.exports = defineConfig({
    testDir: '.',
    testMatch: '*.spec.js',
    timeout: 60000,
    retries: 0,
    workers: 1, // Sequential to avoid port conflicts

    use: {
        baseURL: 'http://localhost:8787',
        screenshot: 'off', // We take manual screenshots
        trace: 'off',
        launchOptions: {
            args: ['--no-sandbox', '--disable-setuid-sandbox', '--disable-gpu', '--disable-dev-shm-usage'],
        },
    },

    projects: [
        {
            name: 'mobile-375',
            use: {
                viewport: { width: 375, height: 667 },
                deviceScaleFactor: 2,
                isMobile: true,
                hasTouch: true,
            },
        },
        {
            name: 'tablet-768',
            use: {
                viewport: { width: 768, height: 1024 },
                deviceScaleFactor: 2,
            },
        },
        {
            name: 'desktop-1200',
            use: {
                viewport: { width: 1200, height: 800 },
            },
        },
        {
            name: 'wide-1920',
            use: {
                viewport: { width: 1920, height: 1080 },
            },
        },
    ],

    webServer: {
        command: 'npx serve ../../rource-wasm/www -l 8787 --no-clipboard',
        port: 8787,
        timeout: 30000,
        reuseExistingServer: true,
    },
});
