// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Mobile Toolbar
 *
 * Handles the floating quick-action toolbar on mobile devices.
 * Provides easy access to common actions: screenshot, labels, fullscreen, theme, help.
 */

import { addManagedEventListener, getState, getRource } from '../state.js';
import { showToast } from '../toast.js';

// External function references (set via init)
let captureScreenshotFn = null;
let toggleThemeFn = null;
let toggleFullscreenFn = null;
let showHelpFn = null;
let toggleLabelsFn = null;

// Track labels state
let labelsEnabled = true;

/**
 * Initializes the mobile toolbar with event handlers.
 * Call this after WASM is ready.
 *
 * @param {Object} options - External functions to connect
 * @param {Function} options.captureScreenshot - Screenshot capture function
 * @param {Function} options.toggleTheme - Theme toggle function
 * @param {Function} options.toggleFullscreen - Fullscreen toggle function
 * @param {Function} options.showHelp - Help display function
 */
export function initMobileToolbar(options = {}) {
    captureScreenshotFn = options.captureScreenshot;
    toggleThemeFn = options.toggleTheme;
    toggleFullscreenFn = options.toggleFullscreen;
    showHelpFn = options.showHelp;
    toggleLabelsFn = options.toggleLabels;

    const screenshotBtn = document.getElementById('mobile-screenshot-btn');
    const labelsBtn = document.getElementById('mobile-labels-btn');
    const fullscreenBtn = document.getElementById('mobile-fullscreen-btn');
    const themeBtn = document.getElementById('mobile-theme-btn');
    const helpBtn = document.getElementById('mobile-help-btn');

    // Screenshot button
    if (screenshotBtn) {
        addManagedEventListener(screenshotBtn, 'click', handleScreenshot);
    }

    // Labels toggle button
    if (labelsBtn) {
        addManagedEventListener(labelsBtn, 'click', handleLabelsToggle);
        // Set initial active state based on default
        updateLabelsButtonState(labelsBtn, labelsEnabled);
    }

    // Fullscreen button
    if (fullscreenBtn) {
        addManagedEventListener(fullscreenBtn, 'click', handleFullscreen);
    }

    // Theme button
    if (themeBtn) {
        addManagedEventListener(themeBtn, 'click', handleTheme);
        // Update icon visibility based on current theme
        updateThemeButtonIcons(themeBtn);
    }

    // Help button
    if (helpBtn) {
        addManagedEventListener(helpBtn, 'click', handleHelp);
    }

    console.log('Mobile toolbar initialized');
}

/**
 * Handles screenshot button click.
 */
async function handleScreenshot() {
    if (captureScreenshotFn) {
        try {
            await captureScreenshotFn();
        } catch (error) {
            showToast('Screenshot failed: ' + error.message, 'error');
        }
    } else {
        showToast('Screenshot not available', 'error');
    }
}

/**
 * Handles labels toggle button click.
 */
function handleLabelsToggle() {
    const rource = getRource();
    if (!rource) return;

    labelsEnabled = !labelsEnabled;

    try {
        rource.setLabelsEnabled(labelsEnabled);
        const labelsBtn = document.getElementById('mobile-labels-btn');
        if (labelsBtn) {
            updateLabelsButtonState(labelsBtn, labelsEnabled);
        }
    } catch (error) {
        console.error('Failed to toggle labels:', error);
    }
}

/**
 * Updates the labels button visual state.
 * @param {HTMLElement} btn - The button element
 * @param {boolean} enabled - Whether labels are enabled
 */
function updateLabelsButtonState(btn, enabled) {
    if (enabled) {
        btn.classList.add('active');
    } else {
        btn.classList.remove('active');
    }
}

/**
 * Handles fullscreen button click.
 */
function handleFullscreen() {
    if (toggleFullscreenFn) {
        toggleFullscreenFn();
    } else {
        // Fallback: try to enter fullscreen on the canvas container
        const container = document.getElementById('canvas-container');
        if (container && container.requestFullscreen) {
            container.requestFullscreen().catch(() => {
                showToast('Fullscreen not available', 'error');
            });
        }
    }
}

/**
 * Handles theme button click.
 */
function handleTheme() {
    if (toggleThemeFn) {
        toggleThemeFn();
    } else {
        // Fallback: toggle light-theme class
        document.documentElement.classList.toggle('light-theme');
    }

    // Update button icons
    const themeBtn = document.getElementById('mobile-theme-btn');
    if (themeBtn) {
        updateThemeButtonIcons(themeBtn);
    }
}

/**
 * Updates the theme button icon visibility based on current theme.
 * @param {HTMLElement} btn - The button element
 */
function updateThemeButtonIcons(btn) {
    const isLight = document.documentElement.classList.contains('light-theme');
    const sunIcon = btn.querySelector('.sun-icon');
    const moonIcon = btn.querySelector('.moon-icon');

    if (sunIcon && moonIcon) {
        sunIcon.style.display = isLight ? 'block' : 'none';
        moonIcon.style.display = isLight ? 'none' : 'block';
    }
}

/**
 * Handles help button click.
 */
function handleHelp() {
    if (showHelpFn) {
        showHelpFn();
    } else {
        // Fallback: show help overlay using visibility class pattern
        const helpOverlay = document.querySelector('.help-overlay');
        if (helpOverlay) {
            helpOverlay.classList.add('visible');
        }
    }
}

/**
 * Sets the labels enabled state (for external synchronization).
 * @param {boolean} enabled - Whether labels are enabled
 */
export function setLabelsState(enabled) {
    labelsEnabled = enabled;
    const labelsBtn = document.getElementById('mobile-labels-btn');
    if (labelsBtn) {
        updateLabelsButtonState(labelsBtn, enabled);
    }
}

/**
 * Enables or disables the screenshot button.
 * @param {boolean} enabled - Whether to enable the button
 */
export function setScreenshotEnabled(enabled) {
    const btn = document.getElementById('mobile-screenshot-btn');
    if (btn) {
        btn.disabled = !enabled;
    }
}
