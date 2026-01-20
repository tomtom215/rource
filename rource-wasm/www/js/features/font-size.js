/**
 * Rource - Font Size Control Feature
 *
 * Allows users to adjust the label font size dynamically.
 */

import { getElement } from '../dom.js';
import { getRource, hasData } from '../state.js';
import { safeWasmCall, safeWasmVoid } from '../wasm-api.js';
import { showToast } from '../toast.js';

// Font size limits
const MIN_FONT_SIZE = 6;
const MAX_FONT_SIZE = 32;
const FONT_SIZE_STEP = 2;

// Default font size
const DEFAULT_FONT_SIZE = 12;

/**
 * Gets the current font size from WASM.
 * @returns {number} Current font size
 */
export function getFontSize() {
    const rource = getRource();
    if (!rource) return DEFAULT_FONT_SIZE;
    return safeWasmCall('getFontSize', () => rource.getFontSize(), DEFAULT_FONT_SIZE);
}

/**
 * Sets the font size in WASM and updates UI.
 * @param {number} size - New font size
 */
export function setFontSize(size) {
    const rource = getRource();
    if (!rource) return;

    const clampedSize = Math.max(MIN_FONT_SIZE, Math.min(MAX_FONT_SIZE, size));
    safeWasmVoid('setFontSize', () => rource.setFontSize(clampedSize));
    updateFontSizeUI();
}

/**
 * Increases the font size by one step.
 */
export function increaseFontSize() {
    const currentSize = getFontSize();
    if (currentSize < MAX_FONT_SIZE) {
        setFontSize(currentSize + FONT_SIZE_STEP);
    }
}

/**
 * Decreases the font size by one step.
 */
export function decreaseFontSize() {
    const currentSize = getFontSize();
    if (currentSize > MIN_FONT_SIZE) {
        setFontSize(currentSize - FONT_SIZE_STEP);
    }
}

/**
 * Resets font size to default.
 */
export function resetFontSize() {
    setFontSize(DEFAULT_FONT_SIZE);
}

/**
 * Updates the font size UI display.
 */
export function updateFontSizeUI() {
    const fontSizeValue = getElement('fontSizeValue');
    const btnDecrease = getElement('btnFontDecrease');
    const btnIncrease = getElement('btnFontIncrease');

    if (!fontSizeValue) return;

    const currentSize = getFontSize();
    fontSizeValue.textContent = Math.round(currentSize).toString();

    // Update button states
    if (btnDecrease) {
        btnDecrease.disabled = !hasData() || currentSize <= MIN_FONT_SIZE;
    }
    if (btnIncrease) {
        btnIncrease.disabled = !hasData() || currentSize >= MAX_FONT_SIZE;
    }
}

/**
 * Enables font size controls after data is loaded.
 */
export function enableFontSizeControls() {
    const btnDecrease = getElement('btnFontDecrease');
    const btnIncrease = getElement('btnFontIncrease');

    if (btnDecrease) btnDecrease.disabled = false;
    if (btnIncrease) btnIncrease.disabled = false;

    updateFontSizeUI();
}

/**
 * Disables font size controls.
 */
export function disableFontSizeControls() {
    const btnDecrease = getElement('btnFontDecrease');
    const btnIncrease = getElement('btnFontIncrease');

    if (btnDecrease) btnDecrease.disabled = true;
    if (btnIncrease) btnIncrease.disabled = true;
}

/**
 * Initializes font size control handlers.
 */
export function initFontSizeControl() {
    const btnDecrease = getElement('btnFontDecrease');
    const btnIncrease = getElement('btnFontIncrease');

    if (btnDecrease) {
        btnDecrease.addEventListener('click', () => {
            decreaseFontSize();
        });
    }

    if (btnIncrease) {
        btnIncrease.addEventListener('click', () => {
            increaseFontSize();
        });
    }

    // Initialize display
    updateFontSizeUI();
}

// Export constants for use elsewhere
export { MIN_FONT_SIZE, MAX_FONT_SIZE, DEFAULT_FONT_SIZE };
