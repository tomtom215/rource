// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Mobile Controls
 *
 * Handles mobile-specific UI patterns:
 * - Auto-hide controls (YouTube/Netflix pattern)
 * - Center play button overlay
 * - Uncapped FPS toggle in mobile toolbar
 * - Gesture feedback
 *
 * References:
 * - YouTube: Controls auto-hide after 4s during playback
 * - Netflix: Tap to show, auto-hide resumes
 * - Video games: Quick-access "turbo mode" toggles
 */

import { getRource, addManagedEventListener, get, setState, subscribe } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';
import { getElement } from '../dom.js';
import { hapticLight, hapticMedium } from '../utils.js';

// =============================================================================
// Constants
// =============================================================================

/** Hide delay in milliseconds (matches YouTube's 4 second pattern) */
const HIDE_DELAY = 4000;

/** Minimum screen width considered "mobile" */
const MOBILE_BREAKPOINT = 768;

// =============================================================================
// State
// =============================================================================

/** Timeout ID for auto-hide */
let hideTimeout = null;

/** Whether controls are currently visible */
let controlsVisible = true;

/** Whether the app is currently in mobile mode */
let isMobileMode = false;

/** Callback to check if animation is playing */
let isPlayingFn = null;

/** Callback to toggle play/pause */
let togglePlayFn = null;

// =============================================================================
// Auto-Hide Controls (YouTube/Netflix Pattern)
// =============================================================================

/**
 * Shows all mobile controls and resets the auto-hide timer.
 */
export function showControls() {
    if (!isMobileMode) return;

    controlsVisible = true;
    document.body.classList.remove('controls-hidden');

    // Clear any existing hide timer
    clearTimeout(hideTimeout);

    // Start new hide timer if playing
    if (isPlayingFn && isPlayingFn()) {
        hideTimeout = setTimeout(hideControls, HIDE_DELAY);
    }
}

/**
 * Hides all mobile controls.
 */
export function hideControls() {
    if (!isMobileMode) return;

    // Only hide if actually playing
    if (isPlayingFn && !isPlayingFn()) {
        return;
    }

    controlsVisible = false;
    document.body.classList.add('controls-hidden');
}

/**
 * Resets the auto-hide timer (call when user interacts).
 */
export function resetHideTimer() {
    if (!isMobileMode || !controlsVisible) return;

    clearTimeout(hideTimeout);

    if (isPlayingFn && isPlayingFn()) {
        hideTimeout = setTimeout(hideControls, HIDE_DELAY);
    }
}

/**
 * Called when playback state changes.
 * @param {boolean} playing - Whether currently playing
 */
export function onPlaybackStateChange(playing) {
    if (!isMobileMode) return;

    if (playing) {
        // Start hide timer when playback starts
        hideTimeout = setTimeout(hideControls, HIDE_DELAY);
        // Hide center play button
        updateCenterPlayButton(false);
    } else {
        // Show controls when paused
        showControls();
        // Show center play button
        updateCenterPlayButton(true);
    }
}

// =============================================================================
// Center Play Button (YouTube Pattern)
// =============================================================================

/**
 * Updates the center play button visibility.
 * @param {boolean} visible - Whether to show the button
 */
function updateCenterPlayButton(visible) {
    const centerPlay = document.getElementById('mobile-center-play');
    if (centerPlay) {
        centerPlay.classList.toggle('visible', visible && isMobileMode);
    }
}

/**
 * Handles center play button click.
 */
function handleCenterPlayClick() {
    hapticMedium(); // Confirmation feedback for play/pause
    if (togglePlayFn) {
        togglePlayFn();
    }
}

// =============================================================================
// Uncapped FPS Toggle (Mobile Toolbar)
// =============================================================================

/**
 * Updates the uncapped toggle button state.
 * @param {boolean} uncapped - Whether uncapped mode is enabled
 */
function updateUncappedButton(uncapped) {
    const btn = document.getElementById('mobile-uncapped-btn');
    if (btn) {
        btn.classList.toggle('active', uncapped);
        btn.setAttribute('aria-pressed', uncapped.toString());
    }

    // Also sync with the main perf overlay checkbox
    const checkbox = document.getElementById('perf-uncapped');
    if (checkbox && checkbox.checked !== uncapped) {
        checkbox.checked = uncapped;
    }
}

/**
 * Handles uncapped toggle button click.
 */
function handleUncappedToggle() {
    hapticMedium(); // Toggle feedback
    const currentState = get('uncappedFps');
    const newState = !currentState;

    setState({ uncappedFps: newState });
    updateUncappedButton(newState);

    // Trigger the change event on the main checkbox to sync all handlers
    const checkbox = document.getElementById('perf-uncapped');
    if (checkbox) {
        checkbox.checked = newState;
        checkbox.dispatchEvent(new Event('change', { bubbles: true }));
    }
}

// =============================================================================
// Canvas Tap Handler
// =============================================================================

/**
 * Handles tap/click on the canvas to show controls.
 * @param {Event} e - Click or touch event
 */
function handleCanvasTap(e) {
    if (!isMobileMode) return;

    // Don't interfere with drag gestures
    if (e.type === 'touchend' && e.changedTouches.length > 1) {
        return;
    }

    // Light haptic feedback for canvas tap
    hapticLight();

    // Toggle controls visibility
    if (controlsVisible) {
        // If controls are visible and playing, hide them
        if (isPlayingFn && isPlayingFn()) {
            hideControls();
        }
    } else {
        // If controls are hidden, show them
        showControls();
    }
}

// =============================================================================
// Mobile Mode Detection
// =============================================================================

/**
 * Checks if we're in mobile mode (has-bottom-sheet).
 * @returns {boolean} True if mobile mode is active
 */
function checkMobileMode() {
    return document.body.classList.contains('has-bottom-sheet') ||
           window.innerWidth <= MOBILE_BREAKPOINT;
}

/**
 * Updates mobile mode state.
 */
function updateMobileMode() {
    const wasMobile = isMobileMode;
    isMobileMode = checkMobileMode();

    // Clean up if switching from mobile to desktop
    if (wasMobile && !isMobileMode) {
        showControls();
        clearTimeout(hideTimeout);
    }
}

// =============================================================================
// Initialization
// =============================================================================

/**
 * Initializes mobile controls.
 *
 * @param {Object} options - Configuration options
 * @param {Function} options.isPlaying - Function to check if currently playing
 * @param {Function} options.togglePlay - Function to toggle play/pause
 */
export function initMobileControls(options = {}) {
    isPlayingFn = options.isPlaying;
    togglePlayFn = options.togglePlay;

    // Check initial mobile mode
    updateMobileMode();

    // Auto-collapse performance overlay on mobile for cleaner UI
    if (isMobileMode) {
        const perfOverlay = document.getElementById('perf-overlay');
        if (perfOverlay && !perfOverlay.classList.contains('collapsed')) {
            perfOverlay.classList.add('collapsed');
        }
    }

    // Canvas tap to show/hide controls
    const canvas = getElement('canvas');
    if (canvas) {
        // Use click for simple tap detection
        addManagedEventListener(canvas, 'click', handleCanvasTap);
    }

    // Center play button
    const centerPlay = document.getElementById('mobile-center-play');
    if (centerPlay) {
        addManagedEventListener(centerPlay, 'click', handleCenterPlayClick);
    }

    // Uncapped toggle button in mobile toolbar
    const uncappedBtn = document.getElementById('mobile-uncapped-btn');
    if (uncappedBtn) {
        addManagedEventListener(uncappedBtn, 'click', handleUncappedToggle);
        // Set initial state
        updateUncappedButton(get('uncappedFps') || false);
    }

    // Subscribe to uncapped state changes
    subscribe('uncappedFps', (value) => {
        updateUncappedButton(value);
    });

    // Listen for resize to update mobile mode
    addManagedEventListener(window, 'resize', updateMobileMode);

    // Reset hide timer on any user interaction with controls
    const controlElements = [
        '.mobile-toolbar',
        '.timeline-container',
        '.bottom-sheet-fab',
        '.perf-overlay'
    ];

    controlElements.forEach(selector => {
        const elements = document.querySelectorAll(selector);
        elements.forEach(el => {
            addManagedEventListener(el, 'click', resetHideTimer);
            addManagedEventListener(el, 'touchstart', resetHideTimer, { passive: true });
        });
    });

    console.log('Mobile controls initialized');
}

/**
 * Returns whether controls are currently visible.
 * @returns {boolean} True if controls are visible
 */
export function areControlsVisible() {
    return controlsVisible;
}

/**
 * Returns whether mobile mode is active.
 * @returns {boolean} True if in mobile mode
 */
export function isMobile() {
    return isMobileMode;
}
