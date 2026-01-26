// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Immersive Fullscreen Mode
 *
 * Provides a cinema/video-game style fullscreen experience on mobile landscape:
 * - Auto-prompts for fullscreen when landscape is detected
 * - Minimal HUD overlay controls that auto-hide
 * - Touch anywhere to show/hide controls
 * - Swipe up/down gestures for quick actions
 *
 * Inspired by:
 * - YouTube's fullscreen video player
 * - Netflix's immersive viewing experience
 * - Video game HUD patterns (minimal, auto-hide, edge-positioned)
 */

import { addManagedEventListener, getRource, get, set } from '../state.js';
import { getElement } from '../dom.js';
import { hapticLight, hapticMedium } from '../utils.js';
import { safeWasmCall } from '../wasm-api.js';
import { getPreference } from '../preferences.js';

// =============================================================================
// Constants
// =============================================================================

/** Delay before auto-hiding controls in immersive mode (ms) */
const IMMERSIVE_HIDE_DELAY = 3000;

/** LocalStorage key for "don't show again" preference */
const FULLSCREEN_PROMPT_DISMISSED_KEY = 'rource_fullscreen_prompt_dismissed';

/** Minimum time between fullscreen prompts (24 hours) */
const PROMPT_COOLDOWN_MS = 24 * 60 * 60 * 1000;

// =============================================================================
// State
// =============================================================================

/** Whether immersive mode is currently active */
let isImmersiveMode = false;

/** Timeout ID for auto-hiding controls */
let hideControlsTimeout = null;

/** Whether HUD controls are currently visible */
let hudVisible = true;

/** Callback to toggle play/pause */
let togglePlayFn = null;

/** Callback to check if playing */
let isPlayingFn = null;

/** Last time the prompt was shown */
let lastPromptTime = 0;

/** Previous label state before entering immersive mode (to restore on exit) */
let previousLabelsState = true;

// =============================================================================
// Fullscreen Prompt
// =============================================================================

/**
 * Shows the fullscreen prompt dialog.
 */
function showFullscreenPrompt() {
    const prompt = document.getElementById('fullscreen-prompt');
    if (!prompt) return;

    // Check if user has dismissed the prompt recently
    const dismissedUntil = localStorage.getItem(FULLSCREEN_PROMPT_DISMISSED_KEY);
    if (dismissedUntil && Date.now() < parseInt(dismissedUntil, 10)) {
        return;
    }

    // Rate limit prompts
    if (Date.now() - lastPromptTime < 5000) {
        return;
    }
    lastPromptTime = Date.now();

    prompt.classList.add('visible');
    hapticLight();
}

/**
 * Hides the fullscreen prompt dialog.
 */
function hideFullscreenPrompt() {
    const prompt = document.getElementById('fullscreen-prompt');
    if (prompt) {
        prompt.classList.remove('visible');
    }
}

/**
 * Handles "Enter Fullscreen" button click.
 */
async function handleEnterFullscreen() {
    hideFullscreenPrompt();
    hapticMedium();

    try {
        await enterImmersiveMode();
    } catch (error) {
        console.warn('Failed to enter immersive mode:', error);
    }
}

/**
 * Handles "Not Now" button click.
 */
function handleNotNow() {
    hideFullscreenPrompt();
}

/**
 * Handles "Don't show again" checkbox change.
 */
function handleDontShowAgain(e) {
    if (e.target.checked) {
        // Set to not show for 24 hours
        localStorage.setItem(
            FULLSCREEN_PROMPT_DISMISSED_KEY,
            (Date.now() + PROMPT_COOLDOWN_MS).toString()
        );
    } else {
        localStorage.removeItem(FULLSCREEN_PROMPT_DISMISSED_KEY);
    }
}

// =============================================================================
// Immersive Mode
// =============================================================================

/**
 * Enters immersive fullscreen mode.
 */
export async function enterImmersiveMode() {
    if (isImmersiveMode) return;

    const canvasContainer = getElement('canvasContainer');
    if (!canvasContainer) return;

    // Try to enter native fullscreen
    try {
        if (canvasContainer.requestFullscreen) {
            await canvasContainer.requestFullscreen();
        } else if (canvasContainer.webkitRequestFullscreen) {
            await canvasContainer.webkitRequestFullscreen();
        }
    } catch (error) {
        console.warn('Fullscreen request failed, using pseudo-fullscreen:', error);
    }

    // Enable immersive mode classes
    document.body.classList.add('immersive-mode');
    isImmersiveMode = true;

    // Hide entity labels for immersive experience (L11)
    // Store the current state first so we can restore on exit
    const rource = getRource();
    if (rource) {
        previousLabelsState = safeWasmCall(
            'getShowLabels',
            () => rource.getShowLabels(),
            getPreference('showLabels', true)
        );
        safeWasmCall('setShowLabels', () => rource.setShowLabels(false), undefined);
    }

    // Show HUD initially
    showHUD();

    // Start auto-hide timer if playing
    if (isPlayingFn && isPlayingFn()) {
        startHideTimer();
    }

    console.log('Entered immersive mode');
}

/**
 * Exits immersive fullscreen mode.
 */
export function exitImmersiveMode() {
    if (!isImmersiveMode) return;

    // Exit native fullscreen if active
    if (document.fullscreenElement || document.webkitFullscreenElement) {
        if (document.exitFullscreen) {
            document.exitFullscreen().catch(() => {});
        } else if (document.webkitExitFullscreen) {
            document.webkitExitFullscreen();
        }
    }

    // Remove immersive mode classes
    document.body.classList.remove('immersive-mode');
    isImmersiveMode = false;

    // Restore entity labels to previous state (L11)
    const rource = getRource();
    if (rource) {
        safeWasmCall('setShowLabels', () => rource.setShowLabels(previousLabelsState), undefined);
    }

    // Clear hide timer
    clearTimeout(hideControlsTimeout);

    // Show HUD (reset state)
    showHUD();

    console.log('Exited immersive mode');
}

/**
 * Toggles immersive mode.
 */
export function toggleImmersiveMode() {
    if (isImmersiveMode) {
        exitImmersiveMode();
    } else {
        enterImmersiveMode();
    }
}

// =============================================================================
// HUD Controls
// =============================================================================

/**
 * Shows the HUD overlay controls.
 */
function showHUD() {
    if (!isImmersiveMode) return;

    hudVisible = true;
    document.body.classList.remove('hud-hidden');

    // Reset hide timer
    clearTimeout(hideControlsTimeout);
    if (isPlayingFn && isPlayingFn()) {
        startHideTimer();
    }
}

/**
 * Hides the HUD overlay controls.
 */
function hideHUD() {
    if (!isImmersiveMode) return;

    // Only hide if playing
    if (isPlayingFn && !isPlayingFn()) {
        return;
    }

    hudVisible = false;
    document.body.classList.add('hud-hidden');
}

/**
 * Starts the auto-hide timer for HUD controls.
 */
function startHideTimer() {
    clearTimeout(hideControlsTimeout);
    hideControlsTimeout = setTimeout(hideHUD, IMMERSIVE_HIDE_DELAY);
}

/**
 * Resets the auto-hide timer (call on user interaction).
 */
function resetHideTimer() {
    if (!isImmersiveMode || !hudVisible) return;

    clearTimeout(hideControlsTimeout);
    if (isPlayingFn && isPlayingFn()) {
        startHideTimer();
    }
}

/**
 * Toggles HUD visibility on canvas tap.
 */
function handleCanvasTap() {
    if (!isImmersiveMode) return;

    hapticLight();

    if (hudVisible) {
        // If HUD is visible and playing, hide it
        if (isPlayingFn && isPlayingFn()) {
            hideHUD();
        }
    } else {
        // If HUD is hidden, show it
        showHUD();
    }
}

/**
 * Called when playback state changes.
 * @param {boolean} playing - Whether currently playing
 */
export function onImmersivePlaybackChange(playing) {
    if (!isImmersiveMode) return;

    if (playing) {
        startHideTimer();
    } else {
        // When paused, show HUD and keep it visible
        showHUD();
        clearTimeout(hideControlsTimeout);
    }
}

// =============================================================================
// Landscape Detection
// =============================================================================

/**
 * Checks if device is in landscape mobile orientation.
 * @returns {boolean} True if landscape mobile
 */
function isLandscapeMobile() {
    const width = window.innerWidth;
    const height = window.innerHeight;
    const isLandscape = width > height;
    const isMobileHeight = height <= 500;
    const hasTouch = 'ontouchstart' in window || navigator.maxTouchPoints > 0;

    return isLandscape && isMobileHeight && hasTouch;
}

/**
 * Handles orientation change events.
 */
function handleOrientationChange() {
    // Small delay for viewport to settle
    setTimeout(() => {
        if (isLandscapeMobile() && !isImmersiveMode) {
            // Only show prompt if visualization is loaded
            const rource = getRource();
            if (rource && get('dataLoaded')) {
                showFullscreenPrompt();
            }
        } else if (!isLandscapeMobile() && isImmersiveMode) {
            // Auto-exit immersive mode when rotating to portrait
            exitImmersiveMode();
        }
    }, 150);
}

// =============================================================================
// HUD Play Button
// =============================================================================

/**
 * Handles HUD play button click.
 */
function handleHUDPlayClick() {
    hapticMedium();
    if (togglePlayFn) {
        togglePlayFn();
    }
}

/**
 * Updates the HUD play button icon based on playback state.
 * @param {boolean} playing - Whether currently playing
 */
export function updateHUDPlayButton(playing) {
    const playIcon = document.getElementById('immersive-play-icon');
    if (!playIcon) return;

    if (playing) {
        // Show pause icon
        playIcon.innerHTML = '<rect x="6" y="4" width="4" height="16"></rect><rect x="14" y="4" width="4" height="16"></rect>';
    } else {
        // Show play icon
        playIcon.innerHTML = '<polygon points="5 3 19 12 5 21 5 3"></polygon>';
    }
}

// =============================================================================
// Timeline Slider
// =============================================================================

/**
 * Handles immersive timeline slider input.
 */
function handleImmersiveSliderInput(e) {
    const rource = getRource();
    if (!rource) return;

    const value = parseInt(e.target.value, 10);
    safeWasmCall('seek', () => rource.seek(value), undefined);

    // Update time display
    updateImmersiveTimeDisplay();

    // Reset hide timer since user interacted
    resetHideTimer();
}

/**
 * Updates the immersive time display with current timestamp.
 */
function updateImmersiveTimeDisplay() {
    const rource = getRource();
    if (!rource) return;

    const timeDisplay = document.getElementById('immersive-time-display');
    if (!timeDisplay) return;

    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);

    if (total > 0) {
        const currentIndex = Math.min(current, total - 1);
        const timestamp = safeWasmCall(
            'getCommitTimestamp',
            () => rource.getCommitTimestamp(currentIndex),
            0
        );

        if (timestamp > 0) {
            const date = new Date(timestamp * 1000);
            const month = date.toLocaleString('en-US', { month: 'short' });
            const year = date.getFullYear();
            timeDisplay.textContent = `${month} ${year}`;
        } else {
            timeDisplay.textContent = '--';
        }
    } else {
        timeDisplay.textContent = '--';
    }
}

/**
 * Updates the immersive stats display.
 */
export function updateImmersiveStats() {
    const rource = getRource();
    if (!rource) return;

    const commitsEl = document.getElementById('immersive-stat-commits');
    const filesEl = document.getElementById('immersive-stat-files');

    if (commitsEl) {
        const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
        commitsEl.textContent = total.toLocaleString();
    }

    if (filesEl) {
        const fileCount = safeWasmCall('getTotalFiles', () => rource.getTotalFiles(), 0);
        filesEl.textContent = fileCount.toLocaleString();
    }
}

// =============================================================================
// Initialization
// =============================================================================

/**
 * Initializes immersive mode functionality.
 *
 * @param {Object} options - Configuration options
 * @param {Function} options.togglePlay - Function to toggle play/pause
 * @param {Function} options.isPlaying - Function to check if playing
 */
export function initImmersiveMode(options = {}) {
    togglePlayFn = options.togglePlay;
    isPlayingFn = options.isPlaying;

    // Fullscreen prompt handlers
    const enterBtn = document.getElementById('fullscreen-prompt-enter');
    const notNowBtn = document.getElementById('fullscreen-prompt-not-now');
    const dontShowCheckbox = document.getElementById('fullscreen-prompt-dont-show');

    if (enterBtn) {
        addManagedEventListener(enterBtn, 'click', handleEnterFullscreen);
    }
    if (notNowBtn) {
        addManagedEventListener(notNowBtn, 'click', handleNotNow);
    }
    if (dontShowCheckbox) {
        addManagedEventListener(dontShowCheckbox, 'change', handleDontShowAgain);
    }

    // HUD controls
    const hudPlayBtn = document.getElementById('immersive-play-btn');
    if (hudPlayBtn) {
        addManagedEventListener(hudPlayBtn, 'click', handleHUDPlayClick);
    }

    const hudExitBtn = document.getElementById('immersive-exit-btn');
    if (hudExitBtn) {
        addManagedEventListener(hudExitBtn, 'click', exitImmersiveMode);
    }

    // Immersive timeline slider
    const immersiveSlider = document.getElementById('immersive-timeline-slider');
    if (immersiveSlider) {
        addManagedEventListener(immersiveSlider, 'input', handleImmersiveSliderInput);
    }

    // Canvas tap to toggle HUD
    const canvas = getElement('canvas');
    if (canvas) {
        addManagedEventListener(canvas, 'click', (e) => {
            // Only handle if in immersive mode
            if (isImmersiveMode) {
                handleCanvasTap();
                e.stopPropagation();
            }
        });
    }

    // Listen for orientation changes
    if (window.screen && window.screen.orientation) {
        addManagedEventListener(window.screen.orientation, 'change', handleOrientationChange);
    } else {
        addManagedEventListener(window, 'orientationchange', handleOrientationChange);
    }

    // Also check on resize
    addManagedEventListener(window, 'resize', () => {
        // Debounce resize handling
        clearTimeout(handleOrientationChange._debounce);
        handleOrientationChange._debounce = setTimeout(handleOrientationChange, 200);
    });

    // Listen for fullscreen exit (Esc key, etc.)
    addManagedEventListener(document, 'fullscreenchange', () => {
        if (!document.fullscreenElement && isImmersiveMode) {
            exitImmersiveMode();
        }
    });
    addManagedEventListener(document, 'webkitfullscreenchange', () => {
        if (!document.webkitFullscreenElement && isImmersiveMode) {
            exitImmersiveMode();
        }
    });

    // HUD interaction resets hide timer
    const hudElements = document.querySelectorAll('.immersive-hud, .immersive-timeline');
    hudElements.forEach(el => {
        addManagedEventListener(el, 'click', resetHideTimer);
        addManagedEventListener(el, 'touchstart', resetHideTimer, { passive: true });
    });

    console.log('Immersive mode initialized');
}

/**
 * Returns whether immersive mode is active.
 * @returns {boolean}
 */
export function isInImmersiveMode() {
    return isImmersiveMode;
}
