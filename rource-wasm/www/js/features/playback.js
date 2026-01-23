// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Playback Controls
 *
 * Handles play/pause, navigation, timeline, and speed controls.
 * Single responsibility: playback state and timeline interaction.
 */

import { getRource, hasData, addManagedEventListener, get } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';
import { getElement } from '../dom.js';
import { updatePlaybackUI, isAtEnd, resetUncappedFpsStats } from '../animation.js';
import { updatePreference } from '../preferences.js';
import { updateUrlState } from '../url-state.js';
import { validateSpeed } from '../telemetry.js';

/**
 * Handles play/pause button click with replay support.
 */
function handlePlayPause() {
    const rource = getRource();
    if (!rource) return;

    // If at end and paused, restart from beginning
    if (isAtEnd() && !safeWasmCall('isPlaying', () => rource.isPlaying(), false)) {
        safeWasmCall('seek', () => rource.seek(0), undefined);
        // Reset FPS tracking stats when restarting playback in uncapped mode
        if (get('uncappedFps')) {
            resetUncappedFpsStats();
        }
    }

    safeWasmCall('togglePlay', () => rource.togglePlay(), undefined);
    updatePlaybackUI();
}

/**
 * Handles previous commit button click.
 */
function handlePrevious() {
    const rource = getRource();
    if (!rource || !hasData()) return;
    safeWasmCall('stepBackward', () => rource.stepBackward(), undefined);
    updatePlaybackUI();
}

/**
 * Handles next commit button click.
 */
function handleNext() {
    const rource = getRource();
    if (!rource || !hasData()) return;
    safeWasmCall('stepForward', () => rource.stepForward(), undefined);
    updatePlaybackUI();
}

/**
 * Handles reset button click.
 */
function handleReset() {
    const rource = getRource();
    if (!rource || !hasData()) return;
    safeWasmCall('seek', () => rource.seek(0), undefined);
    // Reset FPS tracking stats when resetting timeline in uncapped mode
    if (get('uncappedFps')) {
        resetUncappedFpsStats();
    }
    updatePlaybackUI();
}

/**
 * Handles timeline slider input.
 * @param {Event} e - Input event
 */
function handleTimelineInput(e) {
    const rource = getRource();
    if (!rource) return;

    const commitIndex = parseInt(e.target.value, 10);
    safeWasmCall('pause', () => rource.pause(), undefined);
    safeWasmCall('seek', () => rource.seek(commitIndex), undefined);
    updatePlaybackUI();
}

/**
 * Handles speed selector change.
 * @param {Event} e - Change event
 */
function handleSpeedChange(e) {
    const rource = getRource();
    if (!rource) return;

    const speed = validateSpeed(e.target.value);
    safeWasmCall('setSpeed', () => rource.setSpeed(speed), undefined);
    updatePreference('speed', e.target.value);
    updateUrlState({ speed: e.target.value });
}

/**
 * Handles labels toggle button click.
 */
function handleLabelsToggle() {
    const rource = getRource();
    if (!rource || !hasData()) return;

    const labelsText = getElement('labelsText');
    const btnLabels = getElement('btnLabels');

    const currentState = safeWasmCall('getShowLabels', () => rource.getShowLabels(), true);
    const newState = !currentState;
    safeWasmCall('setShowLabels', () => rource.setShowLabels(newState), undefined);

    if (labelsText) {
        labelsText.textContent = newState ? 'On' : 'Off';
    }
    if (btnLabels) {
        btnLabels.classList.toggle('active', newState);
    }
    updatePreference('showLabels', newState);
}

/**
 * Initializes playback control event listeners.
 */
export function initPlayback() {
    const btnPlayMain = getElement('btnPlayMain');
    const btnPrev = getElement('btnPrev');
    const btnNext = getElement('btnNext');
    const btnResetBar = getElement('btnResetBar');
    const btnLabels = getElement('btnLabels');
    const timelineSlider = getElement('timelineSlider');
    const speedSelect = getElement('speedSelect');

    // Play button
    if (btnPlayMain) {
        addManagedEventListener(btnPlayMain, 'click', handlePlayPause);
    }

    // Navigation buttons
    if (btnPrev) {
        addManagedEventListener(btnPrev, 'click', handlePrevious);
    }

    if (btnNext) {
        addManagedEventListener(btnNext, 'click', handleNext);
    }

    // Reset button
    if (btnResetBar) {
        addManagedEventListener(btnResetBar, 'click', handleReset);
    }

    // Labels toggle button
    if (btnLabels) {
        addManagedEventListener(btnLabels, 'click', handleLabelsToggle);
    }

    // Timeline slider
    if (timelineSlider) {
        addManagedEventListener(timelineSlider, 'input', handleTimelineInput);
    }

    // Speed selector
    if (speedSelect) {
        addManagedEventListener(speedSelect, 'change', handleSpeedChange);
    }
}
