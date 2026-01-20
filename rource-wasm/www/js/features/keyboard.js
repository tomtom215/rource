/**
 * Rource - Keyboard Shortcuts
 *
 * Centralized keyboard event handling.
 */

import { getRource, hasData, isContextLost } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';
import { getElement, getAllElements } from '../dom.js';
import { toggleFullscreen } from './fullscreen.js';
import { captureScreenshot } from './screenshot.js';
import { toggleTheme } from './theme.js';
import { showHelp, hideHelp } from './help.js';
import { isAtEnd, updatePlaybackUI } from '../animation.js';
import { updatePreference } from '../preferences.js';
import { updateUrlState } from '../url-state.js';
import { validateSpeed } from '../telemetry.js';

/**
 * Handles play/pause with replay support.
 */
function handlePlayPause() {
    const rource = getRource();
    if (!rource || !hasData()) return;

    // If at end and paused, restart from beginning
    if (isAtEnd() && !safeWasmCall('isPlaying', () => rource.isPlaying(), false)) {
        safeWasmCall('seek', () => rource.seek(0), undefined);
    }

    safeWasmCall('togglePlay', () => rource.togglePlay(), undefined);
    updatePlaybackUI();
}

/**
 * Steps to previous commit.
 */
function stepPrevious() {
    const rource = getRource();
    if (!rource || !hasData()) return;
    safeWasmCall('stepBackward', () => rource.stepBackward(), undefined);
    updatePlaybackUI();
}

/**
 * Steps to next commit.
 */
function stepNext() {
    const rource = getRource();
    if (!rource || !hasData()) return;
    safeWasmCall('stepForward', () => rource.stepForward(), undefined);
    updatePlaybackUI();
}

/**
 * Zooms in.
 */
function zoomIn() {
    const rource = getRource();
    if (!rource) return;
    safeWasmCall('zoom', () => rource.zoom(1.2), undefined);
}

/**
 * Zooms out.
 */
function zoomOut() {
    const rource = getRource();
    if (!rource) return;
    safeWasmCall('zoom', () => rource.zoom(0.8), undefined);
}

/**
 * Resets camera position and zoom.
 */
function resetCamera() {
    const rource = getRource();
    if (!rource) return;
    safeWasmCall('resetCamera', () => rource.resetCamera(), undefined);
}

/**
 * Toggles labels.
 */
function toggleLabels() {
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
}

/**
 * Restarts visualization from beginning.
 */
function restart() {
    const rource = getRource();
    if (!rource || !hasData()) return;
    safeWasmCall('seek', () => rource.seek(0), undefined);
    updatePlaybackUI();
}

/**
 * Speed options in order.
 */
const SPEED_OPTIONS = ['0.5', '1', '2', '5', '10', '20', '50', '100'];

/**
 * Changes speed to the next or previous option.
 * @param {boolean} increase - True to increase speed, false to decrease
 */
function changeSpeed(increase) {
    const rource = getRource();
    const speedSelect = getElement('speedSelect');
    if (!rource || !speedSelect) return;

    const currentValue = speedSelect.value;
    const currentIndex = SPEED_OPTIONS.indexOf(currentValue);

    let newIndex;
    if (increase) {
        newIndex = Math.min(currentIndex + 1, SPEED_OPTIONS.length - 1);
    } else {
        newIndex = Math.max(currentIndex - 1, 0);
    }

    if (newIndex !== currentIndex) {
        const newSpeed = SPEED_OPTIONS[newIndex];
        speedSelect.value = newSpeed;
        safeWasmCall('setSpeed', () => rource.setSpeed(parseFloat(newSpeed)), undefined);
        updatePreference('speed', newSpeed);
        updateUrlState({ speed: newSpeed });
    }
}

/**
 * Initializes keyboard shortcuts.
 */
export function initKeyboard() {
    document.addEventListener('keydown', (e) => {
        // Ignore if typing in an input field
        if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;

        // Ignore if context is lost
        if (isContextLost()) return;

        const key = e.key.toLowerCase();

        switch (key) {
            // Playback
            case ' ':
                e.preventDefault();
                handlePlayPause();
                break;

            // Navigation
            case ',':
            case '<':
            case 'arrowleft':
                if (!e.ctrlKey && !e.metaKey) {
                    stepPrevious();
                }
                break;

            case '.':
            case '>':
            case 'arrowright':
                if (!e.ctrlKey && !e.metaKey) {
                    stepNext();
                }
                break;

            // Zoom
            case '=':
            case '+':
                e.preventDefault();
                zoomIn();
                break;

            case '-':
            case '_':
                e.preventDefault();
                zoomOut();
                break;

            // Speed control
            case '[':
                e.preventDefault();
                changeSpeed(false); // Slower
                break;

            case ']':
                e.preventDefault();
                changeSpeed(true); // Faster
                break;

            // Camera
            case 'r':
                if (!e.ctrlKey && !e.metaKey) {
                    resetCamera();
                }
                break;

            case 'home':
                restart();
                break;

            // UI toggles
            case 'l':
                toggleLabels();
                break;

            case 'f':
                toggleFullscreen();
                break;

            case 's':
                if (!e.ctrlKey && !e.metaKey) {
                    e.preventDefault();
                    captureScreenshot();
                }
                break;

            case 't':
                if (!e.ctrlKey && !e.metaKey) {
                    toggleTheme();
                }
                break;

            // Help
            case '?':
                e.preventDefault();
                showHelp();
                break;

            case '/':
                if (e.shiftKey) {
                    e.preventDefault();
                    showHelp();
                }
                break;

            // Authors panel toggle
            case 'a':
                if (!e.ctrlKey && !e.metaKey && hasData()) {
                    const authorsPanel = getElement('authorsPanel');
                    const authorsToggle = getElement('authorsToggle');
                    if (authorsPanel && !authorsPanel.classList.contains('hidden')) {
                        authorsPanel.classList.toggle('collapsed');
                        const isExpanded = !authorsPanel.classList.contains('collapsed');
                        if (authorsToggle) {
                            authorsToggle.setAttribute('aria-expanded', isExpanded.toString());
                        }
                    }
                }
                break;

            // Performance overlay toggle
            case 'p':
                if (!e.ctrlKey && !e.metaKey && hasData()) {
                    const perfOverlay = getElement('perfOverlay');
                    if (perfOverlay) {
                        perfOverlay.classList.toggle('hidden');
                    }
                }
                break;
        }
    });
}
