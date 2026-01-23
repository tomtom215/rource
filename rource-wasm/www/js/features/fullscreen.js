/**
 * Rource - Fullscreen Feature
 *
 * Enables fullscreen presentation mode for demos and presentations.
 * Uses native Fullscreen API where available, falls back to CSS-based
 * pseudo-fullscreen for mobile browsers (especially iOS Safari).
 */

import { getElement, getAllElements } from '../dom.js';
import { getRource } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';
import { resizeCanvas } from '../animation.js';

// Fullscreen icons
const ENTER_FULLSCREEN_PATH = 'M7 14H5v5h5v-2H7v-3zm-2-4h2V7h3V5H5v5zm12 7h-3v2h5v-5h-2v3zM14 5v2h3v3h2V5h-5z';
const EXIT_FULLSCREEN_PATH = 'M5 16h3v3h2v-5H5v2zm3-8H5v2h5V5H8v3zm6 11h2v-3h3v-2h-5v5zm2-11V5h-2v5h5V8h-3z';

// Track pseudo-fullscreen state for mobile fallback
let isPseudoFullscreen = false;

/**
 * Checks if native fullscreen is active.
 * @returns {boolean} True if native fullscreen
 */
export function isNativeFullscreen() {
    return !!(document.fullscreenElement || document.webkitFullscreenElement);
}

/**
 * Checks if any fullscreen mode is active.
 * @returns {boolean} True if in fullscreen
 */
export function isInFullscreenMode() {
    return isNativeFullscreen() || isPseudoFullscreen;
}

/**
 * Checks if pseudo-fullscreen is active.
 * @returns {boolean} True if pseudo-fullscreen
 */
export function isPseudo() {
    return isPseudoFullscreen;
}

/**
 * Updates the fullscreen button icon using safe DOM APIs (no innerHTML).
 */
export function updateFullscreenIcon() {
    const elements = getAllElements();
    const { btnFullscreen, fullscreenIcon } = elements;

    if (!btnFullscreen || !fullscreenIcon) return;

    const isFullscreen = isInFullscreenMode();
    const pathD = isFullscreen ? EXIT_FULLSCREEN_PATH : ENTER_FULLSCREEN_PATH;

    // Clear existing content safely
    while (fullscreenIcon.firstChild) {
        fullscreenIcon.removeChild(fullscreenIcon.firstChild);
    }

    // Create path element using DOM APIs (no innerHTML)
    const pathEl = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    pathEl.setAttribute('d', pathD);
    fullscreenIcon.appendChild(pathEl);

    btnFullscreen.title = isFullscreen ? 'Exit fullscreen (F)' : 'Fullscreen (F)';
}

/**
 * Handles canvas resize after fullscreen change.
 */
function handleFullscreenResize() {
    const rource = getRource();
    const canvas = getElement('canvas');

    if (rource && canvas) {
        setTimeout(() => {
            const rect = canvas.getBoundingClientRect();
            canvas.width = Math.floor(rect.width * window.devicePixelRatio);
            canvas.height = Math.floor(rect.height * window.devicePixelRatio);
            safeWasmCall('resize', () => rource.resize(canvas.width, canvas.height), undefined);
        }, 50);
    }
}

/**
 * Enters pseudo-fullscreen mode (CSS-based).
 */
export function enterPseudoFullscreen() {
    isPseudoFullscreen = true;
    document.body.classList.add('pseudo-fullscreen');
    updateFullscreenIcon();
    handleFullscreenResize();
}

/**
 * Exits pseudo-fullscreen mode.
 */
export function exitPseudoFullscreen() {
    isPseudoFullscreen = false;
    document.body.classList.remove('pseudo-fullscreen');
    updateFullscreenIcon();
    handleFullscreenResize();
}

/**
 * Checks if native fullscreen is supported.
 * @returns {boolean} True if supported
 */
export function supportsNativeFullscreen() {
    return !!(document.documentElement.requestFullscreen || document.documentElement.webkitRequestFullscreen);
}

/**
 * Toggles fullscreen mode.
 */
export async function toggleFullscreen() {
    // Use viz-panel as fullscreen target to include timeline controls
    const vizPanel = document.querySelector('.viz-panel');

    if (isInFullscreenMode()) {
        // Exit fullscreen
        if (isNativeFullscreen()) {
            if (document.exitFullscreen) {
                await document.exitFullscreen();
            } else if (document.webkitExitFullscreen) {
                document.webkitExitFullscreen();
            }
        } else {
            exitPseudoFullscreen();
        }
    } else {
        // Enter fullscreen - try native first, fall back to pseudo
        let nativeWorked = false;

        if (vizPanel?.requestFullscreen) {
            try {
                await vizPanel.requestFullscreen();
                nativeWorked = true;
            } catch {
                // Native fullscreen failed, use pseudo
            }
        } else if (vizPanel?.webkitRequestFullscreen) {
            try {
                vizPanel.webkitRequestFullscreen();
                nativeWorked = true;
            } catch {
                // Native fullscreen failed, use pseudo
            }
        }

        // Fall back to pseudo-fullscreen for iOS and other unsupported browsers
        if (!nativeWorked) {
            enterPseudoFullscreen();
        }
    }
}

/**
 * Initializes fullscreen feature.
 */
export function initFullscreen() {
    const elements = getAllElements();
    const { btnFullscreen, mobileFullscreenExit } = elements;

    // Main fullscreen button
    if (btnFullscreen) {
        btnFullscreen.addEventListener('click', toggleFullscreen);
    }

    // Exit fullscreen button (mobile-friendly)
    const btnExitFullscreen = document.getElementById('btn-exit-fullscreen');
    if (btnExitFullscreen) {
        btnExitFullscreen.addEventListener('click', () => {
            if (isInFullscreenMode()) {
                toggleFullscreen();
            }
        });
    }

    // Mobile fullscreen exit button
    if (mobileFullscreenExit) {
        mobileFullscreenExit.addEventListener('click', () => {
            if (isInFullscreenMode()) {
                toggleFullscreen();
            }
        });
    }

    // Listen for native fullscreen changes
    document.addEventListener('fullscreenchange', () => {
        if (!isNativeFullscreen() && !isPseudoFullscreen) {
            updateFullscreenIcon();
        }
        handleFullscreenResize();
        updateFullscreenIcon();
    });

    document.addEventListener('webkitfullscreenchange', () => {
        handleFullscreenResize();
        updateFullscreenIcon();
    });

    // Escape key exits pseudo-fullscreen
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape' && isPseudoFullscreen) {
            exitPseudoFullscreen();
        }
    });

    // Initial icon state
    updateFullscreenIcon();
}
