// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Window & Context Events
 *
 * Handles window resize and WebGL context loss/restoration events.
 * Single responsibility: global browser events.
 */

import { setState, addManagedEventListener } from '../state.js';
import { getElement, getAllElements } from '../dom.js';
import { debounce } from '../utils.js';
import { CONFIG } from '../config.js';
import { resizeCanvas, startAnimation, stopAnimation, isAnimating, wakeFromIdle } from '../animation.js';
import { showToast } from '../toast.js';

/**
 * Whether the animation was running when the tab was hidden.
 * Used to restore animation state when the tab becomes visible again.
 */
let wasAnimatingBeforeHide = false;

/**
 * Initializes window resize handler.
 */
function initWindowResize() {
    addManagedEventListener(window, 'resize', debounce(resizeCanvas, CONFIG.DEBOUNCE_DELAY_MS));
}

/**
 * Initializes WebGL context loss/restoration handlers.
 */
function initContextHandlers() {
    const canvas = getElement('canvas');
    const elements = getAllElements();

    if (!canvas) return;

    // Context lost handler
    addManagedEventListener(canvas, 'webglcontextlost', (event) => {
        event.preventDefault();
        setState({ isContextLost: true });
        stopAnimation();
        if (elements.contextLostOverlay) {
            elements.contextLostOverlay.classList.remove('hidden');
        }
    });

    // Context restored handler
    addManagedEventListener(canvas, 'webglcontextrestored', () => {
        setState({ isContextLost: false });
        if (elements.contextLostOverlay) {
            elements.contextLostOverlay.classList.add('hidden');
        }
        startAnimation();
    });

    // Restore context button
    if (elements.btnRestoreContext) {
        addManagedEventListener(elements.btnRestoreContext, 'click', () => {
            if (elements.contextLostOverlay) {
                elements.contextLostOverlay.classList.add('hidden');
            }
            showToast('Restoring visualization...', 'success');
            // Re-initialize after a short delay
            setTimeout(() => window.location.reload(), CONFIG.CONTEXT_RESTORE_DELAY_MS);
        });
    }
}

/**
 * Initializes Page Visibility API handler (Level 1 power management).
 *
 * When the user switches to another tab or minimizes the browser,
 * the animation loop is stopped completely. When the tab becomes
 * visible again, the loop is restarted (if it was running before).
 *
 * This is the most effective power-saving measure: a hidden tab
 * performs zero GPU work, zero CPU animation scheduling, and zero
 * WASM frame calls.
 */
function initPageVisibility() {
    addManagedEventListener(document, 'visibilitychange', () => {
        if (document.visibilityState === 'hidden') {
            // Tab is being hidden — save animation state and stop the loop
            wasAnimatingBeforeHide = isAnimating();
            if (wasAnimatingBeforeHide) {
                stopAnimation();
                console.debug('Rource: Tab hidden — animation stopped');
            }
        } else {
            // Tab is visible again — restore animation if it was running
            if (wasAnimatingBeforeHide) {
                wasAnimatingBeforeHide = false;
                // Also wake from idle in case the scene was idle when hidden
                wakeFromIdle();
                startAnimation();
                console.debug('Rource: Tab visible — animation restored');
            }
        }
    });
}

/**
 * Initializes all window-level event listeners.
 */
export function initWindowEvents() {
    initWindowResize();
    initContextHandlers();
    initPageVisibility();
}
