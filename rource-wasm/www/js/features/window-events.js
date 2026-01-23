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
import { resizeCanvas, startAnimation, stopAnimation } from '../animation.js';
import { showToast } from '../toast.js';

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
 * Initializes all window-level event listeners.
 */
export function initWindowEvents() {
    initWindowResize();
    initContextHandlers();
}
