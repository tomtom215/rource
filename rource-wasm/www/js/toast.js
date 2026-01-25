// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Toast Notifications
 *
 * Provides user feedback via toast messages.
 */

import { CONFIG } from './config.js';
import { getElement } from './dom.js';

/** Track current toast timeout to allow clearing on rapid re-trigger */
let currentToastTimeout = null;

/** Track last toast message to prevent duplicate spam */
let lastToastMessage = null;
let lastToastTime = 0;

/** Minimum time between identical toasts (ms) */
const TOAST_DEBOUNCE_MS = 1000;

/**
 * Shows a toast notification.
 * @param {string} message - Message to display
 * @param {string} [type='error'] - Type: 'error', 'success', 'info'
 * @param {number} [duration] - Duration in ms (default based on type)
 */
export function showToast(message, type = 'error', duration) {
    const toast = getElement('toast');
    if (!toast) return;

    // Debounce identical messages to prevent spam (e.g., rapid uncapped toggles)
    const now = Date.now();
    if (message === lastToastMessage && (now - lastToastTime) < TOAST_DEBOUNCE_MS) {
        return;
    }
    lastToastMessage = message;
    lastToastTime = now;

    // Clear any existing timeout to prevent race conditions
    if (currentToastTimeout !== null) {
        clearTimeout(currentToastTimeout);
        currentToastTimeout = null;
    }

    // Determine duration based on type if not provided
    if (duration === undefined) {
        switch (type) {
            case 'success':
                duration = CONFIG.TOAST_SUCCESS_DURATION_MS;
                break;
            case 'error':
                duration = CONFIG.TOAST_ERROR_DURATION_MS;
                break;
            default:
                duration = CONFIG.TOAST_DURATION_MS;
        }
    }

    const messageEl = toast.querySelector('.toast-message');
    if (messageEl) {
        messageEl.textContent = message;
    }

    toast.className = `toast ${type} visible`;

    // Auto-hide after duration
    currentToastTimeout = setTimeout(() => {
        toast.classList.remove('visible');
        currentToastTimeout = null;
    }, duration);
}

/**
 * Hides the current toast immediately.
 */
export function hideToast() {
    const toast = getElement('toast');
    if (toast) {
        toast.classList.remove('visible');
    }
}

/**
 * Initializes toast close button handler.
 */
export function initToast() {
    const toast = getElement('toast');
    if (!toast) return;

    const closeBtn = toast.querySelector('.toast-close');
    if (closeBtn) {
        closeBtn.addEventListener('click', () => {
            toast.classList.remove('visible');
        });
    }
}
