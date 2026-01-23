// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Toast Notifications
 *
 * Provides user feedback via toast messages.
 */

import { CONFIG } from './config.js';
import { getElement } from './dom.js';

/**
 * Shows a toast notification.
 * @param {string} message - Message to display
 * @param {string} [type='error'] - Type: 'error', 'success', 'info'
 * @param {number} [duration] - Duration in ms (default based on type)
 */
export function showToast(message, type = 'error', duration) {
    const toast = getElement('toast');
    if (!toast) return;

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
    setTimeout(() => {
        toast.classList.remove('visible');
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
