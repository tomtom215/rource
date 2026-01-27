// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Utility Functions
 *
 * General-purpose helper functions used across modules.
 */

/**
 * Creates a debounced version of a function.
 * @param {Function} func - Function to debounce
 * @param {number} wait - Milliseconds to wait
 * @returns {Function} Debounced function
 */
export function debounce(func, wait) {
    let timeout;
    return function executedFunction(...args) {
        const later = () => {
            clearTimeout(timeout);
            func(...args);
        };
        clearTimeout(timeout);
        timeout = setTimeout(later, wait);
    };
}

/**
 * Escapes a string for safe use in HTML content.
 * Prevents XSS attacks by escaping special characters.
 * @param {string} str - The string to escape
 * @returns {string} The escaped string safe for HTML content
 */
export function escapeHtml(str) {
    if (typeof str !== 'string') return '';
    return str
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#x27;');
}

/**
 * Formats a number with thousand separators.
 * @param {number} num - Number to format
 * @returns {string} Formatted number
 */
export function formatNumber(num) {
    return num.toLocaleString();
}

/**
 * Formats a date timestamp into a readable string.
 * @param {number} timestamp - Unix timestamp in seconds
 * @returns {string} Formatted date string
 */
export function formatDate(timestamp) {
    const date = new Date(timestamp * 1000);
    return date.toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
    });
}

/**
 * Formats a duration in milliseconds to a human-readable string.
 * @param {number} ms - Duration in milliseconds
 * @returns {string} Formatted duration
 */
export function formatDuration(ms) {
    if (ms < 1000) return `${ms}ms`;
    if (ms < 60000) return `${(ms / 1000).toFixed(1)}s`;
    return `${(ms / 60000).toFixed(1)}m`;
}

/**
 * Clamps a value between min and max.
 * @param {number} value - Value to clamp
 * @param {number} min - Minimum value
 * @param {number} max - Maximum value
 * @returns {number} Clamped value
 */
export function clamp(value, min, max) {
    return Math.max(min, Math.min(max, value));
}

/**
 * Formats bytes into a human-readable string (KB, MB, GB).
 * @param {number} bytes - Number of bytes
 * @param {number} [decimals=1] - Number of decimal places
 * @returns {string} Formatted size string
 */
export function formatBytes(bytes, decimals = 1) {
    if (bytes === 0) return '0 B';
    if (bytes < 1024) return `${bytes} B`;

    const k = 1024;
    const sizes = ['B', 'KB', 'MB', 'GB'];
    const i = Math.min(Math.floor(Math.log(bytes) / Math.log(k)), sizes.length - 1);

    return `${(bytes / Math.pow(k, i)).toFixed(decimals)} ${sizes[i]}`;
}

/**
 * Generates a simple hash from a string (for color generation).
 * @param {string} str - Input string
 * @returns {number} Hash value
 */
export function hashString(str) {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
        const char = str.charCodeAt(i);
        hash = ((hash << 5) - hash) + char;
        hash = hash & hash; // Convert to 32-bit integer
    }
    return Math.abs(hash);
}

/**
 * Traps focus within a container element (for modal accessibility).
 * @param {HTMLElement} container - Container to trap focus in
 * @param {KeyboardEvent} event - Keyboard event
 */
export function trapFocus(container, event) {
    const focusableElements = container.querySelectorAll(
        'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
    );
    const firstFocusable = focusableElements[0];
    const lastFocusable = focusableElements[focusableElements.length - 1];

    if (event.shiftKey) {
        // Shift + Tab
        if (document.activeElement === firstFocusable) {
            lastFocusable.focus();
            event.preventDefault();
        }
    } else {
        // Tab
        if (document.activeElement === lastFocusable) {
            firstFocusable.focus();
            event.preventDefault();
        }
    }
}

// =============================================================================
// Haptic Feedback Utilities
// =============================================================================

/**
 * Check if device supports haptic feedback via Vibration API.
 * @returns {boolean} True if vibration is supported
 */
export function supportsHaptics() {
    return 'vibrate' in navigator;
}

/**
 * Haptic feedback patterns (duration in milliseconds).
 * Subtle patterns that enhance UX without being intrusive.
 */
export const HapticPattern = {
    /** Light tap - button press, selection (10ms) */
    LIGHT: 10,
    /** Medium tap - confirmation, toggle (15ms) */
    MEDIUM: 15,
    /** Heavy tap - important action, error (25ms) */
    HEAVY: 25,
    /** Success pattern - two quick taps */
    SUCCESS: [10, 50, 10],
    /** Error pattern - three quick taps */
    ERROR: [15, 30, 15, 30, 15],
    /** Selection changed - very subtle */
    SELECTION: 5,
};

/**
 * Trigger haptic feedback if supported and user hasn't disabled it.
 * Respects prefers-reduced-motion media query.
 *
 * @param {number|number[]} pattern - Vibration pattern (ms) or array of [vibrate, pause, vibrate...]
 * @returns {boolean} True if haptic was triggered
 */
export function haptic(pattern = HapticPattern.LIGHT) {
    // Check if device supports vibration
    if (!supportsHaptics()) {
        return false;
    }

    // Respect reduced motion preference (haptics can be disorienting)
    if (window.matchMedia('(prefers-reduced-motion: reduce)').matches) {
        return false;
    }

    try {
        navigator.vibrate(pattern);
        return true;
    } catch {
        // Vibration may fail silently on some devices
        return false;
    }
}

/**
 * Convenience function for light haptic (button taps).
 */
export function hapticLight() {
    return haptic(HapticPattern.LIGHT);
}

/**
 * Convenience function for medium haptic (toggles, confirmations).
 */
export function hapticMedium() {
    return haptic(HapticPattern.MEDIUM);
}

/**
 * Convenience function for success haptic.
 */
export function hapticSuccess() {
    return haptic(HapticPattern.SUCCESS);
}

/**
 * Convenience function for error haptic.
 */
export function hapticError() {
    return haptic(HapticPattern.ERROR);
}

// =============================================================================
// Screen Reader Announcements (WCAG 4.1.3 Status Messages)
// =============================================================================

/**
 * Announces a message to screen readers via the status-announcer element.
 * Uses aria-live="polite" so messages don't interrupt current speech.
 *
 * @param {string} message - The message to announce
 * @param {boolean} [clearAfter=true] - Clear the message after announcement (default: true)
 */
export function announce(message, clearAfter = true) {
    const announcer = document.getElementById('status-announcer');
    if (!announcer) return;

    // Clear first to ensure repeated messages are announced
    announcer.textContent = '';

    // Use setTimeout to ensure the DOM update is processed
    setTimeout(() => {
        announcer.textContent = message;

        // Clear after a delay to allow screen readers to read it
        if (clearAfter) {
            setTimeout(() => {
                announcer.textContent = '';
            }, 1000);
        }
    }, 100);
}
