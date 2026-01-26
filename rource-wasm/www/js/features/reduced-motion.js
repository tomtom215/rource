// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Reduced Motion Support (ACC-5)
 *
 * Provides accessibility support for users who prefer reduced motion.
 * Respects the system preference (prefers-reduced-motion) and allows
 * manual override via user preferences.
 *
 * Motion settings:
 * - 'system': Follow system preference (default)
 * - 'always': Always reduce motion regardless of system setting
 * - 'never': Never reduce motion (user explicitly wants animations)
 */

import { getPreference, updatePreference } from '../preferences.js';

/** @type {MediaQueryList|null} */
let mediaQuery = null;

/** @type {Function|null} */
let rourceInstance = null;

/** Original playback speed before reduced motion was applied */
let originalSpeed = null;

/**
 * Check if reduced motion should be active based on user preference and system setting.
 * @returns {boolean} True if reduced motion should be active
 */
export function shouldReduceMotion() {
    const userPref = getPreference('reducedMotion') || 'system';

    switch (userPref) {
        case 'always':
            return true;
        case 'never':
            return false;
        case 'system':
        default:
            return window.matchMedia('(prefers-reduced-motion: reduce)').matches;
    }
}

/**
 * Apply reduced motion settings to the document and WASM instance.
 * @param {boolean} reduce - Whether to reduce motion
 */
function applyReducedMotion(reduce) {
    // Apply CSS class for manual override (works alongside @media query)
    document.documentElement.classList.toggle('reduce-motion', reduce);

    // Apply to WASM instance if available
    if (rourceInstance) {
        try {
            if (reduce) {
                // Store original speed if not already stored
                if (originalSpeed === null) {
                    originalSpeed = rourceInstance.getSpeed();
                }
                // Slow down playback significantly (10x slower)
                // This makes the visualization more comfortable for motion-sensitive users
                const slowSpeed = Math.max(originalSpeed * 10, 50);
                rourceInstance.setSpeed(slowSpeed);
                // Disable bloom effect (reduces visual intensity)
                rourceInstance.setBloom(false);
            } else {
                // Restore original speed if we have it
                if (originalSpeed !== null) {
                    rourceInstance.setSpeed(originalSpeed);
                    originalSpeed = null;
                }
                // Re-enable bloom (user can still disable manually)
                // Note: We don't force-enable bloom; user may have disabled it
            }
        } catch (e) {
            console.warn('Could not apply reduced motion to WASM:', e);
        }
    }

    // Dispatch event for other components to react
    window.dispatchEvent(new CustomEvent('reducedmotionchange', {
        detail: { reduced: reduce }
    }));
}

/**
 * Handle system preference change.
 * @param {MediaQueryListEvent} event - Media query change event
 */
function handleSystemPreferenceChange(event) {
    const userPref = getPreference('reducedMotion') || 'system';

    // Only react to system changes if user preference is 'system'
    if (userPref === 'system') {
        applyReducedMotion(event.matches);
    }
}

/**
 * Set the reduced motion preference.
 * @param {'system'|'always'|'never'} preference - User preference
 */
export function setReducedMotionPreference(preference) {
    const validValues = ['system', 'always', 'never'];
    if (!validValues.includes(preference)) {
        console.warn(`Invalid reduced motion preference: ${preference}`);
        return;
    }

    updatePreference('reducedMotion', preference);
    applyReducedMotion(shouldReduceMotion());
}

/**
 * Get the current reduced motion preference.
 * @returns {'system'|'always'|'never'} Current preference
 */
export function getReducedMotionPreference() {
    return getPreference('reducedMotion') || 'system';
}

/**
 * Initialize reduced motion support.
 * @param {Object} [rource] - Rource WASM instance (optional, can be set later)
 */
export function initReducedMotion(rource = null) {
    rourceInstance = rource;

    // Set up media query listener for system preference changes
    mediaQuery = window.matchMedia('(prefers-reduced-motion: reduce)');

    // Modern browsers use addEventListener, older ones use addListener
    if (mediaQuery.addEventListener) {
        mediaQuery.addEventListener('change', handleSystemPreferenceChange);
    } else if (mediaQuery.addListener) {
        mediaQuery.addListener(handleSystemPreferenceChange);
    }

    // Apply initial state
    applyReducedMotion(shouldReduceMotion());
}

/**
 * Update the Rource instance reference (for late binding).
 * @param {Object} rource - Rource WASM instance
 */
export function setRourceInstance(rource) {
    rourceInstance = rource;
    // Re-apply current state with the new instance
    applyReducedMotion(shouldReduceMotion());
}

/**
 * Clean up reduced motion support.
 */
export function cleanupReducedMotion() {
    if (mediaQuery) {
        if (mediaQuery.removeEventListener) {
            mediaQuery.removeEventListener('change', handleSystemPreferenceChange);
        } else if (mediaQuery.removeListener) {
            mediaQuery.removeListener(handleSystemPreferenceChange);
        }
        mediaQuery = null;
    }
    rourceInstance = null;
    originalSpeed = null;
}
