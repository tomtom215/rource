// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Observability & Telemetry
 *
 * Performance tracking and debugging utilities.
 */

import { CONFIG } from './config.js';

/**
 * Performance telemetry for tracking app behavior.
 */
export const telemetry = {
    wasmErrors: 0,
    eventListenerCount: 0,
    lastError: null,
    initTime: null,
    frameDrops: 0,
};

// Registry of all managed event listeners (for counting)
let eventListenerCount = 0;

/**
 * Records a telemetry event for observability.
 * @param {string} event - Event name
 * @param {Object} [data] - Optional event data
 */
export function recordTelemetry(event, data = {}) {
    if (CONFIG.ENABLE_TELEMETRY) {
        console.log(`[Telemetry:${event}]`, { timestamp: Date.now(), ...data });
    }
}

/**
 * Gets current telemetry stats (useful for debugging).
 * @returns {Object} Current telemetry state
 */
export function getTelemetryStats() {
    return {
        ...telemetry,
        eventListenerCount,
        uptime: telemetry.initTime ? Date.now() - telemetry.initTime : 0,
    };
}

/**
 * Sets the event listener count (called from event management module).
 * @param {number} count - Current count
 */
export function setEventListenerCount(count) {
    eventListenerCount = count;
}

/**
 * Log a debug message (only when CONFIG.DEBUG is true).
 * @param {string} context - The function/area where the log originated
 * @param {string} message - The message to log
 * @param {Error} [error] - Optional error object
 */
export function debugLog(context, message, error = null) {
    if (CONFIG.DEBUG) {
        if (error) {
            console.warn(`[Rource:${context}] ${message}`, error);
        } else {
            console.log(`[Rource:${context}] ${message}`);
        }
    }
}

/**
 * Validates and sanitizes a playback speed value.
 * Returns a valid speed or the default if invalid.
 *
 * @param {string|number} value - Speed value to validate
 * @returns {number} Valid speed value
 */
export function validateSpeed(value) {
    const parsed = typeof value === 'number' ? value : parseFloat(value);

    // Handle NaN, Infinity, or invalid values
    if (!Number.isFinite(parsed) || parsed <= 0) {
        debugLog('validateSpeed', `Invalid speed value: ${value}, using default`);
        return CONFIG.SPEED_DEFAULT;
    }

    // Clamp to valid range
    return Math.max(CONFIG.SPEED_MIN, Math.min(CONFIG.SPEED_MAX, parsed));
}

// Expose telemetry to window for debugging in production
if (typeof window !== 'undefined') {
    window.__ROURCE_TELEMETRY__ = getTelemetryStats;
}
