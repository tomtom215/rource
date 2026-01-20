/**
 * Rource - WASM Error Boundary
 *
 * Provides safe wrappers for all WASM calls to prevent uncaught exceptions
 * from crashing the application. All WASM errors are logged and tracked.
 */

import { CONFIG } from './config.js';
import { telemetry, recordTelemetry } from './telemetry.js';
import { getRource, isContextLost } from './state.js';

/**
 * Safely calls a WASM method with error handling.
 * Logs errors, updates telemetry, and returns a default value on failure.
 *
 * @template T
 * @param {string} methodName - Name of the WASM method (for logging)
 * @param {() => T} fn - Function that calls the WASM method
 * @param {T} defaultValue - Value to return if the call fails
 * @returns {T} Result of the WASM call or default value on error
 *
 * @example
 * // Safe zoom call
 * safeWasmCall('zoom', () => rource.zoom(factor), undefined);
 *
 * // Safe getter with default
 * const fps = safeWasmCall('getFps', () => rource.getFps(), 0);
 */
export function safeWasmCall(methodName, fn, defaultValue) {
    try {
        return fn();
    } catch (error) {
        telemetry.wasmErrors++;
        telemetry.lastError = error;

        if (CONFIG.LOG_WASM_ERRORS) {
            console.error(`[WASM Error:${methodName}]`, error);
        }

        recordTelemetry('wasm_error', { method: methodName, error: error.message });

        return defaultValue;
    }
}

/**
 * Safely calls a WASM method that doesn't return a value.
 * Use this for methods like zoom(), pan(), play(), etc.
 *
 * @param {string} methodName - Name of the WASM method (for logging)
 * @param {() => void} fn - Function that calls the WASM method
 * @returns {boolean} True if the call succeeded, false if it threw
 *
 * @example
 * safeWasmVoid('onMouseDown', () => rource.onMouseDown(x, y));
 */
export function safeWasmVoid(methodName, fn) {
    try {
        fn();
        return true;
    } catch (error) {
        telemetry.wasmErrors++;
        telemetry.lastError = error;

        if (CONFIG.LOG_WASM_ERRORS) {
            console.error(`[WASM Error:${methodName}]`, error);
        }

        recordTelemetry('wasm_error', { method: methodName, error: error.message });

        return false;
    }
}

/**
 * Checks if the WASM runtime is in a healthy state.
 * @returns {boolean} True if WASM is initialized and not in error state
 */
export function isWasmHealthy() {
    return getRource() !== null && !isContextLost() && telemetry.wasmErrors < 10;
}

// ============================================================
// Convenience wrappers for common WASM operations
// ============================================================

/**
 * Safely zooms the visualization.
 * @param {number} factor - Zoom factor
 */
export function zoom(factor) {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('zoom', () => rource.zoom(factor));
    }
}

/**
 * Safely pans the visualization.
 * @param {number} dx - X delta
 * @param {number} dy - Y delta
 */
export function pan(dx, dy) {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('pan', () => rource.pan(dx, dy));
    }
}

/**
 * Safely plays the visualization.
 */
export function play() {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('play', () => rource.play());
    }
}

/**
 * Safely pauses the visualization.
 */
export function pause() {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('pause', () => rource.pause());
    }
}

/**
 * Safely toggles play/pause.
 */
export function togglePlay() {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('togglePlay', () => rource.togglePlay());
    }
}

/**
 * Safely checks if playing.
 * @returns {boolean} True if playing
 */
export function isPlaying() {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('isPlaying', () => rource.isPlaying(), false);
    }
    return false;
}

/**
 * Safely gets FPS.
 * @returns {number} Current FPS
 */
export function getFps() {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('getFps', () => rource.getFps(), 0);
    }
    return 0;
}

/**
 * Safely gets frame time in milliseconds.
 * @returns {number} Frame time
 */
export function getFrameTimeMs() {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('getFrameTimeMs', () => rource.getFrameTimeMs(), 0);
    }
    return 0;
}

/**
 * Safely sets playback speed.
 * @param {number} secondsPerDay - Seconds per day
 */
export function setSpeed(secondsPerDay) {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('setSecondsPerDay', () => rource.setSecondsPerDay(secondsPerDay));
    }
}

/**
 * Safely forces a render.
 */
export function forceRender() {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('forceRender', () => rource.forceRender());
    }
}

/**
 * Safely gets commit count.
 * @returns {number} Total commits
 */
export function getCommitCount() {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('commitCount', () => rource.commitCount(), 0);
    }
    return 0;
}

/**
 * Safely gets current commit index.
 * @returns {number} Current commit index
 */
export function getCurrentCommit() {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    }
    return 0;
}

/**
 * Safely seeks to a commit.
 * @param {number} index - Commit index
 */
export function seekToCommit(index) {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('seekToCommit', () => rource.seekToCommit(index));
    }
}

/**
 * Safely gets author list.
 * @returns {Array} Authors
 */
export function getAuthors() {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('getAuthors', () => rource.getAuthors(), []);
    }
    return [];
}

/**
 * Safely gets author color.
 * @param {string} name - Author name
 * @returns {string} Hex color
 */
export function getAuthorColor(name) {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('getAuthorColor', () => rource.getAuthorColor(name), '#888888');
    }
    return '#888888';
}
