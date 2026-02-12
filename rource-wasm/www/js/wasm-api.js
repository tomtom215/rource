// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

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
 * @param {number} secondsPerDay - Seconds per day of commit history
 */
export function setSpeed(secondsPerDay) {
    const rource = getRource();
    if (rource) {
        safeWasmVoid('setSpeed', () => rource.setSpeed(secondsPerDay));
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

/**
 * Safely gets total directory count from scene.
 * Note: This only includes directories created so far during playback.
 * @returns {number} Directory count
 */
export function getTotalDirectories() {
    const rource = getRource();
    if (rource) {
        return safeWasmCall('getTotalDirectories', () => rource.getTotalDirectories(), 0);
    }
    return 0;
}

/**
 * Safely gets total directory count from all commits.
 * This calculates directory count from file paths, independent of playback state.
 * @returns {number} Directory count
 */
export function getCommitDirectoryCount() {
    const rource = getRource();
    if (rource) {
        // Try the new API first, fall back to getTotalDirectories if not available
        if (typeof rource.getCommitDirectoryCount === 'function') {
            return safeWasmCall('getCommitDirectoryCount', () => rource.getCommitDirectoryCount(), 0);
        }
        // Fallback for older WASM builds
        return safeWasmCall('getTotalDirectories', () => rource.getTotalDirectories(), 0);
    }
    return 0;
}

// ============================================================
// Repository Insights API
//
// Wrappers for the 21 insights analysis methods.
// All methods return parsed JSON objects (or null/[] on failure).
// Insights are computed from commit history, not per-frame data.
// ============================================================

/**
 * Parses a JSON string returned by a WASM insights method.
 * @param {string} methodName - Method name for error logging
 * @param {string|null} json - JSON string from WASM
 * @param {*} defaultValue - Fallback value on parse failure
 * @returns {*} Parsed JSON or default value
 */
function parseInsightsJson(methodName, json, defaultValue) {
    if (json == null) return defaultValue;
    try {
        return JSON.parse(json);
    } catch (e) {
        if (CONFIG.LOG_WASM_ERRORS) {
            console.warn(`[Insights parse error:${methodName}]`, e);
        }
        return defaultValue;
    }
}

/**
 * Returns the full insights report for the loaded repository.
 * Contains all 20 research-backed metrics in a single response.
 * @returns {Object|null} Complete InsightsReport or null if no commits loaded
 */
export function getInsights() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getInsights', () => rource.getInsights(), null);
        return parseInsightsJson('getInsights', json, null);
    }
    return null;
}

/**
 * Returns a dashboard summary: top hotspots, risk directories, and couplings.
 * @returns {Object|null} Summary object or null
 */
export function getInsightsSummary() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getInsightsSummary', () => rource.getInsightsSummary(), null);
        return parseInsightsJson('getInsightsSummary', json, null);
    }
    return null;
}

/**
 * Returns the top N file hotspots (defect-prone files).
 * @param {number} [limit=20] - Maximum number of hotspots
 * @returns {Array} Hotspot objects sorted by score
 */
export function getHotspots(limit = 20) {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getHotspots', () => rource.getHotspots(limit), null);
        return parseInsightsJson('getHotspots', json, []);
    }
    return [];
}

/**
 * Returns change coupling pairs (files that frequently co-change).
 * @param {number} [limit=20] - Maximum number of pairs
 * @returns {Array} Coupling pair objects
 */
export function getChangeCoupling(limit = 20) {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getChangeCoupling', () => rource.getChangeCoupling(limit), null);
        return parseInsightsJson('getChangeCoupling', json, []);
    }
    return [];
}

/**
 * Returns bus factor analysis per directory.
 * @returns {Array} Bus factor objects per directory
 */
export function getBusFactors() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getBusFactors', () => rource.getBusFactors(), null);
        return parseInsightsJson('getBusFactors', json, []);
    }
    return [];
}

/**
 * Returns temporal activity patterns (7x24 heatmap, peaks, bursts).
 * @returns {Object|null} Temporal patterns object
 */
export function getTemporalPatterns() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getTemporalPatterns', () => rource.getTemporalPatterns(), null);
        return parseInsightsJson('getTemporalPatterns', json, null);
    }
    return null;
}

/**
 * Returns codebase growth trajectory over time.
 * @returns {Object|null} Growth data with timeline and trend
 */
export function getCodebaseGrowth() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCodebaseGrowth', () => rource.getCodebaseGrowth(), null);
        return parseInsightsJson('getCodebaseGrowth', json, null);
    }
    return null;
}

/**
 * Returns sliding-window change entropy analysis.
 * @returns {Object|null} Entropy data with per-window values
 */
export function getChangeEntropy() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getChangeEntropy', () => rource.getChangeEntropy(), null);
        return parseInsightsJson('getChangeEntropy', json, null);
    }
    return null;
}

/**
 * Returns per-developer commit cadence analysis.
 * @returns {Object|null} Cadence data per developer
 */
export function getCommitCadence() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCommitCadence', () => rource.getCommitCadence(), null);
        return parseInsightsJson('getCommitCadence', json, null);
    }
    return null;
}

/**
 * Returns developer activity profiles (core/peripheral/drive-by).
 * @returns {Object|null} Profile classifications per developer
 */
export function getDeveloperProfiles() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getDeveloperProfiles', () => rource.getDeveloperProfiles(), null);
        return parseInsightsJson('getDeveloperProfiles', json, null);
    }
    return null;
}

/**
 * Returns developer focus and file diffusion analysis.
 * @returns {Object|null} Focus/diffusion scores per developer and file
 */
export function getDeveloperFocus() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getDeveloperFocus', () => rource.getDeveloperFocus(), null);
        return parseInsightsJson('getDeveloperFocus', json, null);
    }
    return null;
}

/**
 * Returns developer collaboration network analysis.
 * @returns {Object|null} Network metrics (density, components, centrality)
 */
export function getDeveloperNetwork() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getDeveloperNetwork', () => rource.getDeveloperNetwork(), null);
        return parseInsightsJson('getDeveloperNetwork', json, null);
    }
    return null;
}

/**
 * Returns knowledge map and silo analysis (Shannon entropy of ownership).
 * @returns {Object|null} Knowledge distribution data
 */
export function getKnowledgeMap() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getKnowledgeMap', () => rource.getKnowledgeMap(), null);
        return parseInsightsJson('getKnowledgeMap', json, null);
    }
    return null;
}

/**
 * Returns co-change modularity / DSM analysis.
 * @returns {Object|null} Modularity index and cross-module coupling
 */
export function getModularity() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getModularity', () => rource.getModularity(), null);
        return parseInsightsJson('getModularity', json, null);
    }
    return null;
}

/**
 * Returns sociotechnical congruence analysis.
 * @returns {Object|null} Congruence score and alignment data
 */
export function getCongruence() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCongruence', () => rource.getCongruence(), null);
        return parseInsightsJson('getCongruence', json, null);
    }
    return null;
}

/**
 * Returns work-type mix analysis (feature/maintenance/cleanup ratio).
 * @returns {Object|null} Work type percentages
 */
export function getWorkTypeMix() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getWorkTypeMix', () => rource.getWorkTypeMix(), null);
        return parseInsightsJson('getWorkTypeMix', json, null);
    }
    return null;
}

/**
 * Returns circadian (time-of-day) risk patterns.
 * @returns {Object|null} Risk scores per hour/day
 */
export function getCircadianRisk() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCircadianRisk', () => rource.getCircadianRisk(), null);
        return parseInsightsJson('getCircadianRisk', json, null);
    }
    return null;
}

/**
 * Returns per-file change burst detection.
 * @returns {Object|null} Burst data per file
 */
export function getChangeBursts() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getChangeBursts', () => rource.getChangeBursts(), null);
        return parseInsightsJson('getChangeBursts', json, null);
    }
    return null;
}

/**
 * Returns contribution inequality / Gini coefficient analysis.
 * @returns {Object|null} Gini coefficient and Lorenz curve data
 */
export function getContributionInequality() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getContributionInequality', () => rource.getContributionInequality(), null);
        return parseInsightsJson('getContributionInequality', json, null);
    }
    return null;
}

/**
 * Returns file lifecycle analysis (active/stable/ephemeral/dead/deleted).
 * @returns {Object|null} Lifecycle stage distribution
 */
export function getFileLifecycles() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getFileLifecycles', () => rource.getFileLifecycles(), null);
        return parseInsightsJson('getFileLifecycles', json, null);
    }
    return null;
}

/**
 * Returns file survival analysis (Kaplan-Meier estimator).
 * @returns {Object|null} Survival curve data
 */
export function getFileSurvival() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getFileSurvival', () => rource.getFileSurvival(), null);
        return parseInsightsJson('getFileSurvival', json, null);
    }
    return null;
}

// ============================================================================
// InsightsIndex API: Per-entity O(1) metric lookups
// ============================================================================

/**
 * Returns aggregated academic metrics for a specific file.
 *
 * Metrics include: hotspot score (Nagappan 2005), ownership (Bird 2011),
 * lifecycle stage (Godfrey 2000), circadian risk (Eyolfson 2011),
 * knowledge entropy (Rigby 2013), coupling degree (D'Ambros 2009).
 *
 * @param {string} path - File path relative to repository root
 * @returns {Object|null} Per-file academic metrics or null if not found
 */
export function getFileMetrics(path) {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getFileMetrics', () => rource.getFileMetrics(path), null);
        return parseInsightsJson('getFileMetrics', json, null);
    }
    return null;
}

/**
 * Returns aggregated academic metrics for a specific developer.
 *
 * Metrics include: profile type (Mockus 2002), cadence (Eyolfson 2014),
 * network centrality (Meneely 2009), focus score (Posnett 2013).
 *
 * @param {string} author - Author name
 * @returns {Object|null} Per-user academic metrics or null if not found
 */
export function getUserMetrics(author) {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getUserMetrics', () => rource.getUserMetrics(author), null);
        return parseInsightsJson('getUserMetrics', json, null);
    }
    return null;
}

/**
 * Returns the insights index summary (aggregate statistics).
 *
 * Contains: total files/users, knowledge silo count, contributor profile
 * distribution, max hotspot score, average contributors per file.
 *
 * @returns {Object|null} Index summary or null if no data
 */
export function getInsightsIndexSummary() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getInsightsIndexSummary', () => rource.getInsightsIndexSummary(), null);
        return parseInsightsJson('getInsightsIndexSummary', json, null);
    }
    return null;
}

/**
 * Returns all per-file metrics as an array of {path, metrics} objects.
 *
 * Useful for bulk visualization (e.g., coloring all files by hotspot score).
 *
 * @returns {Array} Array of {path, metrics} objects or empty array
 */
export function getAllFileMetrics() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getAllFileMetrics', () => rource.getAllFileMetrics(), null);
        return parseInsightsJson('getAllFileMetrics', json, []);
    }
    return [];
}

/**
 * Returns all per-user metrics as an array of {author, metrics} objects.
 *
 * @returns {Array} Array of {author, metrics} objects or empty array
 */
export function getAllUserMetrics() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getAllUserMetrics', () => rource.getAllUserMetrics(), null);
        return parseInsightsJson('getAllUserMetrics', json, []);
    }
    return [];
}
