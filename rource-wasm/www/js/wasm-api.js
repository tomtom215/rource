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
// Wrappers for the 28 insights analysis methods.
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
 * Contains all 25 research-backed metrics in a single response.
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

/**
 * Returns developer experience scores (Mockus & Votta 2000, Eyolfson et al. 2014).
 * Experience = tenure_days * ln(1 + commits) * file_familiarity.
 * @returns {Object|null} Developer experience data with per-developer scores
 */
export function getDeveloperExperience() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getDeveloperExperience', () => rource.getDeveloperExperience(), null);
        return parseInsightsJson('getDeveloperExperience', json, null);
    }
    return null;
}

/**
 * Returns per-file ownership fragmentation / Gini coefficient (Bird et al. 2011).
 * Measures how unevenly commit ownership is distributed across contributors per file.
 * @returns {Object|null} Ownership fragmentation data with per-file Gini coefficients
 */
export function getOwnershipFragmentation() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getOwnershipFragmentation', () => rource.getOwnershipFragmentation(), null);
        return parseInsightsJson('getOwnershipFragmentation', json, null);
    }
    return null;
}

/**
 * Returns release rhythm analysis (Khomh et al. 2012, da Costa et al. 2016).
 * Analyzes commit velocity patterns to detect release cycles and regularity.
 * @returns {Object|null} Release rhythm data with regularity, phase, trend
 */
export function getReleaseRhythm() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getReleaseRhythm', () => rource.getReleaseRhythm(), null);
        return parseInsightsJson('getReleaseRhythm', json, null);
    }
    return null;
}

/**
 * Returns per-directory knowledge distribution entropy (Constantinou & Mens 2017).
 * Shannon entropy of contributor distribution per directory, normalized by log2(n).
 * @returns {Object|null} Knowledge distribution data with per-directory entropy
 */
export function getKnowledgeDistribution() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getKnowledgeDistribution', () => rource.getKnowledgeDistribution(), null);
        return parseInsightsJson('getKnowledgeDistribution', json, null);
    }
    return null;
}

/**
 * Returns code churn volatility per file (Nagappan & Ball 2005).
 * Coefficient of variation of weighted churn across time windows.
 * @returns {Object|null} Churn volatility data with per-file CV scores
 */
export function getChurnVolatility() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getChurnVolatility', () => rource.getChurnVolatility(), null);
        return parseInsightsJson('getChurnVolatility', json, null);
    }
    return null;
}

/**
 * Returns enhanced truck factor via DOA model (Avelino et al. 2016).
 * Minimum developers whose departure orphans >50% of files.
 * @returns {Object|null} Truck factor data with developer criticality rankings
 */
export function getTruckFactor() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getTruckFactor', () => rource.getTruckFactor(), null);
        return parseInsightsJson('getTruckFactor', json, null);
    }
    return null;
}

/**
 * Returns developer turnover impact analysis (Mockus 2009).
 * Identifies departed developers and orphaned files.
 * @returns {Object|null} Turnover impact data with departed developers and orphan rates
 */
export function getTurnoverImpact() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getTurnoverImpact', () => rource.getTurnoverImpact(), null);
        return parseInsightsJson('getTurnoverImpact', json, null);
    }
    return null;
}

/**
 * Returns per-commit complexity scores (Herzig & Zeller 2013).
 * Shannon entropy of action types × file count × directory count.
 * @returns {Object|null} Commit complexity data with tangled commit detection
 */
export function getCommitComplexity() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCommitComplexity', () => rource.getCommitComplexity(), null);
        return parseInsightsJson('getCommitComplexity', json, null);
    }
    return null;
}

/**
 * Returns defect-introducing change patterns (Kim et al. 2008).
 * Burst edits following large commits as proxy for defect introduction.
 * @returns {Object|null} Defect pattern data with per-file risk scores
 */
export function getDefectPatterns() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getDefectPatterns', () => rource.getDefectPatterns(), null);
        return parseInsightsJson('getDefectPatterns', json, null);
    }
    return null;
}

/**
 * Returns language/technology distribution by file extension (Mockus et al. 2002).
 * Classifies repository files by programming language based on file extensions.
 * @returns {Object|null} Tech distribution data with per-language file counts
 */
export function getTechDistribution() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getTechDistribution', () => rource.getTechDistribution(), null);
        return parseInsightsJson('getTechDistribution', json, null);
    }
    return null;
}

/**
 * Returns commit activity heatmap — day-of-week x hour-of-day (Eyolfson et al. 2011).
 * 7x24 grid showing when development activity occurs.
 * @returns {Object|null} Activity heatmap data with grid and peak metrics
 */
export function getActivityHeatmap() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getActivityHeatmap', () => rource.getActivityHeatmap(), null);
        return parseInsightsJson('getActivityHeatmap', json, null);
    }
    return null;
}

/**
 * Returns developer technology expertise profiles (Mockus & Herbsleb 2002).
 * Maps each developer to technologies they work with based on file extensions.
 * @returns {Object|null} Tech expertise data with per-developer technology profiles
 */
export function getTechExpertise() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getTechExpertise', () => rource.getTechExpertise(), null);
        return parseInsightsJson('getTechExpertise', json, null);
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

// ============================================================================
// Intelligence Tab API: Novel Research Metrics (M1-M7)
// ============================================================================

/**
 * Returns contextual complexity (working set size) analysis.
 * For each file, the number of other files a developer must
 * simultaneously understand to safely modify it.
 *
 * Academic basis: Bavota et al. (ICSM 2013), Gall et al. (ICSE 1998),
 * Denning (CACM 1968) working set model.
 *
 * @returns {Object|null} Contextual complexity data
 */
export function getContextualComplexity() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getContextualComplexity', () => rource.getContextualComplexity(), null);
        return parseInsightsJson('getContextualComplexity', json, null);
    }
    return null;
}

/**
 * Returns commit cohesion index analysis.
 * Measures whether commits are atomic (tightly related) or tangled
 * using normalized pairwise directory distance.
 *
 * Academic basis: Herzig & Zeller (ICSE 2013), Kirinuki et al. (SANER 2014).
 *
 * @returns {Object|null} Commit cohesion data
 */
export function getCommitCohesion() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCommitCohesion', () => rource.getCommitCohesion(), null);
        return parseInsightsJson('getCommitCohesion', json, null);
    }
    return null;
}

/**
 * Returns change propagation prediction analysis.
 * Predicts which files need concurrent modification using historical
 * co-change patterns and transitive cascade depth.
 *
 * Academic basis: Hassan & Holt (ICSM 2004), Zimmermann et al. (ESEC/FSE 2005).
 *
 * @returns {Object|null} Change propagation data
 */
export function getChangePropagation() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getChangePropagation', () => rource.getChangePropagation(), null);
        return parseInsightsJson('getChangePropagation', json, null);
    }
    return null;
}

/**
 * Returns commit message entropy analysis.
 * Measures information density and quality of commit messages
 * using Shannon entropy and cross-entropy.
 *
 * Academic basis: Dyer et al. (MSR 2013), Hindle et al. (ICSE 2012).
 *
 * @returns {Object|null} Commit message entropy data
 */
export function getCommitMessageEntropy() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCommitMessageEntropy', () => rource.getCommitMessageEntropy(), null);
        return parseInsightsJson('getCommitMessageEntropy', json, null);
    }
    return null;
}

/**
 * Returns knowledge half-life analysis.
 * Models exponential knowledge decay per-file with adaptive decay rates.
 *
 * Academic basis: Fritz et al. (ICSE 2010), Robillard et al. (IEEE Software 2014),
 * Ebbinghaus (1885) forgetting curve.
 *
 * @returns {Object|null} Knowledge half-life data
 */
export function getKnowledgeHalfLife() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getKnowledgeHalfLife', () => rource.getKnowledgeHalfLife(), null);
        return parseInsightsJson('getKnowledgeHalfLife', json, null);
    }
    return null;
}

/**
 * Returns architectural drift index analysis.
 * Measures divergence between directory structure and co-change clusters
 * using Normalized Mutual Information (NMI).
 *
 * Academic basis: Garcia et al. (WICSA 2009), Maqbool & Babri (JSS 2007),
 * Raghavan et al. (Phys Rev 2007) label propagation.
 *
 * @returns {Object|null} Architectural drift data
 */
export function getArchitecturalDrift() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getArchitecturalDrift', () => rource.getArchitecturalDrift(), null);
        return parseInsightsJson('getArchitecturalDrift', json, null);
    }
    return null;
}

/**
 * Returns succession readiness analysis.
 * For each file, scores how prepared the team is for the primary
 * contributor to become unavailable.
 *
 * Academic basis: Ricca et al. (JSS 2011), Rigby & Bird (FSE 2013).
 *
 * @returns {Object|null} Succession readiness data
 */
export function getSuccessionReadiness() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getSuccessionReadiness', () => rource.getSuccessionReadiness(), null);
        return parseInsightsJson('getSuccessionReadiness', json, null);
    }
    return null;
}

/**
 * Returns code reviewer recommendations via ownership+recency+review scoring.
 * Academic basis: Thongtanunam et al. (SANER 2015), Balachandran (ICSE 2013).
 * @returns {Object|null} Reviewer recommendation data per file
 */
export function getReviewerRecommendation() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getReviewerRecommendation', () => rource.getReviewerRecommendation(), null);
        return parseInsightsJson('getReviewerRecommendation', json, null);
    }
    return null;
}

/**
 * Returns review response time distribution analysis.
 * Academic basis: Rigby & Storey (ICSE 2011), Baysal et al. (ESE 2016).
 * @returns {Object|null} Review response data with P50/P90 times
 */
export function getReviewResponse() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getReviewResponse', () => rource.getReviewResponse(), null);
        return parseInsightsJson('getReviewResponse', json, null);
    }
    return null;
}

/**
 * Returns contributor onboarding velocity analysis.
 * Academic basis: Zhou & Mockus (ICSE 2012), Steinmacher et al. (ISSE 2015).
 * @returns {Object|null} Onboarding data with developer classifications
 */
export function getOnboardingVelocity() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getOnboardingVelocity', () => rource.getOnboardingVelocity(), null);
        return parseInsightsJson('getOnboardingVelocity', json, null);
    }
    return null;
}

/**
 * Returns interface stability score analysis.
 * Academic basis: Martin (2003 SDP/SAP), MacCormack et al. (Management Science 2006).
 * @returns {Object|null} Interface stability data per directory boundary
 */
export function getInterfaceStability() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getInterfaceStability', () => rource.getInterfaceStability(), null);
        return parseInsightsJson('getInterfaceStability', json, null);
    }
    return null;
}

/**
 * Returns technical debt velocity trend analysis.
 * Academic basis: Wehaibi et al. (SANER 2016), Maldonado & Shihab (MSR 2015).
 * @returns {Object|null} Tech debt velocity with trend classification
 */
export function getTechDebtVelocity() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getTechDebtVelocity', () => rource.getTechDebtVelocity(), null);
        return parseInsightsJson('getTechDebtVelocity', json, null);
    }
    return null;
}

/**
 * Returns development focus drift analysis.
 * Academic basis: Hassan (FoSE 2008), D'Ambros & Lanza (SCP 2010).
 * @returns {Object|null} Focus drift data with per-directory trends
 */
export function getFocusDrift() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getFocusDrift', () => rource.getFocusDrift(), null);
        return parseInsightsJson('getFocusDrift', json, null);
    }
    return null;
}

/**
 * Returns AI-assisted change detection analysis.
 * Academic basis: Imai (ESEM 2022), Dakhel et al. (JSS 2023), Vasilescu et al. (FSE 2015).
 * @returns {Object|null} AI change detection data with flagged commits
 */
export function getAiChangeDetection() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getAiChangeDetection', () => rource.getAiChangeDetection(), null);
        return parseInsightsJson('getAiChangeDetection', json, null);
    }
    return null;
}

/**
 * Returns knowledge Gini coefficient analysis.
 * Academic basis: Yamashita & Moonen (WCRE 2013), Greiler et al. (FSE 2015).
 * @returns {Object|null} Knowledge inequality data with Gini coefficient
 */
export function getKnowledgeGini() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getKnowledgeGini', () => rource.getKnowledgeGini(), null);
        return parseInsightsJson('getKnowledgeGini', json, null);
    }
    return null;
}

/**
 * Returns expertise breadth vs depth profile analysis.
 * Academic basis: Mockus & Herbsleb (ICSE 2002), Fritz et al. (FSE 2010).
 * @returns {Object|null} Expertise profiles with quadrant classifications
 */
export function getExpertiseProfile() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getExpertiseProfile', () => rource.getExpertiseProfile(), null);
        return parseInsightsJson('getExpertiseProfile', json, null);
    }
    return null;
}

/**
 * Returns cognitive load estimation per file.
 * Academic basis: Fakhoury et al. (ICPC 2019), Kapur & Musgrove (ESEC/FSE 2023).
 * @returns {Object|null} Cognitive load data with per-file scores
 */
export function getCognitiveLoad() {
    const rource = getRource();
    if (rource) {
        const json = safeWasmCall('getCognitiveLoad', () => rource.getCognitiveLoad(), null);
        return parseInsightsJson('getCognitiveLoad', json, null);
    }
    return null;
}
