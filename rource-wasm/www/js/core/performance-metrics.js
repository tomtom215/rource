// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Performance Metrics Tracking
 *
 * Handles FPS statistics tracking and performance metrics overlay updates.
 * Provides both uncapped mode statistics (peak/average FPS) and general
 * performance metrics display.
 *
 * @module core/performance-metrics
 */

import { CONFIG } from '../config.js';
import { getAllElements } from '../dom.js';
import { getRource, hasData, get } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';

// =============================================================================
// Module State
// =============================================================================

/** Counter for throttling performance metrics updates. */
let perfUpdateCounter = 0;

/**
 * Uncapped FPS tracking statistics for peak/average display.
 * Reset when entering uncapped mode or restarting playback.
 */
const uncappedFpsStats = {
    maxFps: 0,
    fpsSum: 0,
    frameCount: 0,
    /** Exponential Moving Average for smoother average display. */
    emaFps: 0,
    /** EMA smoothing factor (lower = smoother, higher = more responsive). */
    emaAlpha: 0.1,
};

// =============================================================================
// FPS Statistics
// =============================================================================

/**
 * Updates FPS statistics with the current frame's FPS value.
 * Call this once per frame when in uncapped mode.
 *
 * @param {number} fps - Current frame's FPS value
 */
export function updateFpsStats(fps) {
    if (fps > 0) {
        uncappedFpsStats.maxFps = Math.max(uncappedFpsStats.maxFps, fps);
        uncappedFpsStats.fpsSum += fps;
        uncappedFpsStats.frameCount++;

        // Update EMA for smoother average display
        if (uncappedFpsStats.emaFps === 0) {
            uncappedFpsStats.emaFps = fps;
        } else {
            uncappedFpsStats.emaFps =
                uncappedFpsStats.emaAlpha * fps +
                (1 - uncappedFpsStats.emaAlpha) * uncappedFpsStats.emaFps;
        }
    }
}

/**
 * Resets the uncapped FPS tracking statistics.
 *
 * Call this when:
 * - Entering uncapped mode
 * - Restarting playback
 * - Loading new data
 */
export function resetUncappedFpsStats() {
    uncappedFpsStats.maxFps = 0;
    uncappedFpsStats.fpsSum = 0;
    uncappedFpsStats.frameCount = 0;
    uncappedFpsStats.emaFps = 0;
}

/**
 * Gets the current uncapped FPS statistics.
 *
 * @returns {{maxFps: number, avgFps: number, emaFps: number, frameCount: number}}
 *          Statistics object with peak, average, and EMA FPS values
 */
export function getUncappedFpsStats() {
    const avgFps =
        uncappedFpsStats.frameCount > 0
            ? uncappedFpsStats.fpsSum / uncappedFpsStats.frameCount
            : 0;
    return {
        maxFps: uncappedFpsStats.maxFps,
        avgFps: avgFps,
        emaFps: uncappedFpsStats.emaFps,
        frameCount: uncappedFpsStats.frameCount,
    };
}

// =============================================================================
// Performance Update Throttling
// =============================================================================

/**
 * Increments the performance update counter.
 * @returns {number} The current counter value after incrementing
 */
export function incrementPerfCounter() {
    return ++perfUpdateCounter;
}

/**
 * Checks if performance metrics should be updated based on throttle interval.
 * @returns {boolean} True if update interval has been reached
 */
export function shouldUpdatePerfMetrics() {
    return perfUpdateCounter >= CONFIG.PERF_UPDATE_INTERVAL;
}

/**
 * Resets the performance update counter after updating metrics.
 */
export function resetPerfCounter() {
    perfUpdateCounter = 0;
}

// =============================================================================
// Performance Metrics Display
// =============================================================================

/**
 * Updates the performance metrics overlay.
 *
 * Uses the batched getFrameStats() API to collect all statistics in a single
 * WASM call, reducing overhead by approximately 90% compared to individual calls.
 * Called periodically (controlled by CONFIG.PERF_UPDATE_INTERVAL) rather
 * than every frame to reduce overhead.
 */
export function updatePerfMetrics() {
    const rource = getRource();
    if (!rource || !hasData()) return;

    const elements = getAllElements();
    const {
        perfFps,
        perfFrameTime,
        perfEntities,
        perfVisible,
        perfDraws,
        perfResolution,
        perfPeakAvgRow,
        perfPeakFps,
        perfAvgFps,
        perfPeakBadge,
        perfPeakHeader,
    } = elements;

    if (!perfFps) return;

    try {
        // Get all frame statistics in a single batched WASM call
        // This replaces 12+ individual calls with one, reducing overhead by ~90%
        const statsJson = safeWasmCall('getFrameStats', () => rource.getFrameStats(), null);
        if (!statsJson) return;

        const stats = JSON.parse(statsJson);

        // Extract values from batched response
        const fps = stats.fps;
        const frameTimeMs = stats.frameTimeMs;
        const totalEntities = stats.totalEntities;
        const visibleFiles = stats.visibleFiles;
        const visibleUsers = stats.visibleUsers;
        const visibleDirs = stats.visibleDirectories;
        const drawCalls = stats.drawCalls;
        const width = stats.canvasWidth;
        const height = stats.canvasHeight;
        const isPlaying = stats.isPlaying;
        const total = stats.commitCount;
        const current = stats.currentCommit;

        // Update FPS display with color coding and playback status
        const fpsRounded = Math.round(fps);
        const isComplete = current >= total - 1 && !isPlaying;
        const isUncapped = get('uncappedFps');

        if (isComplete) {
            perfFps.textContent = 'Complete';
            perfFps.className = 'perf-fps complete';
        } else if (!isPlaying) {
            perfFps.textContent = 'Paused';
            perfFps.className = 'perf-fps paused';
        } else if (isUncapped) {
            // In uncapped mode, show FPS with special styling
            perfFps.textContent = `${fpsRounded} FPS`;
            perfFps.className = 'perf-fps uncapped';
        } else {
            perfFps.textContent = `${fpsRounded} FPS`;
            perfFps.className =
                'perf-fps ' + (fpsRounded >= 55 ? 'good' : fpsRounded >= 30 ? 'ok' : 'bad');
        }

        // Update Peak/Avg row visibility and values
        const fpsStats = isUncapped ? getUncappedFpsStats() : null;
        if (perfPeakAvgRow) {
            if (isUncapped && isPlaying) {
                // Show peak/avg row in uncapped mode while playing
                perfPeakAvgRow.classList.remove('hidden');
                if (perfPeakFps) perfPeakFps.textContent = Math.round(fpsStats.maxFps);
                if (perfAvgFps) perfAvgFps.textContent = Math.round(fpsStats.emaFps);
            } else {
                // Hide when not in uncapped mode or not playing
                perfPeakAvgRow.classList.add('hidden');
            }
        }

        // Update Peak badge in header (visible even when overlay is collapsed)
        // This ensures peak FPS is visible on mobile where the overlay is collapsed by default
        if (perfPeakBadge) {
            if (isUncapped && fpsStats && fpsStats.maxFps > 0) {
                // Show badge with peak FPS value
                perfPeakBadge.classList.remove('hidden');
                if (perfPeakHeader) {
                    const newPeak = Math.round(fpsStats.maxFps);
                    const oldPeak = parseInt(perfPeakHeader.textContent, 10) || 0;
                    perfPeakHeader.textContent = newPeak;
                    // Add brief highlight animation when a new peak is reached
                    if (newPeak > oldPeak && oldPeak > 0) {
                        perfPeakBadge.classList.add('new-record');
                        setTimeout(() => perfPeakBadge.classList.remove('new-record'), 600);
                    }
                }
            } else {
                // Hide badge when not in uncapped mode or no data yet
                perfPeakBadge.classList.add('hidden');
            }
        }

        // Update other metrics
        // Frame time display precision depends on mode:
        // - Uncapped mode: show microsecond precision (3 decimals = 0.001ms = 1µs)
        // - Capped mode: show 1 decimal place (sufficient for vsync'd 16.7ms frames)
        //
        // NOTE: Actual timer resolution is limited by browser Spectre mitigations:
        // - Chrome: ~5µs, Firefox: ~20µs, Safari: ~100µs
        // True nanosecond precision is not achievable from JavaScript.
        if (perfFrameTime) {
            if (isUncapped) {
                // Microsecond display for performance analysis
                // (limited by browser timer resolution, not display format)
                if (frameTimeMs < 1.0) {
                    perfFrameTime.textContent = `${(frameTimeMs * 1000).toFixed(0)}µs`;
                } else if (frameTimeMs < 10.0) {
                    perfFrameTime.textContent = `${frameTimeMs.toFixed(3)}ms`;
                } else {
                    perfFrameTime.textContent = `${frameTimeMs.toFixed(2)}ms`;
                }
            } else {
                perfFrameTime.textContent = `${frameTimeMs.toFixed(1)}ms`;
            }
        }
        if (perfEntities) perfEntities.textContent = totalEntities.toLocaleString();
        if (perfVisible)
            perfVisible.textContent = `${visibleFiles + visibleUsers + visibleDirs}`;
        if (perfDraws) perfDraws.textContent = drawCalls.toString();
        if (perfResolution) perfResolution.textContent = `${width}×${height}`;
    } catch {
        // WASM methods may not be available during initialization or context loss
        // Show placeholder values instead of crashing
        if (perfFps) {
            perfFps.textContent = '--';
            perfFps.className = 'perf-fps';
        }
        if (perfFrameTime) perfFrameTime.textContent = '--';
        if (perfEntities) perfEntities.textContent = '--';
        if (perfVisible) perfVisible.textContent = '--';
        if (perfDraws) perfDraws.textContent = '--';
        if (perfPeakAvgRow) perfPeakAvgRow.classList.add('hidden');
        if (perfPeakBadge) perfPeakBadge.classList.add('hidden');
    }
}

/**
 * Performs a single frame's performance tracking tasks.
 * Call this once per frame to handle throttled updates.
 */
export function trackFramePerformance() {
    incrementPerfCounter();
    if (shouldUpdatePerfMetrics()) {
        updatePerfMetrics();
        resetPerfCounter();
    }
}
