// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Playback UI Controls
 *
 * Handles playback controls UI updates including play/pause button state,
 * timeline slider, commit info display, and date formatting.
 *
 * @module ui/playback-ui
 */

import { getAllElements } from '../dom.js';
import { getRource } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';

// Mobile controls callback (set via setPlaybackStateCallback)
let playbackStateCallback = null;

/**
 * Sets the callback for playback state changes.
 * Used by mobile controls to react to play/pause state.
 * @param {Function} callback - Called with (isPlaying: boolean)
 */
export function setPlaybackStateCallback(callback) {
    playbackStateCallback = callback;
}

// =============================================================================
// Module Constants
// =============================================================================

/**
 * Pre-allocated SVG icon strings to avoid allocations in hot path.
 * These are used for the play/pause/replay button states.
 */
const ICON_PAUSE = '<rect x="6" y="4" width="4" height="16"/><rect x="14" y="4" width="4" height="16"/>';
const ICON_PLAY = '<path d="M8 5v14l11-7z"/>';
const ICON_REPLAY = '<path d="M12 5V1L7 6l5 5V7c3.31 0 6 2.69 6 6s-2.69 6-6 6-6-2.69-6-6H4c0 4.42 3.58 8 8 8s8-3.58 8-8-3.58-8-8-8z"/>';

// =============================================================================
// Module State
// =============================================================================

/**
 * Cached state to avoid redundant DOM updates.
 * Prevents memory churn from unnecessary innerHTML assignments.
 */
const playbackUICache = {
    playing: null,
    current: -1,
    total: -1,
    atEnd: null,
    lastTimestamp: 0,
    lastAuthor: '',
    lastFileCount: -1,
};

// =============================================================================
// Date Formatting Utilities
// =============================================================================

/**
 * Formats a Unix timestamp to a readable date string.
 *
 * @param {number} timestamp - Unix timestamp in seconds
 * @param {boolean} [short=false] - If true, use short format with 2-digit year (e.g., "Jan 20 '24")
 * @returns {string} Formatted date string or '--' if invalid
 */
function formatDate(timestamp, short = false) {
    if (!timestamp || timestamp <= 0) return '--';
    const date = new Date(timestamp * 1000);
    if (short) {
        // Include 2-digit year for context in long repos
        return date.toLocaleDateString(undefined, { month: 'short', day: 'numeric', year: '2-digit' });
    }
    return date.toLocaleDateString(undefined, {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
    });
}

/**
 * Formats a Unix timestamp to a date with time.
 *
 * @param {number} timestamp - Unix timestamp in seconds
 * @returns {string} Formatted date and time string or '--' if invalid
 */
function formatDateTime(timestamp) {
    if (!timestamp || timestamp <= 0) return '--';
    const date = new Date(timestamp * 1000);
    return date.toLocaleDateString(undefined, {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
        hour: '2-digit',
        minute: '2-digit',
    });
}

// =============================================================================
// Playback UI Updates
// =============================================================================

/**
 * Updates playback UI (play button, timeline).
 *
 * Uses caching to avoid redundant DOM updates that cause memory churn.
 * Only updates elements when their values have actually changed.
 */
export function updatePlaybackUI() {
    const rource = getRource();
    if (!rource) return;

    const elements = getAllElements();
    const {
        btnPlayMain,
        playIconMain,
        timelineSlider,
        timelineInfoNumbers,
        timelineDate,
        timelineCommitInfo,
        timelineStartDate,
        timelineEndDate,
    } = elements;

    if (!btnPlayMain || !playIconMain) return;

    const playing = safeWasmCall('isPlaying', () => rource.isPlaying(), false);
    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    const atEnd = total > 0 && current >= total - 1 && !playing;

    // Only update play button if state changed (avoids innerHTML allocation)
    if (playing !== playbackUICache.playing || atEnd !== playbackUICache.atEnd) {
        const wasPlaying = playbackUICache.playing;
        playbackUICache.playing = playing;
        playbackUICache.atEnd = atEnd;

        // Notify mobile controls if play state changed
        if (playbackStateCallback && playing !== wasPlaying) {
            playbackStateCallback(playing);
        }

        if (playing) {
            playIconMain.innerHTML = ICON_PAUSE;
            btnPlayMain.title = 'Pause (Space)';
            btnPlayMain.classList.add('active');
            btnPlayMain.classList.remove('replay');
        } else if (atEnd) {
            playIconMain.innerHTML = ICON_REPLAY;
            btnPlayMain.title = 'Replay from start (Space)';
            btnPlayMain.classList.remove('active');
            btnPlayMain.classList.add('replay');
        } else {
            playIconMain.innerHTML = ICON_PLAY;
            btnPlayMain.title = 'Play (Space)';
            btnPlayMain.classList.remove('active');
            btnPlayMain.classList.remove('replay');
        }
    }

    // Only update timeline if current or total changed
    const currentChanged = current !== playbackUICache.current;
    const totalChanged = total !== playbackUICache.total;

    if (timelineSlider && timelineInfoNumbers && (currentChanged || totalChanged)) {
        playbackUICache.current = current;
        playbackUICache.total = total;

        if (total > 0) {
            timelineSlider.max = total - 1;
            timelineSlider.value = Math.min(current, total - 1);
            timelineSlider.disabled = false;
            const displayCurrent = Math.min(current + 1, total);
            const progressText = `${displayCurrent} / ${total}`;
            timelineInfoNumbers.textContent = progressText;
            timelineSlider.setAttribute('aria-valuetext', `Commit ${displayCurrent} of ${total}`);
            // I6: Update minimal HUD progress
            const { minimalHudProgress } = elements;
            if (minimalHudProgress) {
                minimalHudProgress.textContent = progressText;
            }
        } else {
            timelineSlider.max = 0;
            timelineSlider.value = 0;
            timelineSlider.disabled = true;
            timelineInfoNumbers.textContent = '0 / 0';
            timelineSlider.setAttribute('aria-valuetext', '0 of 0 commits');
            // I6: Clear minimal HUD progress
            const { minimalHudProgress } = elements;
            if (minimalHudProgress) {
                minimalHudProgress.textContent = '0 / 0';
            }
        }

        // Sync immersive mode timeline slider
        const immersiveSlider = document.getElementById('immersive-timeline-slider');
        if (immersiveSlider) {
            if (total > 0) {
                immersiveSlider.max = total - 1;
                immersiveSlider.value = Math.min(current, total - 1);
            } else {
                immersiveSlider.max = 0;
                immersiveSlider.value = 0;
            }
        }
    }

    // Only fetch commit details if current index changed
    if (currentChanged && total > 0) {
        const currentIndex = Math.min(current, total - 1);
        const timestamp = safeWasmCall(
            'getCommitTimestamp',
            () => rource.getCommitTimestamp(currentIndex),
            0
        );

        // Only update date display if timestamp changed
        if (timestamp !== playbackUICache.lastTimestamp) {
            playbackUICache.lastTimestamp = timestamp;
            if (timelineDate) {
                timelineDate.textContent = formatDateTime(timestamp);
            }
            // I6: Update minimal HUD date (short format for compact display)
            const { minimalHudDate } = elements;
            if (minimalHudDate) {
                minimalHudDate.textContent = formatDate(timestamp, true);
            }
        }

        // Only update commit info if changed
        if (timelineCommitInfo) {
            const author = safeWasmCall(
                'getCommitAuthor',
                () => rource.getCommitAuthor(currentIndex),
                ''
            );
            const fileCount = safeWasmCall(
                'getCommitFileCount',
                () => rource.getCommitFileCount(currentIndex),
                0
            );

            if (
                author !== playbackUICache.lastAuthor ||
                fileCount !== playbackUICache.lastFileCount
            ) {
                playbackUICache.lastAuthor = author;
                playbackUICache.lastFileCount = fileCount;

                if (author) {
                    const filesText = fileCount === 1 ? '1 file' : `${fileCount} files`;
                    timelineCommitInfo.textContent = `${author} - ${filesText}`;
                } else {
                    timelineCommitInfo.textContent = '';
                }
            }
        }
    } else if (currentChanged && total === 0) {
        // Clear displays when no data
        if (timelineDate) timelineDate.textContent = '--';
        if (timelineCommitInfo) timelineCommitInfo.textContent = '';
        // I6: Clear minimal HUD when no data
        const { minimalHudDate } = elements;
        if (minimalHudDate) minimalHudDate.textContent = '--';
    }

    // Update date range (start and end dates) - only need to do once when data changes
    // We check if the start date shows "--" which indicates it needs updating
    if (timelineStartDate && timelineEndDate && total > 0) {
        if (timelineStartDate.textContent === '--') {
            const startTimestamp = safeWasmCall(
                'getCommitTimestamp',
                () => rource.getCommitTimestamp(0),
                0
            );
            const endTimestamp = safeWasmCall(
                'getCommitTimestamp',
                () => rource.getCommitTimestamp(total - 1),
                0
            );
            timelineStartDate.textContent = formatDate(startTimestamp, true);
            timelineEndDate.textContent = formatDate(endTimestamp, true);
        }
    } else if (timelineStartDate && timelineEndDate && totalChanged && total === 0) {
        timelineStartDate.textContent = '--';
        timelineEndDate.textContent = '--';
    }
}

/**
 * Resets the timeline date range labels and playback UI cache.
 *
 * Call this when new data is loaded to force re-calculation of date range.
 */
export function resetTimelineDateLabels() {
    const elements = getAllElements();
    const { timelineStartDate, timelineEndDate, timelineDate, timelineCommitInfo } = elements;

    if (timelineStartDate) timelineStartDate.textContent = '--';
    if (timelineEndDate) timelineEndDate.textContent = '--';
    if (timelineDate) timelineDate.textContent = '--';
    if (timelineCommitInfo) timelineCommitInfo.textContent = '';

    // Reset cache to force UI refresh with new data
    playbackUICache.playing = null;
    playbackUICache.current = -1;
    playbackUICache.total = -1;
    playbackUICache.atEnd = null;
    playbackUICache.lastTimestamp = 0;
    playbackUICache.lastAuthor = '';
    playbackUICache.lastFileCount = -1;
}

/**
 * Checks if visualization has reached the end.
 * @returns {boolean} True if at the last commit
 */
export function isAtEnd() {
    const rource = getRource();
    if (!rource) return false;

    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    return total > 0 && current >= total - 1;
}
