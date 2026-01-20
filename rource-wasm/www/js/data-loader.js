/**
 * Rource - Data Loading & Parsing
 *
 * Handles loading and parsing of commit log data.
 */

import { getRource, setState, get } from './state.js';
import { getAllElements } from './dom.js';
import { showToast } from './toast.js';
import { safeWasmCall } from './wasm-api.js';
import { debugLog } from './telemetry.js';
import { parseUrlParams } from './url-state.js';
import { ROURCE_CACHED_DATA, DEMO_DATA, ROURCE_STATS, getFullCachedData } from './cached-data.js';

// Callbacks for UI updates
let onDataLoadedCallback = null;

/**
 * Sets the callback to run after data is loaded.
 * @param {Function} callback - Callback function
 */
export function setOnDataLoadedCallback(callback) {
    onDataLoadedCallback = callback;
}

/**
 * Analyzes log data for statistics.
 * @param {string} content - Log content
 * @returns {Object} Stats with commits, files, authors
 */
export function analyzeLogData(content) {
    const lines = content.split('\n');
    const files = new Set();
    const authors = new Set();
    let commits = 0;

    for (const line of lines) {
        if (!line.trim()) continue;
        const parts = line.split('|');
        if (parts.length >= 4) {
            commits++;
            authors.add(parts[1].trim());
            files.add(parts[3].trim());
        }
    }

    return { commits, files: files.size, authors };
}

/**
 * Loads log data into the visualization.
 * @param {string} content - Log content
 * @param {string} [format='custom'] - Format: 'custom' or 'git'
 * @returns {boolean} True if successful
 */
export function loadLogData(content, format = 'custom') {
    const rource = getRource();

    if (!rource || !content.trim()) {
        showToast('Please enter or upload log data first.', 'error');
        return false;
    }

    const elements = getAllElements();

    try {
        let count;
        if (format === 'git') {
            count = safeWasmCall('loadGitLog', () => rource.loadGitLog(content), 0);
        } else {
            count = safeWasmCall('loadCustomLog', () => rource.loadCustomLog(content), 0);
        }

        if (count === 0) {
            showToast('No commits found. Check your log format.', 'error');
            return false;
        }

        // Analyze data
        const stats = analyzeLogData(content);

        // Update stats overlay
        if (elements.statCommits) elements.statCommits.textContent = count;
        if (elements.statFiles) elements.statFiles.textContent = stats.files;
        if (elements.statAuthors) elements.statAuthors.textContent = stats.authors.size;

        // Update state
        setState({
            hasLoadedData: true,
            commitStats: { commits: count, files: stats.files, authors: stats.authors },
        });

        // Update UI visibility
        if (elements.emptyState) elements.emptyState.classList.add('hidden');
        if (elements.statsOverlay) elements.statsOverlay.classList.remove('hidden');
        if (elements.perfOverlay) elements.perfOverlay.classList.remove('hidden');

        // Enable controls
        if (elements.btnPrev) {
            elements.btnPrev.disabled = false;
            elements.btnPrev.title = 'Previous commit (< or ,)';
        }
        if (elements.btnNext) {
            elements.btnNext.disabled = false;
            elements.btnNext.title = 'Next commit (> or .)';
        }
        if (elements.speedSelect) {
            elements.speedSelect.disabled = false;
        }

        // Call callback if set
        if (onDataLoadedCallback) {
            onDataLoadedCallback(content, stats);
        }

        // Check for commit position in URL
        const urlParams = parseUrlParams();
        if (urlParams.commit) {
            const commitIndex = parseInt(urlParams.commit, 10);
            if (!isNaN(commitIndex) && commitIndex >= 0 && commitIndex < count) {
                safeWasmCall('seek', () => rource.seek(commitIndex), undefined);
            }
        }

        // Start paused by default, auto-play only if requested
        if (urlParams.autoplay === 'true') {
            safeWasmCall('play', () => rource.play(), undefined);
        }

        showToast(`Loaded ${count} commits from ${stats.authors.size} authors!`, 'success', 3000);

        return true;

    } catch (e) {
        // Provide user-friendly error messages
        let userMessage = 'Unable to load visualization data. ';
        if (e.message?.includes('Invalid') || e.message?.includes('parse')) {
            userMessage += 'Please check your log format matches: timestamp|author|action|filepath';
        } else if (e.message?.includes('empty')) {
            userMessage += 'The log appears to be empty.';
        } else {
            userMessage += 'Try a different log file or check the format.';
        }
        showToast(userMessage, 'error');
        debugLog('loadLogData', 'Parse error', e);
        return false;
    }
}

/**
 * Loads the cached Rource repository data.
 * @returns {boolean} True if successful
 */
export function loadRourceData() {
    return loadLogData(getFullCachedData(), 'custom');
}

/**
 * Loads the demo data.
 * @returns {boolean} True if successful
 */
export function loadDemoData() {
    return loadLogData(DEMO_DATA, 'custom');
}

/**
 * Gets the cached Rource repository stats.
 * @returns {Object} Stats object
 */
export function getRourceStats() {
    return ROURCE_STATS;
}

/**
 * Parses commits from log content for tooltip display.
 * @param {string} content - Log content
 * @returns {Array} Array of commit objects
 */
export function parseCommits(content) {
    const lines = content.split('\n');
    const commits = [];

    for (const line of lines) {
        if (!line.trim()) continue;
        const parts = line.split('|');
        if (parts.length >= 4) {
            commits.push({
                timestamp: parseInt(parts[0], 10),
                author: parts[1].trim(),
                action: parts[2].trim(),
                file: parts[3].trim(),
            });
        }
    }

    return commits;
}

/**
 * Detects the format of log content.
 * @param {string} content - Log content
 * @returns {string} Format: 'custom', 'git', or 'unknown'
 */
export function detectLogFormat(content) {
    const lines = content.trim().split('\n');
    if (lines.length === 0) return 'unknown';

    const firstLine = lines[0];

    // Check for custom format: timestamp|author|action|filepath
    if (/^\d+\|[^|]+\|[AMD]\|.+$/.test(firstLine)) {
        return 'custom';
    }

    // Check for git log format (simplified detection)
    if (firstLine.match(/^[a-f0-9]{40}/i) || content.includes('commit ')) {
        return 'git';
    }

    return 'unknown';
}

/**
 * Validates log content.
 * @param {string} content - Log content
 * @returns {Object} Validation result { valid, error, lineCount }
 */
export function validateLogContent(content) {
    if (!content || !content.trim()) {
        return { valid: false, error: 'Log content is empty', lineCount: 0 };
    }

    const lines = content.trim().split('\n');
    let validLines = 0;
    let invalidLines = [];

    for (let i = 0; i < lines.length; i++) {
        const line = lines[i].trim();
        if (!line) continue;

        const parts = line.split('|');
        if (parts.length >= 4) {
            const timestamp = parseInt(parts[0], 10);
            const action = parts[2].trim().toUpperCase();

            if (!isNaN(timestamp) && ['A', 'M', 'D'].includes(action)) {
                validLines++;
            } else {
                invalidLines.push(i + 1);
            }
        } else {
            invalidLines.push(i + 1);
        }
    }

    if (validLines === 0) {
        return {
            valid: false,
            error: 'No valid log entries found. Expected format: timestamp|author|action|filepath',
            lineCount: 0,
        };
    }

    if (invalidLines.length > 0 && invalidLines.length > validLines) {
        return {
            valid: false,
            error: `Too many invalid lines (${invalidLines.length}). Check log format.`,
            lineCount: validLines,
        };
    }

    return { valid: true, lineCount: validLines };
}
