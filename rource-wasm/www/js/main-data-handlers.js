// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Data Loading & Legend Handlers
 *
 * Handles the post-data-loaded workflow: legend updates, author lists,
 * timeline markers, and view-state branching (analytics vs viz).
 */

import { CONFIG, getExtensionColor } from './config.js';
import { escapeHtml } from './utils.js';
import { getRource } from './state.js';
import { getElement, getAllElements } from './dom.js';
import { safeWasmCall } from './wasm-api.js';
import {
    updatePlaybackUI, resetTimelineDateLabels
} from './animation.js';
import { parseCommits } from './data-loader.js';
import { generateTimelineTicks } from './timeline-markers.js';
import { enableFontSizeControls, updateFontSizeUI } from './features/font-size.js';
import { maybeShowFirstTimeHelp } from './features/help.js';
import { updateBottomSheetFileTypes, updateBottomSheetAuthors } from './features/bottom-sheet.js';
import { updateImmersiveStats } from './features/immersive-mode.js';
import { invalidateInsightsCache, loadInsightsSummary, renderDashboard } from './features/insights.js';
import { getCurrentView } from './features/view-manager.js';

// Parsed commits for tooltip display
let parsedCommits = [];

/**
 * Returns the parsed commits array (for hover tooltip usage).
 * @returns {Array} Parsed commit entries
 */
export function getParsedCommits() {
    return parsedCommits;
}

/**
 * Handles data loaded event.
 * @param {string} content - Loaded log content
 * @param {Object} stats - Data statistics
 * @param {string} [format='custom'] - Log format: 'custom' or 'git'
 */
export function handleDataLoaded(content, stats, format = 'custom') {
    const elements = getAllElements();

    resetTimelineDateLabels();
    invalidateInsightsCache();
    loadInsightsSummary();

    parsedCommits = parseCommits(content);

    if (elements.showcaseCommits) elements.showcaseCommits.textContent = stats.commits.toLocaleString();
    if (elements.showcaseFiles) elements.showcaseFiles.textContent = stats.files.toLocaleString();
    if (elements.showcaseAuthors) elements.showcaseAuthors.textContent = stats.authors.size.toLocaleString();

    updateLegend(content, format);
    updateAuthorsLegend();

    enableFontSizeControls();
    updateFontSizeUI();
    updateImmersiveStats();
    updateTimelineMarkers(content);

    if (elements.authorsPanel) {
        elements.authorsPanel.classList.remove('hidden');
        elements.authorsPanel.classList.remove('collapsed');
        if (elements.authorsToggle) {
            elements.authorsToggle.setAttribute('aria-expanded', 'true');
        }
    }

    if (elements.legendPanel) {
        elements.legendPanel.classList.remove('collapsed');
        if (elements.legendToggle) {
            elements.legendToggle.setAttribute('aria-expanded', 'true');
        }
    }

    if (getCurrentView() === 'analytics') {
        renderDashboard();
    } else {
        const rource = getRource();
        if (rource) {
            safeWasmCall('play', () => rource.play(), undefined);
            updatePlaybackUI();
        }
        maybeShowFirstTimeHelp();
    }
}

/**
 * Updates the file types legend with file counts.
 * @param {string} content - Log content
 * @param {string} [format='custom'] - Log format: 'custom' or 'git'
 */
function updateLegend(content, format = 'custom') {
    const legendItems = getElement('legendItems');
    if (!legendItems) return;

    const extensionCounts = new Map();
    const lines = content.split('\n');
    const processedFiles = new Set();

    for (const line of lines) {
        let file = null;

        if (format === 'git') {
            const trimmed = line.trim();
            const statusMatch = trimmed.match(/^([AMDRCTU])\d*[\t\s]+(.+)$/i);
            if (statusMatch) {
                file = statusMatch[2].trim();
                const arrowIdx = file.indexOf(' -> ');
                if (arrowIdx > 0) {
                    file = file.slice(arrowIdx + 4).trim();
                }
                const tabIdx = file.indexOf('\t');
                if (tabIdx > 0) {
                    file = file.slice(tabIdx + 1).trim();
                }
            }
        } else {
            const parts = line.split('|');
            if (parts.length >= 4) {
                file = parts[3].trim();
            }
        }

        if (file && !processedFiles.has(file)) {
            processedFiles.add(file);
            const ext = file.includes('.') ? file.split('.').pop()?.toLowerCase() : '';
            if (ext) {
                extensionCounts.set(ext, (extensionCounts.get(ext) || 0) + 1);
            }
        }
    }

    const sortedExts = Array.from(extensionCounts.entries())
        .sort((a, b) => b[1] - a[1])
        .slice(0, 20);

    let html = '';
    for (const [ext, count] of sortedExts) {
        const color = getExtensionColor(ext);
        html += `<div class="legend-item" role="listitem">
            <span class="legend-color" style="background-color: ${escapeHtml(color)}"></span>
            <span class="legend-label">.${escapeHtml(ext)}</span>
            <span class="legend-count">${count}</span>
        </div>`;
    }

    html += `<div class="legend-divider" role="separator" aria-hidden="true"></div>
        <div class="legend-item legend-item-structure" role="listitem" title="Directories are shown as gray circles with center dots. Lines connect parent folders to child folders.">
            <svg class="legend-structure-icon" viewBox="0 0 20 20" aria-hidden="true">
                <circle cx="10" cy="10" r="7" fill="none" stroke="#6e7681" stroke-width="1.5" opacity="0.7"/>
                <circle cx="10" cy="10" r="2" fill="#6e7681" opacity="0.6"/>
            </svg>
            <span class="legend-ext">Directories</span>
        </div>`;

    legendItems.innerHTML = html;
    legendItems.setAttribute('role', 'list');

    const bsFileTypes = sortedExts.map(([ext, count]) => ({
        extension: ext,
        color: getExtensionColor(ext),
        count: count
    }));
    updateBottomSheetFileTypes(bsFileTypes);
}

/**
 * Updates the authors legend with commit counts.
 * Uses the WASM getAuthors() API which works for all log formats.
 */
function updateAuthorsLegend() {
    const authorsItems = getElement('authorsItems');
    const rource = getRource();
    if (!authorsItems || !rource) {
        console.warn('[Rource] updateAuthorsLegend: Missing authorsItems or rource');
        return;
    }

    try {
        const authorsJson = safeWasmCall('getAuthors', () => rource.getAuthors(), '[]');

        if (CONFIG.LOG_WASM_ERRORS) {
            console.log('[Rource] getAuthors returned:', authorsJson.substring(0, 200) + (authorsJson.length > 200 ? '...' : ''));
        }

        const authors = JSON.parse(authorsJson);

        if (!Array.isArray(authors)) {
            console.error('[Rource] getAuthors did not return an array:', typeof authors);
            return;
        }

        if (CONFIG.LOG_WASM_ERRORS) {
            console.log(`[Rource] Parsed ${authors.length} authors from WASM`);
        }

        const topAuthors = authors.slice(0, 30);

        let html = '';

        for (const author of topAuthors) {
            if (!author || !author.name) {
                console.warn('[Rource] Skipping invalid author entry:', author);
                continue;
            }
            html += `<div class="author-item" role="listitem" data-author="${escapeHtml(author.name)}">
                <span class="author-color" style="background-color: ${escapeHtml(author.color || '#888888')}"></span>
                <span class="author-name">${escapeHtml(author.name)}</span>
                <span class="author-commits">${author.commits || 0}</span>
            </div>`;
        }

        authorsItems.innerHTML = html;
        if (html) {
            authorsItems.setAttribute('role', 'list');
        }

        const bsAuthors = topAuthors.map(author => ({
            name: author.name || 'Unknown',
            color: author.color || '#888888',
            commits: author.commits || 0
        }));
        updateBottomSheetAuthors(bsAuthors);
    } catch (error) {
        console.error('[Rource] updateAuthorsLegend error:', error);
    }
}

/**
 * Updates timeline markers for significant commits.
 * @param {string} content - Log content (unused, timestamps come from WASM)
 */
function updateTimelineMarkers(content) {
    generateTimelineTicks();
}
