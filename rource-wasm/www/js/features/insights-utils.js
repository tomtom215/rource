// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Insights Formatting & Utility Functions
 *
 * Shared formatting helpers used by both the insights tab renderers
 * and the table rendering functions.
 */

/**
 * Formats a number with the specified decimal places using locale formatting.
 * @param {number|null} n - Number to format
 * @param {number} decimals - Number of decimal places
 * @returns {string} Formatted number or 'N/A'
 */
export function formatNumber(n, decimals = 2) {
    if (n == null || isNaN(n) || !isFinite(n)) return 'N/A';
    return Number(n).toLocaleString(undefined, {
        minimumFractionDigits: decimals,
        maximumFractionDigits: decimals,
    });
}

/**
 * Formats a number with fixed decimal places (no locale grouping).
 * @param {number|null} n - Number to format
 * @param {number} decimals - Number of decimal places
 * @returns {string} Formatted number or 'N/A'
 */
export function formatFixed(n, decimals = 1) {
    if (n == null || !isFinite(n)) return 'N/A';
    return Number(n).toFixed(decimals);
}

/**
 * Formats an integer with locale grouping (e.g., 1,234).
 * @param {number|null} n - Number to format
 * @returns {string} Formatted integer or em-dash
 */
export function formatInt(n) {
    if (n == null || !isFinite(n)) return '\u2014';
    return Number(n).toLocaleString();
}

/**
 * Formats a decimal ratio as a percentage (e.g., 0.25 -> "25.0%").
 * @param {number|null} n - Ratio to format (0-1 scale)
 * @returns {string} Formatted percentage or 'N/A'
 */
export function formatPercentage(n) {
    if (n == null || !isFinite(n)) return 'N/A';
    return (Number(n) * 100).toFixed(1) + '%';
}

/**
 * Truncates a file path for display, preserving first and last segments.
 * @param {string} path - File path to truncate
 * @returns {string} Truncated path (max ~40 chars)
 */
export function truncatePath(path) {
    if (!path) return '';
    if (path.length <= 40) return path;
    const parts = path.split('/');
    if (parts.length <= 3) return path;
    const tail = parts.slice(-2).join('/');
    return parts[0] + '/\u2026/' + tail;
}

/**
 * Escapes special HTML characters to prevent XSS.
 * @param {string} str - String to escape
 * @returns {string} HTML-safe string
 */
export function escapeHtml(str) {
    if (!str) return '';
    return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/**
 * Capitalizes the first letter of a string.
 * @param {string} str - String to capitalize
 * @returns {string} Capitalized string
 */
export function capitalize(str) {
    if (!str) return '';
    return str.charAt(0).toUpperCase() + str.slice(1);
}

/**
 * Interprets a Gini coefficient as a human-readable inequality level.
 * @param {number|null} gini - Gini coefficient (0-1)
 * @returns {string} Human-readable interpretation
 */
export function giniInterpretation(gini) {
    if (gini == null || isNaN(gini)) return 'N/A';
    if (gini < 0.3) return 'Low inequality (healthy)';
    if (gini < 0.5) return 'Moderate inequality';
    if (gini < 0.7) return 'High inequality';
    return 'Very high inequality (risk)';
}

/**
 * Renders an empty state with contextual explanation.
 * @param {string} message - Primary message
 * @param {string} [hint] - Explanation of what data is needed
 * @returns {string} HTML string
 */
export function emptyState(message, hint) {
    let html = `<div class="insights-empty"><p>${escapeHtml(message)}</p>`;
    if (hint) {
        html += `<p class="insights-empty-hint">${escapeHtml(hint)}</p>`;
    }
    html += '</div>';
    return html;
}

/**
 * Renders a metric section with title, description, content, and optional "Why it matters".
 * @param {string} title - Section heading
 * @param {string} description - Metric description (may contain HTML entities)
 * @param {string} citation - Academic citation
 * @param {string} content - Inner HTML content (table, key-value list, etc.)
 * @param {string} [whyItMatters] - Optional contextual explanation
 * @returns {string} HTML string
 */
export function renderMetricSection(title, description, citation, content, whyItMatters) {
    let html = `<div class="insights-metric">
        <h4 class="insights-metric-title">${escapeHtml(title)}</h4>
        <p class="insights-metric-desc">${description}</p>
        ${content}`;
    if (whyItMatters) {
        html += `<p class="insights-metric-why"><strong>Why it matters:</strong> ${whyItMatters}</p>`;
    }
    html += `<cite class="insights-citation">${citation}</cite>
    </div>`;
    return html;
}

/**
 * Renders a tab introduction with title and description.
 * Provides context before the metrics, explaining what the tab shows
 * and why it matters in plain language.
 * @param {string} title - Intro heading
 * @param {string} description - Plain-language explanation
 * @returns {string} HTML string
 */
export function renderTabIntro(title, description) {
    return `<div class="insights-tab-intro">
        <div>
            <strong>${escapeHtml(title)}</strong>
            <p>${escapeHtml(description)}</p>
        </div>
    </div>`;
}

/**
 * Renders a list of key-value pairs.
 * @param {Array<[string, string]>} pairs - Key-value pairs
 * @returns {string} HTML string
 */
export function renderKeyValueList(pairs) {
    const rows = pairs.map(([key, value]) =>
        `<div class="insights-kv-row">
            <span class="insights-kv-key">${escapeHtml(key)}</span>
            <span class="insights-kv-value">${escapeHtml(String(value))}</span>
        </div>`
    ).join('');
    return `<div class="insights-kv-list">${rows}</div>`;
}
