// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Insights Table Rendering Functions
 *
 * Each function renders a specific data table for the insights dashboard.
 * Field names are verified against the Rust source in:
 *   rource-wasm/src/wasm_api/insights.rs
 */

import {
    formatNumber, formatFixed, formatInt, formatPercentage,
    truncatePath, escapeHtml, capitalize
} from './insights-utils.js';

/**
 * Renders the hotspots table.
 * Field names verified: insights.rs:786-796
 *   path, totalChanges, score (also: weightedChanges, creates, modifies, deletes)
 */
export function renderHotspotsTable(hotspots) {
    const visible = hotspots.slice(0, 10);
    const hidden = hotspots.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">Score</th>
                <th scope="col" class="num">Changes</th>
            </tr></thead>
            <tbody>`;
    for (const h of visible) {
        html += `<tr>
            <td class="filepath" title="${escapeHtml(h.path)}">${escapeHtml(truncatePath(h.path))}</td>
            <td class="num">${formatNumber(h.score, 2)}</td>
            <td class="num">${formatInt(h.totalChanges)}</td>
        </tr>`;
    }
    for (const h of hidden) {
        html += `<tr class="insights-hidden-row">
            <td class="filepath" title="${escapeHtml(h.path)}">${escapeHtml(truncatePath(h.path))}</td>
            <td class="num">${formatNumber(h.score, 2)}</td>
            <td class="num">${formatInt(h.totalChanges)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${hotspots.length})</button>`;
    }
    return html;
}

/**
 * Renders the bus factor table.
 * Field names verified: insights.rs:858-876
 *   directory, busFactor, fileCount (also: contributorCount, criticalContributors)
 */
export function renderBusFactorTable(busFactors) {
    const sorted = [...busFactors].sort((a, b) => a.busFactor - b.busFactor);
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Directory</th>
                <th scope="col" class="num">Bus Factor</th>
                <th scope="col" class="num">Files</th>
            </tr></thead>
            <tbody>`;
    for (const b of visible) {
        const riskClass = b.busFactor <= 1 ? 'risk-high' : b.busFactor <= 2 ? 'risk-medium' : '';
        const riskLabel = b.busFactor <= 1 ? ' (Critical)' : b.busFactor <= 2 ? ' (At Risk)' : '';
        html += `<tr class="${riskClass}">
            <td class="filepath" title="${escapeHtml(b.directory)}">${escapeHtml(truncatePath(b.directory))}</td>
            <td class="num">${b.busFactor}${riskLabel}</td>
            <td class="num">${formatInt(b.fileCount)}</td>
        </tr>`;
    }
    for (const b of hidden) {
        html += `<tr class="insights-hidden-row">
            <td class="filepath">${escapeHtml(truncatePath(b.directory))}</td>
            <td class="num">${b.busFactor}</td>
            <td class="num">${formatInt(b.fileCount)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${busFactors.length})</button>`;
    }
    return html;
}

/**
 * Renders the change bursts table.
 * Field names verified: insights.rs:567-575
 *   path, burstCount (also: maxBurstLength, totalBurstCommits, maxBurstAuthors, riskScore)
 */
export function renderBurstsTable(files) {
    const sorted = [...files].sort((a, b) => (b.burstCount || 0) - (a.burstCount || 0));
    const visible = sorted.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">Bursts</th>
                <th scope="col" class="num">Risk</th>
            </tr></thead>
            <tbody>`;
    for (const f of visible) {
        html += `<tr>
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatInt(f.burstCount || 0)}</td>
            <td class="num">${formatNumber(f.riskScore, 2)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

/**
 * Renders the knowledge silo table.
 * Field names verified: insights.rs:343-351
 *   path, entropy (JSON key), isSilo, primaryOwner, contributorCount
 */
export function renderKnowledgeTable(silos) {
    const visible = silos.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">Entropy</th>
                <th scope="col">Owner</th>
            </tr></thead>
            <tbody>`;
    for (const s of visible) {
        html += `<tr>
            <td class="filepath" title="${escapeHtml(s.path || '')}">${escapeHtml(truncatePath(s.path || ''))}</td>
            <td class="num">${formatNumber(s.entropy, 3)}</td>
            <td>${escapeHtml(s.primaryOwner || 'N/A')}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

/**
 * Renders the coupling table.
 * Field names verified: insights.rs:824-838
 *   fileA, fileB, support (also: confidenceAB, confidenceBA)
 */
export function renderCouplingTable(couplings) {
    const visible = couplings.slice(0, 10);
    const hidden = couplings.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File A</th>
                <th scope="col">File B</th>
                <th scope="col" class="num">Co-changes</th>
            </tr></thead>
            <tbody>`;
    for (const c of visible) {
        html += `<tr>
            <td class="filepath" title="${escapeHtml(c.fileA)}">${escapeHtml(truncatePath(c.fileA))}</td>
            <td class="filepath" title="${escapeHtml(c.fileB)}">${escapeHtml(truncatePath(c.fileB))}</td>
            <td class="num">${formatInt(c.support)}</td>
        </tr>`;
    }
    for (const c of hidden) {
        html += `<tr class="insights-hidden-row">
            <td class="filepath">${escapeHtml(truncatePath(c.fileA))}</td>
            <td class="filepath">${escapeHtml(truncatePath(c.fileB))}</td>
            <td class="num">${formatInt(c.support)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${couplings.length})</button>`;
    }
    return html;
}

/**
 * Renders the developer profiles table.
 * Field names verified: insights.rs:388-396
 *   author (NOT "name"), commitCount (NOT "commits"), classification, uniqueFiles, activeSpanDays
 */
export function renderProfilesTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.commitCount || 0) - (a.commitCount || 0));
    const visible = sorted.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Developer</th>
                <th scope="col">Type</th>
                <th scope="col" class="num">Commits</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        html += `<tr>
            <td>${escapeHtml(d.author || '')}</td>
            <td><span class="insights-badge insights-badge-${(d.classification || 'unknown').toLowerCase()}">${escapeHtml(d.classification || 'Unknown')}</span></td>
            <td class="num">${formatInt(d.commitCount || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

/**
 * Renders the cadence table.
 * Field names verified: insights.rs:317-325
 *   author (NOT "name"), cadenceType (NOT "pattern"), meanInterval (seconds, NOT "avgIntervalDays"),
 *   commitCount, medianInterval, cv, activeSpan
 */
export function renderCadenceTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.commitCount || 0) - (a.commitCount || 0));
    const visible = sorted.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Developer</th>
                <th scope="col">Pattern</th>
                <th scope="col" class="num">Avg Interval</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        const intervalDays = d.meanInterval != null ? (d.meanInterval / 86400) : null;
        html += `<tr>
            <td>${escapeHtml(d.author || '')}</td>
            <td>${escapeHtml(capitalize(d.cadenceType || 'N/A'))}</td>
            <td class="num">${intervalDays != null ? formatNumber(intervalDays, 1) + ' days' : 'N/A'}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

/**
 * Renders the developer focus table.
 * Field names verified: insights.rs:593-599
 *   author (NOT "name"), focusScore (NOT "focus"), directoriesTouched (NOT "filesTouched"), commitCount
 */
export function renderFocusTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.focusScore || 0) - (a.focusScore || 0));
    const visible = sorted.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Developer</th>
                <th scope="col" class="num">Focus</th>
                <th scope="col" class="num">Dirs Touched</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        html += `<tr>
            <td>${escapeHtml(d.author || '')}</td>
            <td class="num">${formatNumber(d.focusScore, 3)}</td>
            <td class="num">${formatInt(d.directoriesTouched || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}
