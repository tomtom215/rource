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

/**
 * Renders the developer experience table.
 * Field names verified: insights.rs:1671-1679
 *   author, experienceScore, tenureDays, totalCommits, uniqueFiles
 */
export function renderExperienceTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.experienceScore || 0) - (a.experienceScore || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Developer</th>
                <th scope="col" class="num">Experience</th>
                <th scope="col" class="num">Tenure</th>
                <th scope="col" class="num">Commits</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        html += `<tr>
            <td>${escapeHtml(d.author || '')}</td>
            <td class="num">${formatNumber(d.experienceScore, 1)}</td>
            <td class="num">${formatNumber(d.tenureDays, 0)} days</td>
            <td class="num">${formatInt(d.totalCommits || 0)}</td>
        </tr>`;
    }
    for (const d of hidden) {
        html += `<tr class="insights-hidden-row">
            <td>${escapeHtml(d.author || '')}</td>
            <td class="num">${formatNumber(d.experienceScore, 1)}</td>
            <td class="num">${formatNumber(d.tenureDays, 0)} days</td>
            <td class="num">${formatInt(d.totalCommits || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${devs.length})</button>`;
    }
    return html;
}

/**
 * Renders the ownership fragmentation table.
 * Field names verified: insights.rs:1698-1705
 *   path, giniCoefficient, contributorCount, ownershipType
 */
export function renderOwnershipTable(files) {
    const sorted = [...files].sort((a, b) => (b.giniCoefficient || 0) - (a.giniCoefficient || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">Gini</th>
                <th scope="col">Ownership</th>
            </tr></thead>
            <tbody>`;
    for (const f of visible) {
        const typeClass = f.ownershipType === 'Fragmented' ? 'risk-medium' : '';
        html += `<tr class="${typeClass}">
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatNumber(f.giniCoefficient, 3)}</td>
            <td>${escapeHtml(f.ownershipType || 'N/A')}</td>
        </tr>`;
    }
    for (const f of hidden) {
        html += `<tr class="insights-hidden-row">
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatNumber(f.giniCoefficient, 3)}</td>
            <td>${escapeHtml(f.ownershipType || 'N/A')}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${files.length})</button>`;
    }
    return html;
}

/**
 * Renders the knowledge distribution table (per-directory entropy).
 * Field names verified: insights.rs:1737-1747
 *   directory, normalizedEntropy, contributorCount, dominantContributor, dominantContributorShare
 */
export function renderKnowledgeDistributionTable(dirs) {
    const sorted = [...dirs].sort((a, b) => (a.normalizedEntropy || 0) - (b.normalizedEntropy || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Directory</th>
                <th scope="col" class="num">Entropy</th>
                <th scope="col">Top Contributor</th>
                <th scope="col" class="num">Share</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        const riskClass = (d.normalizedEntropy || 0) < 0.3 ? 'risk-medium' : '';
        html += `<tr class="${riskClass}">
            <td class="filepath" title="${escapeHtml(d.directory || '')}">${escapeHtml(truncatePath(d.directory || ''))}</td>
            <td class="num">${formatNumber(d.normalizedEntropy, 3)}</td>
            <td>${escapeHtml(d.dominantContributor || 'N/A')}</td>
            <td class="num">${formatPercentage(d.dominantContributorShare)}</td>
        </tr>`;
    }
    for (const d of hidden) {
        html += `<tr class="insights-hidden-row">
            <td class="filepath" title="${escapeHtml(d.directory || '')}">${escapeHtml(truncatePath(d.directory || ''))}</td>
            <td class="num">${formatNumber(d.normalizedEntropy, 3)}</td>
            <td>${escapeHtml(d.dominantContributor || 'N/A')}</td>
            <td class="num">${formatPercentage(d.dominantContributorShare)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${dirs.length})</button>`;
    }
    return html;
}

/**
 * Renders the churn volatility table (per-file CV scores).
 * Field names verified: insights.rs write_churn_volatility_json
 *   path, cv, totalChurn, activeWindows, volatilityClass
 */
export function renderChurnVolatilityTable(files) {
    const sorted = [...files].sort((a, b) => (b.cv || 0) - (a.cv || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">CV</th>
                <th scope="col" class="num">Churn</th>
                <th scope="col">Class</th>
            </tr></thead>
            <tbody>`;
    for (const f of visible) {
        const riskClass = (f.cv || 0) >= 2.0 ? 'risk-high' : (f.cv || 0) >= 1.0 ? 'risk-medium' : '';
        html += `<tr class="${riskClass}">
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatNumber(f.cv, 2)}</td>
            <td class="num">${formatNumber(f.totalChurn, 1)}</td>
            <td>${escapeHtml(capitalize(f.volatilityClass || 'N/A'))}</td>
        </tr>`;
    }
    for (const f of hidden) {
        html += `<tr class="insights-hidden-row">
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatNumber(f.cv, 2)}</td>
            <td class="num">${formatNumber(f.totalChurn, 1)}</td>
            <td>${escapeHtml(capitalize(f.volatilityClass || 'N/A'))}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${files.length})</button>`;
    }
    return html;
}

/**
 * Renders the truck factor developer criticality table.
 * Field names verified: insights.rs write_truck_factor_json
 *   name, totalDoa, expertFileCount, soleExpertCount
 */
export function renderTruckFactorTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.totalDoa || 0) - (a.totalDoa || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Developer</th>
                <th scope="col" class="num">DOA</th>
                <th scope="col" class="num">Expert Files</th>
                <th scope="col" class="num">Sole Expert</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        const riskClass = (d.soleExpertCount || 0) > 5 ? 'risk-high' : (d.soleExpertCount || 0) > 0 ? 'risk-medium' : '';
        html += `<tr class="${riskClass}">
            <td>${escapeHtml(d.name || '')}</td>
            <td class="num">${formatNumber(d.totalDoa, 1)}</td>
            <td class="num">${formatInt(d.expertFileCount || 0)}</td>
            <td class="num">${formatInt(d.soleExpertCount || 0)}</td>
        </tr>`;
    }
    for (const d of hidden) {
        html += `<tr class="insights-hidden-row">
            <td>${escapeHtml(d.name || '')}</td>
            <td class="num">${formatNumber(d.totalDoa, 1)}</td>
            <td class="num">${formatInt(d.expertFileCount || 0)}</td>
            <td class="num">${formatInt(d.soleExpertCount || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${devs.length})</button>`;
    }
    return html;
}

/**
 * Renders the turnover impact departed developers table.
 * Field names verified: insights.rs write_turnover_impact_json
 *   name, daysSinceLast, ownedFiles, orphanedFiles, impactScore
 */
export function renderTurnoverImpactTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.impactScore || 0) - (a.impactScore || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Developer</th>
                <th scope="col" class="num">Days Gone</th>
                <th scope="col" class="num">Orphaned</th>
                <th scope="col" class="num">Impact</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        const riskClass = (d.impactScore || 0) > 0.5 ? 'risk-high' : (d.impactScore || 0) > 0.2 ? 'risk-medium' : '';
        html += `<tr class="${riskClass}">
            <td>${escapeHtml(d.name || '')}</td>
            <td class="num">${formatInt(d.daysSinceLast || 0)}</td>
            <td class="num">${formatInt(d.orphanedFiles || 0)} / ${formatInt(d.ownedFiles || 0)}</td>
            <td class="num">${formatPercentage(d.impactScore)}</td>
        </tr>`;
    }
    for (const d of hidden) {
        html += `<tr class="insights-hidden-row">
            <td>${escapeHtml(d.name || '')}</td>
            <td class="num">${formatInt(d.daysSinceLast || 0)}</td>
            <td class="num">${formatInt(d.orphanedFiles || 0)} / ${formatInt(d.ownedFiles || 0)}</td>
            <td class="num">${formatPercentage(d.impactScore)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${devs.length})</button>`;
    }
    return html;
}

/**
 * Renders the commit complexity table (top complex/tangled commits).
 * Field names verified: insights.rs write_commit_complexity_json
 *   author, fileCount, dirCount, complexityScore, isTangled
 */
export function renderCommitComplexityTable(commits) {
    const sorted = [...commits].sort((a, b) => (b.complexityScore || 0) - (a.complexityScore || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10, 50);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Author</th>
                <th scope="col" class="num">Files</th>
                <th scope="col" class="num">Dirs</th>
                <th scope="col" class="num">Score</th>
                <th scope="col">Tangled</th>
            </tr></thead>
            <tbody>`;
    for (const c of visible) {
        const riskClass = c.isTangled ? 'risk-high' : '';
        html += `<tr class="${riskClass}">
            <td>${escapeHtml(c.author || '')}</td>
            <td class="num">${formatInt(c.fileCount || 0)}</td>
            <td class="num">${formatInt(c.dirCount || 0)}</td>
            <td class="num">${formatNumber(c.complexityScore, 1)}</td>
            <td>${c.isTangled ? 'Yes' : 'No'}</td>
        </tr>`;
    }
    for (const c of hidden) {
        html += `<tr class="insights-hidden-row">
            <td>${escapeHtml(c.author || '')}</td>
            <td class="num">${formatInt(c.fileCount || 0)}</td>
            <td class="num">${formatInt(c.dirCount || 0)}</td>
            <td class="num">${formatNumber(c.complexityScore, 1)}</td>
            <td>${c.isTangled ? 'Yes' : 'No'}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${Math.min(commits.length, 50)})</button>`;
    }
    return html;
}

/**
 * Renders the defect-introducing change patterns table.
 * Field names verified: insights.rs write_defect_patterns_json
 *   path, burstAfterLarge, largeCommitAppearances, score, totalEdits
 */
export function renderDefectPatternsTable(files) {
    const sorted = [...files].sort((a, b) => (b.score || 0) - (a.score || 0));
    const visible = sorted.slice(0, 10);
    const hidden = sorted.slice(10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">Score</th>
                <th scope="col" class="num">Bursts</th>
                <th scope="col" class="num">Edits</th>
            </tr></thead>
            <tbody>`;
    for (const f of visible) {
        const riskClass = (f.score || 0) > 0.5 ? 'risk-high' : (f.score || 0) > 0.2 ? 'risk-medium' : '';
        html += `<tr class="${riskClass}">
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatNumber(f.score, 2)}</td>
            <td class="num">${formatInt(f.burstAfterLarge || 0)} / ${formatInt(f.largeCommitAppearances || 0)}</td>
            <td class="num">${formatInt(f.totalEdits || 0)}</td>
        </tr>`;
    }
    for (const f of hidden) {
        html += `<tr class="insights-hidden-row">
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatNumber(f.score, 2)}</td>
            <td class="num">${formatInt(f.burstAfterLarge || 0)} / ${formatInt(f.largeCommitAppearances || 0)}</td>
            <td class="num">${formatInt(f.totalEdits || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    if (hidden.length > 0) {
        html += `<button type="button" class="insights-show-all">Show all (${files.length})</button>`;
    }
    return html;
}
