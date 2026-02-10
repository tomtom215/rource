// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Repository Insights Dashboard
 *
 * Mobile-first tabbed dashboard displaying 20 research-backed repository
 * health metrics. Data is lazy-loaded on first panel open and cached
 * per repository load.
 *
 * Research citations:
 * - Hotspots: Nagappan et al. 2005 (ICSE)
 * - Coupling: D'Ambros et al. 2009 (EMSE)
 * - Ownership / Bus Factor: Bird et al. 2011 (FSE)
 * - Entropy: Hassan 2009 (ICSE)
 * - Bursts: Nagappan et al. 2010 (ICSE)
 * - Circadian: Eyolfson et al. 2011 (MSR)
 * - Focus: Posnett et al. 2013 (ICSE)
 * - Survival: Cito et al. 2021 (EMSE)
 * - Network: Begel et al. 2023
 * - Modularity: MacCormack et al. 2006
 * - Congruence: Cataldo et al. 2009 (ICSE)
 * - Inequality: Chelkowski et al. 2016
 * - Growth: Lehman 1996
 * - Profiles: Mockus et al. 2002
 * - Knowledge: Rigby & Bird 2013
 * - Cadence: Eyolfson et al. 2014
 */

import { addManagedEventListener } from '../state.js';
import {
    getInsightsSummary, getHotspots, getChangeCoupling,
    getBusFactors, getTemporalPatterns, getCodebaseGrowth,
    getChangeEntropy, getCommitCadence, getDeveloperProfiles,
    getDeveloperFocus, getDeveloperNetwork, getKnowledgeMap,
    getModularity, getCongruence, getWorkTypeMix,
    getCircadianRisk, getChangeBursts, getContributionInequality,
    getFileLifecycles, getFileSurvival
} from '../wasm-api.js';

// Module state
let loaded = false;
let cachedData = {};
let activeTab = 'hotspots';

// DOM references
let panel = null;
let tabButtons = null;
let tabPanels = null;

/**
 * Initializes the insights dashboard module.
 * Sets up tab switching, panel toggle, and keyboard navigation.
 */
export function initInsights() {
    panel = document.getElementById('insights-panel');
    if (!panel) return;

    tabButtons = panel.querySelectorAll('[role="tab"]');
    tabPanels = panel.querySelectorAll('[role="tabpanel"]');

    setupTabHandlers();
    setupPanelToggle();
    setupBottomSheetInsights();
}

/**
 * Loads insights data on first panel open (lazy loading).
 * Subsequent calls return cached data.
 */
export function loadInsightsData() {
    if (loaded) return;

    showLoading();

    // Fetch summary and hotspots (default tab) eagerly
    cachedData.summary = getInsightsSummary();
    cachedData.hotspots = getHotspots(50);

    loaded = true;

    renderTab(activeTab);
    updateBottomSheetSummary();
}

/**
 * Invalidates cached insights data (call on repository change).
 */
export function invalidateInsightsCache() {
    loaded = false;
    cachedData = {};
    activeTab = 'hotspots';

    if (panel) {
        // Reset all tab panels to empty
        const panels = panel.querySelectorAll('[role="tabpanel"]');
        panels.forEach(p => {
            const content = p.querySelector('.insights-tab-body');
            if (content) content.innerHTML = '';
        });

        // Reset tab selection
        const tabs = panel.querySelectorAll('[role="tab"]');
        tabs.forEach((tab, i) => {
            tab.setAttribute('aria-selected', i === 0 ? 'true' : 'false');
            tab.classList.toggle('active', i === 0);
        });
        panels.forEach((p, i) => {
            p.classList.toggle('active', i === 0);
        });
    }
}

/**
 * Returns whether insights data has been loaded.
 * @returns {boolean}
 */
export function isInsightsLoaded() {
    return loaded;
}

// ============================================================
// Tab Management
// ============================================================

function setupTabHandlers() {
    tabButtons.forEach(btn => {
        addManagedEventListener(btn, 'click', () => {
            switchTab(btn.dataset.tab);
        });

        // Keyboard navigation: Left/Right arrows between tabs
        addManagedEventListener(btn, 'keydown', (e) => {
            const tabs = Array.from(tabButtons);
            const idx = tabs.indexOf(btn);

            if (e.key === 'ArrowRight') {
                e.preventDefault();
                const next = tabs[(idx + 1) % tabs.length];
                next.focus();
                switchTab(next.dataset.tab);
            } else if (e.key === 'ArrowLeft') {
                e.preventDefault();
                const prev = tabs[(idx - 1 + tabs.length) % tabs.length];
                prev.focus();
                switchTab(prev.dataset.tab);
            } else if (e.key === 'Home') {
                e.preventDefault();
                tabs[0].focus();
                switchTab(tabs[0].dataset.tab);
            } else if (e.key === 'End') {
                e.preventDefault();
                tabs[tabs.length - 1].focus();
                switchTab(tabs[tabs.length - 1].dataset.tab);
            }
        });
    });
}

function switchTab(tabName) {
    if (tabName === activeTab && loaded) return;
    activeTab = tabName;

    // Update tab button states
    tabButtons.forEach(btn => {
        const selected = btn.dataset.tab === tabName;
        btn.setAttribute('aria-selected', selected ? 'true' : 'false');
        btn.classList.toggle('active', selected);
    });

    // Update tab panel visibility
    tabPanels.forEach(p => {
        p.classList.toggle('active', p.id === `ipanel-${tabName}`);
    });

    // Lazy-load tab data
    if (loaded) {
        ensureTabData(tabName);
        renderTab(tabName);
    }
}

function ensureTabData(tabName) {
    switch (tabName) {
        case 'hotspots':
            if (!cachedData.hotspots) cachedData.hotspots = getHotspots(50);
            if (!cachedData.entropy) cachedData.entropy = getChangeEntropy();
            if (!cachedData.bursts) cachedData.bursts = getChangeBursts();
            break;
        case 'risk':
            if (!cachedData.busFactors) cachedData.busFactors = getBusFactors();
            if (!cachedData.knowledge) cachedData.knowledge = getKnowledgeMap();
            if (!cachedData.circadian) cachedData.circadian = getCircadianRisk();
            break;
        case 'team':
            if (!cachedData.profiles) cachedData.profiles = getDeveloperProfiles();
            if (!cachedData.cadence) cachedData.cadence = getCommitCadence();
            if (!cachedData.network) cachedData.network = getDeveloperNetwork();
            if (!cachedData.inequality) cachedData.inequality = getContributionInequality();
            if (!cachedData.focus) cachedData.focus = getDeveloperFocus();
            break;
        case 'temporal':
            if (!cachedData.temporal) cachedData.temporal = getTemporalPatterns();
            if (!cachedData.growth) cachedData.growth = getCodebaseGrowth();
            if (!cachedData.lifecycle) cachedData.lifecycle = getFileLifecycles();
            if (!cachedData.survival) cachedData.survival = getFileSurvival();
            break;
        case 'quality':
            if (!cachedData.workType) cachedData.workType = getWorkTypeMix();
            if (!cachedData.modularity) cachedData.modularity = getModularity();
            if (!cachedData.congruence) cachedData.congruence = getCongruence();
            if (!cachedData.coupling) cachedData.coupling = getChangeCoupling(20);
            break;
    }
}

// ============================================================
// Panel Toggle
// ============================================================

function setupPanelToggle() {
    const toggle = document.getElementById('insights-panel-toggle');
    if (!toggle) return;

    addManagedEventListener(toggle, 'click', () => {
        const isExpanded = toggle.getAttribute('aria-expanded') === 'true';
        toggle.setAttribute('aria-expanded', isExpanded ? 'false' : 'true');
        panel.classList.toggle('collapsed', isExpanded);

        // Lazy-load on first expand
        if (!isExpanded && !loaded) {
            loadInsightsData();
        }
    });
}

// ============================================================
// Bottom Sheet Integration
// ============================================================

function setupBottomSheetInsights() {
    const expandBtn = document.getElementById('bs-insights-expand');
    if (expandBtn) {
        addManagedEventListener(expandBtn, 'click', () => {
            // Open sidebar insights panel if available
            const toggle = document.getElementById('insights-panel-toggle');
            if (toggle) {
                // Expand the panel
                toggle.setAttribute('aria-expanded', 'true');
                if (panel) panel.classList.remove('collapsed');
                if (!loaded) loadInsightsData();
            }
        });
    }
}

/**
 * Updates the bottom sheet insights summary section.
 * Called after insights data is loaded.
 */
export function updateBottomSheetSummary() {
    const section = document.getElementById('bs-insights-section');
    const container = document.getElementById('bs-insights-summary');
    if (!section || !container) return;

    const summary = cachedData.summary;
    if (!summary) {
        section.classList.add('hidden');
        return;
    }

    section.classList.remove('hidden');

    const s = summary.summary || {};
    const hotspots = summary.topHotspots || [];
    const risks = summary.riskDirectories || [];

    let html = '<div class="insights-summary-stats">';
    html += renderSummaryStat(formatInt(hotspots.length), 'Hotspots');
    html += renderSummaryStat(formatInt(risks.length), 'At Risk');
    if (s.totalAuthors != null) {
        html += renderSummaryStat(formatInt(s.totalAuthors), 'Authors');
    }
    if (s.totalCommits != null) {
        html += renderSummaryStat(formatInt(s.totalCommits), 'Commits');
    }
    html += '</div>';

    container.innerHTML = html;
}

function renderSummaryStat(value, label) {
    return `<div class="insights-summary-stat">
        <span class="stat-value">${escapeHtml(String(value))}</span>
        <span class="stat-label">${escapeHtml(label)}</span>
    </div>`;
}

// ============================================================
// Rendering
// ============================================================

function showLoading() {
    tabPanels.forEach(p => {
        const body = p.querySelector('.insights-tab-body');
        if (body) {
            body.innerHTML = '<div class="insights-loading"><div class="insights-spinner"></div><span>Analyzing repository...</span></div>';
        }
    });
}

function renderTab(tabName) {
    const tabPanel = document.getElementById(`ipanel-${tabName}`);
    if (!tabPanel) return;

    const body = tabPanel.querySelector('.insights-tab-body');
    if (!body) return;

    switch (tabName) {
        case 'hotspots':
            body.innerHTML = renderHotspotsTab();
            break;
        case 'risk':
            body.innerHTML = renderRiskTab();
            break;
        case 'team':
            body.innerHTML = renderTeamTab();
            break;
        case 'temporal':
            body.innerHTML = renderTemporalTab();
            break;
        case 'quality':
            body.innerHTML = renderQualityTab();
            break;
    }

    // Wire up "Show all" toggles
    body.querySelectorAll('.insights-show-all').forEach(btn => {
        btn.addEventListener('click', () => {
            const target = btn.closest('.insights-metric');
            if (target) {
                target.classList.toggle('expanded');
                btn.textContent = target.classList.contains('expanded') ? 'Show less' : 'Show all';
            }
        });
    });
}

// ============================================================
// Tab Renderers
// ============================================================

function renderHotspotsTab() {
    const parts = [];

    // Hotspots table
    const hotspots = cachedData.hotspots;
    parts.push(renderMetricSection(
        'File Hotspots',
        'Files with disproportionately high change frequency, weighted by recency.',
        'Nagappan et al. 2005, ICSE',
        hotspots && hotspots.length > 0
            ? renderHotspotsTable(hotspots)
            : emptyState('No hotspots detected')
    ));

    // Change entropy
    if (cachedData.entropy) {
        const e = cachedData.entropy;
        parts.push(renderMetricSection(
            'Change Entropy',
            'Shannon entropy of file modification distribution within time windows.',
            'Hassan 2009, ICSE',
            renderKeyValueList([
                ['Average Entropy', formatNumber(e.averageEntropy, 3)],
                ['Max Entropy', formatNumber(e.maxEntropy, 3)],
                ['Windows Analyzed', formatInt(e.windowCount || 0)],
            ])
        ));
    }

    // Change bursts
    if (cachedData.bursts) {
        const b = cachedData.bursts;
        const files = b.files || [];
        parts.push(renderMetricSection(
            'Change Bursts',
            'Rapid consecutive changes to individual files predict defects.',
            'Nagappan et al. 2010, ICSE',
            files.length > 0
                ? renderBurstsTable(files)
                : emptyState('No change bursts detected')
        ));
    }

    return parts.join('');
}

function renderRiskTab() {
    const parts = [];

    // Bus factors
    const bus = cachedData.busFactors;
    parts.push(renderMetricSection(
        'Bus Factor',
        'Minimum contributors who must leave before a directory becomes unmaintained.',
        'Bird et al. 2011, FSE',
        bus && bus.length > 0
            ? renderBusFactorTable(bus)
            : emptyState('No bus factor data')
    ));

    // Knowledge silos
    if (cachedData.knowledge) {
        const k = cachedData.knowledge;
        const silos = k.silos || [];
        parts.push(renderMetricSection(
            'Knowledge Silos',
            'Files with concentrated ownership (low Shannon entropy).',
            'Rigby &amp; Bird 2013',
            silos.length > 0
                ? renderKnowledgeTable(silos)
                : emptyState('No knowledge silos detected')
        ));
    }

    // Circadian risk
    if (cachedData.circadian) {
        const c = cachedData.circadian;
        parts.push(renderMetricSection(
            'Circadian Risk',
            'Commits between midnight-4 AM are significantly buggier.',
            'Eyolfson et al. 2011, MSR',
            renderKeyValueList([
                ['High-Risk Commits', formatPercentage(c.highRiskPct)],
                ['Peak Risk Hour', `${c.peakRiskHour || 0}:00 UTC`],
                ['Total Commits Analyzed', formatInt(c.totalCommits || 0)],
            ])
        ));
    }

    return parts.join('');
}

function renderTeamTab() {
    const parts = [];

    // Developer profiles
    if (cachedData.profiles) {
        const p = cachedData.profiles;
        const devs = p.developers || [];
        parts.push(renderMetricSection(
            'Developer Profiles',
            'Contributors classified as core, peripheral, or drive-by.',
            'Mockus et al. 2002',
            devs.length > 0
                ? renderProfilesTable(devs)
                : emptyState('No developer profile data')
        ));
    }

    // Commit cadence
    if (cachedData.cadence) {
        const c = cachedData.cadence;
        const devs = c.developers || [];
        parts.push(renderMetricSection(
            'Commit Cadence',
            'Inter-commit interval patterns per developer.',
            'Eyolfson et al. 2014',
            devs.length > 0
                ? renderCadenceTable(devs)
                : emptyState('No cadence data')
        ));
    }

    // Collaboration network
    if (cachedData.network) {
        const n = cachedData.network;
        parts.push(renderMetricSection(
            'Collaboration Network',
            'Co-authorship network density and key developers.',
            'Begel et al. 2023',
            renderKeyValueList([
                ['Network Density', formatNumber(n.density, 3)],
                ['Components', formatInt(n.components || 0)],
                ['Avg Clustering', formatNumber(n.avgClustering, 3)],
            ])
        ));
    }

    // Contribution inequality
    if (cachedData.inequality) {
        const g = cachedData.inequality;
        parts.push(renderMetricSection(
            'Contribution Inequality',
            'How unevenly commits are distributed (Gini coefficient).',
            'Chelkowski et al. 2016',
            renderKeyValueList([
                ['Gini Coefficient', formatNumber(g.gini, 3)],
                ['Top 20% Share', formatPercentage(g.top20Pct)],
                ['Interpretation', giniInterpretation(g.gini)],
            ])
        ));
    }

    // Developer focus
    if (cachedData.focus) {
        const f = cachedData.focus;
        const devs = f.developers || [];
        parts.push(renderMetricSection(
            'Developer Focus',
            'Focused developers introduce fewer defects.',
            'Posnett et al. 2013, ICSE',
            devs.length > 0
                ? renderFocusTable(devs)
                : emptyState('No focus data')
        ));
    }

    return parts.join('');
}

function renderTemporalTab() {
    const parts = [];

    // Temporal patterns
    if (cachedData.temporal) {
        const t = cachedData.temporal;
        const days = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
        parts.push(renderMetricSection(
            'Activity Patterns',
            '7-day x 24-hour activity heatmap with peak detection.',
            'Eyolfson et al. 2011, MSR',
            renderKeyValueList([
                ['Peak Hour', `${t.peakHour || 0}:00 UTC`],
                ['Peak Day', days[t.peakDay || 0] || 'N/A'],
                ['Burst Count', formatInt(t.burstCount || 0)],
                ['Avg Files in Bursts', formatNumber(t.avgFilesInBursts, 1)],
                ['Avg Files Outside', formatNumber(t.avgFilesOutsideBursts, 1)],
            ])
        ));
    }

    // Codebase growth
    if (cachedData.growth) {
        const g = cachedData.growth;
        parts.push(renderMetricSection(
            'Codebase Growth',
            'File count over time and growth trend classification.',
            'Lehman 1996',
            renderKeyValueList([
                ['Current Files', formatInt(g.currentFileCount || 0)],
                ['Growth Rate', formatNumber(g.growthRate, 2) + ' files/day'],
                ['Trend', escapeHtml(g.trend || 'unknown')],
                ['Data Points', formatInt(g.dataPoints || 0)],
            ])
        ));
    }

    // File lifecycles
    if (cachedData.lifecycle) {
        const l = cachedData.lifecycle;
        parts.push(renderMetricSection(
            'File Lifecycles',
            'File stage distribution: active, stable, ephemeral, dead, deleted.',
            'Godfrey &amp; Tu 2000',
            renderKeyValueList([
                ['Active', formatInt(l.active || 0)],
                ['Stable', formatInt(l.stable || 0)],
                ['Ephemeral', formatInt(l.ephemeral || 0)],
                ['Dead', formatInt(l.dead || 0)],
                ['Deleted', formatInt(l.deleted || 0)],
            ])
        ));
    }

    // File survival
    if (cachedData.survival) {
        const s = cachedData.survival;
        parts.push(renderMetricSection(
            'File Survival',
            'Kaplan-Meier estimator: how long files survive before deletion.',
            'Cito et al. 2021, EMSE',
            renderKeyValueList([
                ['Median Survival', s.medianSurvivalDays != null ? formatInt(s.medianSurvivalDays) + ' days' : 'N/A'],
                ['Files Observed', formatInt(s.totalFiles || 0)],
                ['Deletions', formatInt(s.events || 0)],
            ])
        ));
    }

    return parts.join('');
}

function renderQualityTab() {
    const parts = [];

    // Work type mix
    if (cachedData.workType) {
        const w = cachedData.workType;
        parts.push(renderMetricSection(
            'Work Type Mix',
            'Feature vs. maintenance vs. cleanup ratio.',
            'Hindle et al. 2008',
            renderKeyValueList([
                ['Feature (Create)', formatPercentage(w.createPct)],
                ['Maintenance (Modify)', formatPercentage(w.modifyPct)],
                ['Cleanup (Delete)', formatPercentage(w.deletePct)],
            ])
        ));
    }

    // Modularity
    if (cachedData.modularity) {
        const m = cachedData.modularity;
        parts.push(renderMetricSection(
            'Modularity',
            'Whether co-changing files respect directory boundaries.',
            'MacCormack et al. 2006',
            renderKeyValueList([
                ['Modularity Index', formatNumber(m.modularityIndex, 3)],
                ['Cross-Module Ratio', formatPercentage(m.crossModuleRatio)],
                ['Modules Analyzed', formatInt(m.moduleCount || 0)],
            ])
        ));
    }

    // Congruence
    if (cachedData.congruence) {
        const c = cachedData.congruence;
        parts.push(renderMetricSection(
            'Sociotechnical Congruence',
            'Alignment between technical dependencies and actual coordination.',
            'Cataldo et al. 2009, ICSE',
            renderKeyValueList([
                ['Congruence Score', formatNumber(c.congruenceScore, 3)],
                ['Coordination Gaps', formatInt(c.gaps || 0)],
            ])
        ));
    }

    // Change coupling
    const coupling = cachedData.coupling;
    parts.push(renderMetricSection(
        'Change Coupling',
        'Hidden co-change dependencies that static analysis misses.',
        'D\'Ambros et al. 2009, EMSE',
        coupling && coupling.length > 0
            ? renderCouplingTable(coupling)
            : emptyState('No coupling pairs detected')
    ));

    return parts.join('');
}

// ============================================================
// Rendering Helpers
// ============================================================

function renderMetricSection(title, description, citation, content) {
    return `<div class="insights-metric">
        <h4 class="insights-metric-title">${escapeHtml(title)}</h4>
        <p class="insights-metric-desc">${description}</p>
        ${content}
        <cite class="insights-citation">${citation}</cite>
    </div>`;
}

function renderKeyValueList(pairs) {
    const rows = pairs.map(([key, value]) =>
        `<div class="insights-kv-row">
            <span class="insights-kv-key">${escapeHtml(key)}</span>
            <span class="insights-kv-value">${escapeHtml(String(value))}</span>
        </div>`
    ).join('');
    return `<div class="insights-kv-list">${rows}</div>`;
}

function renderHotspotsTable(hotspots) {
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

function renderBusFactorTable(busFactors) {
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

function renderBurstsTable(files) {
    const sorted = [...files].sort((a, b) => (b.burstCount || 0) - (a.burstCount || 0));
    const visible = sorted.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">Bursts</th>
            </tr></thead>
            <tbody>`;
    for (const f of visible) {
        html += `<tr>
            <td class="filepath" title="${escapeHtml(f.path || '')}">${escapeHtml(truncatePath(f.path || ''))}</td>
            <td class="num">${formatInt(f.burstCount || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderKnowledgeTable(silos) {
    const visible = silos.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">File</th>
                <th scope="col" class="num">Entropy</th>
                <th scope="col">Primary Owner</th>
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

function renderCouplingTable(couplings) {
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

function renderProfilesTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.commits || 0) - (a.commits || 0));
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
            <td>${escapeHtml(d.name || '')}</td>
            <td><span class="insights-badge insights-badge-${(d.classification || 'unknown').toLowerCase()}">${escapeHtml(d.classification || 'Unknown')}</span></td>
            <td class="num">${formatInt(d.commits || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderCadenceTable(devs) {
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
        html += `<tr>
            <td>${escapeHtml(d.name || '')}</td>
            <td>${escapeHtml(d.pattern || 'N/A')}</td>
            <td class="num">${d.avgIntervalDays != null ? formatNumber(d.avgIntervalDays, 1) + ' days' : 'N/A'}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderFocusTable(devs) {
    const sorted = [...devs].sort((a, b) => (b.focus || 0) - (a.focus || 0));
    const visible = sorted.slice(0, 10);
    let html = `<div class="insights-table-wrap">
        <table class="insights-table">
            <thead><tr>
                <th scope="col">Developer</th>
                <th scope="col" class="num">Focus</th>
                <th scope="col" class="num">Files Touched</th>
            </tr></thead>
            <tbody>`;
    for (const d of visible) {
        html += `<tr>
            <td>${escapeHtml(d.name || '')}</td>
            <td class="num">${formatNumber(d.focus, 3)}</td>
            <td class="num">${formatInt(d.filesTouched || 0)}</td>
        </tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function emptyState(message) {
    return `<div class="insights-empty">${escapeHtml(message)}</div>`;
}

// ============================================================
// Formatting Utilities
// ============================================================

function formatNumber(n, decimals = 2) {
    if (n == null || isNaN(n)) return 'N/A';
    return Number(n).toLocaleString(undefined, {
        minimumFractionDigits: decimals,
        maximumFractionDigits: decimals,
    });
}

function formatInt(n) {
    if (n == null || isNaN(n)) return '0';
    return Number(n).toLocaleString();
}

function formatPercentage(n) {
    if (n == null || isNaN(n)) return 'N/A';
    return (Number(n) * 100).toFixed(1) + '%';
}

function truncatePath(path) {
    if (!path) return '';
    if (path.length <= 40) return path;
    const parts = path.split('/');
    if (parts.length <= 2) return path;
    return parts[0] + '/.../' + parts[parts.length - 1];
}

function escapeHtml(str) {
    if (!str) return '';
    return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function giniInterpretation(gini) {
    if (gini == null || isNaN(gini)) return 'N/A';
    if (gini < 0.3) return 'Low inequality (healthy)';
    if (gini < 0.5) return 'Moderate inequality';
    if (gini < 0.7) return 'High inequality';
    return 'Very high inequality (risk)';
}
