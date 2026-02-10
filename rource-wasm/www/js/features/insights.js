// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Repository Insights Dashboard
 *
 * Mobile-first tabbed dashboard displaying 20 research-backed repository
 * health metrics. Data is lazy-loaded on first panel open and cached
 * per repository load.
 *
 * JSON field names verified against Rust format!() / write!() calls in:
 *   rource-wasm/src/wasm_api/insights.rs (1382 lines)
 *
 * Standalone endpoints wrap data in an outer key:
 *   getCodebaseGrowth()  → { growth: { currentFileCount, ... } }
 *   getWorkTypeMix()     → { workType: { featurePct, ... } }
 *   getCommitCadence()   → { cadence: { authors: [...], ... } }
 *   etc.
 * Array endpoints return flat arrays:
 *   getHotspots()        → [ { path, score, ... } ]
 *   getBusFactors()      → [ { directory, busFactor, ... } ]
 *   getChangeCoupling()  → [ { fileA, fileB, support, ... } ]
 * Object endpoints return flat objects:
 *   getTemporalPatterns()→ { activityHeatmap, peakHour, ... }
 *   getInsightsSummary() → { summary, topHotspots, riskDirectories, ... }
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
 * Loads only the summary for bottom sheet display.
 * Called automatically when data is loaded, without requiring panel open.
 */
export function loadInsightsSummary() {
    if (!cachedData.summary) {
        cachedData.summary = getInsightsSummary();
    }
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

/**
 * Unwraps standalone endpoint data.
 * Standalone endpoints wrap data in an outer key, e.g.:
 *   getCodebaseGrowth() → { growth: { currentFileCount, ... } }
 * This extracts the inner object.
 *
 * @param {Object|null} raw - Raw WASM response
 * @param {string} key - The outer key to unwrap
 * @returns {Object|null} Unwrapped inner object, or null
 */
function unwrap(raw, key) {
    if (!raw) return null;
    return raw[key] || null;
}

function ensureTabData(tabName) {
    switch (tabName) {
        case 'hotspots':
            // getHotspots returns flat array — no unwrap needed
            if (!cachedData.hotspots) cachedData.hotspots = getHotspots(50);
            // getChangeEntropy → { changeEntropy: { windows, avgNormalizedEntropy, ... } }
            if (!cachedData.entropy) cachedData.entropy = unwrap(getChangeEntropy(), 'changeEntropy');
            // getChangeBursts → { changeBursts: { files, totalBursts, ... } }
            if (!cachedData.bursts) cachedData.bursts = unwrap(getChangeBursts(), 'changeBursts');
            break;
        case 'risk':
            // getBusFactors returns flat array — no unwrap needed
            if (!cachedData.busFactors) cachedData.busFactors = getBusFactors();
            // getKnowledgeMap → { knowledge: { files, directories, totalSilos, ... } }
            if (!cachedData.knowledge) cachedData.knowledge = unwrap(getKnowledgeMap(), 'knowledge');
            // getCircadianRisk → { circadian: { files, authors, hourlyRisk, highRiskPct, ... } }
            if (!cachedData.circadian) cachedData.circadian = unwrap(getCircadianRisk(), 'circadian');
            break;
        case 'team':
            // getDeveloperProfiles → { profiles: { developers, coreCount, ... } }
            if (!cachedData.profiles) cachedData.profiles = unwrap(getDeveloperProfiles(), 'profiles');
            // getCommitCadence → { cadence: { authors, teamMeanInterval, ... } }
            if (!cachedData.cadence) cachedData.cadence = unwrap(getCommitCadence(), 'cadence');
            // getDeveloperNetwork → { network: { developers, networkDensity, ... } }
            if (!cachedData.network) cachedData.network = unwrap(getDeveloperNetwork(), 'network');
            // getContributionInequality → { inequality: { giniCoefficient, ... } }
            if (!cachedData.inequality) cachedData.inequality = unwrap(getContributionInequality(), 'inequality');
            // getDeveloperFocus → { focus: { developers, files, avgDeveloperFocus, ... } }
            if (!cachedData.focus) cachedData.focus = unwrap(getDeveloperFocus(), 'focus');
            break;
        case 'temporal':
            // getTemporalPatterns returns flat object — no unwrap needed
            if (!cachedData.temporal) cachedData.temporal = getTemporalPatterns();
            // getCodebaseGrowth → { growth: { currentFileCount, totalCreated, ... } }
            if (!cachedData.growth) cachedData.growth = unwrap(getCodebaseGrowth(), 'growth');
            // getFileLifecycles → { lifecycle: { files, activeCount, ... } }
            if (!cachedData.lifecycle) cachedData.lifecycle = unwrap(getFileLifecycles(), 'lifecycle');
            // getFileSurvival → { survival: { curve, medianSurvivalDays, ... } }
            if (!cachedData.survival) cachedData.survival = unwrap(getFileSurvival(), 'survival');
            break;
        case 'quality':
            // getWorkTypeMix → { workType: { featurePct, maintenancePct, ... } }
            if (!cachedData.workType) cachedData.workType = unwrap(getWorkTypeMix(), 'workType');
            // getModularity → { modularity: { directories, modularityIndex, ... } }
            if (!cachedData.modularity) cachedData.modularity = unwrap(getModularity(), 'modularity');
            // getCongruence → { congruence: { coordinationGaps, congruenceScore, ... } }
            if (!cachedData.congruence) cachedData.congruence = unwrap(getCongruence(), 'congruence');
            // getChangeCoupling returns flat array — no unwrap needed
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
 *
 * getInsightsSummary() returns (insights.rs:934-996):
 * {
 *   summary: { totalCommits, totalFiles, totalAuthors, timeSpanSeconds, ... },
 *   topHotspots: [ { path, score, totalChanges } ],
 *   riskDirectories: [ { directory, busFactor, fileCount } ],
 *   topCouplings: [ { fileA, fileB, support } ]
 * }
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

    // Field names verified: insights.rs:76 (totalAuthors, totalCommits)
    const s = summary.summary || {};
    // Field names verified: insights.rs:947-960 (topHotspots array)
    const hotspots = summary.topHotspots || [];
    // Field names verified: insights.rs:963-976 (riskDirectories array)
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

/**
 * Hotspots tab: file hotspots, change entropy, change bursts.
 *
 * Data sources (all verified against insights.rs):
 * - cachedData.hotspots: flat array from getHotspots()
 *   Fields: path, totalChanges, weightedChanges, score, creates, modifies, deletes
 *   (insights.rs:786-796)
 * - cachedData.entropy: unwrapped from getChangeEntropy().changeEntropy
 *   Fields: windows[], avgNormalizedEntropy, maxEntropyWindowIdx, trend
 *   (insights.rs:486-509)
 * - cachedData.bursts: unwrapped from getChangeBursts().changeBursts
 *   Fields: files[], totalBursts, avgBurstLength, filesWithBursts, multiAuthorBurstCount
 *   (insights.rs:562-582)
 */
function renderHotspotsTab() {
    const parts = [];

    // Hotspots table — fields verified: insights.rs:786-796
    const hotspots = cachedData.hotspots;
    parts.push(renderMetricSection(
        'File Hotspots',
        'Files with disproportionately high change frequency, weighted by recency.',
        'Nagappan et al. 2005, ICSE',
        hotspots && hotspots.length > 0
            ? renderHotspotsTable(hotspots)
            : emptyState('No hotspot files detected', 'Hotspots require files with multiple modifications over time.')
    ));

    // Change entropy — fields verified: insights.rs:486-509
    const e = cachedData.entropy;
    if (e) {
        parts.push(renderMetricSection(
            'Change Entropy',
            'Shannon entropy of file modification distribution within time windows.',
            'Hassan 2009, ICSE',
            renderKeyValueList([
                ['Average Entropy', formatNumber(e.avgNormalizedEntropy, 3)],
                ['Trend', escapeHtml(e.trend || 'stable')],
                ['Windows Analyzed', formatInt(e.windows ? e.windows.length : 0)],
            ])
        ));
    }

    // Change bursts — fields verified: insights.rs:562-582
    const b = cachedData.bursts;
    if (b) {
        const files = b.files || [];
        parts.push(renderMetricSection(
            'Change Bursts',
            'Rapid consecutive changes to individual files predict defects.',
            'Nagappan et al. 2010, ICSE',
            files.length > 0
                ? renderBurstsTable(files)
                : emptyState('No change bursts detected', 'Bursts require rapid consecutive changes to the same file.')
        ));
    }

    return parts.join('');
}

/**
 * Risk tab: bus factor, knowledge silos, circadian risk.
 *
 * Data sources:
 * - cachedData.busFactors: flat array from getBusFactors()
 *   Fields: directory, busFactor, fileCount, contributorCount, criticalContributors
 *   (insights.rs:858-876)
 * - cachedData.knowledge: unwrapped from getKnowledgeMap().knowledge
 *   Fields: files[], directories[], totalSilos, siloPct, avgEntropy
 *   File fields: path, entropy, isSilo, primaryOwner, contributorCount
 *   (insights.rs:336-372)
 * - cachedData.circadian: unwrapped from getCircadianRisk().circadian
 *   Fields: files[], authors[], hourlyRisk[], highRiskPct, totalCommitsAnalyzed
 *   (insights.rs:513-556)
 */
function renderRiskTab() {
    const parts = [];

    // Bus factors — fields verified: insights.rs:858-876
    const bus = cachedData.busFactors;
    parts.push(renderMetricSection(
        'Bus Factor',
        'Minimum contributors who must leave before a directory becomes unmaintained.',
        'Bird et al. 2011, FSE',
        bus && bus.length > 0
            ? renderBusFactorTable(bus)
            : emptyState('No bus factor data', 'Requires 2+ contributors to compute bus factor.')
    ));

    // Knowledge silos — fields verified: insights.rs:336-372
    const k = cachedData.knowledge;
    if (k) {
        // Filter files where isSilo is true (insights.rs:348: "isSilo":true/false)
        const silos = (k.files || []).filter(f => f.isSilo);
        parts.push(renderMetricSection(
            'Knowledge Silos',
            'Files with concentrated ownership (low Shannon entropy).',
            'Rigby &amp; Bird 2013',
            silos.length > 0
                ? renderKnowledgeTable(silos)
                : emptyState('No knowledge silos detected', 'All files have distributed ownership.')
        ));
    }

    // Circadian risk — fields verified: insights.rs:513-556
    const c = cachedData.circadian;
    if (c) {
        // Derive peak risk hour from hourlyRisk array (insights.rs:545-551)
        let peakRiskHour = 0;
        if (c.hourlyRisk && c.hourlyRisk.length > 0) {
            let maxRisk = -1;
            c.hourlyRisk.forEach((r, i) => {
                if (r > maxRisk) { maxRisk = r; peakRiskHour = i; }
            });
        }
        parts.push(renderMetricSection(
            'Circadian Risk',
            'Commits between midnight-4 AM are significantly buggier.',
            'Eyolfson et al. 2011, MSR',
            renderKeyValueList([
                // highRiskPct: insights.rs:554 — already a percentage value (e.g. 25.0)
                ['High-Risk Commits', formatFixed(c.highRiskPct, 1) + '%'],
                ['Peak Risk Hour', `${peakRiskHour}:00 UTC`],
                // totalCommitsAnalyzed: insights.rs:554
                ['Total Analyzed', formatInt(c.totalCommitsAnalyzed || 0)],
            ])
        ));
    }

    return parts.join('');
}

/**
 * Team tab: developer profiles, cadence, network, inequality, focus.
 *
 * Data sources:
 * - cachedData.profiles: unwrapped from getDeveloperProfiles().profiles
 *   Fields: developers[], coreCount, peripheralCount, driveByCount, totalContributors
 *   Developer fields: author, commitCount, uniqueFiles, avgFilesPerCommit, classification, activeSpanDays
 *   (insights.rs:376-403)
 * - cachedData.cadence: unwrapped from getCommitCadence().cadence
 *   Fields: authors[], teamMeanInterval, regularCount, burstyCount, moderateCount
 *   Author fields: author, commitCount, meanInterval, medianInterval, cv, cadenceType, activeSpan
 *   (insights.rs:304-332)
 * - cachedData.network: unwrapped from getDeveloperNetwork().network
 *   Fields: developers[], networkDensity, connectedComponents, largestComponentSize, totalEdges, avgDegree
 *   (insights.rs:698-723)
 * - cachedData.inequality: unwrapped from getContributionInequality().inequality
 *   Fields: giniCoefficient, top1PctShare, top10PctShare, top20PctShare, totalDevelopers, totalCommits, lorenzCurve, windows
 *   (insights.rs:446-475)
 * - cachedData.focus: unwrapped from getDeveloperFocus().focus
 *   Fields: developers[], files[], avgDeveloperFocus, avgFileDiffusion
 *   Developer fields: author, focusScore, directoriesTouched, commitCount
 *   (insights.rs:586-620)
 */
function renderTeamTab() {
    const parts = [];

    // Developer profiles — fields verified: insights.rs:376-403
    const p = cachedData.profiles;
    if (p) {
        // developers array: insights.rs:378
        const devs = p.developers || [];
        parts.push(renderMetricSection(
            'Developer Profiles',
            'Contributors classified as core, peripheral, or drive-by.',
            'Mockus et al. 2002',
            devs.length > 0
                ? renderProfilesTable(devs)
                : emptyState('No developer profile data', 'Requires commit history with author information.')
        ));
    }

    // Commit cadence — fields verified: insights.rs:304-332
    const ca = cachedData.cadence;
    if (ca) {
        // authors array: insights.rs:306 (NOT "developers")
        const devs = ca.authors || [];
        parts.push(renderMetricSection(
            'Commit Cadence',
            'Inter-commit interval patterns per developer.',
            'Eyolfson et al. 2014',
            devs.length > 0
                ? renderCadenceTable(devs)
                : emptyState('No cadence data', 'Requires 2+ commits per author to analyze intervals.')
        ));
    }

    // Collaboration network — fields verified: insights.rs:698-723
    const n = cachedData.network;
    if (n) {
        parts.push(renderMetricSection(
            'Collaboration Network',
            'Co-authorship network density and key developers.',
            'Begel et al. 2023',
            renderKeyValueList([
                // networkDensity: insights.rs:717
                ['Network Density', formatNumber(n.networkDensity, 3)],
                // connectedComponents: insights.rs:718
                ['Components', formatInt(n.connectedComponents || 0)],
                // avgDegree: insights.rs:720
                ['Avg Degree', formatNumber(n.avgDegree, 2)],
                // totalEdges: insights.rs:719
                ['Total Edges', formatInt(n.totalEdges || 0)],
            ])
        ));
    }

    // Contribution inequality — fields verified: insights.rs:446-475
    const g = cachedData.inequality;
    if (g) {
        parts.push(renderMetricSection(
            'Contribution Inequality',
            'How unevenly commits are distributed (Gini coefficient).',
            'Chelkowski et al. 2016',
            renderKeyValueList([
                // giniCoefficient: insights.rs:450
                ['Gini Coefficient', formatNumber(g.giniCoefficient, 3)],
                // top20PctShare: insights.rs:453 — fraction, not percentage
                ['Top 20% Share', formatPercentage(g.top20PctShare)],
                ['Interpretation', giniInterpretation(g.giniCoefficient)],
            ])
        ));
    }

    // Developer focus — fields verified: insights.rs:586-620
    const f = cachedData.focus;
    if (f) {
        // developers array: insights.rs:588
        const devs = f.developers || [];
        parts.push(renderMetricSection(
            'Developer Focus',
            'Focused developers introduce fewer defects.',
            'Posnett et al. 2013, ICSE',
            devs.length > 0
                ? renderFocusTable(devs)
                : emptyState('No focus data', 'Requires commits touching files in directories.')
        ));
    }

    return parts.join('');
}

/**
 * Temporal tab: activity patterns, codebase growth, file lifecycles, file survival.
 *
 * Data sources:
 * - cachedData.temporal: flat object from getTemporalPatterns()
 *   Fields: activityHeatmap, peakHour, peakDay, burstCount, avgFilesInBursts, avgFilesOutsideBursts
 *   (insights.rs:898-922)
 * - cachedData.growth: unwrapped from getCodebaseGrowth().growth
 *   Fields: currentFileCount, totalCreated, totalDeleted, netGrowth, avgMonthlyGrowth, trend, snapshotCount
 *   (insights.rs:266-285)
 * - cachedData.lifecycle: unwrapped from getFileLifecycles().lifecycle
 *   Fields: files[], avgLifespanDays, ephemeralCount, deadCount, deletedCount, activeCount, churnRate, totalFilesSeen
 *   (insights.rs:407-442)
 * - cachedData.survival: unwrapped from getFileSurvival().survival
 *   Fields: curve[], medianSurvivalDays, infantMortalityRate, totalBirths, totalDeaths, censoredCount
 *   (insights.rs:674-694)
 */
function renderTemporalTab() {
    const parts = [];

    // Temporal patterns — fields verified: insights.rs:898-922
    const t = cachedData.temporal;
    if (t) {
        const days = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
        parts.push(renderMetricSection(
            'Activity Patterns',
            '7-day x 24-hour activity heatmap with peak detection.',
            'Eyolfson et al. 2011, MSR',
            renderKeyValueList([
                // peakHour: insights.rs:914
                ['Peak Hour', `${t.peakHour != null ? t.peakHour : 0}:00 UTC`],
                // peakDay: insights.rs:914
                ['Peak Day', days[t.peakDay != null ? t.peakDay : 0] || 'N/A'],
                // burstCount: insights.rs:914 (temporal bursts.len())
                ['Burst Count', formatInt(t.burstCount || 0)],
                // avgFilesInBursts: insights.rs:914
                ['Avg Files in Bursts', formatNumber(t.avgFilesInBursts, 1)],
                // avgFilesOutsideBursts: insights.rs:914
                ['Avg Files Outside', formatNumber(t.avgFilesOutsideBursts, 1)],
            ])
        ));
    }

    // Codebase growth — fields verified: insights.rs:266-285
    const g = cachedData.growth;
    if (g) {
        parts.push(renderMetricSection(
            'Codebase Growth',
            'File count over time and growth trend classification.',
            'Lehman 1996',
            renderKeyValueList([
                // currentFileCount: insights.rs:276
                ['Current Files', formatInt(g.currentFileCount || 0)],
                // avgMonthlyGrowth: insights.rs:276 (files/month)
                ['Monthly Growth', formatNumber(g.avgMonthlyGrowth, 1) + ' files/month'],
                // trend: insights.rs:276 (accelerating|stable|decelerating|shrinking)
                ['Trend', escapeHtml(g.trend || 'unknown')],
                // netGrowth: insights.rs:276
                ['Net Growth', formatInt(g.netGrowth || 0) + ' files'],
                // snapshotCount: insights.rs:283
                ['Data Points', formatInt(g.snapshotCount || 0)],
            ])
        ));
    }

    // File lifecycles — fields verified: insights.rs:407-442
    const l = cachedData.lifecycle;
    if (l) {
        // Compute stable count: files not in other categories
        // activeCount + ephemeralCount + deadCount + deletedCount + stable = totalFilesSeen
        const stableCount = Math.max(0,
            (l.totalFilesSeen || 0) - (l.activeCount || 0) -
            (l.ephemeralCount || 0) - (l.deadCount || 0) - (l.deletedCount || 0)
        );
        parts.push(renderMetricSection(
            'File Lifecycles',
            'File stage distribution: active, stable, ephemeral, dead, deleted.',
            'Godfrey &amp; Tu 2000',
            renderKeyValueList([
                // activeCount: insights.rs:439
                ['Active', formatInt(l.activeCount || 0)],
                // Computed from totalFilesSeen minus explicit categories
                ['Stable', formatInt(stableCount)],
                // ephemeralCount: insights.rs:436
                ['Ephemeral', formatInt(l.ephemeralCount || 0)],
                // deadCount: insights.rs:437
                ['Dead', formatInt(l.deadCount || 0)],
                // deletedCount: insights.rs:438
                ['Deleted', formatInt(l.deletedCount || 0)],
                // churnRate: insights.rs:440
                ['Churn Rate', formatNumber(l.churnRate, 2)],
            ])
        ));
    }

    // File survival — fields verified: insights.rs:674-694
    const s = cachedData.survival;
    if (s) {
        parts.push(renderMetricSection(
            'File Survival',
            'Kaplan-Meier estimator: how long files survive before deletion.',
            'Cito et al. 2021, EMSE',
            renderKeyValueList([
                // medianSurvivalDays: insights.rs:691 (nullable)
                ['Median Survival', s.medianSurvivalDays != null ? formatNumber(s.medianSurvivalDays, 1) + ' days' : 'No deletions observed'],
                // totalBirths: insights.rs:692
                ['Files Created', formatInt(s.totalBirths || 0)],
                // totalDeaths: insights.rs:692
                ['Files Deleted', formatInt(s.totalDeaths || 0)],
                // infantMortalityRate: insights.rs:692
                ['Infant Mortality', formatPercentage(s.infantMortalityRate)],
            ])
        ));
    }

    return parts.join('');
}

/**
 * Quality tab: work type mix, modularity, congruence, change coupling.
 *
 * Data sources:
 * - cachedData.workType: unwrapped from getWorkTypeMix().workType
 *   Fields: featurePct, maintenancePct, cleanupPct, mixedPct, dominantType, totalCommits
 *   (insights.rs:288-300)
 * - cachedData.modularity: unwrapped from getModularity().modularity
 *   Fields: directories[], modularityIndex, crossModuleRatio, totalIntraEdges, totalCrossEdges
 *   (insights.rs:624-644)
 * - cachedData.congruence: unwrapped from getCongruence().congruence
 *   Fields: coordinationGaps[], congruenceScore, requiredCoordinations, actualCoordinations, totalDeveloperPairs
 *   (insights.rs:648-670)
 * - cachedData.coupling: flat array from getChangeCoupling()
 *   Fields: fileA, fileB, support, confidenceAB, confidenceBA
 *   (insights.rs:824-838)
 */
function renderQualityTab() {
    const parts = [];

    // Work type mix — fields verified: insights.rs:288-300
    const w = cachedData.workType;
    if (w) {
        parts.push(renderMetricSection(
            'Work Type Mix',
            'Feature vs. maintenance vs. cleanup ratio.',
            'Hindle et al. 2008',
            renderKeyValueList([
                // featurePct: insights.rs:298 (value like 45.2)
                ['Feature (Create)', formatFixed(w.featurePct, 1) + '%'],
                // maintenancePct: insights.rs:298
                ['Maintenance (Modify)', formatFixed(w.maintenancePct, 1) + '%'],
                // cleanupPct: insights.rs:298
                ['Cleanup (Delete)', formatFixed(w.cleanupPct, 1) + '%'],
                // mixedPct: insights.rs:298
                ['Mixed', formatFixed(w.mixedPct, 1) + '%'],
                // dominantType: insights.rs:298
                ['Dominant Type', escapeHtml(capitalize(w.dominantType || 'unknown'))],
            ])
        ));
    }

    // Modularity — fields verified: insights.rs:624-644
    const m = cachedData.modularity;
    if (m) {
        parts.push(renderMetricSection(
            'Modularity',
            'Whether co-changing files respect directory boundaries.',
            'MacCormack et al. 2006',
            renderKeyValueList([
                // modularityIndex: insights.rs:642
                ['Modularity Index', formatNumber(m.modularityIndex, 3)],
                // crossModuleRatio: insights.rs:642 — fraction, not percentage
                ['Cross-Module Ratio', formatPercentage(m.crossModuleRatio)],
                // directories array length: insights.rs:626
                ['Modules Analyzed', formatInt(m.directories ? m.directories.length : 0)],
            ])
        ));
    }

    // Congruence — fields verified: insights.rs:648-670
    const c = cachedData.congruence;
    if (c) {
        parts.push(renderMetricSection(
            'Sociotechnical Congruence',
            'Alignment between technical dependencies and actual coordination.',
            'Cataldo et al. 2009, ICSE',
            renderKeyValueList([
                // congruenceScore: insights.rs:665
                ['Congruence Score', formatNumber(c.congruenceScore, 3)],
                // coordinationGaps array length: insights.rs:650
                ['Coordination Gaps', formatInt(c.coordinationGaps ? c.coordinationGaps.length : 0)],
                // requiredCoordinations: insights.rs:666
                ['Required Coordinations', formatInt(c.requiredCoordinations || 0)],
                // actualCoordinations: insights.rs:667
                ['Actual Coordinations', formatInt(c.actualCoordinations || 0)],
            ])
        ));
    }

    // Change coupling — fields verified: insights.rs:824-838
    const coupling = cachedData.coupling;
    parts.push(renderMetricSection(
        'Change Coupling',
        'Hidden co-change dependencies that static analysis misses.',
        'D\'Ambros et al. 2009, EMSE',
        coupling && coupling.length > 0
            ? renderCouplingTable(coupling)
            : emptyState('No coupling pairs detected', 'Requires files that frequently change together in the same commit.')
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

/**
 * Renders the hotspots table.
 * Field names verified: insights.rs:786-796
 *   path, totalChanges, score (also: weightedChanges, creates, modifies, deletes)
 */
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

/**
 * Renders the bus factor table.
 * Field names verified: insights.rs:858-876
 *   directory, busFactor, fileCount (also: contributorCount, criticalContributors)
 */
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

/**
 * Renders the change bursts table.
 * Field names verified: insights.rs:567-575
 *   path, burstCount (also: maxBurstLength, totalBurstCommits, maxBurstAuthors, riskScore)
 */
function renderBurstsTable(files) {
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

/**
 * Renders the coupling table.
 * Field names verified: insights.rs:824-838
 *   fileA, fileB, support (also: confidenceAB, confidenceBA)
 */
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

/**
 * Renders the developer profiles table.
 * Field names verified: insights.rs:388-396
 *   author (NOT "name"), commitCount (NOT "commits"), classification, uniqueFiles, activeSpanDays
 */
function renderProfilesTable(devs) {
    // Sort by commitCount descending
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
        // author: insights.rs:390, classification: insights.rs:395, commitCount: insights.rs:391
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
        // author: insights.rs:319, cadenceType: insights.rs:324, meanInterval: insights.rs:320 (seconds)
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
function renderFocusTable(devs) {
    // Sort by focusScore descending (most focused first)
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
        // author: insights.rs:595, focusScore: insights.rs:596, directoriesTouched: insights.rs:597
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
 * Renders an empty state with contextual explanation.
 * @param {string} message - Primary message
 * @param {string} [hint] - Explanation of what data is needed
 */
function emptyState(message, hint) {
    let html = `<div class="insights-empty"><p>${escapeHtml(message)}</p>`;
    if (hint) {
        html += `<p class="insights-empty-hint">${escapeHtml(hint)}</p>`;
    }
    html += '</div>';
    return html;
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

function formatFixed(n, decimals = 1) {
    if (n == null || isNaN(n)) return 'N/A';
    return Number(n).toFixed(decimals);
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

function capitalize(str) {
    if (!str) return '';
    return str.charAt(0).toUpperCase() + str.slice(1);
}

function giniInterpretation(gini) {
    if (gini == null || isNaN(gini)) return 'N/A';
    if (gini < 0.3) return 'Low inequality (healthy)';
    if (gini < 0.5) return 'Moderate inequality';
    if (gini < 0.7) return 'High inequality';
    return 'Very high inequality (risk)';
}
