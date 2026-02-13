// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Repository Insights Dashboard
 *
 * Mobile-first tabbed dashboard displaying 40 research-backed repository
 * health metrics across 6 tabs. Data is lazy-loaded on first panel open
 * and cached per repository load.
 *
 * Module structure:
 *   insights.js          - Core state, tab management, data loading, dashboard
 *   insights-renderers.js - Tab content renderers (hotspots, risk, team, temporal, quality, intelligence)
 *   insights-tables.js   - Table rendering functions (data tables for each metric)
 *   insights-utils.js    - Formatting helpers and shared UI components
 *
 * JSON field names verified against Rust format!() / write!() calls in:
 *   rource-wasm/src/wasm_api/insights.rs
 */

import { addManagedEventListener } from '../state.js';
import {
    getInsightsSummary, getHotspots, getChangeCoupling,
    getBusFactors, getTemporalPatterns, getCodebaseGrowth,
    getChangeEntropy, getCommitCadence, getDeveloperProfiles,
    getDeveloperFocus, getDeveloperNetwork, getKnowledgeMap,
    getModularity, getCongruence, getWorkTypeMix,
    getCircadianRisk, getChangeBursts, getContributionInequality,
    getFileLifecycles, getFileSurvival,
    getDeveloperExperience, getOwnershipFragmentation,
    getReleaseRhythm, getKnowledgeDistribution,
    getChurnVolatility, getTruckFactor, getTurnoverImpact,
    getCommitComplexity, getDefectPatterns,
    getTechDistribution, getActivityHeatmap, getTechExpertise,
    getContextualComplexity, getCommitCohesion, getChangePropagation,
    getCommitMessageEntropy, getKnowledgeHalfLife,
    getArchitecturalDrift, getSuccessionReadiness,
    getReviewerRecommendation, getReviewResponse, getOnboardingVelocity,
    getInterfaceStability, getTechDebtVelocity, getFocusDrift,
    getAiChangeDetection, getKnowledgeGini, getExpertiseProfile,
    getCognitiveLoad,
    getDoraProxy, getKnowledgeCurrency, getTeamRhythm,
    getCommitCoherence, getMarkovPrediction, getRepoHealth
} from '../wasm-api.js';
import { formatInt, escapeHtml } from './insights-utils.js';
import {
    renderHotspotsTab, renderRiskTab, renderTeamTab,
    renderTemporalTab, renderQualityTab, renderIntelligenceTab,
    renderStrategicTab
} from './insights-renderers.js';

// Module state
let loaded = false;
let cachedData = {};
let activeTab = 'hotspots';
let dashboardActiveTab = 'hotspots';

// DOM references -- sidebar
let panel = null;
let tabButtons = null;
let tabPanels = null;

// DOM references -- dashboard
let dashboardPanel = null;
let dashboardTabButtons = null;
let dashboardTabPanels = null;
let dashboardInitialized = false;

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
            tab.setAttribute('tabindex', i === 0 ? '0' : '-1');
        });
        panels.forEach((p, i) => {
            p.classList.toggle('active', i === 0);
            p.hidden = i !== 0;
        });
    }

    // Also reset the dashboard
    resetDashboard();
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
        btn.setAttribute('tabindex', selected ? '0' : '-1');
    });

    // Update tab panel visibility (CSS class + hidden attribute for accessibility)
    tabPanels.forEach(p => {
        const isActive = p.id === `ipanel-${tabName}`;
        p.classList.toggle('active', isActive);
        p.hidden = !isActive;
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
 *   getCodebaseGrowth() -> { growth: { currentFileCount, ... } }
 * This extracts the inner object.
 */
function unwrap(raw, key) {
    if (!raw) return null;
    return raw[key] || null;
}

function ensureTabData(tabName) {
    switch (tabName) {
        case 'hotspots':
            if (!cachedData.hotspots) cachedData.hotspots = getHotspots(50);
            if (!cachedData.entropy) cachedData.entropy = unwrap(getChangeEntropy(), 'changeEntropy');
            if (!cachedData.bursts) cachedData.bursts = unwrap(getChangeBursts(), 'changeBursts');
            if (!cachedData.techDistribution) cachedData.techDistribution = unwrap(getTechDistribution(), 'techDistribution');
            break;
        case 'risk':
            if (!cachedData.busFactors) cachedData.busFactors = getBusFactors();
            if (!cachedData.knowledge) cachedData.knowledge = unwrap(getKnowledgeMap(), 'knowledge');
            if (!cachedData.ownershipFrag) cachedData.ownershipFrag = unwrap(getOwnershipFragmentation(), 'ownershipFragmentation');
            if (!cachedData.knowledgeDist) cachedData.knowledgeDist = unwrap(getKnowledgeDistribution(), 'knowledgeDistribution');
            if (!cachedData.circadian) cachedData.circadian = unwrap(getCircadianRisk(), 'circadian');
            if (!cachedData.truckFactor) cachedData.truckFactor = unwrap(getTruckFactor(), 'truckFactor');
            if (!cachedData.turnoverImpact) cachedData.turnoverImpact = unwrap(getTurnoverImpact(), 'turnoverImpact');
            break;
        case 'team':
            if (!cachedData.profiles) cachedData.profiles = unwrap(getDeveloperProfiles(), 'profiles');
            if (!cachedData.cadence) cachedData.cadence = unwrap(getCommitCadence(), 'cadence');
            if (!cachedData.network) cachedData.network = unwrap(getDeveloperNetwork(), 'network');
            if (!cachedData.inequality) cachedData.inequality = unwrap(getContributionInequality(), 'inequality');
            if (!cachedData.focus) cachedData.focus = unwrap(getDeveloperFocus(), 'focus');
            if (!cachedData.experience) cachedData.experience = unwrap(getDeveloperExperience(), 'developerExperience');
            if (!cachedData.techExpertise) cachedData.techExpertise = unwrap(getTechExpertise(), 'techExpertise');
            break;
        case 'temporal':
            if (!cachedData.temporal) cachedData.temporal = getTemporalPatterns();
            if (!cachedData.growth) cachedData.growth = unwrap(getCodebaseGrowth(), 'growth');
            if (!cachedData.lifecycle) cachedData.lifecycle = unwrap(getFileLifecycles(), 'lifecycle');
            if (!cachedData.survival) cachedData.survival = unwrap(getFileSurvival(), 'survival');
            if (!cachedData.releaseRhythm) cachedData.releaseRhythm = unwrap(getReleaseRhythm(), 'releaseRhythm');
            if (!cachedData.activityHeatmap) cachedData.activityHeatmap = unwrap(getActivityHeatmap(), 'activityHeatmap');
            break;
        case 'quality':
            if (!cachedData.workType) cachedData.workType = unwrap(getWorkTypeMix(), 'workType');
            if (!cachedData.modularity) cachedData.modularity = unwrap(getModularity(), 'modularity');
            if (!cachedData.congruence) cachedData.congruence = unwrap(getCongruence(), 'congruence');
            if (!cachedData.coupling) cachedData.coupling = getChangeCoupling(20);
            if (!cachedData.churnVolatility) cachedData.churnVolatility = unwrap(getChurnVolatility(), 'churnVolatility');
            if (!cachedData.commitComplexity) cachedData.commitComplexity = unwrap(getCommitComplexity(), 'commitComplexity');
            if (!cachedData.defectPatterns) cachedData.defectPatterns = unwrap(getDefectPatterns(), 'defectPatterns');
            break;
        case 'intelligence':
            if (!cachedData.contextualComplexity) cachedData.contextualComplexity = unwrap(getContextualComplexity(), 'contextualComplexity');
            if (!cachedData.commitCohesion) cachedData.commitCohesion = unwrap(getCommitCohesion(), 'commitCohesion');
            if (!cachedData.changePropagation) cachedData.changePropagation = unwrap(getChangePropagation(), 'changePropagation');
            if (!cachedData.commitMessageEntropy) cachedData.commitMessageEntropy = unwrap(getCommitMessageEntropy(), 'commitMessageEntropy');
            if (!cachedData.knowledgeHalfLife) cachedData.knowledgeHalfLife = unwrap(getKnowledgeHalfLife(), 'knowledgeHalfLife');
            if (!cachedData.architecturalDrift) cachedData.architecturalDrift = unwrap(getArchitecturalDrift(), 'architecturalDrift');
            if (!cachedData.successionReadiness) cachedData.successionReadiness = unwrap(getSuccessionReadiness(), 'successionReadiness');
            if (!cachedData.reviewerRecommendation) cachedData.reviewerRecommendation = unwrap(getReviewerRecommendation(), 'reviewerRecommendation');
            if (!cachedData.reviewResponse) cachedData.reviewResponse = unwrap(getReviewResponse(), 'reviewResponse');
            if (!cachedData.onboardingVelocity) cachedData.onboardingVelocity = unwrap(getOnboardingVelocity(), 'onboardingVelocity');
            if (!cachedData.interfaceStability) cachedData.interfaceStability = unwrap(getInterfaceStability(), 'interfaceStability');
            if (!cachedData.techDebtVelocity) cachedData.techDebtVelocity = unwrap(getTechDebtVelocity(), 'techDebtVelocity');
            if (!cachedData.focusDrift) cachedData.focusDrift = unwrap(getFocusDrift(), 'focusDrift');
            if (!cachedData.aiChangeDetection) cachedData.aiChangeDetection = unwrap(getAiChangeDetection(), 'aiChangeDetection');
            if (!cachedData.knowledgeGini) cachedData.knowledgeGini = unwrap(getKnowledgeGini(), 'knowledgeGini');
            if (!cachedData.expertiseProfile) cachedData.expertiseProfile = unwrap(getExpertiseProfile(), 'expertiseProfile');
            if (!cachedData.cognitiveLoad) cachedData.cognitiveLoad = unwrap(getCognitiveLoad(), 'cognitiveLoad');
            break;
        case 'strategic':
            if (!cachedData.doraProxy) cachedData.doraProxy = unwrap(getDoraProxy(), 'doraProxy');
            if (!cachedData.knowledgeCurrencyData) cachedData.knowledgeCurrencyData = unwrap(getKnowledgeCurrency(), 'knowledgeCurrency');
            if (!cachedData.teamRhythmData) cachedData.teamRhythmData = unwrap(getTeamRhythm(), 'teamRhythm');
            if (!cachedData.commitCoherenceData) cachedData.commitCoherenceData = unwrap(getCommitCoherence(), 'commitCoherence');
            if (!cachedData.markovPrediction) cachedData.markovPrediction = unwrap(getMarkovPrediction(), 'markovPrediction');
            if (!cachedData.repoHealth) cachedData.repoHealth = unwrap(getRepoHealth(), 'repoHealth');
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
            const toggle = document.getElementById('insights-panel-toggle');
            if (toggle) {
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

/**
 * Renders a tab into a specific target context.
 * @param {string} tabName - Tab identifier (hotspots, risk, team, temporal, quality, intelligence)
 * @param {'sidebar'|'dashboard'} target - Which DOM context to render into
 */
function renderTabInto(tabName, target) {
    const prefix = target === 'dashboard' ? 'apanel' : 'ipanel';
    const bodyClass = target === 'dashboard' ? '.analytics-tab-body' : '.insights-tab-body';

    const tabPanel = document.getElementById(`${prefix}-${tabName}`);
    if (!tabPanel) return;

    const body = tabPanel.querySelector(bodyClass);
    if (!body) return;

    switch (tabName) {
        case 'hotspots':
            body.innerHTML = renderHotspotsTab(cachedData);
            break;
        case 'risk':
            body.innerHTML = renderRiskTab(cachedData);
            break;
        case 'team':
            body.innerHTML = renderTeamTab(cachedData);
            break;
        case 'temporal':
            body.innerHTML = renderTemporalTab(cachedData);
            break;
        case 'quality':
            body.innerHTML = renderQualityTab(cachedData);
            break;
        case 'intelligence':
            body.innerHTML = renderIntelligenceTab(cachedData);
            break;
        case 'strategic':
            body.innerHTML = renderStrategicTab(cachedData);
            break;
    }

    // Wire up "Show all" toggles
    body.querySelectorAll('.insights-show-all').forEach(btn => {
        addManagedEventListener(btn, 'click', () => {
            const toggleTarget = btn.closest('.insights-metric');
            if (toggleTarget) {
                toggleTarget.classList.toggle('expanded');
                btn.textContent = toggleTarget.classList.contains('expanded') ? 'Show less' : 'Show all';
            }
        });
    });

    // Wire up info tooltip toggles
    body.querySelectorAll('.insights-info-btn').forEach(btn => {
        addManagedEventListener(btn, 'click', () => {
            const infoPanel = btn.closest('.insights-metric-header').nextElementSibling;
            if (infoPanel && infoPanel.classList.contains('insights-info-panel')) {
                const isOpen = !infoPanel.hidden;
                infoPanel.hidden = isOpen;
                btn.setAttribute('aria-expanded', isOpen ? 'false' : 'true');
            }
        });
    });

    // Wire up metric quick-nav pill buttons
    body.querySelectorAll('.insights-metric-pill').forEach(pill => {
        addManagedEventListener(pill, 'click', () => {
            const targetId = pill.dataset.target;
            const targetEl = document.getElementById(targetId);
            if (targetEl) {
                targetEl.scrollIntoView({ behavior: 'smooth', block: 'start' });
                // Highlight active pill briefly
                const nav = pill.closest('.insights-metric-nav');
                if (nav) {
                    nav.querySelectorAll('.insights-metric-pill').forEach(p => p.classList.remove('active'));
                }
                pill.classList.add('active');
            }
        });
    });
}

function renderTab(tabName) {
    renderTabInto(tabName, 'sidebar');
}

// ============================================================
// Dashboard Rendering (Full-Width Analytics View)
// ============================================================

/**
 * Shows loading state in the analytics dashboard.
 */
export function showDashboardLoading() {
    const dp = document.getElementById('analytics-dashboard');
    if (!dp) return;

    const activePanel = dp.querySelector('.analytics-tab-panel.active .analytics-tab-body');
    if (activePanel && !activePanel.innerHTML.trim()) {
        activePanel.innerHTML = '<div class="analytics-loading"><div class="insights-spinner"></div><span>Analyzing repository...</span></div>';
    }
}

/**
 * Renders the full analytics dashboard.
 * Called from main.js when data is loaded and view is 'analytics'.
 * Uses the SAME rendering functions as the sidebar -- no duplication.
 */
export function renderDashboard() {
    // Ensure all data is loaded
    if (!loaded) {
        cachedData.summary = getInsightsSummary();
        cachedData.hotspots = getHotspots(50);
        loaded = true;
    }

    // Render summary cards
    renderDashboardSummaryCards();

    // Initialize dashboard tabs and card navigation if not yet done
    if (!dashboardInitialized) {
        setupDashboardTabs();
        setupCardNavigation();
        dashboardInitialized = true;
    }

    // Ensure default tab data and render
    ensureTabData(dashboardActiveTab);
    renderTabInto(dashboardActiveTab, 'dashboard');

    // Also update sidebar if it was previously rendered
    if (panel) {
        renderTab(activeTab);
    }

    // Update bottom sheet summary
    updateBottomSheetSummary();

    // Enable the visualize button
    const vizBtn = document.getElementById('btn-switch-to-viz');
    if (vizBtn) vizBtn.disabled = false;
}

/**
 * Renders summary cards in the dashboard header.
 */
function renderDashboardSummaryCards() {
    const summary = cachedData.summary;
    if (!summary) return;

    const s = summary.summary || {};
    const hotspots = summary.topHotspots || [];
    const risks = summary.riskDirectories || [];

    setCardValue('acard-commits-value', formatInt(s.totalCommits));
    setCardValue('acard-files-value', formatInt(s.totalFiles));
    setCardValue('acard-authors-value', formatInt(s.totalAuthors));
    setCardValue('acard-hotspots-value', formatInt(hotspots.length));
    setCardValue('acard-risk-value', formatInt(risks.length));
}

function setCardValue(id, value) {
    const el = document.getElementById(id);
    if (el) el.textContent = value;
}

/**
 * Sets up dashboard tab handlers.
 */
function setupDashboardTabs() {
    dashboardPanel = document.getElementById('analytics-dashboard');
    if (!dashboardPanel) return;

    dashboardTabButtons = dashboardPanel.querySelectorAll('[role="tab"]');
    dashboardTabPanels = dashboardPanel.querySelectorAll('[role="tabpanel"]');

    dashboardTabButtons.forEach(btn => {
        addManagedEventListener(btn, 'click', () => {
            switchDashboardTab(btn.dataset.tab);
        });

        addManagedEventListener(btn, 'keydown', (e) => {
            const tabs = Array.from(dashboardTabButtons);
            const idx = tabs.indexOf(btn);

            if (e.key === 'ArrowRight') {
                e.preventDefault();
                const next = tabs[(idx + 1) % tabs.length];
                next.focus();
                switchDashboardTab(next.dataset.tab);
            } else if (e.key === 'ArrowLeft') {
                e.preventDefault();
                const prev = tabs[(idx - 1 + tabs.length) % tabs.length];
                prev.focus();
                switchDashboardTab(prev.dataset.tab);
            } else if (e.key === 'Home') {
                e.preventDefault();
                tabs[0].focus();
                switchDashboardTab(tabs[0].dataset.tab);
            } else if (e.key === 'End') {
                e.preventDefault();
                tabs[tabs.length - 1].focus();
                switchDashboardTab(tabs[tabs.length - 1].dataset.tab);
            }
        });
    });
}

/**
 * Sets up summary card -> tab navigation.
 * Clicking a summary card switches to the corresponding tab
 * and scrolls it into view for an intuitive drill-down experience.
 */
function setupCardNavigation() {
    const cards = document.querySelectorAll('.analytics-card-interactive[data-navigate-tab]');
    cards.forEach(card => {
        addManagedEventListener(card, 'click', () => {
            const targetTab = card.dataset.navigateTab;
            if (targetTab) {
                switchDashboardTab(targetTab);
                const tabsContainer = document.querySelector('.analytics-tabs-container');
                if (tabsContainer) {
                    tabsContainer.scrollIntoView({ behavior: 'smooth', block: 'start' });
                }
            }
        });
    });
}

function switchDashboardTab(tabName) {
    if (tabName === dashboardActiveTab && loaded) return;
    dashboardActiveTab = tabName;

    if (dashboardTabButtons) {
        dashboardTabButtons.forEach(btn => {
            const selected = btn.dataset.tab === tabName;
            btn.setAttribute('aria-selected', selected ? 'true' : 'false');
            btn.classList.toggle('active', selected);
            btn.setAttribute('tabindex', selected ? '0' : '-1');
        });
    }

    if (dashboardTabPanels) {
        dashboardTabPanels.forEach(p => {
            const isActive = p.id === `apanel-${tabName}`;
            p.classList.toggle('active', isActive);
            p.hidden = !isActive;
        });
    }

    if (loaded) {
        ensureTabData(tabName);
        renderTabInto(tabName, 'dashboard');
    }
}

/**
 * Resets dashboard state (call on repository change).
 */
export function resetDashboard() {
    dashboardActiveTab = 'hotspots';
    dashboardInitialized = false;

    if (dashboardPanel) {
        const panels = dashboardPanel.querySelectorAll('[role="tabpanel"]');
        panels.forEach(p => {
            const content = p.querySelector('.analytics-tab-body');
            if (content) content.innerHTML = '';
        });

        const tabs = dashboardPanel.querySelectorAll('[role="tab"]');
        tabs.forEach((tab, i) => {
            tab.setAttribute('aria-selected', i === 0 ? 'true' : 'false');
            tab.classList.toggle('active', i === 0);
            tab.setAttribute('tabindex', i === 0 ? '0' : '-1');
        });
        panels.forEach((p, i) => {
            p.classList.toggle('active', i === 0);
            p.hidden = i !== 0;
        });
    }

    // Reset summary card values
    ['acard-commits-value', 'acard-files-value', 'acard-authors-value',
     'acard-hotspots-value', 'acard-risk-value'].forEach(id => {
        setCardValue(id, '--');
    });
}
