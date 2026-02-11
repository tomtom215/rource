// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - View Manager
 *
 * Manages transitions between the analytics dashboard view and the
 * canvas visualization view. Uses CSS classes on .app-container to
 * control layout, and hidden attribute on sections for visibility.
 *
 * View states:
 *   'analytics' — Full-width analytics dashboard (default landing)
 *   'viz'       — Canvas visualization with sidebar (original layout)
 */

import { setState, get, subscribe, addManagedEventListener, hasData } from '../state.js';
import { updateUrlState } from '../url-state.js';
import { stopAnimation, startAnimation } from '../animation.js';

// DOM references
let appContainer = null;
let analyticsPanel = null;
let vizPanel = null;
let sidebarWrapper = null;
let btnSwitchToViz = null;
let btnBackToAnalytics = null;
let timelineContainer = null;
let backDivider = null;

/**
 * Initializes the view manager.
 * Sets up DOM references and subscribes to view state changes.
 */
export function initViewManager() {
    appContainer = document.querySelector('.app-container');
    analyticsPanel = document.getElementById('analytics-dashboard');
    vizPanel = document.getElementById('viz-panel');
    sidebarWrapper = document.getElementById('sidebar-wrapper');
    btnSwitchToViz = document.getElementById('btn-switch-to-viz');
    btnBackToAnalytics = document.getElementById('btn-back-to-analytics');
    timelineContainer = document.querySelector('.timeline-container');
    backDivider = document.querySelector('.control-divider-dashboard');

    if (!appContainer) return;

    // Subscribe to view state changes
    subscribe('currentView', (view) => {
        applyViewState(view);
    });

    // Wire up buttons
    if (btnBackToAnalytics) {
        addManagedEventListener(btnBackToAnalytics, 'click', () => {
            switchToAnalytics();
        });
    }

    // Apply initial state
    applyViewState(get('currentView'));
}

/**
 * Switches to the analytics dashboard view.
 */
export function switchToAnalytics() {
    setState({ currentView: 'analytics' });
    updateUrlState({ view: 'analytics' });
}

/**
 * Switches to the canvas visualization view.
 */
export function switchToVisualization() {
    setState({ currentView: 'viz' });
    updateUrlState({ view: 'viz' });
}

/**
 * Returns the current view state.
 * @returns {'analytics'|'viz'}
 */
export function getCurrentView() {
    return get('currentView');
}

/**
 * Applies the view state to the DOM.
 * @param {'analytics'|'viz'} view
 */
function applyViewState(view) {
    if (!appContainer) return;

    // Elements outside .app-container that belong to the viz view
    const bottomSheet = document.getElementById('bottom-sheet');
    const bottomSheetBackdrop = document.getElementById('bottom-sheet-backdrop');
    const bottomSheetFab = document.querySelector('.bottom-sheet-fab');
    const sidebarToggle = document.getElementById('sidebar-toggle');

    if (view === 'viz') {
        // Resume animation loop when returning to visualization
        if (hasData()) {
            startAnimation();
        }

        // Show visualization, hide analytics dashboard
        appContainer.classList.remove('view-analytics');
        appContainer.classList.add('view-viz');

        if (analyticsPanel) analyticsPanel.hidden = true;
        if (vizPanel) vizPanel.hidden = false;
        if (sidebarWrapper) sidebarWrapper.hidden = false;
        if (timelineContainer) timelineContainer.hidden = false;
        if (btnBackToAnalytics) btnBackToAnalytics.hidden = false;
        if (backDivider) backDivider.hidden = false;

        // Restore bottom sheet elements for viz view
        if (bottomSheet) bottomSheet.hidden = false;
        if (bottomSheetBackdrop) bottomSheetBackdrop.hidden = false;
        if (bottomSheetFab) bottomSheetFab.hidden = false;
        // Sidebar toggle is outside .app-container; restore for viz
        if (sidebarToggle) sidebarToggle.hidden = false;
    } else {
        // Stop animation loop — no need to render when canvas is hidden
        stopAnimation();

        // Show analytics dashboard, hide visualization
        appContainer.classList.remove('view-viz');
        appContainer.classList.add('view-analytics');

        if (analyticsPanel) analyticsPanel.hidden = false;
        if (vizPanel) vizPanel.hidden = true;
        if (sidebarWrapper) sidebarWrapper.hidden = true;
        if (timelineContainer) timelineContainer.hidden = true;
        if (btnBackToAnalytics) btnBackToAnalytics.hidden = true;
        if (backDivider) backDivider.hidden = true;

        // Hide viz-only elements outside .app-container
        const fsPrompt = document.getElementById('fullscreen-prompt');
        if (fsPrompt) fsPrompt.classList.remove('visible');
        if (bottomSheet) bottomSheet.hidden = true;
        if (bottomSheetBackdrop) bottomSheetBackdrop.hidden = true;
        if (bottomSheetFab) bottomSheetFab.hidden = true;
        // Sidebar toggle is outside .app-container; hide in analytics
        if (sidebarToggle) sidebarToggle.hidden = true;
    }
}
