// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Component Injection
 *
 * Injects HTML templates from modular JS files into placeholder elements
 * in index.html. This reduces the monolithic HTML file size and improves
 * maintainability by keeping component HTML in dedicated JS modules.
 *
 * Called once during app initialization, before any feature modules
 * that depend on these DOM elements.
 */

import {
    getShowcasePanelTemplate,
    getGithubPanelTemplate,
    getManualLoadPanelTemplate,
    getKeyboardShortcutsPanelTemplate,
} from './sidebar-template.js';

import { getBottomSheetContentTemplate } from './bottom-sheet-template.js';
import { getHelpTemplate } from './help-template.js';

/**
 * Injects component HTML into placeholder elements.
 * Must be called before initDomElements() and feature modules.
 *
 * All injected sections are hidden/collapsed by default (no FOUC risk):
 *   - Sidebar panels (sidebar hidden in analytics view)
 *   - Bottom sheet content (hidden by default)
 *   - Help overlay (hidden by default)
 *   - Keyboard shortcuts panel (collapsed by default)
 */
export function initComponents() {
    // Sidebar panels (sidebar is hidden by default in analytics view)
    inject('showcase-panel', getShowcasePanelTemplate);
    inject('panel-github', getGithubPanelTemplate);
    inject('panel-manual-load', getManualLoadPanelTemplate);
    inject('panel-shortcuts-body', getKeyboardShortcutsPanelTemplate);

    // Bottom sheet content (hidden by default)
    inject('bottom-sheet-content', getBottomSheetContentTemplate);

    // Help overlay (hidden by default)
    inject('help-overlay', getHelpTemplate);
}

/**
 * Injects template HTML into an element by ID.
 * Only injects if the element exists and is empty.
 * @param {string} id - Target element ID
 * @param {Function} templateFn - Function returning HTML string
 */
function inject(id, templateFn) {
    const el = document.getElementById(id);
    if (el && el.children.length === 0) {
        el.innerHTML = templateFn();
    }
}
