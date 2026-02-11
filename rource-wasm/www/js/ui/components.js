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
    getKeyboardShortcutsPanelTemplate,
} from './sidebar-template.js';

/**
 * Injects component HTML into placeholder elements.
 * Must be called before initDomElements() and feature modules.
 *
 * Only extracts sections that are hidden/collapsed by default
 * (no FOUC risk). Visible-on-load content stays in index.html.
 *
 * Current extractions:
 *   - Keyboard shortcuts panel body (collapsed by default)
 *
 * Future candidates (hidden by default, safe to extract):
 *   - Help overlay content
 *   - Bottom sheet content
 *   - Tech specs panel body
 *
 * Template modules available but not yet wired:
 *   - help-template.js
 *   - bottom-sheet-template.js
 *   - sidebar-template.js (showcase, github, manual load panels)
 */
export function initComponents() {
    inject('panel-shortcuts-body', getKeyboardShortcutsPanelTemplate);
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
