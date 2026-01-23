// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Hover Tooltip Handler
 *
 * Handles hover detection over canvas entities and displays tooltip information.
 * Single responsibility: show entity details on hover.
 */

import { getRource } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';
import { getElement } from '../dom.js';
import { CONFIG } from '../config.js';

// State for debouncing hover detection
let hoverTimeout = null;
let lastHoverX = -1;
let lastHoverY = -1;
let tooltipVisible = false;

/**
 * Shows the tooltip with entity information.
 * @param {Object} entityInfo - Parsed entity info from WASM
 * @param {number} screenX - Screen X position for tooltip
 * @param {number} screenY - Screen Y position for tooltip
 */
function showTooltip(entityInfo, screenX, screenY) {
    const tooltip = getElement('commitTooltip');
    const authorColor = getElement('tooltipAuthorColor');
    const author = getElement('tooltipAuthor');
    const date = getElement('tooltipDate');
    const file = getElement('tooltipFile');
    const action = getElement('tooltipAction');

    if (!tooltip) return;

    // Update tooltip content based on entity type
    if (entityInfo.entityType === 'user') {
        authorColor.style.backgroundColor = entityInfo.color;
        author.textContent = entityInfo.name;
        date.textContent = 'Author';
        file.textContent = '';
        action.textContent = '';
        action.className = 'commit-tooltip-action';
    } else if (entityInfo.entityType === 'file') {
        // Extract author color from current context if available
        authorColor.style.backgroundColor = entityInfo.color;
        author.textContent = entityInfo.extension ? `${entityInfo.extension.toUpperCase()} file` : 'File';
        date.textContent = '';
        file.textContent = entityInfo.path || entityInfo.name;
        action.textContent = entityInfo.name;
        action.className = 'commit-tooltip-action';
    } else if (entityInfo.entityType === 'directory') {
        authorColor.style.backgroundColor = entityInfo.color;
        author.textContent = 'Directory';
        date.textContent = '';
        file.textContent = entityInfo.path || entityInfo.name;
        action.textContent = entityInfo.name;
        action.className = 'commit-tooltip-action';
    }

    // Position tooltip near cursor but keep it on screen
    const canvas = getElement('canvas');
    const tooltipWidth = CONFIG.TOOLTIP_WIDTH || 320;
    const tooltipHeight = CONFIG.TOOLTIP_HEIGHT || 150;
    const padding = 15;

    let x = screenX + padding;
    let y = screenY + padding;

    // Keep tooltip on screen
    if (canvas) {
        const rect = canvas.getBoundingClientRect();
        if (x + tooltipWidth > rect.right) {
            x = screenX - tooltipWidth - padding;
        }
        if (y + tooltipHeight > rect.bottom) {
            y = screenY - tooltipHeight - padding;
        }
        if (x < rect.left) {
            x = rect.left + padding;
        }
        if (y < rect.top) {
            y = rect.top + padding;
        }
    }

    tooltip.style.left = `${x}px`;
    tooltip.style.top = `${y}px`;
    tooltip.classList.add('visible');
    tooltip.setAttribute('aria-hidden', 'false');
    tooltipVisible = true;
}

/**
 * Hides the tooltip.
 */
function hideTooltip() {
    const tooltip = getElement('commitTooltip');
    if (tooltip) {
        tooltip.classList.remove('visible');
        tooltip.setAttribute('aria-hidden', 'true');
    }
    tooltipVisible = false;
}

/**
 * Checks for entity under cursor and updates tooltip.
 * @param {number} x - Canvas-relative X coordinate
 * @param {number} y - Canvas-relative Y coordinate
 * @param {number} clientX - Screen X coordinate for tooltip positioning
 * @param {number} clientY - Screen Y coordinate for tooltip positioning
 */
function checkHover(x, y, clientX, clientY) {
    const rource = getRource();
    if (!rource) {
        hideTooltip();
        return;
    }

    const jsonStr = safeWasmCall('getEntityAtCursor', () => rource.getEntityAtCursor(x, y), null);

    if (jsonStr) {
        try {
            const entityInfo = JSON.parse(jsonStr);
            showTooltip(entityInfo, clientX, clientY);
        } catch (e) {
            console.warn('Failed to parse entity info:', e);
            hideTooltip();
        }
    } else {
        hideTooltip();
    }
}

/**
 * Handles mousemove for hover detection with debouncing.
 * @param {MouseEvent} e - Mouse event
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
export function handleHover(e, canvas) {
    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    // Skip if position hasn't changed significantly
    const dx = Math.abs(x - lastHoverX);
    const dy = Math.abs(y - lastHoverY);
    if (dx < 2 && dy < 2 && tooltipVisible) {
        return;
    }

    lastHoverX = x;
    lastHoverY = y;

    // Debounce hover check
    if (hoverTimeout) {
        clearTimeout(hoverTimeout);
    }

    hoverTimeout = setTimeout(() => {
        checkHover(x, y, e.clientX, e.clientY);
    }, 50); // 50ms debounce for smooth hover
}

/**
 * Handles mouse leave to hide tooltip.
 */
export function handleMouseLeaveTooltip() {
    if (hoverTimeout) {
        clearTimeout(hoverTimeout);
        hoverTimeout = null;
    }
    hideTooltip();
    lastHoverX = -1;
    lastHoverY = -1;
}

/**
 * Initializes hover tooltip handling.
 * Should be called after canvas input is initialized.
 */
export function initHoverTooltip() {
    const canvas = getElement('canvas');
    if (!canvas) return;

    // Track hover on mousemove
    canvas.addEventListener('mousemove', (e) => {
        handleHover(e, canvas);
    });

    // Hide tooltip on mouse leave
    canvas.addEventListener('mouseleave', handleMouseLeaveTooltip);

    // Hide tooltip when starting a drag
    canvas.addEventListener('mousedown', () => {
        hideTooltip();
    });
}

/**
 * Returns whether the tooltip is currently visible.
 * @returns {boolean} True if tooltip is visible
 */
export function isTooltipVisible() {
    return tooltipVisible;
}
