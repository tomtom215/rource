/**
 * Rource - Help Feature
 *
 * Manages the help overlay for first-time users.
 */

import { getElement, getAllElements } from '../dom.js';
import { trapFocus } from '../utils.js';

const HELP_SHOWN_KEY = 'rource_help_shown';

/**
 * Checks if help has been shown before.
 * @returns {boolean} True if help was previously shown
 */
export function hasHelpBeenShown() {
    return localStorage.getItem(HELP_SHOWN_KEY) === 'true';
}

/**
 * Marks help as shown.
 */
export function markHelpShown() {
    localStorage.setItem(HELP_SHOWN_KEY, 'true');
}

/**
 * Shows the help overlay.
 */
export function showHelp() {
    const helpOverlay = getElement('helpOverlay');
    if (helpOverlay) {
        helpOverlay.classList.add('visible');
        // Focus the close button for accessibility
        const closeBtn = helpOverlay.querySelector('.help-close, #help-close');
        if (closeBtn) closeBtn.focus();
    }
}

/**
 * Hides the help overlay.
 */
export function hideHelp() {
    const helpOverlay = getElement('helpOverlay');
    if (helpOverlay) {
        helpOverlay.classList.remove('visible');
        markHelpShown();
    }
}

/**
 * Shows help if this is the first visit.
 */
export function maybeShowFirstTimeHelp() {
    if (!hasHelpBeenShown()) {
        // Slight delay to let the visualization load first
        setTimeout(showHelp, 500);
    }
}

/**
 * Initializes help feature.
 */
export function initHelp() {
    const elements = getAllElements();
    const { helpBtn, helpOverlay, helpClose, helpGotIt } = elements;

    // Help button opens overlay
    if (helpBtn) {
        helpBtn.addEventListener('click', showHelp);
    }

    // Close button
    if (helpClose) {
        helpClose.addEventListener('click', hideHelp);
    }

    // "Got it" button
    if (helpGotIt) {
        helpGotIt.addEventListener('click', hideHelp);
    }

    // Click outside to close
    if (helpOverlay) {
        helpOverlay.addEventListener('click', (e) => {
            if (e.target === helpOverlay) hideHelp();
        });
    }

    // Keyboard handling
    document.addEventListener('keydown', (e) => {
        // Focus trap when help overlay is visible
        if (e.key === 'Tab' && helpOverlay?.classList.contains('visible')) {
            const helpContent = helpOverlay.querySelector('.help-content');
            if (helpContent) {
                trapFocus(helpContent, e);
            }
        }

        // Ignore if in input field
        if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;

        // ? or Shift+/ opens help
        if (e.key === '?' || (e.key === '/' && e.shiftKey)) {
            e.preventDefault();
            showHelp();
        }

        // Escape closes help
        if (e.key === 'Escape' && helpOverlay?.classList.contains('visible')) {
            hideHelp();
        }
    });
}
