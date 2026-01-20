/**
 * Rource - Panel Management
 *
 * Handles panel toggles, tab switching, sidebar mobile controls,
 * and performance overlay settings.
 * Single responsibility: UI panel state management.
 */

import { setState, addManagedEventListener } from '../state.js';
import { getElement, getAllElements } from '../dom.js';
import { updatePreference } from '../preferences.js';
import { restartAnimation } from '../animation.js';
import { showToast } from '../toast.js';

/**
 * Creates a panel toggle handler.
 * @param {HTMLElement} panel - The panel element
 * @param {HTMLElement} toggle - The toggle button/header element
 * @param {string} preferencePath - Preference path for saving state
 * @returns {Function} Toggle handler function
 */
function createPanelToggle(panel, toggle, preferencePath) {
    return () => {
        if (!panel) return;
        panel.classList.toggle('collapsed');
        const isExpanded = !panel.classList.contains('collapsed');
        if (toggle) {
            toggle.setAttribute('aria-expanded', isExpanded.toString());
        }
        updatePreference(preferencePath, !isExpanded);
    };
}

/**
 * Adds keyboard accessibility to a toggle element.
 * @param {HTMLElement} toggle - The toggle element
 * @param {Function} handler - The click handler
 */
function addKeyboardHandler(toggle, handler) {
    if (!toggle) return;
    addManagedEventListener(toggle, 'keydown', (e) => {
        if (e.key === 'Enter' || e.key === ' ') {
            e.preventDefault();
            handler();
        }
    });
}

/**
 * Initializes legend panel toggle.
 */
function initLegendPanel() {
    const legendPanel = getElement('legendPanel');
    const legendToggle = getElement('legendToggle');

    if (!legendToggle || !legendPanel) return;

    const handler = createPanelToggle(legendPanel, legendToggle, 'panelStates.legend');
    addManagedEventListener(legendToggle, 'click', handler);
    addKeyboardHandler(legendToggle, handler);
}

/**
 * Initializes authors panel toggle.
 */
function initAuthorsPanel() {
    const authorsPanel = getElement('authorsPanel');
    const authorsToggle = getElement('authorsToggle');

    if (!authorsToggle || !authorsPanel) return;

    const handler = createPanelToggle(authorsPanel, authorsToggle, 'panelStates.authors');
    addManagedEventListener(authorsToggle, 'click', handler);
    addKeyboardHandler(authorsToggle, handler);
}

/**
 * Initializes performance overlay toggle.
 */
function initPerfOverlay() {
    const perfOverlay = getElement('perfOverlay');
    const perfToggle = getElement('perfToggle');

    if (!perfToggle || !perfOverlay) return;

    const handler = createPanelToggle(perfOverlay, perfToggle, 'panelStates.perf');
    addManagedEventListener(perfToggle, 'click', handler);
    addKeyboardHandler(perfToggle, handler);
}

/**
 * Initializes uncapped FPS toggle.
 */
function initUncappedFps() {
    const perfUncapped = getElement('perfUncapped');
    if (!perfUncapped) return;

    addManagedEventListener(perfUncapped, 'change', (e) => {
        const isUncapped = e.target.checked;
        setState({ uncappedFps: isUncapped });
        // Restart animation loop to switch between requestAnimationFrame and setTimeout
        restartAnimation();
        if (isUncapped) {
            showToast('Uncapped mode: Testing maximum frame rate', 'info');
        }
    });
}

/**
 * Initializes tab switching for data input tabs.
 */
function initTabs() {
    const tabButtons = document.querySelectorAll('.tab-btn');

    tabButtons.forEach(btn => {
        addManagedEventListener(btn, 'click', () => {
            const tab = btn.dataset.tab;

            // Update tab buttons
            tabButtons.forEach(b => {
                b.classList.remove('active');
                b.setAttribute('aria-selected', 'false');
            });
            btn.classList.add('active');
            btn.setAttribute('aria-selected', 'true');

            // Update tab content
            document.querySelectorAll('.tab-content').forEach(c => {
                c.classList.remove('active');
                c.setAttribute('hidden', '');
            });
            const content = document.getElementById(`tab-${tab}`);
            if (content) {
                content.classList.add('active');
                content.removeAttribute('hidden');
            }
        });
    });
}

/**
 * Closes the sidebar (mobile).
 */
function closeSidebar() {
    const elements = getAllElements();
    if (elements.sidebarPanel) {
        elements.sidebarPanel.classList.remove('open');
    }
    if (elements.sidebarOverlay) {
        elements.sidebarOverlay.classList.remove('visible');
    }
}

/**
 * Opens the sidebar (mobile).
 */
function openSidebar() {
    const elements = getAllElements();
    if (elements.sidebarPanel) {
        elements.sidebarPanel.classList.add('open');
    }
    if (elements.sidebarOverlay) {
        elements.sidebarOverlay.classList.add('visible');
    }
}

/**
 * Initializes sidebar mobile controls.
 */
function initSidebarMobile() {
    const sidebarToggle = getElement('sidebarToggle');
    const sidebarClose = getElement('sidebarClose');
    const sidebarOverlay = getElement('sidebarOverlay');

    if (sidebarToggle) {
        addManagedEventListener(sidebarToggle, 'click', openSidebar);
    }

    if (sidebarClose) {
        addManagedEventListener(sidebarClose, 'click', closeSidebar);
    }

    if (sidebarOverlay) {
        addManagedEventListener(sidebarOverlay, 'click', closeSidebar);
    }
}

/**
 * Initializes scroll indicator for sidebar.
 */
function initScrollIndicator() {
    const sidebarPanel = getElement('sidebarPanel');
    const scrollIndicator = document.querySelector('.sidebar-scroll-indicator');

    if (!sidebarPanel || !scrollIndicator) return;

    const checkScroll = () => {
        const scrollTop = sidebarPanel.scrollTop;
        const scrollHeight = sidebarPanel.scrollHeight;
        const clientHeight = sidebarPanel.clientHeight;
        const nearBottom = scrollHeight - scrollTop - clientHeight < 50;
        scrollIndicator.classList.toggle('hidden', nearBottom);
    };

    addManagedEventListener(sidebarPanel, 'scroll', checkScroll);
    // Initial check after a short delay to ensure layout is complete
    setTimeout(checkScroll, 100);
}

/**
 * Initializes all panel-related event listeners.
 */
export function initPanels() {
    initLegendPanel();
    initAuthorsPanel();
    initPerfOverlay();
    initUncappedFps();
    initTabs();
    initSidebarMobile();
    initScrollIndicator();
}

// Export closeSidebar for use by other modules
export { closeSidebar };
