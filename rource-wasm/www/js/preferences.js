/**
 * Rource - User Preferences (localStorage)
 *
 * Handles persistent user preferences stored in localStorage.
 */

const PREFS_KEY = 'rource_preferences';

/**
 * Default user preferences.
 */
const defaultPrefs = {
    speed: '10',           // Default speed (1x)
    showLabels: true,      // Show file/user labels
    panelStates: {         // Collapsed state for panels
        shortcuts: true,   // Keyboard shortcuts panel
        guide: false,      // Quick guide panel (expanded by default)
        techSpecs: true,   // Technical specifications panel
        legend: true,      // File types legend
        authors: true,     // Authors legend
        perf: false,       // Performance overlay (hidden by default)
    },
    theme: 'dark',         // Theme preference
};

/**
 * Cached preferences (loaded once at startup).
 * @type {Object|null}
 */
let cachedPrefs = null;

/**
 * Load user preferences from localStorage.
 * @returns {Object} User preferences merged with defaults
 */
export function loadPreferences() {
    if (cachedPrefs) {
        return cachedPrefs;
    }

    try {
        const stored = localStorage.getItem(PREFS_KEY);
        if (stored) {
            const parsed = JSON.parse(stored);
            // Deep merge with defaults to handle new preference keys
            cachedPrefs = {
                ...defaultPrefs,
                ...parsed,
                panelStates: {
                    ...defaultPrefs.panelStates,
                    ...(parsed.panelStates || {}),
                },
            };
            return cachedPrefs;
        }
    } catch (e) {
        console.warn('Failed to load preferences:', e);
    }

    cachedPrefs = { ...defaultPrefs };
    return cachedPrefs;
}

/**
 * Save user preferences to localStorage.
 * @param {Object} prefs - Preferences to save
 * @returns {boolean} True if save was successful, false otherwise
 */
export function savePreferences(prefs) {
    try {
        localStorage.setItem(PREFS_KEY, JSON.stringify(prefs));
        cachedPrefs = prefs;
        return true;
    } catch (e) {
        // Handle quota exceeded error specifically
        if (e.name === 'QuotaExceededError' ||
            e.code === 22 || // Legacy Chrome
            (e.code === 1014 && e.name === 'NS_ERROR_DOM_QUOTA_REACHED')) { // Firefox
            console.error('localStorage quota exceeded. Preferences could not be saved.');
            // Try to clear and retry once
            try {
                localStorage.removeItem(PREFS_KEY);
                localStorage.setItem(PREFS_KEY, JSON.stringify(prefs));
                cachedPrefs = prefs;
                console.info('Cleared old preferences and saved successfully.');
                return true;
            } catch (retryError) {
                console.error('Failed to save preferences even after clearing:', retryError);
            }
        } else {
            console.warn('Failed to save preferences:', e);
        }
        return false;
    }
}

/**
 * Update a single preference value.
 * @param {string} key - Preference key (supports dot notation for nested, e.g., 'panelStates.shortcuts')
 * @param {*} value - New value
 */
export function updatePreference(key, value) {
    const prefs = loadPreferences();
    const keys = key.split('.');
    let obj = prefs;
    for (let i = 0; i < keys.length - 1; i++) {
        if (!obj[keys[i]]) obj[keys[i]] = {};
        obj = obj[keys[i]];
    }
    obj[keys[keys.length - 1]] = value;
    savePreferences(prefs);
}

/**
 * Get a single preference value.
 * @param {string} key - Preference key (supports dot notation)
 * @returns {*} Preference value
 */
export function getPreference(key) {
    const prefs = loadPreferences();
    const keys = key.split('.');
    let obj = prefs;
    for (const k of keys) {
        if (obj === undefined || obj === null) return undefined;
        obj = obj[k];
    }
    return obj;
}

/**
 * Reset all preferences to defaults.
 */
export function resetPreferences() {
    cachedPrefs = { ...defaultPrefs };
    savePreferences(cachedPrefs);
}

/**
 * Apply saved panel collapsed states from preferences.
 */
export function applyPanelPreferences() {
    const prefs = loadPreferences();
    const states = prefs.panelStates || {};

    // Keyboard shortcuts panel
    const shortcutsPanel = document.getElementById('panel-shortcuts');
    if (shortcutsPanel) {
        shortcutsPanel.classList.toggle('collapsed', states.shortcuts !== false);
    }

    // Quick guide panel
    const guidePanel = document.getElementById('panel-guide');
    if (guidePanel) {
        guidePanel.classList.toggle('collapsed', states.guide !== false);
    }

    // Technical specs panel
    const techPanel = document.getElementById('tech-info-panel');
    if (techPanel) {
        techPanel.classList.toggle('collapsed', states.techSpecs !== false);
    }

    // Legend panel
    const legendPanel = document.getElementById('legend-panel');
    if (legendPanel) {
        legendPanel.classList.toggle('collapsed', states.legend !== false);
    }
}

/**
 * Setup panel toggle handlers with preference saving.
 * Consolidated handler for all collapsible sidebar panels.
 */
export function setupPanelToggleHandlers() {
    // Make collapsible panels save their state
    const panelMappings = [
        { id: 'panel-shortcuts', pref: 'panelStates.shortcuts' },
        { id: 'panel-guide', pref: 'panelStates.guide' },
        { id: 'tech-info-panel', pref: 'panelStates.techSpecs' },
    ];

    panelMappings.forEach(({ id, pref }) => {
        const panel = document.getElementById(id);
        if (!panel) return;

        const header = panel.querySelector('.panel-header, .tech-info-header');
        if (!header) return;

        // Use addEventListener for proper event handling
        header.addEventListener('click', () => {
            panel.classList.toggle('collapsed');
            const isCollapsed = panel.classList.contains('collapsed');

            // Update aria-expanded for accessibility
            header.setAttribute('aria-expanded', (!isCollapsed).toString());

            // Save preference
            updatePreference(pref, isCollapsed);
        });
    });
}
