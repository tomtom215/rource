/**
 * Rource - Application State Management
 *
 * Centralized state management for the application.
 * Uses a simple observable pattern for state updates.
 */

import { debugLog, setEventListenerCount } from './telemetry.js';

/**
 * Application state container.
 * All state should be accessed through getState() and updated through setState().
 */
const appState = {
    // Core WASM instance
    rource: null,

    // Animation
    animationId: null,

    // Data state
    uploadedFileContent: null,
    hasLoadedData: false,
    commitStats: { commits: 0, files: 0, authors: new Set() },
    lastLoadedRepo: null,

    // UI state
    isContextLost: false,
    showLabels: true,

    // GitHub fetch state (prevents race conditions)
    githubFetchInProgress: false,
    githubFetchController: null,

    // First visit state for help overlay
    isFirstVisit: true,

    // Author filter state
    authorFilters: new Set(),

    // Fullscreen state
    isPseudoFullscreen: false,

    // Performance testing - uncapped FPS mode
    uncappedFps: false,
};

/**
 * State change listeners.
 * @type {Map<string, Set<Function>>}
 */
const listeners = new Map();

/**
 * Gets the current application state.
 * @returns {Object} Current state (read-only view)
 */
export function getState() {
    return { ...appState };
}

/**
 * Gets a specific state value.
 * @param {string} key - State key
 * @returns {*} State value
 */
export function get(key) {
    return appState[key];
}

/**
 * Updates the application state.
 * @param {Object} updates - State updates
 */
export function setState(updates) {
    const changedKeys = [];

    for (const [key, value] of Object.entries(updates)) {
        if (appState[key] !== value) {
            appState[key] = value;
            changedKeys.push(key);
        }
    }

    // Notify listeners
    for (const key of changedKeys) {
        const keyListeners = listeners.get(key);
        if (keyListeners) {
            for (const listener of keyListeners) {
                try {
                    listener(appState[key], key);
                } catch (e) {
                    debugLog('setState', `Listener error for ${key}`, e);
                }
            }
        }
    }
}

/**
 * Subscribes to state changes for a specific key.
 * @param {string} key - State key to watch
 * @param {Function} callback - Callback(newValue, key)
 * @returns {Function} Unsubscribe function
 */
export function subscribe(key, callback) {
    if (!listeners.has(key)) {
        listeners.set(key, new Set());
    }
    listeners.get(key).add(callback);

    return () => {
        const keyListeners = listeners.get(key);
        if (keyListeners) {
            keyListeners.delete(callback);
        }
    };
}

// ============================================================
// Event Listener Management
// ============================================================
// Tracks all registered event listeners for proper cleanup on reinitialize.
// This prevents memory leaks when the app state is reset.

/**
 * Registry of all managed event listeners.
 * @type {Array<{element: EventTarget, type: string, handler: Function, options?: AddEventListenerOptions}>}
 */
const eventListenerRegistry = [];

/**
 * Adds an event listener and registers it for cleanup.
 * @param {EventTarget} element - The element to attach the listener to
 * @param {string} type - The event type (e.g., 'click', 'keydown')
 * @param {Function} handler - The event handler function
 * @param {AddEventListenerOptions} [options] - Optional event listener options
 */
export function addManagedEventListener(element, type, handler, options) {
    if (!element) {
        debugLog('addManagedEventListener', `Cannot add listener to null element for event: ${type}`);
        return;
    }
    element.addEventListener(type, handler, options);
    eventListenerRegistry.push({ element, type, handler, options });
    setEventListenerCount(eventListenerRegistry.length);
}

/**
 * Removes all managed event listeners.
 * Call this before reinitializing the application to prevent memory leaks.
 */
export function cleanupEventListeners() {
    for (const { element, type, handler, options } of eventListenerRegistry) {
        try {
            element.removeEventListener(type, handler, options);
        } catch (e) {
            debugLog('cleanupEventListeners', `Failed to remove listener for ${type}`, e);
        }
    }
    const count = eventListenerRegistry.length;
    eventListenerRegistry.length = 0;
    setEventListenerCount(0);
    debugLog('cleanupEventListeners', `Removed ${count} event listeners`);
}

// ============================================================
// Convenience accessors for common state
// ============================================================

/**
 * Gets the WASM Rource instance.
 * @returns {Object|null} Rource instance
 */
export function getRource() {
    return appState.rource;
}

/**
 * Sets the WASM Rource instance.
 * @param {Object|null} instance - Rource instance
 */
export function setRource(instance) {
    setState({ rource: instance });
}

/**
 * Gets the current animation frame ID.
 * @returns {number|null} Animation frame ID
 */
export function getAnimationId() {
    return appState.animationId;
}

/**
 * Sets the animation frame ID.
 * @param {number|null} id - Animation frame ID
 */
export function setAnimationId(id) {
    appState.animationId = id; // Direct set to avoid listener overhead
}

/**
 * Checks if data has been loaded.
 * @returns {boolean} True if data is loaded
 */
export function hasData() {
    return appState.hasLoadedData;
}

/**
 * Checks if WebGL context is lost.
 * @returns {boolean} True if context is lost
 */
export function isContextLost() {
    return appState.isContextLost;
}
