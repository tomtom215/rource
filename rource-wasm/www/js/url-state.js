// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - URL State Management
 *
 * Enables sharing visualization settings via URL parameters.
 * Supported params: repo, speed, autoplay, commit
 */

/**
 * Parses URL parameters and returns configuration object.
 * @returns {Object} Configuration from URL params
 */
export function parseUrlParams() {
    const params = new URLSearchParams(window.location.search);
    return {
        repo: params.get('repo'),           // e.g., "owner/repo" or full URL
        speed: params.get('speed'),         // seconds per day
        autoplay: params.get('autoplay'),   // "true" to auto-play
        commit: params.get('commit'),       // commit index to start at
        view: params.get('view'),           // 'analytics' or 'viz' (default: analytics, omitted from URL)
    };
}

/**
 * Updates URL with current visualization state without page reload.
 * @param {Object} state - State to persist in URL
 */
export function updateUrlState(state) {
    const params = new URLSearchParams(window.location.search);

    if (state.repo !== undefined) {
        if (state.repo) params.set('repo', state.repo);
        else params.delete('repo');
    }
    if (state.speed !== undefined) {
        if (state.speed && state.speed !== '10') params.set('speed', state.speed);
        else params.delete('speed');
    }
    if (state.autoplay !== undefined) {
        if (state.autoplay) params.set('autoplay', 'true');
        else params.delete('autoplay');
    }
    if (state.view !== undefined) {
        // 'analytics' is default — omit from URL for clean URLs
        if (state.view === 'viz') params.set('view', 'viz');
        else params.delete('view');
    }

    const newUrl = params.toString()
        ? `${window.location.pathname}?${params.toString()}`
        : window.location.pathname;

    window.history.replaceState({}, '', newUrl);
}

/**
 * Generates a shareable URL for current state.
 * @returns {string} Full shareable URL
 */
export function getShareableUrl() {
    return window.location.href;
}

/**
 * Creates a shareable URL with specific state.
 * @param {Object} state - State to include in URL
 * @returns {string} Shareable URL
 */
export function createShareableUrl(state) {
    const params = new URLSearchParams();

    if (state.repo) params.set('repo', state.repo);
    if (state.speed && state.speed !== '10') params.set('speed', state.speed);
    if (state.autoplay) params.set('autoplay', 'true');
    if (state.commit) params.set('commit', state.commit);
    if (state.view === 'viz') params.set('view', 'viz');

    const query = params.toString();
    return query
        ? `${window.location.origin}${window.location.pathname}?${query}`
        : `${window.location.origin}${window.location.pathname}`;
}
