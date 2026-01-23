// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Theme Feature
 *
 * Handles light/dark theme toggle with system preference detection.
 * Supports both automatic (system preference) and manual (user toggle) modes.
 */

import { getElement } from '../dom.js';

const THEME_KEY = 'rource_theme';

/**
 * Gets the current theme.
 * @returns {string} 'light' or 'dark'
 */
export function getCurrentTheme() {
    return document.documentElement.classList.contains('light-theme') ? 'light' : 'dark';
}

/**
 * Sets the theme manually (overrides system preference).
 * @param {string} theme - 'light' or 'dark'
 */
export function setTheme(theme) {
    // Mark as manually set to override CSS prefers-color-scheme
    document.documentElement.classList.add('theme-manual');

    if (theme === 'light') {
        document.documentElement.classList.add('light-theme');
    } else {
        document.documentElement.classList.remove('light-theme');
    }
    localStorage.setItem(THEME_KEY, theme);
}

/**
 * Toggles the theme between light and dark.
 * Marks the theme as manually set to override system preference.
 */
export function toggleTheme() {
    // Mark as manually set to override CSS prefers-color-scheme
    document.documentElement.classList.add('theme-manual');

    const isLight = document.documentElement.classList.toggle('light-theme');
    localStorage.setItem(THEME_KEY, isLight ? 'light' : 'dark');
}

/**
 * Initializes theme from saved preference or system preference.
 *
 * Priority:
 * 1. Saved user preference (localStorage)
 * 2. System preference (prefers-color-scheme media query)
 * 3. Default to dark theme
 */
export function initTheme() {
    const savedTheme = localStorage.getItem(THEME_KEY);

    if (savedTheme) {
        // User has a saved preference - use it and mark as manual
        document.documentElement.classList.add('theme-manual');
        if (savedTheme === 'light') {
            document.documentElement.classList.add('light-theme');
        }
    }
    // If no saved preference, CSS @media (prefers-color-scheme: light) handles auto-detection
    // The :not(.theme-manual) selector ensures it only applies when not manually set

    // Set up theme toggle button
    const themeToggle = getElement('themeToggle');
    if (themeToggle) {
        themeToggle.addEventListener('click', toggleTheme);
    }

    // Listen for system theme changes (only affects users who haven't manually toggled)
    if (window.matchMedia) {
        const mediaQuery = window.matchMedia('(prefers-color-scheme: light)');
        mediaQuery.addEventListener('change', (e) => {
            // Only auto-switch if user hasn't manually set a preference
            if (!document.documentElement.classList.contains('theme-manual')) {
                // CSS handles the styling via @media query, but we may need to update UI
                // The CSS custom properties will update automatically
            }
        });
    }
}
