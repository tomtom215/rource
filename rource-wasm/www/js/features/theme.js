/**
 * Rource - Theme Feature
 *
 * Handles light/dark theme toggle.
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
 * Sets the theme.
 * @param {string} theme - 'light' or 'dark'
 */
export function setTheme(theme) {
    if (theme === 'light') {
        document.documentElement.classList.add('light-theme');
    } else {
        document.documentElement.classList.remove('light-theme');
    }
    localStorage.setItem(THEME_KEY, theme);
}

/**
 * Toggles the theme between light and dark.
 */
export function toggleTheme() {
    const isLight = document.documentElement.classList.toggle('light-theme');
    localStorage.setItem(THEME_KEY, isLight ? 'light' : 'dark');
}

/**
 * Initializes theme from saved preference.
 */
export function initTheme() {
    const savedTheme = localStorage.getItem(THEME_KEY);
    if (savedTheme === 'light') {
        document.documentElement.classList.add('light-theme');
    }

    // Set up theme toggle button
    const themeToggle = getElement('themeToggle');
    if (themeToggle) {
        themeToggle.addEventListener('click', toggleTheme);
    }
}
