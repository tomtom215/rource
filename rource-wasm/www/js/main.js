/**
 * Rource - Main Entry Point
 *
 * Thin orchestrator that initializes the WASM application and coordinates all modules.
 * All event handling is delegated to feature modules for maintainability.
 */

import init, { Rource } from '../pkg/rource_wasm.js';

// Core modules
import { CONFIG, getExtensionColor } from './config.js';
import { telemetry, validateSpeed } from './telemetry.js';
import { escapeHtml } from './utils.js';
import {
    setState, getRource, setRource, hasData
} from './state.js';
import { initDomElements, getElement, getAllElements } from './dom.js';
import {
    loadPreferences, updatePreference,
    applyPanelPreferences, setupPanelToggleHandlers
} from './preferences.js';
import { parseUrlParams, updateUrlState } from './url-state.js';
import { safeWasmCall } from './wasm-api.js';
import { ROURCE_STATS, getFullCachedData } from './cached-data.js';

// Application modules
import { showToast, initToast } from './toast.js';
import {
    initAnimation, startAnimation,
    updatePlaybackUI, setUIUpdateCallback, resetTimelineDateLabels
} from './animation.js';
import { loadLogData, loadRourceData, parseCommits, setOnDataLoadedCallback } from './data-loader.js';
import { fetchGitHubWithProgress } from './github-fetch.js';

// Feature modules
import { initPlayback } from './features/playback.js';
import { initCanvasInput } from './features/canvas-input.js';
import { initPanels } from './features/panels.js';
import { initDataInput } from './features/data-input.js';
import { initWindowEvents } from './features/window-events.js';
import { initScreenshot, setAnimateCallback, captureScreenshot } from './features/screenshot.js';
import { initFullscreen } from './features/fullscreen.js';
import { initTheme } from './features/theme.js';
import { initHelp, maybeShowFirstTimeHelp } from './features/help.js';
import { initKeyboard } from './features/keyboard.js';
import { initFullMapExport, setFullMapAnimateCallback } from './features/full-map-export.js';
import { initFontSizeControl, enableFontSizeControls, updateFontSizeUI } from './features/font-size.js';
import {
    initVideoRecording, enableRecordButton, setRecordingAnimateCallback,
    isRecordingSupported
} from './features/video-recording.js';
import { animate } from './animation.js';

// Parsed commits for tooltip display
let parsedCommits = [];

/**
 * Main initialization function.
 */
async function main() {
    console.log('Rource: Initializing...');
    telemetry.initTime = Date.now();

    try {
        // Initialize WASM
        await init();

        // Initialize DOM references
        initDomElements();
        const elements = getAllElements();

        // Get canvas and create Rource instance
        const canvas = getElement('canvas');
        if (!canvas) {
            throw new Error('Canvas element not found');
        }

        const rource = new Rource(canvas);
        setRource(rource);

        // Check renderer type
        const isWebGL2 = rource.isWebGL2();
        const rendererType = rource.getRendererType();
        console.log(`Rource: Using ${rendererType} renderer`);

        // Update renderer badge
        if (elements.techRenderer) {
            elements.techRenderer.textContent = isWebGL2 ? 'WebGL2' : 'CPU';
        }

        // Initialize core modules
        initToast();
        initAnimation();

        // Initialize feature modules (order matters for some)
        initTheme();
        initPlayback();
        initCanvasInput();
        initPanels();
        initDataInput();
        initWindowEvents();
        initFullscreen();
        initKeyboard();
        initScreenshot();
        initHelp();
        initFullMapExport();
        initFontSizeControl();
        initVideoRecording();

        // Set up animation callbacks for features that need them
        setAnimateCallback(animate);
        setFullMapAnimateCallback(animate);
        setRecordingAnimateCallback(animate);

        // Set up UI update callback
        setUIUpdateCallback(updatePlaybackUI);

        // Set up data loaded callback
        setOnDataLoadedCallback(handleDataLoaded);

        // Apply saved preferences
        applyPanelPreferences();
        setupPanelToggleHandlers();

        // Apply saved speed preference
        const prefs = loadPreferences();
        if (elements.speedSelect) {
            elements.speedSelect.value = prefs.speed || '10';
            const speed = validateSpeed(prefs.speed || 10);
            safeWasmCall('setSpeed', () => rource.setSpeed(speed), undefined);
        }

        // Apply saved labels preference
        if (prefs.showLabels === false) {
            safeWasmCall('setShowLabels', () => rource.setShowLabels(false), undefined);
            if (elements.labelsText) elements.labelsText.textContent = 'Off';
            if (elements.btnLabels) elements.btnLabels.classList.remove('active');
        }

        // Enable buttons
        enableControls(elements);

        // Update showcase stats
        if (elements.showcaseCommits) elements.showcaseCommits.textContent = ROURCE_STATS.commits.toLocaleString();
        if (elements.showcaseFiles) elements.showcaseFiles.textContent = ROURCE_STATS.files.toLocaleString();
        if (elements.showcaseAuthors) elements.showcaseAuthors.textContent = ROURCE_STATS.authors.toLocaleString();

        // Start animation loop
        startAnimation();

        // Hide loading overlay
        if (elements.loadingEl) elements.loadingEl.classList.add('hidden');

        // Check URL parameters
        const urlParams = parseUrlParams();

        // Apply speed from URL
        if (urlParams.speed) {
            const speedValue = validateSpeed(urlParams.speed);
            if (elements.speedSelect) elements.speedSelect.value = String(speedValue);
            safeWasmCall('setSpeed', () => rource.setSpeed(speedValue), undefined);
        }

        // Load data based on URL params or default
        setTimeout(async () => {
            if (urlParams.repo) {
                // Load from URL param - fetch from GitHub
                console.log('Rource: Loading from URL repo param:', urlParams.repo);
                if (elements.githubUrlInput) {
                    elements.githubUrlInput.value = urlParams.repo;
                }
                if (elements.fetchStatus) {
                    elements.fetchStatus.classList.add('visible', 'loading');
                }
                const logData = await fetchGitHubWithProgress(urlParams.repo, {
                    statusEl: elements.fetchStatusText,
                });
                if (elements.fetchStatus) {
                    elements.fetchStatus.classList.remove('visible', 'loading');
                }
                if (logData) {
                    loadLogData(logData, 'custom');
                } else if (!hasData()) {
                    // Fall back to default if GitHub fetch failed
                    loadRourceData();
                }
            } else if (!hasData()) {
                // Auto-load Rource data if no URL param
                loadRourceData();
            }
        }, CONFIG.INIT_DELAY_MS);

        console.log('Rource: Initialization complete');

    } catch (error) {
        console.error('Rource: Initialization failed', error);
        showToast('Failed to initialize visualization: ' + error.message, 'error');
    }
}

/**
 * Handles data loaded event.
 * @param {string} content - Loaded log content
 * @param {Object} stats - Data statistics
 */
function handleDataLoaded(content, stats) {
    const elements = getAllElements();

    // Reset timeline date labels so they get recalculated
    resetTimelineDateLabels();

    // Parse commits for tooltip
    parsedCommits = parseCommits(content);

    // Update showcase stats with actual loaded data
    if (elements.showcaseCommits) elements.showcaseCommits.textContent = stats.commits.toLocaleString();
    if (elements.showcaseFiles) elements.showcaseFiles.textContent = stats.files.toLocaleString();
    if (elements.showcaseAuthors) elements.showcaseAuthors.textContent = stats.authors.size.toLocaleString();

    // Update legend with file counts
    updateLegend(content);

    // Update authors legend with commit counts
    updateAuthorsLegend(content);

    // Enable font size controls now that data is loaded
    enableFontSizeControls();
    updateFontSizeUI();

    // Update timeline markers
    updateTimelineMarkers(content);

    // Show authors panel
    if (elements.authorsPanel) {
        elements.authorsPanel.classList.remove('hidden');
        elements.authorsPanel.classList.remove('collapsed');
        if (elements.authorsToggle) {
            elements.authorsToggle.setAttribute('aria-expanded', 'true');
        }
    }

    // Show legend panel
    if (elements.legendPanel) {
        elements.legendPanel.classList.remove('collapsed');
        if (elements.legendToggle) {
            elements.legendToggle.setAttribute('aria-expanded', 'true');
        }
    }

    // Auto-play the visualization
    const rource = getRource();
    if (rource) {
        safeWasmCall('play', () => rource.play(), undefined);
        updatePlaybackUI();
    }

    // Show first-time help
    maybeShowFirstTimeHelp();
}

/**
 * Enables controls after initialization.
 * @param {Object} elements - DOM elements
 */
function enableControls(elements) {
    if (elements.btnPlayMain) {
        elements.btnPlayMain.disabled = false;
        elements.btnPlayMain.title = 'Play/Pause (Space)';
    }
    if (elements.btnResetBar) {
        elements.btnResetBar.disabled = false;
        elements.btnResetBar.title = 'Restart from beginning';
    }
    if (elements.btnLabels) {
        elements.btnLabels.disabled = false;
        elements.btnLabels.title = 'Toggle labels (L)';
    }
    if (elements.btnScreenshot) {
        elements.btnScreenshot.disabled = false;
        elements.btnScreenshot.title = 'Save screenshot (S)';
    }
    if (elements.btnFullMap) {
        elements.btnFullMap.disabled = false;
        elements.btnFullMap.title = 'Export full map at high resolution (M)';
    }
    if (elements.btnRecord && isRecordingSupported()) {
        elements.btnRecord.disabled = false;
        elements.btnRecord.title = 'Record visualization as video';
    }
    // Font size controls are enabled separately when data is loaded
    if (elements.btnLoad) elements.btnLoad.disabled = false;
    if (elements.btnFetchGithub) elements.btnFetchGithub.disabled = false;
    if (elements.btnVisualizeRource) elements.btnVisualizeRource.disabled = false;
}

/**
 * Updates the file types legend with file counts.
 * @param {string} content - Log content
 */
function updateLegend(content) {
    const legendItems = getElement('legendItems');
    if (!legendItems) return;

    // Count files per extension
    const extensionCounts = new Map();
    const lines = content.split('\n');
    const processedFiles = new Set();

    for (const line of lines) {
        const parts = line.split('|');
        if (parts.length >= 4) {
            const file = parts[3].trim();
            if (!processedFiles.has(file)) {
                processedFiles.add(file);
                const ext = file.includes('.') ? file.split('.').pop()?.toLowerCase() : '';
                if (ext) {
                    extensionCounts.set(ext, (extensionCounts.get(ext) || 0) + 1);
                }
            }
        }
    }

    // Sort by count descending
    const sortedExts = Array.from(extensionCounts.entries())
        .sort((a, b) => b[1] - a[1])
        .slice(0, 20);

    // Build legend HTML
    let html = '';
    for (const [ext, count] of sortedExts) {
        const color = getExtensionColor(ext);
        html += `<div class="legend-item" role="listitem">
            <span class="legend-color" style="background-color: ${escapeHtml(color)}"></span>
            <span class="legend-label">.${escapeHtml(ext)}</span>
            <span class="legend-count">${count}</span>
        </div>`;
    }

    // Add separator and structure item
    html += `<div class="legend-divider" role="separator" aria-hidden="true"></div>
        <div class="legend-item legend-item-structure" role="listitem" title="Directories are shown as gray circles with center dots. Lines connect parent folders to child folders.">
            <svg class="legend-structure-icon" viewBox="0 0 20 20" aria-hidden="true">
                <circle cx="10" cy="10" r="7" fill="none" stroke="#6e7681" stroke-width="1.5" opacity="0.7"/>
                <circle cx="10" cy="10" r="2" fill="#6e7681" opacity="0.6"/>
            </svg>
            <span class="legend-ext">Directories</span>
        </div>`;

    legendItems.innerHTML = html;
    legendItems.setAttribute('role', 'list');
}

/**
 * Updates the authors legend with commit counts.
 * @param {string} content - Log content
 */
function updateAuthorsLegend(content) {
    const authorsItems = getElement('authorsItems');
    const rource = getRource();
    if (!authorsItems || !rource) return;

    try {
        // Count commits per author from content
        const authorCommitCounts = new Map();
        if (content) {
            const lines = content.split('\n');
            const seenCommits = new Set();

            for (const line of lines) {
                const parts = line.split('|');
                if (parts.length >= 4) {
                    const timestamp = parts[0].trim();
                    const author = parts[1].trim();
                    const commitKey = `${timestamp}|${author}`;
                    if (!seenCommits.has(commitKey)) {
                        seenCommits.add(commitKey);
                        authorCommitCounts.set(author, (authorCommitCounts.get(author) || 0) + 1);
                    }
                }
            }
        }

        // Sort by commit count descending
        const sortedAuthors = Array.from(authorCommitCounts.entries())
            .sort((a, b) => b[1] - a[1])
            .slice(0, 30);

        let html = '';

        for (const [author, commitCount] of sortedAuthors) {
            const color = safeWasmCall('getAuthorColor', () => rource.getAuthorColor(author), '#888');
            html += `<div class="author-item" role="listitem" data-author="${escapeHtml(author)}">
                <span class="author-color" style="background-color: ${escapeHtml(color)}"></span>
                <span class="author-name">${escapeHtml(author)}</span>
                <span class="author-commits">${commitCount}</span>
            </div>`;
        }

        authorsItems.innerHTML = html;
        if (html) {
            authorsItems.setAttribute('role', 'list');
        }
    } catch {
        // Authors may not be available yet
    }
}

/**
 * Updates timeline markers for significant commits.
 * @param {string} content - Log content
 */
function updateTimelineMarkers(content) {
    const timelineMarkers = getElement('timelineMarkers');
    if (!timelineMarkers) return;

    // Clear existing markers
    timelineMarkers.innerHTML = '';
}

// Start the application
main().catch(console.error);
