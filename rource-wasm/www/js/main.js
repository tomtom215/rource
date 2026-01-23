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
import { generateTimelineTicks } from './timeline-markers.js';
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
import { BUILD_INFO } from './build-info.js';
import {
    initVideoRecording, enableRecordButton, setRecordingAnimateCallback,
    isRecordingSupported
} from './features/video-recording.js';
import { animate } from './animation.js';

// Parsed commits for tooltip display
let parsedCommits = [];

/**
 * Update DOM elements with build info (WASM size, test count, etc.)
 * This ensures displayed values match the actual built artifacts.
 */
function updateBuildInfo() {
    const sizeText = `~${BUILD_INFO.wasmGzipKB}KB`;

    // Update feature list
    const featureSize = document.getElementById('feature-wasm-size');
    if (featureSize) {
        featureSize.textContent = sizeText;
    }

    // Update technical specifications
    const techSize = document.getElementById('tech-wasm-size');
    if (techSize) {
        techSize.textContent = sizeText;
    }

    // Update test count
    const techTests = document.getElementById('tech-tests');
    if (techTests) {
        techTests.textContent = BUILD_INFO.testCount.toLocaleString();
    }

    // Update crate count
    const techCrates = document.getElementById('tech-crates');
    if (techCrates) {
        techCrates.textContent = BUILD_INFO.crateCount;
    }
}

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

        // Update build info (WASM size, etc.)
        updateBuildInfo();

        // Get canvas and create Rource instance
        const canvas = getElement('canvas');
        if (!canvas) {
            throw new Error('Canvas element not found');
        }

        // Use async factory method: Rource.create()
        // It tries backends in order: wgpu (WebGPU) → WebGL2 → Software
        const rource = await Rource.create(canvas);
        setRource(rource);

        // Check renderer type - deterministic from WASM, never guessed
        const isGPU = rource.isGPUAccelerated();
        const rendererType = rource.getRendererType();

        // Deterministic backend display text mapping
        const BACKEND_DISPLAY_NAMES = {
            'wgpu': 'WebGPU',
            'webgl2': 'WebGL2',
            'software': 'CPU'
        };
        const displayName = BACKEND_DISPLAY_NAMES[rendererType] || rendererType;

        // Detailed console logging for observability and traceability
        console.group('Rource Backend Detection');
        console.log('Backend type (from WASM):', rendererType);
        console.log('Display name:', displayName);
        console.log('GPU accelerated:', isGPU);
        console.log('isWgpu():', rource.isWgpu());
        console.log('isWebGL2():', rource.isWebGL2());
        console.groupEnd();

        // Update tech panel renderer badge with data attributes
        if (elements.techRenderer) {
            elements.techRenderer.textContent = displayName;
            elements.techRenderer.setAttribute('data-backend', rendererType);
            elements.techRenderer.setAttribute('data-gpu-accelerated', String(isGPU));
        }

        // Update performance overlay backend indicator
        if (elements.perfBackend) {
            elements.perfBackend.textContent = displayName;
            elements.perfBackend.setAttribute('data-backend', rendererType);
            elements.perfBackend.setAttribute('data-gpu-accelerated', String(isGPU));
        }

        // Enable GPU-specific optimizations when WebGPU is available
        if (rource.isWgpu()) {
            console.group('WebGPU Optimizations');

            // Warmup GPU compute pipelines to avoid first-frame stutter
            rource.warmupGPUPhysics();
            console.log('GPU physics pipeline warmed up');

            // Enable GPU physics for large repositories (500+ directories)
            rource.setUseGPUPhysics(true);
            rource.setGPUPhysicsThreshold(500);
            console.log('GPU physics enabled (threshold: 500 directories)');

            // Initialize procedural file icons
            if (rource.initFileIcons()) {
                console.log(`File icons initialized (${rource.getFileIconCount()} types)`);
            }

            // GPU culling is for extreme-scale (10k+ entities), leave at default threshold
            // Users can enable via console: rource.setUseGPUCulling(true)

            console.groupEnd();
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
 * @param {string} [format='custom'] - Log format: 'custom' or 'git'
 */
function handleDataLoaded(content, stats, format = 'custom') {
    const elements = getAllElements();

    // Reset timeline date labels so they get recalculated
    resetTimelineDateLabels();

    // Parse commits for tooltip
    parsedCommits = parseCommits(content);

    // Update showcase stats with actual loaded data
    if (elements.showcaseCommits) elements.showcaseCommits.textContent = stats.commits.toLocaleString();
    if (elements.showcaseFiles) elements.showcaseFiles.textContent = stats.files.toLocaleString();
    if (elements.showcaseAuthors) elements.showcaseAuthors.textContent = stats.authors.size.toLocaleString();

    // Update legend with file counts (pass format for correct parsing)
    updateLegend(content, format);

    // Update authors legend with commit counts (uses WASM API, no content needed)
    updateAuthorsLegend();

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
 * @param {string} [format='custom'] - Log format: 'custom' or 'git'
 */
function updateLegend(content, format = 'custom') {
    const legendItems = getElement('legendItems');
    if (!legendItems) return;

    // Count files per extension
    const extensionCounts = new Map();
    const lines = content.split('\n');
    const processedFiles = new Set();

    for (const line of lines) {
        let file = null;

        if (format === 'git') {
            // Git format: status lines like "A\tfile.txt" or "M  file.txt"
            const trimmed = line.trim();
            const statusMatch = trimmed.match(/^([AMDRCTU])\d*[\t\s]+(.+)$/i);
            if (statusMatch) {
                file = statusMatch[2].trim();
                // For rename/copy format "old -> new", take the new path
                const arrowIdx = file.indexOf(' -> ');
                if (arrowIdx > 0) {
                    file = file.slice(arrowIdx + 4).trim();
                }
                // For tab-separated rename format "old\tnew", take the new path
                const tabIdx = file.indexOf('\t');
                if (tabIdx > 0) {
                    file = file.slice(tabIdx + 1).trim();
                }
            }
        } else {
            // Custom format: timestamp|author|action|filepath
            const parts = line.split('|');
            if (parts.length >= 4) {
                file = parts[3].trim();
            }
        }

        if (file && !processedFiles.has(file)) {
            processedFiles.add(file);
            const ext = file.includes('.') ? file.split('.').pop()?.toLowerCase() : '';
            if (ext) {
                extensionCounts.set(ext, (extensionCounts.get(ext) || 0) + 1);
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
 * Uses the WASM getAuthors() API which works for all log formats (git, custom, etc.)
 */
function updateAuthorsLegend() {
    const authorsItems = getElement('authorsItems');
    const rource = getRource();
    if (!authorsItems || !rource) {
        console.warn('[Rource] updateAuthorsLegend: Missing authorsItems or rource');
        return;
    }

    try {
        // Use WASM API to get authors - works for all log formats
        const authorsJson = safeWasmCall('getAuthors', () => rource.getAuthors(), '[]');

        // Debug log to help diagnose issues
        if (CONFIG.LOG_WASM_ERRORS) {
            console.log('[Rource] getAuthors returned:', authorsJson.substring(0, 200) + (authorsJson.length > 200 ? '...' : ''));
        }

        const authors = JSON.parse(authorsJson);

        if (!Array.isArray(authors)) {
            console.error('[Rource] getAuthors did not return an array:', typeof authors);
            return;
        }

        // Debug log author count
        if (CONFIG.LOG_WASM_ERRORS) {
            console.log(`[Rource] Parsed ${authors.length} authors from WASM`);
        }

        // Take top 30 authors (already sorted by commit count from WASM)
        const topAuthors = authors.slice(0, 30);

        let html = '';

        for (const author of topAuthors) {
            if (!author || !author.name) {
                console.warn('[Rource] Skipping invalid author entry:', author);
                continue;
            }
            html += `<div class="author-item" role="listitem" data-author="${escapeHtml(author.name)}">
                <span class="author-color" style="background-color: ${escapeHtml(author.color || '#888888')}"></span>
                <span class="author-name">${escapeHtml(author.name)}</span>
                <span class="author-commits">${author.commits || 0}</span>
            </div>`;
        }

        authorsItems.innerHTML = html;
        if (html) {
            authorsItems.setAttribute('role', 'list');
        }
    } catch (error) {
        // Log the error for debugging
        console.error('[Rource] updateAuthorsLegend error:', error);
    }
}

/**
 * Updates timeline markers for significant commits.
 * Generates date tick marks showing time period boundaries (days/weeks/months/years).
 * @param {string} content - Log content (unused, timestamps come from WASM)
 */
function updateTimelineMarkers(content) {
    // Generate date tick marks based on commit timestamps
    generateTimelineTicks();
}

/**
 * Global debug function for verifying backend detection.
 * Can be called from browser console: window.rourceDebug.getBackendInfo()
 *
 * @returns {Object} Backend information for testing/verification
 */
function getBackendInfo() {
    const rource = getRource();
    if (!rource) {
        return { error: 'Rource not initialized' };
    }

    const info = {
        // Direct WASM queries (deterministic source of truth)
        backend: rource.getRendererType(),
        isGpuAccelerated: rource.isGPUAccelerated(),
        isWgpu: rource.isWgpu(),
        isWebGL2: rource.isWebGL2(),

        // DOM state verification
        domState: {
            techRenderer: {
                text: getElement('techRenderer')?.textContent,
                dataBackend: getElement('techRenderer')?.getAttribute('data-backend'),
                dataGpuAccelerated: getElement('techRenderer')?.getAttribute('data-gpu-accelerated'),
            },
            perfBackend: {
                text: getElement('perfBackend')?.textContent,
                dataBackend: getElement('perfBackend')?.getAttribute('data-backend'),
                dataGpuAccelerated: getElement('perfBackend')?.getAttribute('data-gpu-accelerated'),
            },
        },

        // Consistency check
        isConsistent: false,
    };

    // Verify consistency between WASM and DOM
    const wasmBackend = info.backend;
    const domBackend = info.domState.techRenderer.dataBackend;
    const perfBackend = info.domState.perfBackend.dataBackend;
    info.isConsistent = wasmBackend === domBackend && domBackend === perfBackend;

    if (!info.isConsistent) {
        console.warn('[Rource] Backend state inconsistency detected:', {
            wasm: wasmBackend,
            techRenderer: domBackend,
            perfBackend: perfBackend,
        });
    }

    return info;
}

// Expose debug function globally for console testing
if (typeof window !== 'undefined') {
    window.rourceDebug = {
        getBackendInfo,
        version: '1.0.0',
    };
}

// Start the application
main().catch(console.error);
