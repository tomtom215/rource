/**
 * Rource - Main Entry Point
 *
 * Initializes the WASM application and coordinates all modules.
 */

import init, { Rource } from '../pkg/rource_wasm.js';

// Core modules
import { CONFIG, getExtensionColor } from './config.js';
import { telemetry, debugLog, validateSpeed } from './telemetry.js';
import { debounce, escapeHtml } from './utils.js';
import {
    setState, get, getRource, setRource,
    getAnimationId, setAnimationId, hasData,
    isContextLost, addManagedEventListener
} from './state.js';
import { initDomElements, getElement, getAllElements } from './dom.js';
import {
    loadPreferences, updatePreference, getPreference,
    applyPanelPreferences, setupPanelToggleHandlers
} from './preferences.js';
import { parseUrlParams, updateUrlState } from './url-state.js';
import { safeWasmCall, safeWasmVoid } from './wasm-api.js';
import { ROURCE_STATS, getFullCachedData } from './cached-data.js';

// Application modules
import { showToast, hideToast, initToast } from './toast.js';
import {
    initAnimation, resizeCanvas, startAnimation, stopAnimation,
    animate, updatePlaybackUI, setUIUpdateCallback, isAtEnd
} from './animation.js';
import { loadLogData, analyzeLogData, loadRourceData, setOnDataLoadedCallback, parseCommits } from './data-loader.js';

// Feature modules
import { initScreenshot, setAnimateCallback, captureScreenshot } from './features/screenshot.js';
import { initFullscreen, toggleFullscreen } from './features/fullscreen.js';
import { initTheme, toggleTheme } from './features/theme.js';
import { initHelp, maybeShowFirstTimeHelp, showHelp } from './features/help.js';
import { initKeyboard } from './features/keyboard.js';

// ============================================================
// Initialization
// ============================================================

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

        // Initialize modules
        initToast();
        initTheme();
        initAnimation();
        initFullscreen();
        initHelp();
        initKeyboard();

        // Set up animation callback for screenshot
        setAnimateCallback(animate);

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
            safeWasmCall('setSecondsPerDay', () => rource.setSecondsPerDay(speed), undefined);
        }

        // Apply saved labels preference
        if (prefs.showLabels === false) {
            safeWasmCall('setLabels', () => rource.setLabels(false), undefined);
            if (elements.labelsText) elements.labelsText.textContent = 'Off';
            if (elements.btnLabels) elements.btnLabels.classList.remove('active');
        }

        // Set up event listeners
        setupEventListeners(elements, rource);

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
        if (urlParams.repo) {
            // Load from URL param (TODO: implement GitHub fetch)
            console.log('Rource: URL repo param:', urlParams.repo);
        }

        // Apply speed from URL
        if (urlParams.speed) {
            const speedValue = validateSpeed(urlParams.speed);
            if (elements.speedSelect) elements.speedSelect.value = String(speedValue);
            safeWasmCall('setSecondsPerDay', () => rource.setSecondsPerDay(speedValue), undefined);
        }

        // Auto-load Rource data after a short delay
        setTimeout(() => {
            if (!hasData()) {
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
 */
function handleDataLoaded(content, stats) {
    // Parse commits for tooltip
    parsedCommits = parseCommits(content);

    // Update legend
    updateLegend(content);

    // Update authors legend
    updateAuthorsLegend();

    // Update timeline markers
    updateTimelineMarkers(content);

    // Show first-time help
    maybeShowFirstTimeHelp();
}

/**
 * Enables controls after initialization.
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
    if (elements.btnLoad) elements.btnLoad.disabled = false;
    if (elements.btnFetchGithub) elements.btnFetchGithub.disabled = false;
    if (elements.btnVisualizeRource) elements.btnVisualizeRource.disabled = false;
}

/**
 * Sets up all event listeners.
 */
function setupEventListeners(elements, rource) {
    // Play button
    if (elements.btnPlayMain) {
        elements.btnPlayMain.addEventListener('click', () => {
            // If at end and paused, restart from beginning
            if (isAtEnd() && !safeWasmCall('isPlaying', () => rource.isPlaying(), false)) {
                safeWasmCall('seek', () => rource.seek(0), undefined);
            }
            safeWasmCall('togglePlay', () => rource.togglePlay(), undefined);
            updatePlaybackUI();
        });
    }

    // Navigation buttons
    if (elements.btnPrev) {
        elements.btnPrev.addEventListener('click', () => {
            safeWasmCall('stepBackward', () => rource.stepBackward(), undefined);
            updatePlaybackUI();
        });
    }

    if (elements.btnNext) {
        elements.btnNext.addEventListener('click', () => {
            safeWasmCall('stepForward', () => rource.stepForward(), undefined);
            updatePlaybackUI();
        });
    }

    // Reset button
    if (elements.btnResetBar) {
        elements.btnResetBar.addEventListener('click', () => {
            safeWasmCall('seek', () => rource.seek(0), undefined);
            updatePlaybackUI();
        });
    }

    // Labels toggle
    if (elements.btnLabels) {
        elements.btnLabels.addEventListener('click', () => {
            const showLabels = safeWasmCall('toggleLabels', () => rource.toggleLabels(), false);
            if (elements.labelsText) {
                elements.labelsText.textContent = showLabels ? 'On' : 'Off';
            }
            elements.btnLabels.classList.toggle('active', showLabels);
            updatePreference('showLabels', showLabels);
        });
    }

    // Screenshot button
    if (elements.btnScreenshot) {
        elements.btnScreenshot.addEventListener('click', captureScreenshot);
    }

    // Speed selector
    if (elements.speedSelect) {
        elements.speedSelect.addEventListener('change', (e) => {
            const speed = validateSpeed(e.target.value);
            safeWasmCall('setSecondsPerDay', () => rource.setSecondsPerDay(speed), undefined);
            updatePreference('speed', e.target.value);
            updateUrlState({ speed: e.target.value });
        });
    }

    // Timeline slider
    if (elements.timelineSlider) {
        elements.timelineSlider.addEventListener('input', (e) => {
            const commitIndex = parseInt(e.target.value, 10);
            safeWasmCall('seekToCommit', () => rource.seekToCommit(commitIndex), undefined);
            updatePlaybackUI();
        });
    }

    // Visualize Rource button
    if (elements.btnVisualizeRource) {
        elements.btnVisualizeRource.addEventListener('click', () => {
            loadRourceData();
        });
    }

    // Load button (from textarea)
    if (elements.btnLoad) {
        elements.btnLoad.addEventListener('click', () => {
            const logInput = getElement('logInput');
            if (logInput && logInput.value.trim()) {
                loadLogData(logInput.value, 'custom');
            } else {
                showToast('Please enter log data first', 'error');
            }
        });
    }

    // File input
    if (elements.fileInput) {
        elements.fileInput.addEventListener('change', handleFileSelect);
    }

    // Canvas mouse events
    setupCanvasEvents(elements.canvas, rource);

    // Window resize
    window.addEventListener('resize', debounce(resizeCanvas, CONFIG.DEBOUNCE_DELAY_MS));

    // WebGL context loss handling
    if (elements.canvas) {
        elements.canvas.addEventListener('webglcontextlost', (event) => {
            event.preventDefault();
            setState({ isContextLost: true });
            stopAnimation();
            if (elements.contextLostOverlay) {
                elements.contextLostOverlay.classList.remove('hidden');
            }
        });

        elements.canvas.addEventListener('webglcontextrestored', () => {
            setState({ isContextLost: false });
            if (elements.contextLostOverlay) {
                elements.contextLostOverlay.classList.add('hidden');
            }
            startAnimation();
        });
    }

    if (elements.btnRestoreContext) {
        elements.btnRestoreContext.addEventListener('click', () => {
            if (elements.contextLostOverlay) {
                elements.contextLostOverlay.classList.add('hidden');
            }
            showToast('Restoring visualization...', 'success');
            // Re-initialize after a short delay
            setTimeout(() => window.location.reload(), CONFIG.CONTEXT_RESTORE_DELAY_MS);
        });
    }

    // Legend panel toggle
    if (elements.legendToggle) {
        const toggleLegend = () => {
            if (elements.legendPanel) {
                elements.legendPanel.classList.toggle('collapsed');
                const isExpanded = !elements.legendPanel.classList.contains('collapsed');
                elements.legendToggle.setAttribute('aria-expanded', isExpanded.toString());
                updatePreference('panelStates.legend', !isExpanded);
            }
        };
        elements.legendToggle.addEventListener('click', toggleLegend);
        elements.legendToggle.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' || e.key === ' ') {
                e.preventDefault();
                toggleLegend();
            }
        });
    }

    // Authors panel toggle
    if (elements.authorsToggle) {
        const toggleAuthorsPanel = () => {
            if (elements.authorsPanel) {
                elements.authorsPanel.classList.toggle('collapsed');
                const isExpanded = !elements.authorsPanel.classList.contains('collapsed');
                elements.authorsToggle.setAttribute('aria-expanded', isExpanded.toString());
                updatePreference('panelStates.authors', !isExpanded);
            }
        };
        elements.authorsToggle.addEventListener('click', toggleAuthorsPanel);
        elements.authorsToggle.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' || e.key === ' ') {
                e.preventDefault();
                toggleAuthorsPanel();
            }
        });
    }

    // Performance overlay toggle
    if (elements.perfToggle) {
        const togglePerfOverlay = () => {
            if (elements.perfOverlay) {
                elements.perfOverlay.classList.toggle('collapsed');
                const isExpanded = !elements.perfOverlay.classList.contains('collapsed');
                elements.perfToggle.setAttribute('aria-expanded', isExpanded.toString());
                updatePreference('panelStates.perf', !isExpanded);
            }
        };
        elements.perfToggle.addEventListener('click', togglePerfOverlay);
        elements.perfToggle.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' || e.key === ' ') {
                e.preventDefault();
                togglePerfOverlay();
            }
        });
    }
}

/**
 * Sets up canvas mouse/touch events.
 */
function setupCanvasEvents(canvas, rource) {
    if (!canvas) return;

    let isDragging = false;
    let lastX = 0;
    let lastY = 0;

    canvas.addEventListener('mousedown', (e) => {
        isDragging = true;
        lastX = e.clientX;
        lastY = e.clientY;
        canvas.style.cursor = 'grabbing';
    });

    canvas.addEventListener('mousemove', (e) => {
        if (!isDragging) return;
        const dx = e.clientX - lastX;
        const dy = e.clientY - lastY;
        lastX = e.clientX;
        lastY = e.clientY;
        safeWasmCall('pan', () => rource.pan(-dx, -dy), undefined);
    });

    canvas.addEventListener('mouseup', () => {
        isDragging = false;
        canvas.style.cursor = 'grab';
    });

    canvas.addEventListener('mouseleave', () => {
        isDragging = false;
        canvas.style.cursor = 'grab';
    });

    canvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const factor = e.deltaY > 0 ? 0.9 : 1.1;
        safeWasmCall('zoom', () => rource.zoom(factor), undefined);
    }, { passive: false });

    // Touch events for mobile
    let touchStartDist = 0;

    canvas.addEventListener('touchstart', (e) => {
        if (e.touches.length === 1) {
            isDragging = true;
            lastX = e.touches[0].clientX;
            lastY = e.touches[0].clientY;
        } else if (e.touches.length === 2) {
            touchStartDist = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
        }
    });

    canvas.addEventListener('touchmove', (e) => {
        e.preventDefault();
        if (e.touches.length === 1 && isDragging) {
            const dx = e.touches[0].clientX - lastX;
            const dy = e.touches[0].clientY - lastY;
            lastX = e.touches[0].clientX;
            lastY = e.touches[0].clientY;
            safeWasmCall('pan', () => rource.pan(-dx, -dy), undefined);
        } else if (e.touches.length === 2) {
            const dist = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
            if (touchStartDist > 0) {
                const factor = dist / touchStartDist;
                safeWasmCall('zoom', () => rource.zoom(factor), undefined);
                touchStartDist = dist;
            }
        }
    }, { passive: false });

    canvas.addEventListener('touchend', () => {
        isDragging = false;
        touchStartDist = 0;
    });

    canvas.style.cursor = 'grab';
}

/**
 * Handles file selection.
 */
function handleFileSelect(e) {
    const file = e.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = (event) => {
        const content = event.target.result;
        loadLogData(content, 'custom');

        const fileNameEl = getElement('fileNameEl');
        if (fileNameEl) {
            fileNameEl.textContent = file.name;
        }
    };
    reader.onerror = () => {
        showToast('Failed to read file', 'error');
    };
    reader.readAsText(file);
}

/**
 * Updates the file types legend.
 */
function updateLegend(content) {
    const legendItems = getElement('legendItems');
    if (!legendItems) return;

    // Get unique extensions
    const extensions = new Set();
    const lines = content.split('\n');
    for (const line of lines) {
        const parts = line.split('|');
        if (parts.length >= 4) {
            const file = parts[3].trim();
            const ext = file.split('.').pop()?.toLowerCase();
            if (ext && ext !== file) {
                extensions.add(ext);
            }
        }
    }

    // Build legend HTML
    let html = '';
    const sortedExts = Array.from(extensions).sort();
    for (const ext of sortedExts.slice(0, 20)) { // Limit to 20
        const color = getExtensionColor(ext);
        html += `<div class="legend-item">
            <span class="legend-color" style="background-color: ${escapeHtml(color)}"></span>
            <span class="legend-label">.${escapeHtml(ext)}</span>
        </div>`;
    }

    legendItems.innerHTML = html;
}

/**
 * Updates the authors legend.
 */
function updateAuthorsLegend() {
    const authorsItems = getElement('authorsItems');
    const rource = getRource();
    if (!authorsItems || !rource) return;

    try {
        const authors = safeWasmCall('getAuthors', () => rource.getAuthors(), []);
        let html = '';

        for (const author of authors.slice(0, 30)) { // Limit to 30
            const color = safeWasmCall('getAuthorColor', () => rource.getAuthorColor(author), '#888');
            html += `<div class="author-item" data-author="${escapeHtml(author)}">
                <span class="author-color" style="background-color: ${escapeHtml(color)}"></span>
                <span class="author-name">${escapeHtml(author)}</span>
            </div>`;
        }

        authorsItems.innerHTML = html;
    } catch {
        // Authors may not be available yet
    }
}

/**
 * Updates timeline markers for significant commits.
 */
function updateTimelineMarkers(content) {
    const timelineMarkers = getElement('timelineMarkers');
    if (!timelineMarkers) return;

    // Clear existing markers
    timelineMarkers.innerHTML = '';

    // This is a simplified version - the full implementation would
    // identify significant commits (large changes, milestones, etc.)
}

// Start the application
main().catch(console.error);
