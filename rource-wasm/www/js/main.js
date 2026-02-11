// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Main Entry Point
 *
 * Thin orchestrator that initializes the WASM application and coordinates all modules.
 * All event handling is delegated to feature modules for maintainability.
 *
 * Module structure:
 *   main.js              - WASM init, module wiring, GPU setup
 *   main-lifecycle.js    - Cleanup handlers, retry logic, build info, controls
 *   main-actions.js      - Bottom sheet and dashboard action wiring
 *   main-data-handlers.js - Post-data-loaded workflow (legends, timeline, view branching)
 */

import init from '../pkg/rource_wasm.js';

// Core modules
import { CONFIG } from './config.js';
import { telemetry, validateSpeed } from './telemetry.js';
import {
    setState, get, setRource, hasData, getRource
} from './state.js';
import { initDomElements, getElement, getAllElements } from './dom.js';
import {
    loadPreferences,
    applyPanelPreferences, setupPanelToggleHandlers
} from './preferences.js';
import { parseUrlParams } from './url-state.js';
import { safeWasmCall } from './wasm-api.js';
import { ROURCE_STATS } from './cached-data.js';

// Application modules
import { initToast, showToast } from './toast.js';
import {
    initAnimation, startAnimation,
    updatePlaybackUI, setUIUpdateCallback,
    setPlaybackStateCallback, animate
} from './animation.js';
import { loadLogData, loadRourceData, setOnDataLoadedCallback } from './data-loader.js';
import { fetchGitHubWithProgress } from './github-fetch.js';

// Feature modules
import { initPlayback } from './features/playback.js';
import { initCanvasInput } from './features/canvas-input.js';
import { initPanels } from './features/panels.js';
import { initDataInput } from './features/data-input.js';
import { initWindowEvents } from './features/window-events.js';
import { initScreenshot, setAnimateCallback, captureScreenshot } from './features/screenshot.js';
import { initFullscreen, toggleFullscreen } from './features/fullscreen.js';
import { initTheme, toggleTheme } from './features/theme.js';
import { initHelp, showHelp } from './features/help.js';
import { initKeyboard } from './features/keyboard.js';
import { initFullMapExport, setFullMapAnimateCallback } from './features/full-map-export.js';
import { initFontSizeControl } from './features/font-size.js';
import { initHoverTooltip } from './features/hover-tooltip.js';
import { BUILD_INFO } from './build-info.js';
import { initVideoRecording, setRecordingAnimateCallback } from './features/video-recording.js';
import { initStatsBuffer } from './core/stats-buffer.js';
import { initBottomSheet } from './features/bottom-sheet.js';
import { initMobileToolbar } from './features/mobile-toolbar.js';
import { initMobileControls, onPlaybackStateChange } from './features/mobile-controls.js';
import {
    initImmersiveMode, onImmersivePlaybackChange, updateHUDPlayButton
} from './features/immersive-mode.js';
import { initReducedMotion, setRourceInstance as setReducedMotionRource } from './features/reduced-motion.js';
import { initInsights, showDashboardLoading } from './features/insights.js';
import { initViewManager, getCurrentView } from './features/view-manager.js';
import { initComponents } from './ui/components.js';

// Extracted modules
import { setupCleanupHandler, createRourceWithRetry, updateBuildInfo, enableControls, getBackendInfo } from './main-lifecycle.js';
import { initBottomSheetActions, initAnalyticsDashboardActions } from './main-actions.js';
import { handleDataLoaded } from './main-data-handlers.js';

/**
 * Main initialization function.
 */
async function main() {
    console.log('Rource: Initializing...');
    telemetry.initTime = Date.now();

    // Setup cleanup handler first to catch page unload
    setupCleanupHandler();

    try {
        // Initialize WASM
        await init();

        // Inject component HTML templates (must run before initDomElements)
        initComponents();

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

        // Use async factory method with retry logic
        const rource = await createRourceWithRetry(canvas);
        setRource(rource);
        setReducedMotionRource(rource);

        // Phase 84: Initialize zero-copy stats buffer for direct WASM memory reads
        try {
            const wasmMemory = rource.getWasmMemory();
            if (initStatsBuffer(rource, wasmMemory)) {
                console.log('Rource: Zero-copy stats buffer initialized (Phase 84)');
            }
        } catch (e) {
            console.warn('Rource: Stats buffer init failed, using JSON fallback:', e);
        }

        // Check renderer type
        const isGPU = rource.isGPUAccelerated();
        const rendererType = rource.getRendererType();

        const BACKEND_DISPLAY_NAMES = {
            'wgpu': 'WebGPU',
            'webgl2': 'WebGL2',
            'software': 'CPU'
        };
        const displayName = BACKEND_DISPLAY_NAMES[rendererType] || rendererType;

        console.group('Rource Backend Detection');
        console.log('Backend type (from WASM):', rendererType);
        console.log('Display name:', displayName);
        console.log('GPU accelerated:', isGPU);
        console.log('isWgpu():', rource.isWgpu());
        console.log('isWebGL2():', rource.isWebGL2());
        console.groupEnd();

        if (elements.techRenderer) {
            elements.techRenderer.textContent = displayName;
            elements.techRenderer.setAttribute('data-backend', rendererType);
            elements.techRenderer.setAttribute('data-gpu-accelerated', String(isGPU));
        }

        if (elements.perfBackend) {
            elements.perfBackend.textContent = displayName;
            elements.perfBackend.setAttribute('data-backend', rendererType);
            elements.perfBackend.setAttribute('data-gpu-accelerated', String(isGPU));
        }

        // Enable GPU-specific optimizations when WebGPU is available
        if (rource.isWgpu()) {
            console.group('WebGPU Optimizations');

            const isFirefox = navigator.userAgent.includes('Firefox');

            if (!isFirefox) {
                rource.warmupGPUPhysics();
                console.log('GPU physics pipeline warmed up');

                rource.setUseGPUPhysics(true);
                rource.setGPUPhysicsThreshold(500);
                console.log('GPU physics enabled (threshold: 500 directories)');
            } else {
                console.log('Firefox detected: using CPU physics (GPU compute has overhead)');
            }

            if (rource.initFileIcons()) {
                console.log(`File icons initialized (${rource.getFileIconCount()} types)`);
            }

            console.groupEnd();
        }

        // Enable Rource brand watermark for the demo
        rource.enableRourceWatermark();
        console.log('Rource watermark enabled');

        // Initialize core modules
        initToast();
        initAnimation();

        // Initialize feature modules (order matters for some)
        initTheme();
        initReducedMotion();
        initPlayback();
        initCanvasInput();
        initHoverTooltip();
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
        initBottomSheet();
        initInsights();
        initViewManager();

        // Parse URL parameters
        const urlParams = parseUrlParams();

        // Set initial view from URL params
        const initialView = urlParams.view === 'viz' ? 'viz' : 'analytics';
        setState({ currentView: initialView });

        if (initialView === 'analytics') {
            showDashboardLoading();
        }

        // Wire up UI actions
        initBottomSheetActions();
        initAnalyticsDashboardActions();

        // Initialize mobile toolbar
        initMobileToolbar({
            captureScreenshot,
            toggleTheme,
            toggleFullscreen,
            showHelp,
            toggleLabels: () => {}
        });

        // Initialize mobile controls
        initMobileControls({
            isPlaying: () => safeWasmCall('isPlaying', () => rource.isPlaying(), false),
            togglePlay: () => {
                safeWasmCall('togglePlay', () => rource.togglePlay(), undefined);
                updatePlaybackUI();
            }
        });

        // Initialize immersive mode
        initImmersiveMode({
            isPlaying: () => safeWasmCall('isPlaying', () => rource.isPlaying(), false),
            togglePlay: () => {
                safeWasmCall('togglePlay', () => rource.togglePlay(), undefined);
                updatePlaybackUI();
            }
        });

        // Connect playback state changes
        setPlaybackStateCallback((playing) => {
            onPlaybackStateChange(playing);
            onImmersivePlaybackChange(playing);
            updateHUDPlayButton(playing);
        });

        // Set up animation callbacks
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

        // Start animation loop only if visualization is the active view
        if (getCurrentView() === 'viz') {
            startAnimation();
        }

        // Hide loading overlay
        if (elements.loadingEl) elements.loadingEl.classList.add('hidden');

        // Apply speed from URL
        if (urlParams.speed) {
            const speedValue = validateSpeed(urlParams.speed);
            if (elements.speedSelect) elements.speedSelect.value = String(speedValue);
            safeWasmCall('setSpeed', () => rource.setSpeed(speedValue), undefined);
        }

        // Load data based on URL params or default
        setTimeout(async () => {
            if (urlParams.repo) {
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
                    loadRourceData();
                }
            } else if (!hasData()) {
                loadRourceData();
            }
        }, CONFIG.INIT_DELAY_MS);

        console.log('Rource: Initialization complete');

    } catch (error) {
        console.error('Rource: Initialization failed', error);
        showToast('Failed to initialize visualization: ' + error.message, 'error');
    }
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
