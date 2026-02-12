// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Application Lifecycle Management
 *
 * Handles cleanup on page unload, retry logic for GPU initialization,
 * build info display, and control enablement.
 */

import { Rource } from '../pkg/rource_wasm.js';
import { stopAnimation, getFrameScheduler } from './animation.js';
import { getRource, setRource } from './state.js';
import { disposeStatsBuffer } from './core/stats-buffer.js';
import { getElement } from './dom.js';
import { BUILD_INFO } from './build-info.js';
import { isRecordingSupported } from './features/video-recording.js';

/**
 * Cleanup handler for page unload.
 * Releases GPU resources and stops animation to prevent contention on rapid refresh.
 *
 * On Firefox, rapid page refreshes can cause GPU resource contention
 * and WASM panics if resources aren't properly released. This handler ensures:
 * 1. Animation loop is stopped (prevents new frames during cleanup)
 * 2. Frame scheduler is destroyed (releases MessageChannel ports)
 * 3. WASM resources are disposed (releases GPU buffers and textures)
 */
export function setupCleanupHandler() {
    window.addEventListener('beforeunload', () => {
        try {
            stopAnimation();
        } catch (e) {
            // Ignore errors during cleanup
        }

        try {
            const scheduler = getFrameScheduler();
            scheduler.destroy();
        } catch (e) {
            // Ignore errors during cleanup
        }

        disposeStatsBuffer();

        const rource = getRource();
        if (rource) {
            try {
                rource.dispose();
                console.log('Rource: Resources cleared, awaiting garbage collection');
            } catch (e) {
                // Ignore errors during cleanup
            }
            setRource(null);
        }
    });

    window.addEventListener('pagehide', (event) => {
        if (event.persisted) {
            console.log('Rource: Page cached for back-forward navigation');
            return;
        }

        try {
            stopAnimation();
        } catch (e) {
            // Ignore errors during cleanup
        }

        try {
            const scheduler = getFrameScheduler();
            scheduler.destroy();
        } catch (e) {
            // Ignore errors during cleanup
        }

        disposeStatsBuffer();

        const rource = getRource();
        if (rource) {
            try {
                rource.dispose();
            } catch (e) {
                // Ignore errors during cleanup
            }
            setRource(null);
        }
    });

    // Page Visibility handling is done in window-events.js (Level 1 power management).
    // It stops the animation loop when the tab is hidden and restores it when visible.
}

/**
 * Creates Rource instance with retry logic.
 * Handles GPU resource contention from rapid page refreshes.
 *
 * @param {HTMLCanvasElement} canvas - The canvas element
 * @param {number} maxRetries - Maximum retry attempts (default: 3)
 * @param {number} baseDelay - Base delay in ms (default: 100)
 * @returns {Promise<Object>} Rource instance
 */
export async function createRourceWithRetry(canvas, maxRetries = 3, baseDelay = 100) {
    let lastError = null;

    for (let attempt = 0; attempt <= maxRetries; attempt++) {
        try {
            if (attempt > 0) {
                const delay = baseDelay * Math.pow(2, attempt - 1);
                console.log(`Rource: Retry attempt ${attempt}/${maxRetries} after ${delay}ms...`);
                await new Promise(resolve => setTimeout(resolve, delay));
            }

            const rource = await Rource.create(canvas);
            if (attempt > 0) {
                console.log(`Rource: Successfully initialized on attempt ${attempt + 1}`);
            }
            return rource;
        } catch (error) {
            lastError = error;
            console.warn(`Rource: Initialization attempt ${attempt + 1} failed:`, error.message || error);

            if (attempt === maxRetries) {
                throw lastError;
            }
        }
    }

    throw lastError || new Error('Failed to create Rource instance');
}

/**
 * Update DOM elements with build info (WASM size, test count, etc.)
 */
export function updateBuildInfo() {
    const sizeText = `~${BUILD_INFO.wasmGzipKB}KB`;

    const featureSize = document.getElementById('feature-wasm-size');
    if (featureSize) featureSize.textContent = sizeText;

    const techSize = document.getElementById('tech-wasm-size');
    if (techSize) techSize.textContent = sizeText;

    const techTests = document.getElementById('tech-tests');
    if (techTests) techTests.textContent = BUILD_INFO.testCount.toLocaleString();

    const techCrates = document.getElementById('tech-crates');
    if (techCrates) techCrates.textContent = BUILD_INFO.crateCount;
}

/**
 * Enables controls after initialization.
 * @param {Object} elements - DOM elements
 */
export function enableControls(elements) {
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
    if (elements.btnLoad) elements.btnLoad.disabled = false;
    if (elements.btnFetchGithub) elements.btnFetchGithub.disabled = false;
    if (elements.btnVisualizeRource) elements.btnVisualizeRource.disabled = false;
}

/**
 * Global debug function for verifying backend detection.
 * @returns {Object} Backend information for testing/verification
 */
export function getBackendInfo() {
    const rource = getRource();
    if (!rource) {
        return { error: 'Rource not initialized' };
    }

    const info = {
        backend: rource.getRendererType(),
        isGpuAccelerated: rource.isGPUAccelerated(),
        isWgpu: rource.isWgpu(),
        isWebGL2: rource.isWebGL2(),
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
        isConsistent: false,
    };

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
