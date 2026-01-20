/**
 * Rource - Animation Loop & Canvas Management
 *
 * Handles the main render loop, canvas resizing, and performance metrics.
 */

import { CONFIG } from './config.js';
import { getElement, getAllElements } from './dom.js';
import { getRource, getAnimationId, setAnimationId, hasData, setState, get } from './state.js';
import { safeWasmCall } from './wasm-api.js';
import { debounce } from './utils.js';

// Performance metrics update counter
let perfUpdateCounter = 0;

// UI update callback (set by main module)
let uiUpdateCallback = null;

/**
 * Sets the UI update callback function.
 * @param {Function} callback - Function to call after each frame
 */
export function setUIUpdateCallback(callback) {
    uiUpdateCallback = callback;
}

/**
 * Resizes the canvas to fit its container.
 */
export function resizeCanvas() {
    const canvas = getElement('canvas');
    const container = document.getElementById('canvas-container');
    if (!canvas || !container) return;

    const rect = container.getBoundingClientRect();
    const width = Math.floor(rect.width);
    const height = Math.floor(rect.height);

    if (canvas.width !== width || canvas.height !== height) {
        canvas.width = width;
        canvas.height = height;
        const rource = getRource();
        if (rource) {
            safeWasmCall('resize', () => rource.resize(width, height), undefined);
            safeWasmCall('forceRender', () => rource.forceRender(), undefined);
        }
    }
}

/**
 * Debounced version of resizeCanvas for window resize events.
 */
export const debouncedResize = debounce(resizeCanvas, CONFIG.DEBOUNCE_DELAY_MS);

/**
 * Main animation loop.
 * @param {number} timestamp - Frame timestamp from requestAnimationFrame
 */
export function animate(timestamp) {
    const rource = getRource();

    if (rource) {
        safeWasmCall('frame', () => rource.frame(timestamp), undefined);

        // Call UI update callback if set
        if (uiUpdateCallback) {
            uiUpdateCallback();
        }

        // Update performance metrics periodically
        perfUpdateCounter++;
        if (perfUpdateCounter >= CONFIG.PERF_UPDATE_INTERVAL) {
            updatePerfMetrics();
            perfUpdateCounter = 0;
        }
    }

    setAnimationId(requestAnimationFrame(animate));
}

/**
 * Starts the animation loop.
 */
export function startAnimation() {
    if (getAnimationId() === null) {
        setAnimationId(requestAnimationFrame(animate));
    }
}

/**
 * Stops the animation loop.
 */
export function stopAnimation() {
    const animationId = getAnimationId();
    if (animationId !== null) {
        cancelAnimationFrame(animationId);
        setAnimationId(null);
    }
}

/**
 * Checks if animation is running.
 * @returns {boolean} True if animation is running
 */
export function isAnimating() {
    return getAnimationId() !== null;
}

/**
 * Checks if visualization is at the end.
 * @returns {boolean} True if at end
 */
export function isAtEnd() {
    const rource = getRource();
    if (!rource) return false;

    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    return total > 0 && current >= total - 1;
}

/**
 * Updates performance metrics overlay.
 */
export function updatePerfMetrics() {
    const rource = getRource();
    if (!rource || !hasData()) return;

    const elements = getAllElements();
    const { perfFps, perfFrameTime, perfEntities, perfVisible, perfDraws, perfResolution } = elements;

    if (!perfFps) return;

    try {
        // Get FPS and frame time
        const fps = safeWasmCall('getFps', () => rource.getFps(), 0);
        const frameTimeMs = safeWasmCall('getFrameTimeMs', () => rource.getFrameTimeMs(), 0);

        // Get render statistics
        const totalEntities = safeWasmCall('getTotalEntities', () => rource.getTotalEntities(), 0);
        const visibleFiles = safeWasmCall('getVisibleFiles', () => rource.getVisibleFiles(), 0);
        const visibleUsers = safeWasmCall('getVisibleUsers', () => rource.getVisibleUsers(), 0);
        const visibleDirs = safeWasmCall('getVisibleDirectories', () => rource.getVisibleDirectories(), 0);
        const drawCalls = safeWasmCall('getDrawCalls', () => rource.getDrawCalls(), 0);
        const width = safeWasmCall('getCanvasWidth', () => rource.getCanvasWidth(), 0);
        const height = safeWasmCall('getCanvasHeight', () => rource.getCanvasHeight(), 0);

        // Update FPS display with color coding and playback status
        const fpsRounded = Math.round(fps);
        const isPlaying = safeWasmCall('isPlaying', () => rource.isPlaying(), false);
        const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
        const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
        const isComplete = current >= total - 1 && !isPlaying;

        if (isComplete) {
            perfFps.textContent = `Complete`;
            perfFps.className = 'perf-fps complete';
        } else if (!isPlaying) {
            perfFps.textContent = `Paused`;
            perfFps.className = 'perf-fps paused';
        } else {
            perfFps.textContent = `${fpsRounded} FPS`;
            perfFps.className = 'perf-fps ' + (fpsRounded >= 55 ? 'good' : fpsRounded >= 30 ? 'ok' : 'bad');
        }

        // Update other metrics
        if (perfFrameTime) perfFrameTime.textContent = `${frameTimeMs.toFixed(1)}ms`;
        if (perfEntities) perfEntities.textContent = totalEntities.toLocaleString();
        if (perfVisible) perfVisible.textContent = `${visibleFiles + visibleUsers + visibleDirs}`;
        if (perfDraws) perfDraws.textContent = drawCalls.toString();
        if (perfResolution) perfResolution.textContent = `${width}×${height}`;
    } catch {
        // WASM methods may not be available during initialization or context loss
        // Show placeholder values instead of crashing
        if (perfFps) {
            perfFps.textContent = '--';
            perfFps.className = 'perf-fps';
        }
        if (perfFrameTime) perfFrameTime.textContent = '--';
        if (perfEntities) perfEntities.textContent = '--';
        if (perfVisible) perfVisible.textContent = '--';
        if (perfDraws) perfDraws.textContent = '--';
    }
}

/**
 * Updates playback UI (play button, timeline).
 */
export function updatePlaybackUI() {
    const rource = getRource();
    if (!rource) return;

    const elements = getAllElements();
    const { btnPlayMain, playIconMain, timelineSlider, timelineInfo } = elements;

    if (!btnPlayMain || !playIconMain) return;

    const playing = safeWasmCall('isPlaying', () => rource.isPlaying(), false);
    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    const atEnd = total > 0 && current >= total - 1 && !playing;

    // Update play button icon - show replay icon when at end
    const pauseIcon = '<rect x="6" y="4" width="4" height="16"/><rect x="14" y="4" width="4" height="16"/>';
    const playIconPath = '<path d="M8 5v14l11-7z"/>';
    const replayIcon = '<path d="M12 5V1L7 6l5 5V7c3.31 0 6 2.69 6 6s-2.69 6-6 6-6-2.69-6-6H4c0 4.42 3.58 8 8 8s8-3.58 8-8-3.58-8-8-8z"/>';

    if (playing) {
        playIconMain.innerHTML = pauseIcon;
        btnPlayMain.title = 'Pause (Space)';
        btnPlayMain.classList.add('active');
        btnPlayMain.classList.remove('replay');
    } else if (atEnd) {
        playIconMain.innerHTML = replayIcon;
        btnPlayMain.title = 'Replay from start (Space)';
        btnPlayMain.classList.remove('active');
        btnPlayMain.classList.add('replay');
    } else {
        playIconMain.innerHTML = playIconPath;
        btnPlayMain.title = 'Play (Space)';
        btnPlayMain.classList.remove('active');
        btnPlayMain.classList.remove('replay');
    }

    // Update timeline
    if (timelineSlider && timelineInfo) {
        if (total > 0) {
            timelineSlider.max = total - 1;
            timelineSlider.value = Math.min(current, total - 1);
            timelineSlider.disabled = false;
            const displayCurrent = Math.min(current + 1, total);
            timelineInfo.textContent = `${displayCurrent} / ${total}`;
            timelineSlider.setAttribute('aria-valuetext', `${displayCurrent} of ${total} commits`);
        } else {
            timelineSlider.max = 0;
            timelineSlider.value = 0;
            timelineSlider.disabled = true;
            timelineInfo.textContent = '0 / 0';
            timelineSlider.setAttribute('aria-valuetext', '0 of 0 commits');
        }
    }
}

/**
 * Initializes animation-related event listeners.
 */
export function initAnimation() {
    // Handle window resize
    window.addEventListener('resize', debouncedResize);

    // Initial resize
    resizeCanvas();
}
