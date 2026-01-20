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

// Animation generation counter to prevent race conditions during restart
// When restartAnimation() is called mid-frame, the old animate() call should not schedule next frame
let animationGeneration = 0;

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

// Track uncapped mode timeout ID separately
let uncappedTimeoutId = null;

/**
 * Main animation loop.
 * @param {number} timestamp - Frame timestamp from requestAnimationFrame (or performance.now() in uncapped mode)
 * @param {number} [generation] - Animation generation to detect restarts during execution
 */
export function animate(timestamp, generation = animationGeneration) {
    // If animation was restarted while this frame was executing, don't schedule next frame
    if (generation !== animationGeneration) {
        return;
    }

    const rource = getRource();
    const isUncapped = get('uncappedFps');

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

    // Check generation again before scheduling - animation might have been stopped during frame processing
    if (generation !== animationGeneration) {
        return;
    }

    // Schedule next frame based on mode
    if (isUncapped) {
        // Uncapped mode: use setTimeout(0) to run as fast as possible
        // Note: browsers typically clamp setTimeout to ~4ms minimum
        uncappedTimeoutId = setTimeout(() => animate(performance.now(), generation), 0);
        setAnimationId(uncappedTimeoutId);
    } else {
        setAnimationId(requestAnimationFrame((ts) => animate(ts, generation)));
    }
}

/**
 * Restarts the animation loop (used when switching between capped/uncapped modes).
 */
export function restartAnimation() {
    // stopAnimation() increments generation, which invalidates any currently executing animate() calls
    stopAnimation();
    startAnimation();
}

/**
 * Starts the animation loop.
 */
export function startAnimation() {
    if (getAnimationId() === null) {
        const isUncapped = get('uncappedFps');
        const generation = animationGeneration;
        if (isUncapped) {
            uncappedTimeoutId = setTimeout(() => animate(performance.now(), generation), 0);
            setAnimationId(uncappedTimeoutId);
        } else {
            setAnimationId(requestAnimationFrame((ts) => animate(ts, generation)));
        }
    }
}

/**
 * Stops the animation loop.
 */
export function stopAnimation() {
    // Increment generation to invalidate any currently executing animate() calls
    animationGeneration++;
    const animationId = getAnimationId();
    if (animationId !== null) {
        // Clear both types of animation scheduling
        cancelAnimationFrame(animationId);
        clearTimeout(animationId);
        if (uncappedTimeoutId !== null) {
            clearTimeout(uncappedTimeoutId);
            uncappedTimeoutId = null;
        }
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
        const isUncapped = get('uncappedFps');

        if (isComplete) {
            perfFps.textContent = `Complete`;
            perfFps.className = 'perf-fps complete';
        } else if (!isPlaying) {
            perfFps.textContent = `Paused`;
            perfFps.className = 'perf-fps paused';
        } else if (isUncapped) {
            // In uncapped mode, show FPS with special styling
            perfFps.textContent = `${fpsRounded} FPS`;
            perfFps.className = 'perf-fps uncapped';
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
 * Formats a Unix timestamp to a readable date string.
 * @param {number} timestamp - Unix timestamp in seconds
 * @param {boolean} short - If true, use short format (e.g., "Jan 20")
 * @returns {string} Formatted date string
 */
function formatDate(timestamp, short = false) {
    if (!timestamp || timestamp <= 0) return '--';
    const date = new Date(timestamp * 1000);
    if (short) {
        return date.toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
    }
    return date.toLocaleDateString(undefined, {
        year: 'numeric',
        month: 'short',
        day: 'numeric'
    });
}

/**
 * Formats a Unix timestamp to a date with optional time.
 * @param {number} timestamp - Unix timestamp in seconds
 * @returns {string} Formatted date and time string
 */
function formatDateTime(timestamp) {
    if (!timestamp || timestamp <= 0) return '--';
    const date = new Date(timestamp * 1000);
    return date.toLocaleDateString(undefined, {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
        hour: '2-digit',
        minute: '2-digit'
    });
}

/**
 * Updates playback UI (play button, timeline).
 */
export function updatePlaybackUI() {
    const rource = getRource();
    if (!rource) return;

    const elements = getAllElements();
    const {
        btnPlayMain, playIconMain, timelineSlider, timelineInfoNumbers,
        timelineDate, timelineCommitInfo, timelineStartDate, timelineEndDate
    } = elements;

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

    // Update timeline slider and commit numbers
    if (timelineSlider && timelineInfoNumbers) {
        if (total > 0) {
            timelineSlider.max = total - 1;
            timelineSlider.value = Math.min(current, total - 1);
            timelineSlider.disabled = false;
            const displayCurrent = Math.min(current + 1, total);
            timelineInfoNumbers.textContent = `${displayCurrent} / ${total}`;
            timelineSlider.setAttribute('aria-valuetext', `Commit ${displayCurrent} of ${total}`);
        } else {
            timelineSlider.max = 0;
            timelineSlider.value = 0;
            timelineSlider.disabled = true;
            timelineInfoNumbers.textContent = '0 / 0';
            timelineSlider.setAttribute('aria-valuetext', '0 of 0 commits');
        }
    }

    // Update current commit date display
    if (timelineDate && total > 0) {
        const currentIndex = Math.min(current, total - 1);
        const timestamp = safeWasmCall('getCommitTimestamp', () => rource.getCommitTimestamp(currentIndex), 0);
        timelineDate.textContent = formatDateTime(timestamp);
    } else if (timelineDate) {
        timelineDate.textContent = '--';
    }

    // Update commit info (author and file count)
    if (timelineCommitInfo && total > 0) {
        const currentIndex = Math.min(current, total - 1);
        const author = safeWasmCall('getCommitAuthor', () => rource.getCommitAuthor(currentIndex), '');
        const fileCount = safeWasmCall('getCommitFileCount', () => rource.getCommitFileCount(currentIndex), 0);
        if (author) {
            const filesText = fileCount === 1 ? '1 file' : `${fileCount} files`;
            timelineCommitInfo.textContent = `${author} - ${filesText}`;
        } else {
            timelineCommitInfo.textContent = '';
        }
    } else if (timelineCommitInfo) {
        timelineCommitInfo.textContent = '';
    }

    // Update date range (start and end dates) - only need to do once when data changes
    // We check if the start date shows "--" which indicates it needs updating
    if (timelineStartDate && timelineEndDate && total > 0) {
        if (timelineStartDate.textContent === '--') {
            const startTimestamp = safeWasmCall('getCommitTimestamp', () => rource.getCommitTimestamp(0), 0);
            const endTimestamp = safeWasmCall('getCommitTimestamp', () => rource.getCommitTimestamp(total - 1), 0);
            timelineStartDate.textContent = formatDate(startTimestamp, true);
            timelineEndDate.textContent = formatDate(endTimestamp, true);
        }
    } else if (timelineStartDate && timelineEndDate) {
        timelineStartDate.textContent = '--';
        timelineEndDate.textContent = '--';
    }
}

/**
 * Resets the timeline date range labels.
 * Call this when new data is loaded to force re-calculation of date range.
 */
export function resetTimelineDateLabels() {
    const elements = getAllElements();
    const { timelineStartDate, timelineEndDate, timelineDate, timelineCommitInfo } = elements;

    if (timelineStartDate) timelineStartDate.textContent = '--';
    if (timelineEndDate) timelineEndDate.textContent = '--';
    if (timelineDate) timelineDate.textContent = '--';
    if (timelineCommitInfo) timelineCommitInfo.textContent = '';
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
