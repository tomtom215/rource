/**
 * Rource - Animation Loop & Canvas Management
 *
 * Handles the main render loop, canvas resizing, and performance metrics.
 *
 * Performance Optimization: MessageChannel for Uncapped Mode
 * ----------------------------------------------------------
 * In uncapped FPS mode, we use MessageChannel instead of setTimeout(0) for
 * frame scheduling. This bypasses the browser's 4ms minimum timer clamping,
 * enabling significantly higher frame rates (300-500+ FPS vs ~250 FPS max).
 *
 * MessageChannel posts messages to the macrotask queue without timer overhead,
 * making it ideal for high-performance animation loops where vsync is disabled.
 *
 * Fallback: If MessageChannel is unavailable (extremely rare in modern browsers),
 * we gracefully fall back to setTimeout(0).
 */

import { CONFIG } from './config.js';
import { getElement, getAllElements } from './dom.js';
import { getRource, getAnimationId, setAnimationId, hasData, setState, get } from './state.js';
import { safeWasmCall } from './wasm-api.js';
import { debounce } from './utils.js';

// =============================================================================
// Module Constants
// =============================================================================

/**
 * Pre-allocated SVG icon strings to avoid allocations in hot path.
 * These are used for the play/pause/replay button states.
 */
const ICON_PAUSE = '<rect x="6" y="4" width="4" height="16"/><rect x="14" y="4" width="4" height="16"/>';
const ICON_PLAY = '<path d="M8 5v14l11-7z"/>';
const ICON_REPLAY = '<path d="M12 5V1L7 6l5 5V7c3.31 0 6 2.69 6 6s-2.69 6-6 6-6-2.69-6-6H4c0 4.42 3.58 8 8 8s8-3.58 8-8-3.58-8-8-8z"/>';

// =============================================================================
// High-Performance Frame Scheduler (MessageChannel)
// =============================================================================

/**
 * FrameScheduler provides high-performance frame scheduling using MessageChannel.
 *
 * Why MessageChannel over setTimeout(0)?
 * - setTimeout(0) is clamped to ~4ms minimum in browsers (HTML5 spec)
 * - MessageChannel posts directly to macrotask queue with ~0.1-0.5ms overhead
 * - This enables 3-4x higher uncapped FPS (theoretical ~800 FPS vs ~250 FPS)
 *
 * The scheduler is designed for:
 * - Zero memory leaks (proper port cleanup on destroy)
 * - Race condition safety (generation counter integration)
 * - Graceful degradation (falls back to setTimeout if MessageChannel unavailable)
 * - Error isolation (exceptions in callbacks don't break the scheduler)
 *
 * @class
 */
class FrameScheduler {
    constructor() {
        /**
         * The MessageChannel instance for high-performance scheduling.
         * @type {MessageChannel|null}
         */
        this.channel = null;

        /**
         * Pending frame callback to be invoked on next message.
         * @type {Function|null}
         */
        this.pendingCallback = null;

        /**
         * Whether the scheduler is currently active (has a pending frame).
         * Used to prevent duplicate scheduling.
         * @type {boolean}
         */
        this.isScheduled = false;

        /**
         * Whether MessageChannel is supported in this environment.
         * Determined once at construction time for consistent behavior.
         * @type {boolean}
         */
        this.isSupported = typeof MessageChannel !== 'undefined';

        /**
         * Bound message handler for the MessageChannel.
         * Pre-bound to avoid creating new function references.
         * @type {Function}
         */
        this.handleMessage = this._handleMessage.bind(this);

        // Initialize the channel if supported
        if (this.isSupported) {
            this._initChannel();
        }
    }

    /**
     * Initializes the MessageChannel and sets up the message handler.
     * @private
     */
    _initChannel() {
        try {
            this.channel = new MessageChannel();
            this.channel.port1.onmessage = this.handleMessage;
            // Start the port to enable message receiving
            this.channel.port1.start();
        } catch (e) {
            // MessageChannel construction failed (should be extremely rare)
            // Mark as unsupported to use fallback
            console.warn('[FrameScheduler] MessageChannel initialization failed, using setTimeout fallback:', e);
            this.isSupported = false;
            this.channel = null;
        }
    }

    /**
     * Handles incoming messages from the MessageChannel.
     * This is the hot path for frame execution.
     * @private
     */
    _handleMessage() {
        this.isScheduled = false;
        const callback = this.pendingCallback;
        this.pendingCallback = null;

        if (callback) {
            try {
                callback();
            } catch (e) {
                // Isolate callback errors from the scheduler
                // This prevents a bug in the animation loop from breaking the scheduler
                console.error('[FrameScheduler] Callback error:', e);
            }
        }
    }

    /**
     * Schedules a callback to run as soon as possible.
     *
     * If MessageChannel is available, posts a message to trigger the callback.
     * Otherwise, falls back to setTimeout(0).
     *
     * @param {Function} callback - Function to call on next frame
     * @returns {boolean} True if scheduled via MessageChannel, false if using fallback
     */
    schedule(callback) {
        if (!callback) return false;

        this.pendingCallback = callback;

        if (this.isSupported && this.channel) {
            if (!this.isScheduled) {
                this.isScheduled = true;
                try {
                    this.channel.port2.postMessage(null);
                    return true;
                } catch (e) {
                    // Port might be closed or in invalid state
                    // Fall through to setTimeout fallback
                    this.isScheduled = false;
                }
            }
            return true;
        }

        // Fallback: setTimeout(0) - still has ~4ms minimum but better than nothing
        setTimeout(() => {
            const cb = this.pendingCallback;
            this.pendingCallback = null;
            if (cb) {
                try {
                    cb();
                } catch (e) {
                    console.error('[FrameScheduler] Fallback callback error:', e);
                }
            }
        }, 0);
        return false;
    }

    /**
     * Cancels any pending scheduled callback.
     * Safe to call multiple times or when nothing is scheduled.
     */
    cancel() {
        this.pendingCallback = null;
        this.isScheduled = false;
    }

    /**
     * Destroys the scheduler and releases all resources.
     *
     * IMPORTANT: Call this when the scheduler is no longer needed to prevent
     * memory leaks. The MessageChannel ports must be explicitly closed.
     */
    destroy() {
        this.cancel();

        if (this.channel) {
            try {
                // Remove event handler first to prevent any final message processing
                this.channel.port1.onmessage = null;
                // Close both ports to release resources
                this.channel.port1.close();
                this.channel.port2.close();
            } catch (e) {
                // Ports might already be closed, ignore errors
            }
            this.channel = null;
        }
    }

    /**
     * Recreates the MessageChannel after it was destroyed.
     * Useful when restarting the animation after a full stop.
     */
    reinitialize() {
        if (!this.channel && this.isSupported) {
            this._initChannel();
        }
    }

    /**
     * Returns whether high-performance scheduling is available.
     * @returns {boolean} True if MessageChannel is working
     */
    isHighPerformance() {
        return this.isSupported && this.channel !== null;
    }
}

/**
 * Singleton frame scheduler instance for the application.
 * Lazily initialized on first use in uncapped mode.
 * @type {FrameScheduler|null}
 */
let frameScheduler = null;

/**
 * Gets or creates the frame scheduler singleton.
 * @returns {FrameScheduler} The frame scheduler instance
 */
function getFrameScheduler() {
    if (!frameScheduler) {
        frameScheduler = new FrameScheduler();
    } else if (!frameScheduler.channel && frameScheduler.isSupported) {
        // Reinitialize if previously destroyed
        frameScheduler.reinitialize();
    }
    return frameScheduler;
}

// =============================================================================
// Module State
// =============================================================================

/** Counter for throttling performance metrics updates. */
let perfUpdateCounter = 0;

/** UI update callback set by main module. */
let uiUpdateCallback = null;

/**
 * Uncapped FPS tracking statistics for peak/average display.
 * Reset when entering uncapped mode or restarting playback.
 */
let uncappedFpsStats = {
    maxFps: 0,
    fpsSum: 0,
    frameCount: 0,
    /** Exponential Moving Average for smoother average display. */
    emaFps: 0,
    /** EMA smoothing factor (lower = smoother, higher = more responsive). */
    emaAlpha: 0.1,
};

/**
 * Cached state to avoid redundant DOM updates.
 * Prevents memory churn from unnecessary innerHTML assignments.
 */
const playbackUICache = {
    playing: null,
    current: -1,
    total: -1,
    atEnd: null,
    lastTimestamp: 0,
    lastAuthor: '',
    lastFileCount: -1,
};

/**
 * Animation generation counter for race condition prevention.
 *
 * When restartAnimation() is called mid-frame, the old animate() call
 * checks this counter and exits without scheduling another frame.
 * This prevents duplicate animation loops from running simultaneously.
 */
let animationGeneration = 0;

/**
 * Legacy timeout ID for cleanup during stop (setTimeout fallback path).
 * @type {number|null}
 */
let legacyTimeoutId = null;

// =============================================================================
// Public API - Callbacks
// =============================================================================

/**
 * Sets the UI update callback function.
 * Called after each frame to update playback controls.
 * @param {Function} callback - Function to call after each frame
 */
export function setUIUpdateCallback(callback) {
    uiUpdateCallback = callback;
}

// =============================================================================
// Canvas Management
// =============================================================================

/**
 * Resizes the canvas to fit its container.
 *
 * This is called on window resize and ensures the canvas dimensions
 * match the container, maintaining proper aspect ratio and resolution.
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
 * Prevents excessive resize calls during window drag operations.
 */
export const debouncedResize = debounce(resizeCanvas, CONFIG.DEBOUNCE_DELAY_MS);

// =============================================================================
// Animation Loop Core
// =============================================================================

/**
 * Main animation loop.
 *
 * This function is called once per frame and handles:
 * 1. WASM frame rendering
 * 2. FPS statistics tracking (in uncapped mode)
 * 3. UI callback invocation
 * 4. Performance metrics updates
 * 5. Scheduling the next frame
 *
 * The generation parameter prevents race conditions when the animation
 * is restarted while a frame is being processed.
 *
 * @param {number} timestamp - Frame timestamp from requestAnimationFrame or performance.now()
 * @param {number} [generation] - Animation generation for race condition detection
 */
export function animate(timestamp, generation = animationGeneration) {
    // Race condition check: if animation was restarted, exit immediately
    if (generation !== animationGeneration) {
        return;
    }

    const rource = getRource();
    const isUncapped = get('uncappedFps');

    if (rource) {
        // Render the frame via WASM
        safeWasmCall('frame', () => rource.frame(timestamp), undefined);

        // Track FPS statistics in uncapped mode for peak/average display
        if (isUncapped) {
            const fps = safeWasmCall('getFps', () => rource.getFps(), 0);
            if (fps > 0) {
                uncappedFpsStats.maxFps = Math.max(uncappedFpsStats.maxFps, fps);
                uncappedFpsStats.fpsSum += fps;
                uncappedFpsStats.frameCount++;

                // Update EMA for smoother average display
                if (uncappedFpsStats.emaFps === 0) {
                    uncappedFpsStats.emaFps = fps;
                } else {
                    uncappedFpsStats.emaFps =
                        uncappedFpsStats.emaAlpha * fps +
                        (1 - uncappedFpsStats.emaAlpha) * uncappedFpsStats.emaFps;
                }
            }
        }

        // Invoke UI update callback if registered
        if (uiUpdateCallback) {
            uiUpdateCallback();
        }

        // Periodically update performance metrics overlay
        perfUpdateCounter++;
        if (perfUpdateCounter >= CONFIG.PERF_UPDATE_INTERVAL) {
            updatePerfMetrics();
            perfUpdateCounter = 0;
        }
    }

    // Second race condition check after frame processing
    // Animation might have been stopped during the render
    if (generation !== animationGeneration) {
        return;
    }

    // Schedule the next frame based on mode
    if (isUncapped) {
        // Uncapped mode: use MessageChannel for minimal scheduling overhead
        // This enables significantly higher FPS than setTimeout(0)'s ~4ms minimum
        const scheduler = getFrameScheduler();
        scheduler.schedule(() => animate(performance.now(), generation));

        // Set a non-null animation ID to indicate animation is running
        // The actual value doesn't matter for MessageChannel mode
        setAnimationId(1);
    } else {
        // Capped mode: use requestAnimationFrame for vsync-aligned rendering
        // This is more power efficient and prevents screen tearing
        setAnimationId(requestAnimationFrame((ts) => animate(ts, generation)));
    }
}

// =============================================================================
// Animation Control
// =============================================================================

/**
 * Restarts the animation loop.
 *
 * Used when switching between capped/uncapped modes or when the
 * animation needs to be fully reset.
 *
 * @param {boolean} [resetStats=true] - Whether to reset FPS tracking statistics
 */
export function restartAnimation(resetStats = true) {
    // stopAnimation() increments generation, invalidating any executing animate() calls
    stopAnimation();
    if (resetStats) {
        resetUncappedFpsStats();
    }
    startAnimation();
}

/**
 * Resets the uncapped FPS tracking statistics.
 *
 * Call this when:
 * - Entering uncapped mode
 * - Restarting playback
 * - Loading new data
 */
export function resetUncappedFpsStats() {
    uncappedFpsStats.maxFps = 0;
    uncappedFpsStats.fpsSum = 0;
    uncappedFpsStats.frameCount = 0;
    uncappedFpsStats.emaFps = 0;
}

/**
 * Gets the current uncapped FPS statistics.
 *
 * @returns {{maxFps: number, avgFps: number, emaFps: number, frameCount: number}}
 *          Statistics object with peak, average, and EMA FPS values
 */
export function getUncappedFpsStats() {
    const avgFps =
        uncappedFpsStats.frameCount > 0
            ? uncappedFpsStats.fpsSum / uncappedFpsStats.frameCount
            : 0;
    return {
        maxFps: uncappedFpsStats.maxFps,
        avgFps: avgFps,
        emaFps: uncappedFpsStats.emaFps,
        frameCount: uncappedFpsStats.frameCount,
    };
}

/**
 * Starts the animation loop.
 *
 * Safe to call multiple times - will not start duplicate loops.
 * Automatically selects the appropriate scheduling method based on
 * the current uncapped FPS mode setting.
 */
export function startAnimation() {
    if (getAnimationId() !== null) {
        // Animation already running
        return;
    }

    const isUncapped = get('uncappedFps');
    const generation = animationGeneration;

    if (isUncapped) {
        // Uncapped mode: use MessageChannel scheduler
        const scheduler = getFrameScheduler();
        scheduler.schedule(() => animate(performance.now(), generation));
        // Set a marker to indicate animation is running
        setAnimationId(1);
    } else {
        // Capped mode: use requestAnimationFrame
        setAnimationId(requestAnimationFrame((ts) => animate(ts, generation)));
    }
}

/**
 * Stops the animation loop.
 *
 * Properly cleans up all scheduling mechanisms:
 * - Increments generation to invalidate any in-flight animate() calls
 * - Cancels requestAnimationFrame
 * - Cancels MessageChannel pending callbacks
 * - Clears any legacy setTimeout fallbacks
 *
 * Safe to call multiple times or when animation is not running.
 */
export function stopAnimation() {
    // Increment generation to invalidate any currently executing animate() calls
    // This is the primary mechanism for preventing race conditions
    animationGeneration++;

    const animationId = getAnimationId();
    if (animationId !== null) {
        // Cancel requestAnimationFrame (safe even if ID is from MessageChannel)
        cancelAnimationFrame(animationId);

        // Cancel MessageChannel pending callbacks
        if (frameScheduler) {
            frameScheduler.cancel();
        }

        // Clear legacy setTimeout fallback if used
        if (legacyTimeoutId !== null) {
            clearTimeout(legacyTimeoutId);
            legacyTimeoutId = null;
        }

        setAnimationId(null);
    }
}

/**
 * Checks if animation is currently running.
 * @returns {boolean} True if animation loop is active
 */
export function isAnimating() {
    return getAnimationId() !== null;
}

/**
 * Checks if visualization has reached the end.
 * @returns {boolean} True if at the last commit
 */
export function isAtEnd() {
    const rource = getRource();
    if (!rource) return false;

    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    return total > 0 && current >= total - 1;
}

/**
 * Returns whether high-performance scheduling is available.
 *
 * This can be used by the UI to indicate when MessageChannel
 * acceleration is active for uncapped mode.
 *
 * @returns {boolean} True if MessageChannel is available and working
 */
export function isHighPerformanceSchedulerAvailable() {
    const scheduler = getFrameScheduler();
    return scheduler.isHighPerformance();
}

// =============================================================================
// Performance Metrics Display
// =============================================================================

/**
 * Updates the performance metrics overlay.
 *
 * Collects various statistics from WASM and updates the DOM.
 * Called periodically (controlled by CONFIG.PERF_UPDATE_INTERVAL) rather
 * than every frame to reduce overhead.
 */
export function updatePerfMetrics() {
    const rource = getRource();
    if (!rource || !hasData()) return;

    const elements = getAllElements();
    const {
        perfFps,
        perfFrameTime,
        perfEntities,
        perfVisible,
        perfDraws,
        perfResolution,
        perfPeakAvgRow,
        perfPeakFps,
        perfAvgFps,
    } = elements;

    if (!perfFps) return;

    try {
        // Get FPS and frame time
        const fps = safeWasmCall('getFps', () => rource.getFps(), 0);
        const frameTimeMs = safeWasmCall('getFrameTimeMs', () => rource.getFrameTimeMs(), 0);

        // Get render statistics
        const totalEntities = safeWasmCall('getTotalEntities', () => rource.getTotalEntities(), 0);
        const visibleFiles = safeWasmCall('getVisibleFiles', () => rource.getVisibleFiles(), 0);
        const visibleUsers = safeWasmCall('getVisibleUsers', () => rource.getVisibleUsers(), 0);
        const visibleDirs = safeWasmCall(
            'getVisibleDirectories',
            () => rource.getVisibleDirectories(),
            0
        );
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
            perfFps.textContent = 'Complete';
            perfFps.className = 'perf-fps complete';
        } else if (!isPlaying) {
            perfFps.textContent = 'Paused';
            perfFps.className = 'perf-fps paused';
        } else if (isUncapped) {
            // In uncapped mode, show FPS with special styling
            perfFps.textContent = `${fpsRounded} FPS`;
            perfFps.className = 'perf-fps uncapped';
        } else {
            perfFps.textContent = `${fpsRounded} FPS`;
            perfFps.className =
                'perf-fps ' + (fpsRounded >= 55 ? 'good' : fpsRounded >= 30 ? 'ok' : 'bad');
        }

        // Update Peak/Avg row visibility and values
        if (perfPeakAvgRow) {
            if (isUncapped && isPlaying) {
                // Show peak/avg row in uncapped mode while playing
                perfPeakAvgRow.classList.remove('hidden');
                const stats = getUncappedFpsStats();
                if (perfPeakFps) perfPeakFps.textContent = Math.round(stats.maxFps);
                if (perfAvgFps) perfAvgFps.textContent = Math.round(stats.emaFps);
            } else {
                // Hide when not in uncapped mode or not playing
                perfPeakAvgRow.classList.add('hidden');
            }
        }

        // Update other metrics
        if (perfFrameTime) perfFrameTime.textContent = `${frameTimeMs.toFixed(1)}ms`;
        if (perfEntities) perfEntities.textContent = totalEntities.toLocaleString();
        if (perfVisible)
            perfVisible.textContent = `${visibleFiles + visibleUsers + visibleDirs}`;
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
        if (perfPeakAvgRow) perfPeakAvgRow.classList.add('hidden');
    }
}

// =============================================================================
// Date Formatting Utilities
// =============================================================================

/**
 * Formats a Unix timestamp to a readable date string.
 *
 * @param {number} timestamp - Unix timestamp in seconds
 * @param {boolean} [short=false] - If true, use short format (e.g., "Jan 20")
 * @returns {string} Formatted date string or '--' if invalid
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
        day: 'numeric',
    });
}

/**
 * Formats a Unix timestamp to a date with time.
 *
 * @param {number} timestamp - Unix timestamp in seconds
 * @returns {string} Formatted date and time string or '--' if invalid
 */
function formatDateTime(timestamp) {
    if (!timestamp || timestamp <= 0) return '--';
    const date = new Date(timestamp * 1000);
    return date.toLocaleDateString(undefined, {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
        hour: '2-digit',
        minute: '2-digit',
    });
}

// =============================================================================
// Playback UI Updates
// =============================================================================

/**
 * Updates playback UI (play button, timeline).
 *
 * Uses caching to avoid redundant DOM updates that cause memory churn.
 * Only updates elements when their values have actually changed.
 */
export function updatePlaybackUI() {
    const rource = getRource();
    if (!rource) return;

    const elements = getAllElements();
    const {
        btnPlayMain,
        playIconMain,
        timelineSlider,
        timelineInfoNumbers,
        timelineDate,
        timelineCommitInfo,
        timelineStartDate,
        timelineEndDate,
    } = elements;

    if (!btnPlayMain || !playIconMain) return;

    const playing = safeWasmCall('isPlaying', () => rource.isPlaying(), false);
    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    const atEnd = total > 0 && current >= total - 1 && !playing;

    // Only update play button if state changed (avoids innerHTML allocation)
    if (playing !== playbackUICache.playing || atEnd !== playbackUICache.atEnd) {
        playbackUICache.playing = playing;
        playbackUICache.atEnd = atEnd;

        if (playing) {
            playIconMain.innerHTML = ICON_PAUSE;
            btnPlayMain.title = 'Pause (Space)';
            btnPlayMain.classList.add('active');
            btnPlayMain.classList.remove('replay');
        } else if (atEnd) {
            playIconMain.innerHTML = ICON_REPLAY;
            btnPlayMain.title = 'Replay from start (Space)';
            btnPlayMain.classList.remove('active');
            btnPlayMain.classList.add('replay');
        } else {
            playIconMain.innerHTML = ICON_PLAY;
            btnPlayMain.title = 'Play (Space)';
            btnPlayMain.classList.remove('active');
            btnPlayMain.classList.remove('replay');
        }
    }

    // Only update timeline if current or total changed
    const currentChanged = current !== playbackUICache.current;
    const totalChanged = total !== playbackUICache.total;

    if (timelineSlider && timelineInfoNumbers && (currentChanged || totalChanged)) {
        playbackUICache.current = current;
        playbackUICache.total = total;

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

    // Only fetch commit details if current index changed
    if (currentChanged && total > 0) {
        const currentIndex = Math.min(current, total - 1);
        const timestamp = safeWasmCall(
            'getCommitTimestamp',
            () => rource.getCommitTimestamp(currentIndex),
            0
        );

        // Only update date display if timestamp changed
        if (timestamp !== playbackUICache.lastTimestamp) {
            playbackUICache.lastTimestamp = timestamp;
            if (timelineDate) {
                timelineDate.textContent = formatDateTime(timestamp);
            }
        }

        // Only update commit info if changed
        if (timelineCommitInfo) {
            const author = safeWasmCall(
                'getCommitAuthor',
                () => rource.getCommitAuthor(currentIndex),
                ''
            );
            const fileCount = safeWasmCall(
                'getCommitFileCount',
                () => rource.getCommitFileCount(currentIndex),
                0
            );

            if (
                author !== playbackUICache.lastAuthor ||
                fileCount !== playbackUICache.lastFileCount
            ) {
                playbackUICache.lastAuthor = author;
                playbackUICache.lastFileCount = fileCount;

                if (author) {
                    const filesText = fileCount === 1 ? '1 file' : `${fileCount} files`;
                    timelineCommitInfo.textContent = `${author} - ${filesText}`;
                } else {
                    timelineCommitInfo.textContent = '';
                }
            }
        }
    } else if (currentChanged && total === 0) {
        // Clear displays when no data
        if (timelineDate) timelineDate.textContent = '--';
        if (timelineCommitInfo) timelineCommitInfo.textContent = '';
    }

    // Update date range (start and end dates) - only need to do once when data changes
    // We check if the start date shows "--" which indicates it needs updating
    if (timelineStartDate && timelineEndDate && total > 0) {
        if (timelineStartDate.textContent === '--') {
            const startTimestamp = safeWasmCall(
                'getCommitTimestamp',
                () => rource.getCommitTimestamp(0),
                0
            );
            const endTimestamp = safeWasmCall(
                'getCommitTimestamp',
                () => rource.getCommitTimestamp(total - 1),
                0
            );
            timelineStartDate.textContent = formatDate(startTimestamp, true);
            timelineEndDate.textContent = formatDate(endTimestamp, true);
        }
    } else if (timelineStartDate && timelineEndDate && totalChanged && total === 0) {
        timelineStartDate.textContent = '--';
        timelineEndDate.textContent = '--';
    }
}

/**
 * Resets the timeline date range labels and playback UI cache.
 *
 * Call this when new data is loaded to force re-calculation of date range.
 */
export function resetTimelineDateLabels() {
    const elements = getAllElements();
    const { timelineStartDate, timelineEndDate, timelineDate, timelineCommitInfo } = elements;

    if (timelineStartDate) timelineStartDate.textContent = '--';
    if (timelineEndDate) timelineEndDate.textContent = '--';
    if (timelineDate) timelineDate.textContent = '--';
    if (timelineCommitInfo) timelineCommitInfo.textContent = '';

    // Reset cache to force UI refresh with new data
    playbackUICache.playing = null;
    playbackUICache.current = -1;
    playbackUICache.total = -1;
    playbackUICache.atEnd = null;
    playbackUICache.lastTimestamp = 0;
    playbackUICache.lastAuthor = '';
    playbackUICache.lastFileCount = -1;
}

// =============================================================================
// Initialization
// =============================================================================

/**
 * Initializes animation-related event listeners.
 *
 * Sets up window resize handling and performs initial canvas sizing.
 */
export function initAnimation() {
    // Handle window resize
    window.addEventListener('resize', debouncedResize);

    // Initial resize
    resizeCanvas();
}
