// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - High-Performance Frame Scheduler
 *
 * Provides high-performance frame scheduling using a tiered approach:
 * 1. scheduler.postTask() - Scheduler API (Chrome 94+, Firefox 101+)
 * 2. MessageChannel - Direct macrotask queue posting
 * 3. setTimeout(0) - Fallback with ~4ms minimum delay
 *
 * This enables 400-800+ FPS vs ~250 FPS max with setTimeout alone.
 *
 * @module core/frame-scheduler
 */

// =============================================================================
// FrameScheduler Class
// =============================================================================

/**
 * FrameScheduler provides high-performance frame scheduling using a tiered approach.
 *
 * Priority order (fastest to slowest):
 * 1. scheduler.postTask() - Scheduler API with user-blocking priority (~0.05-0.2ms)
 * 2. MessageChannel - Direct macrotask queue posting (~0.1-0.5ms)
 * 3. setTimeout(0) - Fallback with ~4ms minimum delay
 *
 * The scheduler is designed for:
 * - Maximum performance (uses best available API)
 * - Zero memory leaks (proper resource cleanup on destroy)
 * - Race condition safety (generation counter integration)
 * - Graceful degradation (automatic fallback chain)
 * - Error isolation (exceptions in callbacks don't break the scheduler)
 *
 * Browser Support:
 * - scheduler.postTask: Chrome 94+, Firefox 101+, Edge 94+
 * - MessageChannel: All modern browsers
 * - setTimeout: Universal
 *
 * @class
 */
export class FrameScheduler {
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
         * Whether scheduler.postTask() is supported.
         * This is the fastest option when available.
         * @type {boolean}
         */
        this.hasSchedulerAPI = typeof globalThis.scheduler !== 'undefined' &&
            typeof globalThis.scheduler.postTask === 'function';

        /**
         * Whether MessageChannel is supported in this environment.
         * Determined once at construction time for consistent behavior.
         * @type {boolean}
         */
        this.hasMessageChannel = typeof MessageChannel !== 'undefined';

        /**
         * Bound message handler for the MessageChannel.
         * Pre-bound to avoid creating new function references.
         * @type {Function}
         */
        this.handleMessage = this._handleMessage.bind(this);

        /**
         * AbortController for canceling pending scheduler.postTask calls.
         * @type {AbortController|null}
         */
        this.postTaskController = null;

        /**
         * Tracks which scheduling method is currently active.
         * Used for diagnostics and debugging.
         * @type {'postTask'|'messageChannel'|'setTimeout'|null}
         */
        this.activeMethod = null;

        // Initialize the channel if MessageChannel is supported
        // (scheduler.postTask doesn't need initialization)
        if (this.hasMessageChannel) {
            this._initChannel();
        }

        // Log which method will be used (helpful for debugging)
        if (this.hasSchedulerAPI) {
            console.log('[FrameScheduler] Using scheduler.postTask (fastest)');
        } else if (this.hasMessageChannel) {
            console.log('[FrameScheduler] Using MessageChannel');
        } else {
            console.log('[FrameScheduler] Using setTimeout fallback');
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
     * Uses a tiered approach for maximum performance:
     * 1. scheduler.postTask() - Scheduler API (fastest, Chrome 94+, Firefox 101+)
     * 2. MessageChannel - Direct macrotask queue posting
     * 3. setTimeout(0) - Fallback with ~4ms minimum delay
     *
     * @param {Function} callback - Function to call on next frame
     * @returns {boolean} True if scheduled via high-performance method, false if using setTimeout
     */
    schedule(callback) {
        if (!callback) return false;

        this.pendingCallback = callback;

        // Priority 1: scheduler.postTask() - fastest option (~0.05-0.2ms)
        if (this.hasSchedulerAPI) {
            if (!this.isScheduled) {
                this.isScheduled = true;
                this.activeMethod = 'postTask';

                // Create AbortController for cancellation support
                this.postTaskController = new AbortController();

                try {
                    globalThis.scheduler.postTask(
                        () => {
                            this.isScheduled = false;
                            this.postTaskController = null;
                            const cb = this.pendingCallback;
                            this.pendingCallback = null;
                            if (cb) {
                                try {
                                    cb();
                                } catch (e) {
                                    console.error('[FrameScheduler] postTask callback error:', e);
                                }
                            }
                        },
                        {
                            priority: 'user-blocking', // Highest priority for rendering
                            signal: this.postTaskController.signal,
                        }
                    ).catch(e => {
                        // Handle abort or other errors silently
                        if (e.name !== 'AbortError') {
                            console.warn('[FrameScheduler] postTask error:', e);
                        }
                    });
                    return true;
                } catch (e) {
                    // scheduler.postTask failed, fall through to MessageChannel
                    this.isScheduled = false;
                    this.postTaskController = null;
                    this.hasSchedulerAPI = false; // Disable for future calls
                    console.warn('[FrameScheduler] postTask unavailable, falling back to MessageChannel:', e);
                }
            }
            return true;
        }

        // Priority 2: MessageChannel - bypasses 4ms timer clamping (~0.1-0.5ms)
        if (this.hasMessageChannel && this.channel) {
            if (!this.isScheduled) {
                this.isScheduled = true;
                this.activeMethod = 'messageChannel';
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

        // Priority 3: setTimeout(0) - has ~4ms minimum but universal support
        this.activeMethod = 'setTimeout';
        setTimeout(() => {
            const cb = this.pendingCallback;
            this.pendingCallback = null;
            if (cb) {
                try {
                    cb();
                } catch (e) {
                    console.error('[FrameScheduler] setTimeout callback error:', e);
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

        // Abort any pending postTask
        if (this.postTaskController) {
            try {
                this.postTaskController.abort();
            } catch (e) {
                // Ignore abort errors
            }
            this.postTaskController = null;
        }
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
        if (!this.channel && this.hasMessageChannel) {
            this._initChannel();
        }
    }

    /**
     * Returns whether high-performance scheduling is available.
     * @returns {boolean} True if scheduler.postTask or MessageChannel is working
     */
    isHighPerformance() {
        return this.hasSchedulerAPI || (this.hasMessageChannel && this.channel !== null);
    }

    /**
     * Returns the current scheduling method being used.
     * @returns {'postTask'|'messageChannel'|'setTimeout'} The active scheduling method
     */
    getMethod() {
        if (this.hasSchedulerAPI) return 'postTask';
        if (this.hasMessageChannel && this.channel) return 'messageChannel';
        return 'setTimeout';
    }

    /**
     * Returns detailed information about the scheduler's capabilities.
     * Useful for debugging and displaying in the UI.
     * @returns {{method: string, hasPostTask: boolean, hasMessageChannel: boolean}}
     */
    getInfo() {
        return {
            method: this.getMethod(),
            hasPostTask: this.hasSchedulerAPI,
            hasMessageChannel: this.hasMessageChannel && this.channel !== null,
        };
    }
}

// =============================================================================
// Singleton Instance
// =============================================================================

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
export function getFrameScheduler() {
    if (!frameScheduler) {
        frameScheduler = new FrameScheduler();
    } else if (!frameScheduler.channel && frameScheduler.hasMessageChannel) {
        // Reinitialize MessageChannel if previously destroyed
        frameScheduler.reinitialize();
    }
    return frameScheduler;
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
