// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Animation Loop Core
 *
 * Handles the main render loop, canvas resizing, and frame scheduling.
 * Coordinates between the FrameScheduler, performance metrics, and UI updates.
 *
 * @module core/animation-loop
 */

import { CONFIG } from '../config.js';
import { getElement } from '../dom.js';
import { getRource, getAnimationId, setAnimationId, get, setState } from '../state.js';
import { safeWasmCall, isWasmHealthy } from '../wasm-api.js';
import { debounce } from '../utils.js';
import { getFrameScheduler } from './frame-scheduler.js';
import {
    updateFpsStats,
    resetUncappedFpsStats,
    trackFramePerformance,
} from './performance-metrics.js';
import { showToast } from '../toast.js';

// =============================================================================
// Module Constants
// =============================================================================

/**
 * Frame time threshold in milliseconds above which we yield to the browser.
 * When frames take longer than this, we use setTimeout to let the browser
 * process other events, preventing the UI from becoming unresponsive.
 */
const YIELD_THRESHOLD_MS = 50;

/**
 * How often to yield (in frames) when frame times are below threshold.
 * Every 100 frames at 60fps = ~1.7 seconds between yields.
 */
const YIELD_INTERVAL_FRAMES = 100;

// =============================================================================
// Module State
// =============================================================================

/** UI update callback set by main module. */
let uiUpdateCallback = null;

/**
 * Animation generation counter for race condition prevention.
 *
 * When restartAnimation() is called mid-frame, the old animate() call
 * checks this counter and exits without scheduling another frame.
 * This prevents duplicate animation loops from running simultaneously.
 */
let animationGeneration = 0;

/**
 * Re-entrancy guard for WASM frame calls.
 *
 * When GPU physics is active, device.poll(wgpu::Maintain::Wait) can yield to the
 * JavaScript event loop, allowing scheduler callbacks to fire. If a new frame
 * starts before the previous one completes, wasm-bindgen detects the recursive
 * borrow and panics with "recursive use of an object detected".
 *
 * This flag prevents that by skipping animate() calls while a frame is in progress.
 */
let frameInProgress = false;

/**
 * Legacy timeout ID for cleanup during stop (setTimeout fallback path).
 * @type {number|null}
 */
let legacyTimeoutId = null;

/**
 * Counter for yielding every N frames even when frame times are low.
 * This ensures the browser can process events periodically.
 */
let yieldCounter = 0;

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
 * Resizes the canvas to fit its container with high-DPI support.
 *
 * This is called on window resize and ensures the canvas dimensions
 * match the container, maintaining proper aspect ratio and resolution.
 *
 * For crisp rendering on high-DPI displays (mobile, Retina, etc.),
 * we scale the canvas by devicePixelRatio while keeping the CSS
 * display size at 100% of the container.
 *
 * @see https://developer.mozilla.org/en-US/docs/Web/API/Window/devicePixelRatio
 */
export function resizeCanvas() {
    const canvas = getElement('canvas');
    const container = document.getElementById('canvas-container');
    if (!canvas || !container) return;

    const rect = container.getBoundingClientRect();

    // Guard: Do not resize canvas to 0×0 when the container is hidden.
    // When #viz-panel is hidden (e.g., analytics view is active),
    // getBoundingClientRect() returns 0×0. Setting canvas.width = 0
    // destroys the WebGPU swapchain backing store, causing Dawn to emit
    // cascading errors: Invalid Texture → Invalid TextureView →
    // Invalid CommandBuffer on the next frame that tries to render.
    // Keep the canvas at its current dimensions until the container is visible.
    if (rect.width < 1 || rect.height < 1) {
        return;
    }

    // Get device pixel ratio, clamped to reasonable range for performance
    // Mobile devices often have DPR of 2-3, ultra-high-DPI can be 4+
    const dpr = Math.min(window.devicePixelRatio || 1, 3);

    // Calculate the actual rendering resolution
    const displayWidth = Math.floor(rect.width);
    const displayHeight = Math.floor(rect.height);
    const renderWidth = Math.floor(displayWidth * dpr);
    const renderHeight = Math.floor(displayHeight * dpr);

    // Only resize if dimensions have actually changed
    if (canvas.width !== renderWidth || canvas.height !== renderHeight) {
        // Set the canvas buffer size for high-DPI rendering
        canvas.width = renderWidth;
        canvas.height = renderHeight;

        // CRITICAL for Safari: explicitly set CSS dimensions to match container.
        // Safari may not properly scale the canvas buffer to CSS dimensions
        // when using just `width: 100%; height: 100%`. Setting explicit pixel
        // values ensures 1:1 mapping between CSS and buffer dimensions.
        canvas.style.width = `${displayWidth}px`;
        canvas.style.height = `${displayHeight}px`;

        const rource = getRource();
        if (rource) {
            // Pass the high-resolution dimensions to WASM for sharp rendering
            safeWasmCall('resize', () => rource.resize(renderWidth, renderHeight), undefined);
            safeWasmCall('forceRender', () => rource.forceRender(), undefined);
        }

        // Log DPR-aware resize for debugging (only when significant)
        if (dpr > 1) {
            console.debug(`Canvas resized: ${displayWidth}x${displayHeight} @ ${dpr}x DPR = ${renderWidth}x${renderHeight} render`);
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

    // Re-entrancy guard: skip if a frame is already being processed.
    // This prevents crashes when GPU physics' device.poll() yields to the JS event loop
    // and a scheduler callback tries to start a new frame.
    if (frameInProgress) {
        // Schedule retry on next frame instead of calling WASM recursively
        const isUncapped = get('uncappedFps');
        if (isUncapped) {
            // In uncapped mode, use scheduler but with a small delay to avoid spin-waiting
            setTimeout(() => {
                if (generation === animationGeneration) {
                    animate(performance.now(), generation);
                }
            }, 1);
        }
        // In capped mode, the next requestAnimationFrame will handle it
        return;
    }

    // Mark frame as in progress to prevent re-entrancy
    frameInProgress = true;

    const rource = getRource();
    const isUncapped = get('uncappedFps');

    // Check WASM health before proceeding - stop animation if WASM has crashed
    // This prevents infinite error cascades after a WASM panic
    if (!isWasmHealthy()) {
        frameInProgress = false;
        handleWasmCrash();
        return;
    }

    if (rource) {
        // Render the frame via WASM
        safeWasmCall('frame', () => rource.frame(timestamp), undefined);

        // Track FPS statistics in uncapped mode for peak/average display
        if (isUncapped) {
            const fps = safeWasmCall('getFps', () => rource.getFps(), 0);
            updateFpsStats(fps);
        }

        // Invoke UI update callback if registered
        if (uiUpdateCallback) {
            uiUpdateCallback();
        }

        // Periodically update performance metrics overlay
        trackFramePerformance();
    }

    // Second race condition check after frame processing
    // Animation might have been stopped during the render
    if (generation !== animationGeneration) {
        frameInProgress = false;
        return;
    }

    // Frame processing complete - clear re-entrancy guard before scheduling next frame
    frameInProgress = false;

    // Schedule the next frame based on mode
    if (isUncapped) {
        // Get frame time to decide whether to yield to browser
        const frameTimeMs = rource ? safeWasmCall('getFrameTimeMs', () => rource.getFrameTimeMs(), 0) : 0;
        yieldCounter++;

        // Yield to browser when:
        // 1. Frame time exceeds threshold (prevents UI freeze on slow frames)
        // 2. Periodically every N frames (ensures browser can process events)
        const shouldYield = frameTimeMs > YIELD_THRESHOLD_MS || yieldCounter >= YIELD_INTERVAL_FRAMES;

        if (shouldYield) {
            yieldCounter = 0;
            // Use setTimeout(0) to yield to browser's event loop
            // This allows UI events, garbage collection, and other tasks to run
            legacyTimeoutId = setTimeout(() => {
                legacyTimeoutId = null;
                animate(performance.now(), generation);
            }, 0);
        } else {
            // Uncapped mode: use MessageChannel for minimal scheduling overhead
            // This enables significantly higher FPS than setTimeout(0)'s ~4ms minimum
            const scheduler = getFrameScheduler();
            scheduler.schedule(() => animate(performance.now(), generation));
        }

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
// WASM Crash Handling
// =============================================================================

/** Flag to track if crash has already been handled (prevent multiple notifications). */
let crashHandled = false;

/**
 * Handles a WASM crash by stopping the animation loop and notifying the user.
 *
 * This is called when isWasmHealthy() returns false (after 10+ consecutive errors).
 * The WASM module has likely panicked and all subsequent calls will fail.
 *
 * Recovery options:
 * 1. Reload the page (recommended)
 * 2. Try loading a smaller repository
 */
function handleWasmCrash() {
    // Only show notification once per crash
    if (crashHandled) {
        return;
    }
    crashHandled = true;

    // Stop the animation loop
    stopAnimation();

    // Mark WASM as crashed in state for other components
    setState({ wasmCrashed: true });

    // Log to console for debugging
    console.error(
        '[WASM Crash] The visualization engine has encountered an error and stopped. ' +
        'This may be due to memory limits with large repositories. ' +
        'Please reload the page to try again, or use a smaller repository.'
    );

    // Show user-friendly notification
    showToast(
        'Visualization error: The engine crashed, likely due to repository size. ' +
        'Please reload the page or try a smaller repository.',
        'error',
        0 // Persistent - don't auto-dismiss
    );

    // Show context-lost-like overlay for visual feedback
    const overlay = document.getElementById('context-lost-overlay');
    if (overlay) {
        // Update the overlay text for WASM crash case
        const heading = overlay.querySelector('h2');
        const paragraph = overlay.querySelector('p');
        if (heading) heading.textContent = 'Visualization Error';
        if (paragraph) {
            paragraph.textContent =
                'The rendering engine crashed, possibly due to memory limits with large repositories. ' +
                'Reload the page to try again, or choose a smaller repository.';
        }
        overlay.classList.remove('hidden');
    }
}

/**
 * Resets the crash handling state (for page reload or recovery).
 */
export function resetCrashState() {
    crashHandled = false;
    setState({ wasmCrashed: false });
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
 * IMPORTANT: This function ensures clean state transitions by waiting for
 * any in-flight callbacks to drain before starting the new loop. This is
 * especially important for Firefox where scheduler timing can be inconsistent.
 *
 * @param {boolean} [resetStats=true] - Whether to reset FPS tracking statistics
 */
export function restartAnimation(resetStats = true) {
    // stopAnimation() increments generation, invalidating any executing animate() calls
    stopAnimation();
    if (resetStats) {
        resetUncappedFpsStats();
    }

    // Use a microtask to ensure any pending scheduler callbacks have been
    // processed before starting the new animation loop. This prevents race
    // conditions where old callbacks might interfere with the new loop,
    // which was causing animation freezes on Firefox.
    queueMicrotask(() => {
        // Double-check we're still stopped (user might have triggered another action)
        if (getAnimationId() === null) {
            startAnimation();
        }
    });
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

    // Reset re-entrancy guard - do this AFTER incrementing generation so any
    // in-flight frames that check frameInProgress will also fail generation check
    frameInProgress = false;

    // Reset yield counter to ensure clean state on restart
    yieldCounter = 0;

    const animationId = getAnimationId();
    if (animationId !== null) {
        // Cancel requestAnimationFrame (safe even if ID is from MessageChannel)
        cancelAnimationFrame(animationId);

        // Cancel MessageChannel pending callbacks
        const scheduler = getFrameScheduler();
        scheduler.cancel();

        // Clear legacy setTimeout fallback if used
        if (legacyTimeoutId !== null) {
            clearTimeout(legacyTimeoutId);
            legacyTimeoutId = null;
        }

        setAnimationId(null);
    } else {
        // Even if no animation ID, still cancel scheduler in case there are
        // pending callbacks from a previous uncapped session
        const scheduler = getFrameScheduler();
        scheduler.cancel();
    }
}

/**
 * Checks if animation is currently running.
 * @returns {boolean} True if animation loop is active
 */
export function isAnimating() {
    return getAnimationId() !== null;
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
