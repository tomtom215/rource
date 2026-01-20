/**
 * Rource - Screenshot Feature
 *
 * Handles capturing and downloading screenshots of the visualization.
 */

import { getElement } from '../dom.js';
import { getRource, isContextLost, getAnimationId, setAnimationId } from '../state.js';
import { showToast } from '../toast.js';
import { safeWasmCall } from '../wasm-api.js';
import { hasData } from '../state.js';

// Reference to animate function (set by main module)
let animateCallback = null;

/**
 * Sets the animate callback for resuming animation after screenshot.
 * @param {Function} callback - The animate function
 */
export function setAnimateCallback(callback) {
    animateCallback = callback;
}

/**
 * Captures and downloads a screenshot of the canvas.
 */
export function captureScreenshot() {
    const rource = getRource();
    const canvas = getElement('canvas');

    if (!rource || isContextLost()) {
        showToast('Load data first to capture a screenshot', 'error');
        return;
    }

    if (!canvas) {
        showToast('Canvas not found', 'error');
        return;
    }

    try {
        // Generate filename with timestamp
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
        const filename = `rource-${timestamp}.png`;

        // CRITICAL: Stop the animation loop BEFORE capturing.
        // The animation loop continuously renders frames, and toBlob() is async.
        // Without pausing, the next frame's begin_frame()/clear() will wipe the
        // framebuffer before toBlob() can read it, resulting in corrupted output.
        const wasAnimating = getAnimationId() !== null;
        if (getAnimationId()) {
            cancelAnimationFrame(getAnimationId());
            setAnimationId(null);
        }

        // Force a render to ensure the buffer has the current frame content
        safeWasmCall('forceRender', () => rource.forceRender(), undefined);

        // Use canvas.toBlob for best quality (works with WebGL2 too)
        canvas.toBlob((blob) => {
            // Resume animation loop AFTER capture completes
            if (wasAnimating && !getAnimationId() && animateCallback) {
                setAnimationId(requestAnimationFrame(animateCallback));
            }

            if (!blob) {
                showToast('Screenshot failed. Try pausing the visualization first.', 'error');
                return;
            }

            // Create download link
            const url = URL.createObjectURL(blob);
            const link = document.createElement('a');
            link.href = url;
            link.download = filename;
            link.click();

            // Cleanup
            URL.revokeObjectURL(url);
            showToast(`Screenshot saved: ${filename}`, 'success', 3000);
        }, 'image/png', 1.0);

    } catch (error) {
        console.error('Screenshot error:', error);
        showToast('Failed to capture screenshot: ' + error.message, 'error');

        // Resume animation on error
        if (!getAnimationId() && animateCallback && hasData()) {
            setAnimationId(requestAnimationFrame(animateCallback));
        }
    }
}

/**
 * Initializes screenshot button handler.
 */
export function initScreenshot() {
    const btnScreenshot = getElement('btnScreenshot');
    if (btnScreenshot) {
        btnScreenshot.addEventListener('click', captureScreenshot);
    }
}
