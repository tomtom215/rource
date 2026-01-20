/**
 * Rource - Full Map Export Feature
 *
 * Exports the entire visualization at high resolution with readable labels.
 * This creates a "poster-style" image of the complete codebase structure.
 */

import { getElement, getAllElements } from '../dom.js';
import { getRource, isContextLost, getAnimationId, setAnimationId, hasData } from '../state.js';
import { showToast } from '../toast.js';
import { safeWasmCall, safeWasmVoid } from '../wasm-api.js';

// Reference to animate function (set by main module)
let animateCallback = null;

// Export state
let isExporting = false;

// Default minimum font size for readable labels
const DEFAULT_MIN_FONT_SIZE = 12;

// Maximum export dimension warning threshold
const LARGE_EXPORT_WARNING_THRESHOLD = 8000;

/**
 * Sets the animate callback for resuming animation after export.
 * @param {Function} callback - The animate function
 */
export function setFullMapAnimateCallback(callback) {
    animateCallback = callback;
}

/**
 * Gets the full map dimensions from WASM.
 * @param {number} minFontSize - Minimum font size for readable labels
 * @returns {Object|null} { width, height, zoom, centerX, centerY } or null
 */
function getFullMapDimensions(minFontSize = DEFAULT_MIN_FONT_SIZE) {
    const rource = getRource();
    if (!rource) return null;

    const result = safeWasmCall('getFullMapDimensions', () => rource.getFullMapDimensions(minFontSize), null);
    if (!result) return null;

    try {
        return JSON.parse(result);
    } catch (e) {
        console.error('Failed to parse full map dimensions:', e);
        return null;
    }
}

/**
 * Gets the entity bounds from WASM.
 * @returns {Object|null} { minX, minY, maxX, maxY, width, height } or null
 */
export function getEntityBounds() {
    const rource = getRource();
    if (!rource) return null;

    const result = safeWasmCall('getEntityBounds', () => rource.getEntityBounds(), null);
    if (!result) return null;

    try {
        return JSON.parse(result);
    } catch (e) {
        console.error('Failed to parse entity bounds:', e);
        return null;
    }
}

/**
 * Gets the current camera state for restoration.
 * @returns {Object|null} { x, y, zoom } or null
 */
function getCameraState() {
    const rource = getRource();
    if (!rource) return null;

    const result = safeWasmCall('getCameraState', () => rource.getCameraState(), null);
    if (!result) return null;

    try {
        return JSON.parse(result);
    } catch (e) {
        console.error('Failed to parse camera state:', e);
        return null;
    }
}

/**
 * Calculates the estimated file size for the export.
 * @param {number} width - Canvas width
 * @param {number} height - Canvas height
 * @returns {string} Human-readable size estimate
 */
function estimateFileSize(width, height) {
    // PNG compression varies, but rough estimate for this type of content
    // Typical compression ratio for visualizations is about 5-10:1
    const uncompressedBytes = width * height * 4; // RGBA
    const estimatedBytes = uncompressedBytes / 6; // Conservative estimate

    if (estimatedBytes < 1024) {
        return `${Math.round(estimatedBytes)} B`;
    } else if (estimatedBytes < 1024 * 1024) {
        return `${Math.round(estimatedBytes / 1024)} KB`;
    } else {
        return `${(estimatedBytes / (1024 * 1024)).toFixed(1)} MB`;
    }
}

/**
 * Shows the export options modal.
 * @returns {Promise<Object|null>} Export options or null if cancelled
 */
function showExportModal(defaultDimensions) {
    return new Promise((resolve) => {
        // Check if modal already exists
        let modal = document.getElementById('full-map-modal');
        if (modal) {
            modal.remove();
        }

        const { width, height, zoom } = defaultDimensions;
        const estimatedSize = estimateFileSize(width, height);
        const isLarge = width > LARGE_EXPORT_WARNING_THRESHOLD || height > LARGE_EXPORT_WARNING_THRESHOLD;

        // Create modal
        modal = document.createElement('div');
        modal.id = 'full-map-modal';
        modal.className = 'modal-overlay';
        modal.innerHTML = `
            <div class="modal-content export-modal">
                <button type="button" class="modal-close" aria-label="Close">&times;</button>
                <h2>
                    <svg width="20" height="20" viewBox="0 0 24 24" fill="currentColor">
                        <path d="M21 19V5c0-1.1-.9-2-2-2H5c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h14c1.1 0 2-.9 2-2zM8.5 13.5l2.5 3.01L14.5 12l4.5 6H5l3.5-4.5z"/>
                    </svg>
                    Export Full Map
                </h2>
                <p class="modal-description">
                    Export the entire visualization at high resolution with readable labels.
                    Perfect for printing, presentations, or detailed analysis.
                </p>

                <div class="export-preview">
                    <div class="export-dimensions">
                        <span class="export-dim-value">${width.toLocaleString()} × ${height.toLocaleString()}</span>
                        <span class="export-dim-label">pixels</span>
                    </div>
                    <div class="export-estimate">
                        <span class="export-estimate-label">Estimated size:</span>
                        <span class="export-estimate-value">${estimatedSize}</span>
                    </div>
                </div>

                ${isLarge ? `
                <div class="export-warning">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor">
                        <path d="M1 21h22L12 2 1 21zm12-3h-2v-2h2v2zm0-4h-2v-4h2v4z"/>
                    </svg>
                    <span>Large image! Export may take several seconds and use significant memory.</span>
                </div>
                ` : ''}

                <div class="export-options">
                    <label class="export-option">
                        <span>Label Size</span>
                        <div class="export-slider-group">
                            <input type="range" id="export-font-size" min="8" max="24" value="12" step="1">
                            <span id="export-font-value">12px</span>
                        </div>
                    </label>
                    <p class="export-option-help">
                        Larger labels = larger export image. Adjust based on your needs.
                    </p>
                </div>

                <div class="export-actions">
                    <button type="button" class="btn btn-secondary" id="export-cancel">Cancel</button>
                    <button type="button" class="btn btn-primary" id="export-confirm">
                        <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor">
                            <path d="M19 9h-4V3H9v6H5l7 7 7-7zM5 18v2h14v-2H5z"/>
                        </svg>
                        Export PNG
                    </button>
                </div>
            </div>
        `;

        document.body.appendChild(modal);

        // Elements
        const closeBtn = modal.querySelector('.modal-close');
        const cancelBtn = modal.querySelector('#export-cancel');
        const confirmBtn = modal.querySelector('#export-confirm');
        const fontSlider = modal.querySelector('#export-font-size');
        const fontValue = modal.querySelector('#export-font-value');
        const dimValue = modal.querySelector('.export-dim-value');
        const estimateValue = modal.querySelector('.export-estimate-value');
        const warningEl = modal.querySelector('.export-warning');

        // Update dimensions when font size changes
        fontSlider.addEventListener('input', () => {
            const fontSize = parseInt(fontSlider.value, 10);
            fontValue.textContent = `${fontSize}px`;

            const newDims = getFullMapDimensions(fontSize);
            if (newDims) {
                dimValue.textContent = `${newDims.width.toLocaleString()} × ${newDims.height.toLocaleString()}`;
                estimateValue.textContent = estimateFileSize(newDims.width, newDims.height);

                // Update warning
                const isNewLarge = newDims.width > LARGE_EXPORT_WARNING_THRESHOLD ||
                                   newDims.height > LARGE_EXPORT_WARNING_THRESHOLD;
                if (warningEl) {
                    warningEl.style.display = isNewLarge ? 'flex' : 'none';
                } else if (isNewLarge) {
                    // Add warning if it doesn't exist
                    const preview = modal.querySelector('.export-preview');
                    const warning = document.createElement('div');
                    warning.className = 'export-warning';
                    warning.innerHTML = `
                        <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor">
                            <path d="M1 21h22L12 2 1 21zm12-3h-2v-2h2v2zm0-4h-2v-4h2v4z"/>
                        </svg>
                        <span>Large image! Export may take several seconds and use significant memory.</span>
                    `;
                    preview.parentNode.insertBefore(warning, preview.nextSibling);
                }
            }
        });

        // Close handlers
        const closeModal = (result) => {
            modal.classList.add('closing');
            setTimeout(() => {
                modal.remove();
                resolve(result);
            }, 150);
        };

        closeBtn.addEventListener('click', () => closeModal(null));
        cancelBtn.addEventListener('click', () => closeModal(null));

        modal.addEventListener('click', (e) => {
            if (e.target === modal) closeModal(null);
        });

        // Confirm handler
        confirmBtn.addEventListener('click', () => {
            const fontSize = parseInt(fontSlider.value, 10);
            const dims = getFullMapDimensions(fontSize);
            closeModal(dims);
        });

        // Escape key
        const escHandler = (e) => {
            if (e.key === 'Escape') {
                document.removeEventListener('keydown', escHandler);
                closeModal(null);
            }
        };
        document.addEventListener('keydown', escHandler);

        // Focus the confirm button
        setTimeout(() => confirmBtn.focus(), 50);
    });
}

/**
 * Performs the full map export.
 * @param {Object} options - Export options from modal
 */
async function performExport(options) {
    const rource = getRource();
    const canvas = getElement('canvas');

    if (!rource || !canvas || !options) {
        showToast('Export failed: missing data', 'error');
        return;
    }

    const { width, height, zoom, centerX, centerY } = options;

    // Show progress toast
    showToast('Preparing full map export...', 'info', 0);

    // Stop animation
    const wasAnimating = getAnimationId() !== null;
    if (getAnimationId()) {
        cancelAnimationFrame(getAnimationId());
        setAnimationId(null);
    }

    // Save original state
    const originalWidth = canvas.width;
    const originalHeight = canvas.height;
    const originalCamera = getCameraState();

    try {
        // Prepare renderer for export (handles canvas resize, viewport, and camera)
        safeWasmVoid('prepareFullMapExport', () =>
            rource.prepareFullMapExport(width, height, zoom, centerX, centerY)
        );

        // Force render with synchronized dimensions
        safeWasmVoid('forceRender', () => rource.forceRender());

        // Small delay to ensure render completes
        await new Promise(resolve => setTimeout(resolve, 100));

        // Generate filename
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
        const filename = `rource-fullmap-${width}x${height}-${timestamp}.png`;

        // Export using toBlob
        await new Promise((resolve, reject) => {
            canvas.toBlob((blob) => {
                if (!blob) {
                    reject(new Error('Failed to create blob'));
                    return;
                }

                // Download
                const url = URL.createObjectURL(blob);
                const link = document.createElement('a');
                link.href = url;
                link.download = filename;
                link.click();

                URL.revokeObjectURL(url);
                resolve();
            }, 'image/png', 1.0);
        });

        showToast(`Full map exported: ${filename}`, 'success', 5000);

    } catch (error) {
        console.error('Full map export error:', error);
        showToast(`Export failed: ${error.message}`, 'error');

    } finally {
        // Restore original size and camera
        // restoreAfterExport handles canvas, viewport, camera, and settings
        if (originalCamera) {
            // Restore to specific camera state
            safeWasmVoid('restoreAfterExport', () =>
                rource.restoreAfterExport(originalWidth, originalHeight)
            );
            safeWasmVoid('restoreCameraState', () =>
                rource.restoreCameraState(originalCamera.x, originalCamera.y, originalCamera.zoom)
            );
        } else {
            // Restore and fit to content
            safeWasmVoid('restoreAfterExport', () =>
                rource.restoreAfterExport(originalWidth, originalHeight)
            );
        }

        // Force render at original size with synchronized dimensions
        safeWasmVoid('forceRender', () => rource.forceRender());

        // Resume animation
        if (wasAnimating && !getAnimationId() && animateCallback) {
            setAnimationId(requestAnimationFrame(animateCallback));
        }

        isExporting = false;
    }
}

/**
 * Initiates the full map export process.
 * Shows a modal with options, then performs the export.
 */
export async function exportFullMap() {
    const rource = getRource();

    if (!rource || isContextLost()) {
        showToast('Load data first to export full map', 'error');
        return;
    }

    if (!hasData()) {
        showToast('Load data first to export full map', 'error');
        return;
    }

    if (isExporting) {
        showToast('Export already in progress', 'warning');
        return;
    }

    // Get default dimensions
    const defaultDims = getFullMapDimensions(DEFAULT_MIN_FONT_SIZE);
    if (!defaultDims) {
        showToast('No entities to export', 'error');
        return;
    }

    isExporting = true;

    // Show modal and get options
    const options = await showExportModal(defaultDims);

    if (!options) {
        isExporting = false;
        return; // User cancelled
    }

    // Perform export
    await performExport(options);
}

/**
 * Quick export without modal (uses default settings).
 * Useful for keyboard shortcut.
 */
export async function quickExportFullMap() {
    const rource = getRource();

    if (!rource || isContextLost() || !hasData()) {
        showToast('Load data first to export full map', 'error');
        return;
    }

    if (isExporting) {
        showToast('Export already in progress', 'warning');
        return;
    }

    const options = getFullMapDimensions(DEFAULT_MIN_FONT_SIZE);
    if (!options) {
        showToast('No entities to export', 'error');
        return;
    }

    isExporting = true;
    await performExport(options);
}

/**
 * Initializes the full map export button handler.
 */
export function initFullMapExport() {
    const btnFullMap = getElement('btnFullMap');
    if (btnFullMap) {
        btnFullMap.addEventListener('click', exportFullMap);
    }
}

/**
 * Checks if export is currently in progress.
 * @returns {boolean}
 */
export function isExportInProgress() {
    return isExporting;
}
