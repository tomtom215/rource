/**
 * Rource - Video Recording Feature
 *
 * Records the visualization as a WebM video using the MediaRecorder API.
 * Supports various quality presets including 1080p and 4K.
 *
 * By default, recording starts from the beginning and stops at the end
 * of the visualization. Users can also manually start/stop recording.
 */

import { getElement } from '../dom.js';
import { getRource, isContextLost, hasData, getAnimationId, setAnimationId } from '../state.js';
import { showToast } from '../toast.js';
import { safeWasmVoid, safeWasmCall } from '../wasm-api.js';

// Recording state
let mediaRecorder = null;
let recordedChunks = [];
let isRecording = false;
let recordingStartTime = 0;
let recordingDurationInterval = null;
let endCheckInterval = null;

// Reference to animate callback
let animateCallback = null;

// Quality presets (bitrates in bps)
const QUALITY_PRESETS = {
    low: { bitrate: 2_500_000, label: '720p' },
    medium: { bitrate: 8_000_000, label: '1080p' },
    high: { bitrate: 16_000_000, label: '1440p' },
    ultra: { bitrate: 35_000_000, label: '4K' }
};

// Default quality
const DEFAULT_QUALITY = 'medium';

/**
 * Sets the animate callback for use during recording.
 * @param {Function} callback - The animate function
 */
export function setRecordingAnimateCallback(callback) {
    animateCallback = callback;
}

/**
 * Checks if MediaRecorder is supported.
 * @returns {boolean}
 */
export function isRecordingSupported() {
    return typeof MediaRecorder !== 'undefined' && MediaRecorder.isTypeSupported('video/webm');
}

/**
 * Gets the best supported video codec.
 * @returns {string} MIME type with codec
 */
function getBestCodec() {
    const codecs = [
        'video/webm;codecs=vp9',
        'video/webm;codecs=vp8',
        'video/webm'
    ];

    for (const codec of codecs) {
        if (MediaRecorder.isTypeSupported(codec)) {
            return codec;
        }
    }

    return 'video/webm';
}

/**
 * Starts recording the canvas.
 * @param {string} quality - Quality preset key
 * @param {Object} options - Recording options
 * @param {boolean} options.fromBeginning - Start from beginning (default: true)
 * @param {boolean} options.stopAtEnd - Stop when visualization ends (default: true)
 */
export function startRecording(quality = DEFAULT_QUALITY, options = {}) {
    const { fromBeginning = true, stopAtEnd = true } = options;

    const rource = getRource();
    const canvas = getElement('canvas');

    if (!rource || isContextLost() || !canvas) {
        showToast('Cannot start recording: visualization not ready', 'error');
        return false;
    }

    if (!hasData()) {
        showToast('Load data first to record', 'error');
        return false;
    }

    if (!isRecordingSupported()) {
        showToast('Video recording is not supported in this browser', 'error');
        return false;
    }

    if (isRecording) {
        showToast('Already recording', 'warning');
        return false;
    }

    try {
        // Seek to beginning if requested
        if (fromBeginning) {
            safeWasmVoid('seek', () => rource.seek(0));
            showToast('Starting recording from beginning...', 'info', 2000);
        }

        // Get quality settings
        const preset = QUALITY_PRESETS[quality] || QUALITY_PRESETS[DEFAULT_QUALITY];

        // Capture canvas stream at 60 FPS
        const stream = canvas.captureStream(60);

        // Get the best supported codec
        const mimeType = getBestCodec();

        // Create MediaRecorder
        mediaRecorder = new MediaRecorder(stream, {
            mimeType,
            videoBitsPerSecond: preset.bitrate
        });

        // Reset chunks
        recordedChunks = [];

        // Handle data available
        mediaRecorder.ondataavailable = (event) => {
            if (event.data && event.data.size > 0) {
                recordedChunks.push(event.data);
            }
        };

        // Handle recording stop
        mediaRecorder.onstop = () => {
            finishRecording();
        };

        // Handle errors
        mediaRecorder.onerror = (event) => {
            console.error('MediaRecorder error:', event.error);
            showToast(`Recording error: ${event.error?.message || 'Unknown error'}`, 'error');
            cleanupRecording();
        };

        // Start recording
        mediaRecorder.start(1000); // Collect data every second
        isRecording = true;
        recordingStartTime = Date.now();

        // Start duration display update
        recordingDurationInterval = setInterval(updateRecordingDuration, 1000);

        // Start end detection if requested
        if (stopAtEnd) {
            endCheckInterval = setInterval(() => {
                checkForVisualizationEnd();
            }, 500);
        }

        // Update UI
        updateRecordingUI(true);

        // Ensure visualization is playing
        safeWasmVoid('play', () => rource.play());

        // Resume animation if stopped
        if (!getAnimationId() && animateCallback) {
            setAnimationId(requestAnimationFrame(animateCallback));
        }

        return true;

    } catch (error) {
        console.error('Failed to start recording:', error);
        showToast(`Failed to start recording: ${error.message}`, 'error');
        cleanupRecording();
        return false;
    }
}

/**
 * Checks if the visualization has reached the end and stops recording if so.
 */
function checkForVisualizationEnd() {
    const rource = getRource();
    if (!rource || !isRecording) return;

    const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
    const isPlaying = safeWasmCall('isPlaying', () => rource.isPlaying(), false);

    // Check if we've reached the end
    if (total > 0 && current >= total - 1 && !isPlaying) {
        // Give a small delay to capture the final state
        setTimeout(() => {
            if (isRecording) {
                showToast('Visualization complete - saving recording...', 'info', 2000);
                stopRecording();
            }
        }, 1500);
    }
}

/**
 * Stops the current recording.
 */
export function stopRecording() {
    if (!isRecording || !mediaRecorder) {
        return;
    }

    try {
        mediaRecorder.stop();
    } catch (error) {
        console.error('Error stopping recording:', error);
        cleanupRecording();
    }
}

/**
 * Toggles recording on/off.
 */
export function toggleRecording() {
    if (isRecording) {
        stopRecording();
    } else {
        startRecording();
    }
}

/**
 * Finishes the recording and triggers download.
 */
function finishRecording() {
    if (recordedChunks.length === 0) {
        showToast('No data recorded', 'warning');
        cleanupRecording();
        return;
    }

    try {
        // Create blob from chunks
        const blob = new Blob(recordedChunks, { type: 'video/webm' });

        // Generate filename
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
        const duration = Math.round((Date.now() - recordingStartTime) / 1000);
        const filename = `rource-recording-${duration}s-${timestamp}.webm`;

        // Create download link
        const url = URL.createObjectURL(blob);
        const link = document.createElement('a');
        link.href = url;
        link.download = filename;
        link.click();

        // Cleanup
        URL.revokeObjectURL(url);

        const sizeMB = (blob.size / (1024 * 1024)).toFixed(1);
        showToast(`Recording saved: ${filename} (${sizeMB} MB)`, 'success', 5000);

    } catch (error) {
        console.error('Error finishing recording:', error);
        showToast(`Failed to save recording: ${error.message}`, 'error');
    }

    cleanupRecording();
}

/**
 * Cleans up recording state.
 */
function cleanupRecording() {
    isRecording = false;
    mediaRecorder = null;
    recordedChunks = [];
    recordingStartTime = 0;

    if (recordingDurationInterval) {
        clearInterval(recordingDurationInterval);
        recordingDurationInterval = null;
    }

    if (endCheckInterval) {
        clearInterval(endCheckInterval);
        endCheckInterval = null;
    }

    updateRecordingUI(false);
}

/**
 * Updates the recording duration display.
 */
function updateRecordingDuration() {
    if (!isRecording) return;

    const recordText = getElement('recordText');
    if (!recordText) return;

    const elapsed = Math.floor((Date.now() - recordingStartTime) / 1000);
    const minutes = Math.floor(elapsed / 60);
    const seconds = elapsed % 60;
    recordText.textContent = `${minutes}:${seconds.toString().padStart(2, '0')}`;
}

/**
 * Updates the recording UI.
 * @param {boolean} recording - Whether recording is active
 */
function updateRecordingUI(recording) {
    const btnRecord = getElement('btnRecord');
    const recordText = getElement('recordText');

    if (btnRecord) {
        btnRecord.classList.toggle('recording', recording);
        btnRecord.title = recording ? 'Stop recording' : 'Record visualization as video';
    }

    if (recordText) {
        recordText.textContent = recording ? '0:00' : 'Record';
    }
}

/**
 * Checks if currently recording.
 * @returns {boolean}
 */
export function getIsRecording() {
    return isRecording;
}

/**
 * Enables the record button after data is loaded.
 */
export function enableRecordButton() {
    const btnRecord = getElement('btnRecord');
    if (btnRecord && isRecordingSupported()) {
        btnRecord.disabled = false;
    }
}

/**
 * Disables the record button.
 */
export function disableRecordButton() {
    const btnRecord = getElement('btnRecord');
    if (btnRecord) {
        btnRecord.disabled = true;
    }
}

/**
 * Initializes video recording handlers.
 */
export function initVideoRecording() {
    const btnRecord = getElement('btnRecord');

    if (!isRecordingSupported()) {
        // Hide record button if not supported
        if (btnRecord) {
            btnRecord.style.display = 'none';
        }
        console.log('MediaRecorder not supported, video recording disabled');
        return;
    }

    if (btnRecord) {
        btnRecord.addEventListener('click', toggleRecording);
    }
}

// Export quality presets for UI
export { QUALITY_PRESETS };
