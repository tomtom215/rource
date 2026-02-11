// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Zero-Copy Stats Buffer Reader (Phase 84)
 *
 * Reads frame statistics directly from WASM linear memory via a Float32Array
 * view, eliminating JSON serialization overhead entirely.
 *
 * Cost comparison (Rust-side, measured):
 *   - format!() JSON path: ~718 ns/op (string alloc + format + WASM→JS copy + JSON.parse)
 *   - Buffer write path:   ~1.4 ns/op (20 f32 store instructions)
 *
 * @module core/stats-buffer
 */

// =============================================================================
// Buffer Layout Constants
// =============================================================================

/**
 * Stats buffer field indices. Must match the layout in lib.rs stats_buffer.
 * @readonly
 * @enum {number}
 */
export const STATS = Object.freeze({
    FPS: 0,
    FRAME_TIME_MS: 1,
    TOTAL_ENTITIES: 2,
    VISIBLE_FILES: 3,
    VISIBLE_USERS: 4,
    VISIBLE_DIRECTORIES: 5,
    ACTIVE_ACTIONS: 6,
    DRAW_CALLS: 7,
    CANVAS_WIDTH: 8,
    CANVAS_HEIGHT: 9,
    IS_PLAYING: 10,
    COMMIT_COUNT: 11,
    CURRENT_COMMIT: 12,
    TOTAL_FILES: 13,
    TOTAL_USERS: 14,
    TOTAL_DIRECTORIES: 15,
    MOUSE_SCREEN_X: 16,
    MOUSE_SCREEN_Y: 17,
    MOUSE_WORLD_X: 18,
    MOUSE_WORLD_Y: 19,
});

// =============================================================================
// Module State
// =============================================================================

/** @type {Float32Array|null} */
let statsView = null;

/** @type {WebAssembly.Memory|null} */
let wasmMemory = null;

/** @type {number} Byte offset into WASM memory */
let bufferByteOffset = 0;

/** @type {number} Number of f32 elements */
let bufferLength = 0;

/** @type {boolean} */
let initialized = false;

// =============================================================================
// Initialization
// =============================================================================

/**
 * Initializes the zero-copy stats buffer reader.
 *
 * @param {object} rource - The Rource WASM instance
 * @param {WebAssembly.Memory} memory - WASM linear memory from getWasmMemory()
 * @returns {boolean} True if initialization succeeded
 */
export function initStatsBuffer(rource, memory) {
    try {
        const ptr = rource.getStatsBufferPtr();
        const len = rource.getStatsBufferLen();

        if (!ptr || !len || !memory) {
            return false;
        }

        wasmMemory = memory;
        // ptr is a byte offset into the WASM linear memory ArrayBuffer
        bufferByteOffset = ptr;
        bufferLength = len;

        // Create initial Float32Array view
        statsView = new Float32Array(wasmMemory.buffer, bufferByteOffset, bufferLength);
        initialized = true;
        return true;
    } catch (e) {
        initialized = false;
        return false;
    }
}

// =============================================================================
// View Management
// =============================================================================

/**
 * Ensures the Float32Array view is valid.
 *
 * WASM memory can grow (via memory.grow()), which detaches the underlying
 * ArrayBuffer and invalidates all existing TypedArray views. When this
 * happens, byteLength drops to 0 and we must recreate the view.
 *
 * @returns {boolean} True if view is valid
 */
function ensureView() {
    if (!initialized || !wasmMemory) return false;

    // Check if ArrayBuffer was detached (WASM memory grew)
    if (statsView.buffer.byteLength === 0) {
        try {
            statsView = new Float32Array(wasmMemory.buffer, bufferByteOffset, bufferLength);
        } catch {
            initialized = false;
            return false;
        }
    }
    return true;
}

// =============================================================================
// Public API
// =============================================================================

/**
 * Returns true if the stats buffer is initialized and ready to read.
 * @returns {boolean}
 */
export function isStatsBufferReady() {
    return initialized;
}

/**
 * Reads a single stat value from the buffer.
 *
 * @param {number} index - Field index from STATS enum
 * @returns {number} The stat value, or 0 if buffer not ready
 */
export function readStat(index) {
    if (!ensureView()) return 0;
    return statsView[index];
}

/**
 * Reads all stats into a plain object matching the JSON stats format.
 * This is the zero-copy replacement for JSON.parse(getFrameStats()).
 *
 * @returns {object|null} Stats object, or null if buffer not ready
 */
export function readAllStats() {
    if (!ensureView()) return null;

    return {
        fps: statsView[STATS.FPS],
        frameTimeMs: statsView[STATS.FRAME_TIME_MS],
        totalEntities: statsView[STATS.TOTAL_ENTITIES],
        visibleFiles: statsView[STATS.VISIBLE_FILES],
        visibleUsers: statsView[STATS.VISIBLE_USERS],
        visibleDirectories: statsView[STATS.VISIBLE_DIRECTORIES],
        activeActions: statsView[STATS.ACTIVE_ACTIONS],
        drawCalls: statsView[STATS.DRAW_CALLS],
        canvasWidth: statsView[STATS.CANVAS_WIDTH],
        canvasHeight: statsView[STATS.CANVAS_HEIGHT],
        isPlaying: statsView[STATS.IS_PLAYING] === 1.0,
        commitCount: statsView[STATS.COMMIT_COUNT],
        currentCommit: statsView[STATS.CURRENT_COMMIT],
        totalFiles: statsView[STATS.TOTAL_FILES],
        totalUsers: statsView[STATS.TOTAL_USERS],
        totalDirectories: statsView[STATS.TOTAL_DIRECTORIES],
    };
}

/**
 * Releases references to WASM memory.
 * Call this before disposing the Rource instance.
 */
export function disposeStatsBuffer() {
    statsView = null;
    wasmMemory = null;
    initialized = false;
    bufferByteOffset = 0;
    bufferLength = 0;
}
