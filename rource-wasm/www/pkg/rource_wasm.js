/* @ts-self-types="./rource_wasm.d.ts" */

/**
 * The main Rource visualization controller for browser usage.
 *
 * This struct manages the entire visualization lifecycle including:
 * - Rendering (wgpu, WebGL2, or Software backend)
 * - Scene management (files, users, directories)
 * - Camera controls (pan, zoom)
 * - Playback timeline (play, pause, seek)
 * - User interaction (mouse, keyboard)
 *
 * ## API Organization
 *
 * The public API is organized into focused modules:
 * - **Constructor/Renderer**: `create()`, `getRendererType()`, `isGPUAccelerated()`
 * - **Data Loading**: `loadCustomLog()`, `loadGitLog()`, `commitCount()`
 * - **Playback**: `play()`, `pause()`, `seek()`, `setSpeed()` (see `wasm_api::playback`)
 * - **Camera**: `zoom()`, `pan()`, `resize()` (see `wasm_api::camera`)
 * - **Input**: `onMouseDown()`, `onKeyDown()` (see `wasm_api::input`)
 * - **Layout**: `setLayoutPreset()`, `configureLayoutForRepo()` (see `wasm_api::layout`)
 * - **Settings**: `setBloom()`, `setShowLabels()` (see `wasm_api::settings`)
 * - **Export**: `captureScreenshot()`, `getFullMapDimensions()` (see `wasm_api::export`)
 * - **Stats**: `getTotalFiles()`, `getVisibleEntities()` (see `wasm_api::stats`)
 * - **Authors**: `getAuthors()`, `getAuthorColor()` (see `wasm_api::authors`)
 */
export class Rource {
    static __wrap(ptr) {
        ptr = ptr >>> 0;
        const obj = Object.create(Rource.prototype);
        obj.__wbg_ptr = ptr;
        RourceFinalization.register(obj, obj.__wbg_ptr, obj);
        return obj;
    }
    __destroy_into_raw() {
        const ptr = this.__wbg_ptr;
        this.__wbg_ptr = 0;
        RourceFinalization.unregister(this);
        return ptr;
    }
    free() {
        const ptr = this.__destroy_into_raw();
        wasm.__wbg_rource_free(ptr, 0);
    }
    /**
     * Captures a screenshot and returns it as PNG data.
     *
     * Only works with software renderer. WebGL2/wgpu renderers don't support
     * direct pixel readback from JavaScript.
     *
     * # Returns
     * PNG file data as a byte vector, or error message.
     * @returns {Uint8Array}
     */
    captureScreenshot() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_captureScreenshot(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            var r2 = getDataViewMemory0().getInt32(retptr + 4 * 2, true);
            var r3 = getDataViewMemory0().getInt32(retptr + 4 * 3, true);
            if (r3) {
                throw takeObject(r2);
            }
            var v1 = getArrayU8FromWasm0(r0, r1).slice();
            wasm.__wbindgen_export4(r0, r1 * 1, 1);
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the number of loaded commits.
     * @returns {number}
     */
    commitCount() {
        const ret = wasm.rource_commitCount(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Configures the layout algorithm for a given repository size.
     *
     * This automatically computes optimal layout parameters based on
     * repository statistics. Should be called after loading data or
     * when repository characteristics are known.
     *
     * # Arguments
     * * `file_count` - Total number of files
     * * `max_depth` - Maximum directory depth (0 if unknown)
     * * `dir_count` - Total number of directories (0 if unknown)
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.configureLayoutForRepo(50000, 12, 3000);
     * ```
     * @param {number} file_count
     * @param {number} max_depth
     * @param {number} dir_count
     */
    configureLayoutForRepo(file_count, max_depth, dir_count) {
        wasm.rource_configureLayoutForRepo(this.__wbg_ptr, file_count, max_depth, dir_count);
    }
    /**
     * Creates a new Rource instance attached to a canvas element (async factory method).
     *
     * Automatically tries wgpu (WebGPU) first, then WebGL2, falling back to
     * software rendering if neither is available.
     *
     * # Arguments
     *
     * * `canvas` - The HTML canvas element to render to
     *
     * # Backend Selection Priority
     *
     * 1. **wgpu (WebGPU)**: Best performance, modern GPU API (Chrome 113+, Edge 113+)
     * 2. **WebGL2**: Good performance, widely supported
     * 3. **Software**: Maximum compatibility, CPU-based
     *
     * # JavaScript Usage
     *
     * ```javascript
     * const rource = await Rource.create(canvas);
     * ```
     *
     * # Note on Send
     *
     * This future is not `Send` because JavaScript/browser APIs are single-threaded.
     * This is expected and safe for WASM usage.
     * @param {HTMLCanvasElement} canvas
     * @returns {Promise<Rource>}
     */
    static create(canvas) {
        const ret = wasm.rource_create(addHeapObject(canvas));
        return takeObject(ret);
    }
    /**
     * Returns the current commit index.
     * @returns {number}
     */
    currentCommit() {
        const ret = wasm.rource_currentCommit(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns debug information about hit testing at the given coordinates.
     *
     * Use this to diagnose why drag might not be working:
     * - Check if `screen_to_world` conversion is correct
     * - Check if entities are in the spatial index
     * - Check if entities are within hit radius
     * @param {number} x
     * @param {number} y
     * @returns {string}
     */
    debugHitTest(x, y) {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_debugHitTest(retptr, this.__wbg_ptr, x, y);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Disables the watermark.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.disableWatermark();
     * ```
     */
    disableWatermark() {
        wasm.rource_disableWatermark(this.__wbg_ptr);
    }
    /**
     * Releases GPU resources immediately.
     *
     * Call this method before the page unloads to prevent GPU resource
     * contention when the page is refreshed quickly. This is especially
     * important for WebGPU which may hold onto adapter resources.
     *
     * After calling `dispose()`, the Rource instance should not be used again.
     *
     * # Example
     *
     * ```javascript
     * window.addEventListener('beforeunload', () => {
     *     if (rource) {
     *         rource.dispose();
     *     }
     * });
     * ```
     */
    dispose() {
        wasm.rource_dispose(this.__wbg_ptr);
    }
    /**
     * Enables the Rource brand watermark preset.
     *
     * This shows "Rource" with "© Tom F" in the bottom-right corner
     * with subtle opacity for non-intrusive branding.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.enableRourceWatermark();
     * ```
     */
    enableRourceWatermark() {
        wasm.rource_enableRourceWatermark(this.__wbg_ptr);
    }
    /**
     * Checks if the total error rate exceeds the given threshold.
     *
     * # Arguments
     *
     * * `threshold_percent` - Maximum acceptable error rate (0.0-100.0)
     *
     * # Example
     *
     * ```javascript
     * // Check if error rate exceeds 0.1%
     * if (rource.errorRateExceedsThreshold(0.1)) {
     *     showErrorAlert('Error rate too high');
     * }
     * ```
     * @param {number} threshold_percent
     * @returns {boolean}
     */
    errorRateExceedsThreshold(threshold_percent) {
        const ret = wasm.rource_errorRateExceedsThreshold(this.__wbg_ptr, threshold_percent);
        return ret !== 0;
    }
    /**
     * Exports the current commits as a binary cache.
     *
     * Returns `null` if no commits are loaded.
     *
     * The returned bytes can be stored in `IndexedDB` for fast subsequent loads.
     *
     * # Example
     *
     * ```javascript
     * const bytes = rource.exportCacheBytes();
     * if (bytes) {
     *     await idb.put('cache', repoHash, bytes);
     * }
     * ```
     * @returns {Uint8Array | undefined}
     */
    exportCacheBytes() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_exportCacheBytes(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getArrayU8FromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Exports the current commits as a binary cache with a repository identifier.
     *
     * The repository hash is used to validate the cache when loading.
     *
     * # Arguments
     *
     * * `repo_id` - A unique identifier for the repository (URL, path, etc.).
     *
     * # Returns
     *
     * The serialized cache bytes, or `null` if no commits are loaded.
     *
     * # Example
     *
     * ```javascript
     * const bytes = rource.exportCacheBytesWithRepoId('https://github.com/owner/repo.git');
     * ```
     * @param {string} repo_id
     * @returns {Uint8Array | undefined}
     */
    exportCacheBytesWithRepoId(repo_id) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            const ptr0 = passStringToWasm0(repo_id, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len0 = WASM_VECTOR_LEN;
            wasm.rource_exportCacheBytesWithRepoId(retptr, this.__wbg_ptr, ptr0, len0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v2;
            if (r0 !== 0) {
                v2 = getArrayU8FromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v2;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Forces a render without updating simulation.
     *
     * Guards against zero-dimension canvas (e.g., when `#viz-panel` is hidden
     * and `resizeCanvas()` hasn't run yet). WebGPU cannot create swapchain
     * textures with 0×0 dimensions, so we skip the render entirely.
     */
    forceRender() {
        wasm.rource_forceRender(this.__wbg_ptr);
    }
    /**
     * Updates and renders a single frame.
     *
     * Returns true if there are more frames to render.
     * @param {number} timestamp
     * @returns {boolean}
     */
    frame(timestamp) {
        const ret = wasm.rource_frame(this.__wbg_ptr, timestamp);
        return ret !== 0;
    }
    /**
     * Returns the number of active action beams.
     * @returns {number}
     */
    getActiveActions() {
        const ret = wasm.rource_getActiveActions(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns commit activity heatmap (day-of-week × hour-of-day grid).
     * @returns {string | undefined}
     */
    getActivityHeatmap() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getActivityHeatmap(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns all per-file metrics as a JSON array.
     *
     * Each element contains the file path and its aggregated academic metrics.
     * Useful for bulk visualization (e.g., coloring all files by hotspot score).
     * @returns {string | undefined}
     */
    getAllFileMetrics() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getAllFileMetrics(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns all per-user metrics as a JSON array.
     *
     * Each element contains the author name and their aggregated academic metrics.
     * @returns {string | undefined}
     */
    getAllUserMetrics() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getAllUserMetrics(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the error count for asset loading operations.
     *
     * Asset errors occur when loading images, fonts, or other resources.
     * @returns {bigint}
     */
    getAssetErrorCount() {
        const ret = wasm.rource_getAssetErrorCount(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns the color for a given author name as a hex string.
     *
     * Colors are deterministically generated from the author name,
     * so the same name always produces the same color.
     *
     * # Returns
     * Hex color string like "#e94560"
     * @param {string} name
     * @returns {string}
     */
    getAuthorColor(name) {
        let deferred2_0;
        let deferred2_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            const ptr0 = passStringToWasm0(name, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len0 = WASM_VECTOR_LEN;
            wasm.rource_getAuthorColor(retptr, this.__wbg_ptr, ptr0, len0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred2_0 = r0;
            deferred2_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred2_0, deferred2_1, 1);
        }
    }
    /**
     * Returns author data as a JSON string array.
     *
     * Iterates over all commits to get complete author statistics,
     * not just users currently visible in the scene.
     *
     * # Returns
     * JSON array of author objects:
     * ```json
     * [
     *   {"name": "Alice", "color": "#e94560", "commits": 42},
     *   {"name": "Bob", "color": "#58a6ff", "commits": 17}
     * ]
     * ```
     *
     * Authors are sorted by commit count (descending).
     * @returns {string}
     */
    getAuthors() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getAuthors(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns bus factor analysis per directory as JSON.
     *
     * The bus factor is the minimum number of contributors who must leave
     * before a directory becomes unmaintained. Low values (1-2) indicate
     * critical key-person risk.
     * @returns {string | undefined}
     */
    getBusFactors() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getBusFactors(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns statistics about the current cache state.
     *
     * Returns a JSON object with cache information, or `null` if
     * no commits are loaded.
     *
     * # Example
     *
     * ```javascript
     * const stats = rource.getCacheStats();
     * if (stats) {
     *     const info = JSON.parse(stats);
     *     console.log(`${info.commits} commits, ${info.sizeBytes} bytes`);
     * }
     * ```
     * @returns {string | undefined}
     */
    getCacheStats() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCacheStats(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the current cache format version.
     *
     * Use this to check compatibility before loading a cache.
     *
     * # Example
     *
     * ```javascript
     * const version = Rource.getCacheVersion();
     * console.log('Cache version:', version);
     * ```
     * @returns {number}
     */
    static getCacheVersion() {
        const ret = wasm.rource_getCacheVersion();
        return ret;
    }
    /**
     * Returns the current camera state as JSON.
     *
     * Returns `{"x": <f32>, "y": <f32>, "zoom": <f32>}`
     * @returns {string}
     */
    getCameraState() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCameraState(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns the canvas height in pixels.
     * @returns {number}
     */
    getCanvasHeight() {
        const ret = wasm.rource_getCanvasHeight(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the canvas width in pixels.
     * @returns {number}
     */
    getCanvasWidth() {
        const ret = wasm.rource_getCanvasWidth(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns per-file change burst detection as JSON.
     *
     * Detects rapid consecutive changes to individual files.
     * Files with many bursts are significantly more defect-prone
     * (Nagappan et al. 2010).
     * @returns {string | undefined}
     */
    getChangeBursts() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getChangeBursts(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns change coupling pairs as JSON.
     *
     * Identifies files that frequently change together, revealing hidden
     * architectural dependencies that static analysis misses.
     * Research shows coupling correlates with defects better than complexity
     * metrics (D'Ambros et al. 2009).
     *
     * # Arguments
     *
     * * `limit` - Maximum number of coupling pairs to return (default: 20)
     * @param {number | null} [limit]
     * @returns {string | undefined}
     */
    getChangeCoupling(limit) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getChangeCoupling(retptr, this.__wbg_ptr, isLikeNone(limit) ? 0x100000001 : (limit) >>> 0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns sliding-window change entropy analysis as JSON.
     *
     * Measures Shannon entropy of file modification distribution within
     * time windows for defect risk prediction (Hassan ICSE 2009).
     * @returns {string | undefined}
     */
    getChangeEntropy() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getChangeEntropy(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns code churn volatility per file (Nagappan & Ball 2005).
     * @returns {string | undefined}
     */
    getChurnVolatility() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getChurnVolatility(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns circadian (time-of-day) risk patterns as JSON.
     *
     * Assigns risk scores based on hour-of-day and day-of-week.
     * Commits between midnight–4AM UTC are significantly buggier
     * (Eyolfson et al. 2011).
     * @returns {string | undefined}
     */
    getCircadianRisk() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCircadianRisk(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns codebase growth trajectory as JSON.
     *
     * Tracks active file count over time, growth rate, and trend
     * classification (Lehman 1996 Laws of Software Evolution).
     * @returns {string | undefined}
     */
    getCodebaseGrowth() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCodebaseGrowth(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the author name for a commit at the given index.
     * @param {number} index
     * @returns {string}
     */
    getCommitAuthor(index) {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCommitAuthor(retptr, this.__wbg_ptr, index);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns commit cadence analysis per developer as JSON.
     *
     * Analyzes inter-commit intervals to classify contributors as
     * regular, moderate, or bursty (Eyolfson et al. 2014).
     * @returns {string | undefined}
     */
    getCommitCadence() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCommitCadence(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns per-commit complexity / tangled change scores (Herzig & Zeller 2013).
     * @returns {string | undefined}
     */
    getCommitComplexity() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCommitComplexity(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the total number of unique directories across all loaded commits.
     *
     * This calculates directory count from file paths, independent of
     * playback state. Useful for displaying total stats before playback
     * reaches the end.
     *
     * # Optimization Notes
     *
     * - Uses `match_indices('/')` for O(n) path parsing instead of O(n²) split+nth
     * - Stores owned Strings to handle `Cow<str>` from `to_string_lossy()`
     * - Pre-allocates `HashSet` capacity based on estimated directory count
     * @returns {number}
     */
    getCommitDirectoryCount() {
        const ret = wasm.rource_getCommitDirectoryCount(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the number of files changed in a commit at the given index.
     * @param {number} index
     * @returns {number}
     */
    getCommitFileCount(index) {
        const ret = wasm.rource_getCommitFileCount(this.__wbg_ptr, index);
        return ret >>> 0;
    }
    /**
     * Returns the timestamp for a commit at the given index.
     * @param {number} index
     * @returns {number}
     */
    getCommitTimestamp(index) {
        const ret = wasm.rource_getCommitTimestamp(this.__wbg_ptr, index);
        return ret;
    }
    /**
     * Returns the error count for configuration operations.
     *
     * Config errors occur when invalid settings are provided.
     * @returns {bigint}
     */
    getConfigErrorCount() {
        const ret = wasm.rource_getConfigErrorCount(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns sociotechnical congruence analysis as JSON.
     *
     * Measures alignment between who SHOULD coordinate (from technical
     * dependencies) and who ACTUALLY does (from shared files).
     * Conway's Law quantified (Cataldo et al. 2008).
     * @returns {string | undefined}
     */
    getCongruence() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getCongruence(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns contribution inequality / Gini coefficient analysis as JSON.
     *
     * Measures how unevenly commits are distributed using the Gini coefficient.
     * Includes Lorenz curve, top-K% share, and windowed trend analysis
     * (Chelkowski et al. 2016).
     * @returns {string | undefined}
     */
    getContributionInequality() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getContributionInequality(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the date range of all commits as a JSON object.
     *
     * Returns `{"startTimestamp": <unix_ts>, "endTimestamp": <unix_ts>}` or null
     * if no commits are loaded.
     * @returns {string | undefined}
     */
    getDateRange() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDateRange(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns defect-introducing change patterns (Kim et al. 2008).
     * @returns {string | undefined}
     */
    getDefectPatterns() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDefectPatterns(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns detailed error metrics with operation counts as JSON.
     *
     * This includes both error counts and operation counts for each category,
     * enabling more detailed analysis.
     *
     * # Returns
     *
     * JSON string with the following structure:
     * ```json
     * {
     *   "errors": {
     *     "parse": 0,
     *     "render": 0,
     *     "webgl": 0,
     *     "config": 0,
     *     "asset": 0,
     *     "io": 0
     *   },
     *   "operations": {
     *     "parse": 100,
     *     "render": 10000,
     *     "webgl": 1,
     *     "config": 5,
     *     "asset": 10,
     *     "io": 0
     *   },
     *   "totals": {
     *     "errors": 0,
     *     "operations": 10116,
     *     "rate": 0.0
     *   }
     * }
     * ```
     * @returns {string}
     */
    getDetailedErrorMetrics() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDetailedErrorMetrics(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns detailed frame profiling statistics as JSON.
     *
     * This provides phase-level timing breakdown for identifying bottlenecks:
     * - `sceneUpdateMs`: Time spent applying commits and updating physics
     * - `renderMs`: Time spent in render passes
     * - `gpuWaitMs`: Time waiting for GPU (WebGPU only)
     * - `effectsMs`: Time in post-processing (bloom, shadows)
     * - `totalMs`: Total frame time
     *
     * Rolling averages (`avg*`) are calculated over the last 60 frames.
     *
     * ## Usage
     *
     * ```javascript
     * const stats = JSON.parse(rource.getDetailedFrameStats());
     * console.log(`Scene: ${stats.sceneUpdateMs.toFixed(2)}ms`);
     * console.log(`Render: ${stats.renderMs.toFixed(2)}ms`);
     * console.log(`WASM heap: ${(stats.wasmHeapBytes / 1024 / 1024).toFixed(1)}MB`);
     * ```
     *
     * ## Chrome `DevTools` Integration
     *
     * When the `profiling` feature is enabled, Performance marks are added
     * that show up in Chrome `DevTools` Performance tab:
     * - `rource:frame_start` / `rource:frame_end`
     * - `rource:scene_update_start` / `rource:scene_update_end`
     * - `rource:render_start` / `rource:render_end`
     * @returns {string}
     */
    getDetailedFrameStats() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDetailedFrameStats(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns developer experience scores (Mockus & Votta 2000).
     * @returns {string | undefined}
     */
    getDeveloperExperience() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDeveloperExperience(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns developer focus and file diffusion analysis as JSON.
     *
     * Measures how concentrated developers' activity is (focus) and
     * how spread out files' contributors are (diffusion).
     * More focused developers introduce fewer defects (Posnett et al. 2013).
     * @returns {string | undefined}
     */
    getDeveloperFocus() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDeveloperFocus(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns developer collaboration network analysis as JSON.
     *
     * Builds and analyzes the co-authorship network: density, components,
     * betweenness centrality, and clustering (Begel et al. 2023).
     * @returns {string | undefined}
     */
    getDeveloperNetwork() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDeveloperNetwork(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns developer activity profiles as JSON.
     *
     * Classifies contributors as core, peripheral, or drive-by based
     * on commit share and recency (Mockus et al. 2002).
     * @returns {string | undefined}
     */
    getDeveloperProfiles() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getDeveloperProfiles(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the estimated draw call count for the current frame.
     * @returns {number}
     */
    getDrawCalls() {
        const ret = wasm.rource_getDrawCalls(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Gets information about the entity at the given screen coordinates.
     *
     * Returns a JSON string with entity information if an entity is found,
     * or null if no entity is under the cursor.
     *
     * # Arguments
     *
     * * `x` - Screen X coordinate (canvas-relative)
     * * `y` - Screen Y coordinate (canvas-relative)
     *
     * # Returns
     *
     * JSON string with format:
     * ```json
     * {
     *   "entityType": "file" | "user" | "directory",
     *   "name": "filename.rs",
     *   "path": "src/lib.rs",
     *   "extension": "rs",
     *   "color": "#FF5500",
     *   "radius": 5.0
     * }
     * ```
     * Or `null` if no entity is under the cursor.
     * @param {number} x
     * @param {number} y
     * @returns {string | undefined}
     */
    getEntityAtCursor(x, y) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getEntityAtCursor(retptr, this.__wbg_ptr, x, y);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the bounding box of all entities as JSON.
     *
     * Returns `{"minX", "minY", "maxX", "maxY", "width", "height"}` or null
     * if no entities exist.
     * @returns {string | undefined}
     */
    getEntityBounds() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getEntityBounds(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns all error metrics as a JSON string.
     *
     * This batches all error metrics into a single call to reduce WASM↔JS overhead.
     *
     * # Returns
     *
     * JSON string with the following structure:
     * ```json
     * {
     *   "parse": 0,
     *   "render": 0,
     *   "webgl": 0,
     *   "config": 0,
     *   "asset": 0,
     *   "io": 0,
     *   "total": 0,
     *   "rate": 0.0
     * }
     * ```
     *
     * Note: The `rate` field is in decimal form (0.001 = 0.1%).
     *
     * # Example
     *
     * ```javascript
     * const metrics = JSON.parse(rource.getErrorMetrics());
     * if (metrics.rate > 0.001) {
     *     console.warn('Error rate exceeds 0.1%');
     * }
     * ```
     * @returns {string}
     */
    getErrorMetrics() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getErrorMetrics(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns the total error rate as a percentage (0.0-100.0).
     *
     * Formula: `(total_errors / total_operations) * 100`
     *
     * Returns 0.0 if no operations have been recorded.
     *
     * # Example
     *
     * ```javascript
     * const errorRate = rource.getErrorRate();
     * if (errorRate > 0.1) {
     *     console.warn(`Error rate ${errorRate.toFixed(3)}% exceeds 0.1% threshold`);
     * }
     * ```
     * @returns {number}
     */
    getErrorRate() {
        const ret = wasm.rource_getErrorRate(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns the number of registered file icon types.
     *
     * # Example (JavaScript)
     * ```javascript
     * const count = rource.getFileIconCount();
     * console.log(`${count} file types registered`);
     * ```
     * @returns {number}
     */
    getFileIconCount() {
        const ret = wasm.rource_getFileIconCount(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns file lifecycle analysis as JSON.
     *
     * Tracks file creation, modification, and deletion patterns to
     * identify ephemeral, dead, and actively maintained files
     * (Godfrey & Tu 2000, Gall et al. 1998).
     * @returns {string | undefined}
     */
    getFileLifecycles() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getFileLifecycles(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns aggregated academic metrics for a specific file as JSON.
     *
     * Computes the full insights index and performs O(1) lookup by file path.
     * Returns `null` if the file is not found in the commit history.
     *
     * # Academic Citations
     *
     * The returned metrics aggregate findings from:
     * - Nagappan & Ball (ICSE 2005): hotspot score
     * - Bird et al. (ICSE 2011): ownership concentration
     * - Eyolfson et al. (MSR 2011): circadian risk
     * - Rigby & Bird (FSE 2013): knowledge entropy
     * - D'Ambros et al. (TSE 2009): coupling degree
     * - Godfrey & Tu (ICSM 2000): lifecycle stage
     * @param {string} path
     * @returns {string | undefined}
     */
    getFileMetrics(path) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            const ptr0 = passStringToWasm0(path, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len0 = WASM_VECTOR_LEN;
            wasm.rource_getFileMetrics(retptr, this.__wbg_ptr, ptr0, len0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v2;
            if (r0 !== 0) {
                v2 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v2;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns file survival analysis (Kaplan-Meier estimator) as JSON.
     *
     * Estimates how long files survive before deletion using the
     * gold-standard survival analysis technique from biostatistics
     * (Cito et al. 2021).
     * @returns {string | undefined}
     */
    getFileSurvival() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getFileSurvival(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Gets the current font size for labels.
     * @returns {number}
     */
    getFontSize() {
        const ret = wasm.rource_getFontSize(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns the current frames per second.
     * @returns {number}
     */
    getFps() {
        const ret = wasm.rource_getFps(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns all frame statistics in a single call to reduce WASM↔JS overhead.
     *
     * This batches 12+ individual getter calls into one, reducing per-frame
     * overhead by approximately 90% when updating the performance metrics UI.
     *
     * # Timing Precision
     *
     * Frame time is returned with 4 decimal places (0.1µs display resolution).
     * Actual measurement precision is limited by browser security mitigations
     * against timing attacks (Spectre/Meltdown):
     *
     * | Browser | Resolution | Source |
     * |---------|------------|--------|
     * | Chrome  | ~5µs       | [Chrome Security Blog](https://security.googleblog.com) |
     * | Firefox | ~20µs      | [MDN Spectre mitigations](https://developer.mozilla.org) |
     * | Safari  | ~100µs     | `WebKit` security notes |
     *
     * Nanosecond precision is not achievable from JavaScript's `performance.now()`.
     * The 4 decimal places display the full resolution available from the browser.
     *
     * Returns a JSON string with the following structure:
     * ```json
     * {
     *   "fps": 60.0,
     *   "frameTimeMs": 16.6700,
     *   "totalEntities": 1500,
     *   "visibleFiles": 200,
     *   "visibleUsers": 5,
     *   "visibleDirectories": 50,
     *   "activeActions": 10,
     *   "drawCalls": 6,
     *   "canvasWidth": 1920,
     *   "canvasHeight": 1080,
     *   "isPlaying": true,
     *   "commitCount": 1000,
     *   "currentCommit": 500,
     *   "totalFiles": 500,
     *   "totalUsers": 20,
     *   "totalDirectories": 100
     * }
     * ```
     * @returns {string}
     */
    getFrameStats() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getFrameStats(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns the last frame time in milliseconds.
     * @returns {number}
     */
    getFrameTimeMs() {
        const ret = wasm.rource_getFrameTimeMs(this.__wbg_ptr);
        return ret;
    }
    /**
     * Calculates the required canvas dimensions for full map export.
     *
     * Returns dimensions that ensure labels are readable at the specified
     * minimum font size, capped at 16384 pixels per dimension.
     *
     * # Arguments
     * * `min_label_font_size` - Minimum font size for readable labels (e.g., 8.0)
     *
     * # Returns
     * JSON object: `{"width", "height", "zoom", "centerX", "centerY"}` or null
     * @param {number} min_label_font_size
     * @returns {string | undefined}
     */
    getFullMapDimensions(min_label_font_size) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getFullMapDimensions(retptr, this.__wbg_ptr, min_label_font_size);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns GPU culling statistics as a JSON string.
     *
     * Returns statistics from the last frame's culling operation, or null
     * if GPU culling is not active or no culling has occurred yet.
     *
     * # Returns
     * JSON string with fields:
     * - `totalInstances`: Total instances submitted for culling
     * - `visibleInstances`: Instances that passed culling
     * - `dispatchCount`: Number of culling dispatches
     * - `cullRatio`: Ratio of visible/total (0.0-1.0)
     * - `culledPercentage`: Percentage culled (0.0-100.0)
     *
     * # Example (JavaScript)
     * ```javascript
     * const stats = rource.getGPUCullingStats();
     * if (stats) {
     *     const data = JSON.parse(stats);
     *     console.log(`Culled ${data.culledPercentage.toFixed(1)}% of instances`);
     * }
     * ```
     * @returns {string | undefined}
     */
    getGPUCullingStats() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getGPUCullingStats(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the current GPU culling threshold.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU culling threshold:', rource.getGPUCullingThreshold());
     * ```
     * @returns {number}
     */
    getGPUCullingThreshold() {
        const ret = wasm.rource_getGPUCullingThreshold(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns GPU adapter information for diagnostics (WebGPU only).
     *
     * Returns a JSON string with hardware details:
     * - `name`: GPU adapter name
     * - `vendor`: Vendor ID
     * - `device`: Device ID
     * - `deviceType`: Type (`DiscreteGpu`, `IntegratedGpu`)
     * - `backend`: Graphics backend (`BrowserWebGpu`)
     * - `maxTextureDimension2d`: Maximum 2D texture size
     * - `maxBufferSize`: Maximum buffer size in bytes
     * - `maxStorageBufferBindingSize`: Maximum storage buffer binding size
     * - `maxComputeWorkgroupSizeX`: Maximum compute workgroup X size
     * - `maxComputeInvocationsPerWorkgroup`: Maximum compute invocations per workgroup
     *
     * Returns `null` for non-WebGPU renderers.
     * @returns {string | undefined}
     */
    getGPUInfo() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getGPUInfo(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the current GPU physics threshold.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU physics threshold:', rource.getGPUPhysicsThreshold());
     * ```
     * @returns {number}
     */
    getGPUPhysicsThreshold() {
        const ret = wasm.rource_getGPUPhysicsThreshold(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the top N file hotspots as JSON.
     *
     * Hotspots are files with disproportionately high change frequency,
     * weighted by recency. Research shows these predict defect-prone code
     * with ~89% accuracy (Nagappan et al. 2005).
     *
     * # Arguments
     *
     * * `limit` - Maximum number of hotspots to return (default: 20)
     * @param {number | null} [limit]
     * @returns {string | undefined}
     */
    getHotspots(limit) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getHotspots(retptr, this.__wbg_ptr, isLikeNone(limit) ? 0x100000001 : (limit) >>> 0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Computes and returns comprehensive repository insights as JSON.
     *
     * Analyzes the loaded commit history to produce research-backed metrics:
     *
     * - **Hotspots**: Files with high change frequency (defect predictors)
     * - **Change Coupling**: Hidden dependencies via co-change patterns
     * - **Code Ownership**: Knowledge concentration per file
     * - **Bus Factor**: Organizational resilience per directory
     * - **Temporal Patterns**: Activity heatmap and burst detection
     * - **Summary**: Commit entropy, author count, time span
     *
     * Returns a JSON string with the complete insights report.
     * Returns `null` if no commits are loaded.
     *
     * # Performance
     *
     * Computed from commit history at call time (not per-frame).
     * Typical computation time: <10ms for 10k commits.
     * @returns {string | undefined}
     */
    getInsights() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getInsights(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the complete insights index summary as JSON.
     *
     * Contains aggregate counts: total files, total users, knowledge silos,
     * contributor profile distribution, max hotspot score.
     * @returns {string | undefined}
     */
    getInsightsIndexSummary() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getInsightsIndexSummary(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns a summary of repository health metrics as JSON.
     *
     * Quick overview suitable for dashboard display:
     * - Total commits, files, authors
     * - Time span
     * - Average commit entropy (change scatter)
     * - Top 5 hotspots
     * - Lowest bus factors
     * @returns {string | undefined}
     */
    getInsightsSummary() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getInsightsSummary(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the error count for I/O operations.
     *
     * I/O errors occur during file reads or network operations.
     * @returns {bigint}
     */
    getIoErrorCount() {
        const ret = wasm.rource_getIoErrorCount(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns per-directory knowledge distribution entropy (Constantinou & Mens 2017).
     * @returns {string | undefined}
     */
    getKnowledgeDistribution() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getKnowledgeDistribution(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns knowledge map and silo analysis as JSON.
     *
     * Computes Shannon entropy of ownership distribution per file to
     * identify knowledge silos (Rigby & Bird 2013, Fritz et al. 2014).
     * @returns {string | undefined}
     */
    getKnowledgeMap() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getKnowledgeMap(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Gets the current layout configuration as a JSON string.
     *
     * Returns a JSON object with all layout parameters.
     *
     * # Example (JavaScript)
     * ```javascript
     * const config = JSON.parse(rource.getLayoutConfig());
     * console.log(config.radial_distance_scale);
     * ```
     * @returns {string}
     */
    getLayoutConfig() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getLayoutConfig(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns the current maximum commits limit.
     * @returns {number}
     */
    getMaxCommits() {
        const ret = wasm.rource_getMaxCommits(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns co-change modularity / DSM analysis as JSON.
     *
     * Measures whether co-changing files respect directory boundaries.
     * High cross-module coupling indicates architectural erosion
     * (Silva et al. 2014).
     * @returns {string | undefined}
     */
    getModularity() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getModularity(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Gets the current mouse position in screen coordinates.
     *
     * Returns an array `[x, y]` of the last known mouse position.
     * @returns {Float32Array}
     */
    getMousePosition() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getMousePosition(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            var v1 = getArrayF32FromWasm0(r0, r1).slice();
            wasm.__wbindgen_export4(r0, r1 * 4, 4);
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Gets the current mouse position in world coordinates.
     *
     * Returns an array `[x, y]` of the mouse position in world space.
     * @returns {Float32Array}
     */
    getMouseWorldPosition() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getMouseWorldPosition(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            var v1 = getArrayF32FromWasm0(r0, r1).slice();
            wasm.__wbindgen_export4(r0, r1 * 4, 4);
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the original commit count before any truncation.
     *
     * This is useful for displaying "Showing X of Y commits" in the UI.
     * @returns {number}
     */
    getOriginalCommitCount() {
        const ret = wasm.rource_getOriginalCommitCount(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns per-file ownership fragmentation / Gini (Bird et al. 2011).
     * @returns {string | undefined}
     */
    getOwnershipFragmentation() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getOwnershipFragmentation(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the error count for parse operations.
     *
     * Parse errors occur when loading git logs or custom log formats
     * with invalid or malformed content.
     * @returns {bigint}
     */
    getParseErrorCount() {
        const ret = wasm.rource_getParseErrorCount(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns the parse error rate as a percentage (0.0-100.0).
     *
     * Parse errors should be below 0.5% for healthy operation.
     * @returns {number}
     */
    getParseErrorRate() {
        const ret = wasm.rource_getParseErrorRate(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns release rhythm analysis (Khomh et al. 2012).
     * @returns {string | undefined}
     */
    getReleaseRhythm() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getReleaseRhythm(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the error count for render operations.
     *
     * Render errors occur during frame rendering, such as buffer allocation
     * failures or texture upload issues.
     * @returns {bigint}
     */
    getRenderErrorCount() {
        const ret = wasm.rource_getRenderErrorCount(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns the type of renderer being used ("wgpu", "webgl2", or "software").
     * @returns {string}
     */
    getRendererType() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getRendererType(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Gets whether labels are being shown.
     * @returns {boolean}
     */
    getShowLabels() {
        const ret = wasm.rource_getShowLabels(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Gets the current playback speed.
     * @returns {number}
     */
    getSpeed() {
        const ret = wasm.rource_getSpeed(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns the length of the stats buffer (number of `f32` elements).
     * @returns {number}
     */
    getStatsBufferLen() {
        const ret = wasm.rource_getStatsBufferLen(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns a pointer to the stats buffer in WASM linear memory.
     *
     * JS uses this pointer offset to create a `Float32Array` view directly
     * into WASM memory, enabling zero-copy reads of all frame statistics.
     *
     * # Safety
     *
     * The returned pointer is valid for the lifetime of the `Rource` instance.
     * The buffer is 32 × `f32` = 128 bytes. JS must not write to this buffer.
     * @returns {number}
     */
    getStatsBufferPtr() {
        const ret = wasm.rource_getStatsBufferPtr(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns language/technology distribution by file extension.
     * @returns {string | undefined}
     */
    getTechDistribution() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getTechDistribution(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns developer technology expertise profiles.
     * @returns {string | undefined}
     */
    getTechExpertise() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getTechExpertise(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns temporal activity patterns as JSON.
     *
     * Includes:
     * - Activity heatmap (7 days x 24 hours)
     * - Peak activity times
     * - Change burst detection
     * - Average files per commit during/outside bursts
     * @returns {string | undefined}
     */
    getTemporalPatterns() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getTemporalPatterns(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the total number of directories currently in the scene.
     *
     * Note: This only includes directories that have been created so far
     * during playback. For total directories across all commits, use
     * `getCommitDirectoryCount()`.
     * @returns {number}
     */
    getTotalDirectories() {
        const ret = wasm.rource_getTotalDirectories(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the total number of entities (files + users + dirs + actions).
     * @returns {number}
     */
    getTotalEntities() {
        const ret = wasm.rource_getTotalEntities(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the total number of errors recorded across all categories.
     *
     * # Example
     *
     * ```javascript
     * const totalErrors = rource.getTotalErrors();
     * console.log(`Total errors: ${totalErrors}`);
     * ```
     * @returns {bigint}
     */
    getTotalErrors() {
        const ret = wasm.rource_getTotalErrors(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns the total number of files in the scene.
     * @returns {number}
     */
    getTotalFiles() {
        const ret = wasm.rource_getTotalFiles(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the total number of frames rendered.
     * @returns {number}
     */
    getTotalFrames() {
        const ret = wasm.rource_getTotalFrames(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns the total number of operations recorded across all categories.
     *
     * This is the denominator for error rate calculations.
     * @returns {bigint}
     */
    getTotalOperations() {
        const ret = wasm.rource_getTotalOperations(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns the total number of users in the scene.
     * @returns {number}
     */
    getTotalUsers() {
        const ret = wasm.rource_getTotalUsers(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns enhanced truck factor via DOA model (Avelino et al. 2016).
     * @returns {string | undefined}
     */
    getTruckFactor() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getTruckFactor(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns developer turnover impact analysis (Mockus 2009).
     * @returns {string | undefined}
     */
    getTurnoverImpact() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getTurnoverImpact(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the uptime in seconds.
     * @returns {number}
     */
    getUptime() {
        const ret = wasm.rource_getUptime(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns aggregated academic metrics for a specific developer as JSON.
     *
     * Computes the full insights index and performs O(1) lookup by author name.
     * Returns `null` if the author is not found in the commit history.
     *
     * # Academic Citations
     *
     * The returned metrics aggregate findings from:
     * - Mockus et al. (TSE 2002): developer profiles (core/peripheral)
     * - Eyolfson et al. (MSR 2014): commit cadence
     * - Meneely & Williams (FSE 2009): network centrality
     * - Posnett et al. (ICSE 2013): developer focus
     * @param {string} author
     * @returns {string | undefined}
     */
    getUserMetrics(author) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            const ptr0 = passStringToWasm0(author, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len0 = WASM_VECTOR_LEN;
            wasm.rource_getUserMetrics(retptr, this.__wbg_ptr, ptr0, len0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v2;
            if (r0 !== 0) {
                v2 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v2;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the number of visible directories (in current viewport).
     * @returns {number}
     */
    getVisibleDirectories() {
        const ret = wasm.rource_getVisibleDirectories(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the number of visible files (in current viewport).
     * @returns {number}
     */
    getVisibleFiles() {
        const ret = wasm.rource_getVisibleFiles(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the number of visible users (in current viewport).
     * @returns {number}
     */
    getVisibleUsers() {
        const ret = wasm.rource_getVisibleUsers(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns a reference to the WASM linear memory.
     *
     * JS needs this to construct a `Float32Array` view over the stats buffer.
     * The `ArrayBuffer` backing this memory may be detached if WASM memory
     * grows; JS code must handle this by recreating the view.
     * @returns {any}
     */
    getWasmMemory() {
        const ret = wasm.rource_getWasmMemory(this.__wbg_ptr);
        return takeObject(ret);
    }
    /**
     * Gets the current watermark opacity.
     * @returns {number}
     */
    getWatermarkOpacity() {
        const ret = wasm.rource_getWatermarkOpacity(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns the error count for WebGL/wgpu operations.
     *
     * WebGL errors include shader compilation failures, context lost events,
     * and program linking issues.
     * @returns {bigint}
     */
    getWebGlErrorCount() {
        const ret = wasm.rource_getWebGlErrorCount(this.__wbg_ptr);
        return BigInt.asUintN(64, ret);
    }
    /**
     * Returns work-type mix analysis as JSON.
     *
     * Classifies commits by Create/Modify/Delete ratio to reveal whether
     * the team is building features, maintaining code, or cleaning up
     * (Hindle et al. 2008, Mockus & Votta 2000).
     * @returns {string | undefined}
     */
    getWorkTypeMix() {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getWorkTypeMix(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            let v1;
            if (r0 !== 0) {
                v1 = getStringFromWasm0(r0, r1).slice();
                wasm.__wbindgen_export4(r0, r1 * 1, 1);
            }
            return v1;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Returns the current zoom level.
     * @returns {number}
     */
    getZoom() {
        const ret = wasm.rource_getZoom(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns debug information about zoom and entity visibility.
     *
     * Returns JSON with zoom level, entity radii, and screen radii to help
     * diagnose visibility issues.
     * @returns {string}
     */
    getZoomDebugInfo() {
        let deferred1_0;
        let deferred1_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_getZoomDebugInfo(retptr, this.__wbg_ptr);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred1_0 = r0;
            deferred1_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred1_0, deferred1_1, 1);
        }
    }
    /**
     * Returns whether file icons are initialized.
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.hasFileIcons()) {
     *     console.log('File icons ready');
     * }
     * ```
     * @returns {boolean}
     */
    hasFileIcons() {
        const ret = wasm.rource_hasFileIcons(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Checks if cache data has a valid magic header.
     *
     * This is a quick check that doesn't fully validate the cache.
     * Use before attempting to import to provide fast feedback.
     *
     * # Arguments
     *
     * * `bytes` - The cache bytes to check.
     *
     * # Returns
     *
     * `true` if the data starts with the "RSVC" magic bytes.
     * @param {Uint8Array} bytes
     * @returns {boolean}
     */
    static hasValidCacheMagic(bytes) {
        const ptr0 = passArray8ToWasm0(bytes, wasm.__wbindgen_export);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.rource_hasValidCacheMagic(ptr0, len0);
        return ret !== 0;
    }
    /**
     * Computes a stable hash for a repository identifier.
     *
     * Use this to create cache keys for `IndexedDB` storage.
     *
     * # Arguments
     *
     * * `repo_id` - A unique identifier for the repository (URL, path, etc.).
     *
     * # Returns
     *
     * A 64-bit hash as a hex string (16 characters).
     *
     * # Example
     *
     * ```javascript
     * const hash = Rource.hashRepoId('https://github.com/owner/repo.git');
     * // Use hash as `IndexedDB` key
     * await idb.put('cache', hash, cacheBytes);
     * ```
     * @param {string} repo_id
     * @returns {string}
     */
    static hashRepoId(repo_id) {
        let deferred2_0;
        let deferred2_1;
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            const ptr0 = passStringToWasm0(repo_id, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len0 = WASM_VECTOR_LEN;
            wasm.rource_hashRepoId(retptr, ptr0, len0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            deferred2_0 = r0;
            deferred2_1 = r1;
            return getStringFromWasm0(r0, r1);
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
            wasm.__wbindgen_export4(deferred2_0, deferred2_1, 1);
        }
    }
    /**
     * Imports commits from a binary cache.
     *
     * Returns the number of commits loaded, or 0 if the cache is invalid.
     *
     * # Arguments
     *
     * * `bytes` - The cache bytes previously exported with `exportCacheBytes()`.
     *
     * # Example
     *
     * ```javascript
     * const bytes = await idb.get('cache', repoHash);
     * if (bytes) {
     *     const count = rource.importCacheBytes(bytes);
     *     if (count > 0) {
     *         console.log(`Loaded ${count} commits from cache`);
     *     }
     * }
     * ```
     * @param {Uint8Array} bytes
     * @returns {number}
     */
    importCacheBytes(bytes) {
        const ptr0 = passArray8ToWasm0(bytes, wasm.__wbindgen_export);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.rource_importCacheBytes(this.__wbg_ptr, ptr0, len0);
        return ret >>> 0;
    }
    /**
     * Imports commits from a binary cache, validating the repository identifier.
     *
     * Returns the number of commits loaded, or 0 if:
     * - The cache is invalid
     * - The repository hash doesn't match
     *
     * # Arguments
     *
     * * `bytes` - The cache bytes.
     * * `repo_id` - The expected repository identifier.
     *
     * # Example
     *
     * ```javascript
     * const bytes = await idb.get('cache', repoHash);
     * const count = rource.importCacheBytesWithRepoId(bytes, repoUrl);
     * if (count === 0) {
     *     // Cache miss or mismatch - fallback to parsing
     * }
     * ```
     * @param {Uint8Array} bytes
     * @param {string} repo_id
     * @returns {number}
     */
    importCacheBytesWithRepoId(bytes, repo_id) {
        const ptr0 = passArray8ToWasm0(bytes, wasm.__wbindgen_export);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(repo_id, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.rource_importCacheBytesWithRepoId(this.__wbg_ptr, ptr0, len0, ptr1, len1);
        return ret >>> 0;
    }
    /**
     * Initializes the file icon system.
     *
     * This pre-generates icons for common file extensions (rs, js, py, etc.)
     * and stores them for efficient rendering:
     * - **wgpu**: Uses GPU texture arrays for batched rendering
     * - **WebGL2**: Uses GPU texture arrays (WebGL2 supports `TEXTURE_2D_ARRAY`)
     * - **Software**: Uses CPU textures
     *
     * # Returns
     *
     * `true` if initialization succeeded, `false` otherwise.
     *
     * # Example (JavaScript)
     * ```javascript
     * const success = rource.initFileIcons();
     * console.log('File icons initialized:', success);
     * ```
     * @returns {boolean}
     */
    initFileIcons() {
        const ret = wasm.rource_initFileIcons(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether auto-fit mode is currently enabled.
     * @returns {boolean}
     */
    isAutoFit() {
        const ret = wasm.rource_isAutoFit(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns true if the GPU context is lost.
     * @returns {boolean}
     */
    isContextLost() {
        const ret = wasm.rource_isContextLost(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns true if using a GPU-accelerated renderer (wgpu or WebGL2).
     * @returns {boolean}
     */
    isGPUAccelerated() {
        const ret = wasm.rource_isGPUAccelerated(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether GPU visibility culling is currently active.
     *
     * This checks all conditions required for GPU culling:
     * 1. GPU culling is enabled via `setUseGPUCulling(true)`
     * 2. wgpu backend is being used
     * 3. Total entity count exceeds threshold (if threshold > 0)
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isGPUCullingActive()) {
     *     console.log('GPU culling is running');
     * }
     * ```
     * @returns {boolean}
     */
    isGPUCullingActive() {
        const ret = wasm.rource_isGPUCullingActive(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether GPU visibility culling is currently enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU culling:', rource.isGPUCullingEnabled());
     * ```
     * @returns {boolean}
     */
    isGPUCullingEnabled() {
        const ret = wasm.rource_isGPUCullingEnabled(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether GPU physics is currently active.
     *
     * This checks all conditions required for GPU physics:
     * 1. GPU physics is enabled via `setUseGPUPhysics(true)`
     * 2. wgpu backend is being used
     * 3. Directory count exceeds threshold (if threshold > 0)
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isGPUPhysicsActive()) {
     *     console.log('GPU physics is running');
     * }
     * ```
     * @returns {boolean}
     */
    isGPUPhysicsActive() {
        const ret = wasm.rource_isGPUPhysicsActive(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether GPU physics is currently enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU physics:', rource.isGPUPhysicsEnabled());
     * ```
     * @returns {boolean}
     */
    isGPUPhysicsEnabled() {
        const ret = wasm.rource_isGPUPhysicsEnabled(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether playback is active.
     * @returns {boolean}
     */
    isPlaying() {
        const ret = wasm.rource_isPlaying(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns true if the `profiling` feature is enabled.
     *
     * When true, Performance API marks are added to frames for Chrome `DevTools`.
     * @returns {boolean}
     */
    isProfilingEnabled() {
        const ret = wasm.rource_isProfilingEnabled(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns true if the `tracing` feature is enabled.
     *
     * When true, Rust tracing spans are routed to browser console.
     * @returns {boolean}
     */
    isTracingEnabled() {
        const ret = wasm.rource_isProfilingEnabled(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether vsync is currently enabled.
     *
     * Returns `true` if:
     * - Using wgpu backend with vsync enabled
     * - Using WebGL2 or software backend (always vsync-aligned)
     *
     * # Example (JavaScript)
     * ```javascript
     * const vsyncEnabled = rource.isVsyncEnabled();
     * console.log('Vsync:', vsyncEnabled ? 'ON' : 'OFF');
     * ```
     * @returns {boolean}
     */
    isVsyncEnabled() {
        const ret = wasm.rource_isVsyncEnabled(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns whether the watermark is enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isWatermarkEnabled()) {
     *     console.log('Watermark is visible');
     * }
     * ```
     * @returns {boolean}
     */
    isWatermarkEnabled() {
        const ret = wasm.rource_isWatermarkEnabled(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns true if using WebGL2 renderer.
     * @returns {boolean}
     */
    isWebGL2() {
        const ret = wasm.rource_isWebGL2(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Returns true if using wgpu (WebGPU) renderer.
     * @returns {boolean}
     */
    isWgpu() {
        const ret = wasm.rource_isWgpu(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Loads commits from custom pipe-delimited format.
     *
     * Format: `timestamp|author|action|path` per line
     *
     * Uses lenient parsing by default to skip invalid lines (e.g., lines with
     * pipe characters in author names or unsupported git statuses).
     *
     * # Commit Limit
     *
     * If the log contains more commits than `maxCommits` (default 100,000),
     * only the first `maxCommits` commits are loaded. Check `wasCommitsTruncated()`
     * to detect if truncation occurred.
     * @param {string} log
     * @returns {number}
     */
    loadCustomLog(log) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            const ptr0 = passStringToWasm0(log, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len0 = WASM_VECTOR_LEN;
            wasm.rource_loadCustomLog(retptr, this.__wbg_ptr, ptr0, len0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            var r2 = getDataViewMemory0().getInt32(retptr + 4 * 2, true);
            if (r2) {
                throw takeObject(r1);
            }
            return r0 >>> 0;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Loads commits from git log format.
     *
     * Uses lenient parsing to handle malformed lines gracefully.
     *
     * # Commit Limit
     *
     * If the log contains more commits than `maxCommits` (default 100,000),
     * only the first `maxCommits` commits are loaded. Check `wasCommitsTruncated()`
     * to detect if truncation occurred.
     * @param {string} log
     * @returns {number}
     */
    loadGitLog(log) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            const ptr0 = passStringToWasm0(log, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len0 = WASM_VECTOR_LEN;
            wasm.rource_loadGitLog(retptr, this.__wbg_ptr, ptr0, len0);
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            var r2 = getDataViewMemory0().getInt32(retptr + 4 * 2, true);
            if (r2) {
                throw takeObject(r1);
            }
            return r0 >>> 0;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Handles keyboard events.
     *
     * Supports the following shortcuts:
     * - Space: Toggle play/pause
     * - +/-: Zoom in/out
     * - Arrows: Pan camera
     * - R: Reset camera
     * - L: Toggle labels
     * - [/]: Decrease/increase speed
     * - </> or ,/.: Step backward/forward
     * - Home/End: Jump to start/end
     * @param {string} key
     */
    onKeyDown(key) {
        const ptr0 = passStringToWasm0(key, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_onKeyDown(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Handles mouse down events.
     *
     * Initiates entity dragging if an entity is clicked, otherwise starts
     * camera panning mode.
     * @param {number} x
     * @param {number} y
     */
    onMouseDown(x, y) {
        wasm.rource_onMouseDown(this.__wbg_ptr, x, y);
    }
    /**
     * Handles mouse move events.
     *
     * Updates entity position if dragging, or pans camera if no entity is selected.
     * @param {number} x
     * @param {number} y
     */
    onMouseMove(x, y) {
        wasm.rource_onMouseMove(this.__wbg_ptr, x, y);
    }
    /**
     * Handles mouse up events.
     *
     * Releases any dragged entity and resets drag state.
     */
    onMouseUp() {
        wasm.rource_onMouseUp(this.__wbg_ptr);
    }
    /**
     * Handles mouse wheel events for zooming.
     *
     * Zooms toward the mouse cursor position for intuitive navigation.
     * @param {number} delta_y
     * @param {number} mouse_x
     * @param {number} mouse_y
     */
    onWheel(delta_y, mouse_x, mouse_y) {
        wasm.rource_onWheel(this.__wbg_ptr, delta_y, mouse_x, mouse_y);
    }
    /**
     * Pans the camera by the given delta in screen pixels.
     * Disables auto-fit when user manually pans.
     * @param {number} dx
     * @param {number} dy
     */
    pan(dx, dy) {
        wasm.rource_pan(this.__wbg_ptr, dx, dy);
    }
    /**
     * Pauses playback.
     */
    pause() {
        wasm.rource_pause(this.__wbg_ptr);
    }
    /**
     * Starts playback.
     */
    play() {
        wasm.rource_play(this.__wbg_ptr);
    }
    /**
     * Prepares the renderer for full map export.
     *
     * Resizes canvas and positions camera for high-resolution capture.
     * Call `forceRender()` after this, then `captureScreenshot()`.
     *
     * # Arguments
     * * `width` - Target canvas width
     * * `height` - Target canvas height
     * * `zoom` - Zoom level for the export
     * * `center_x` - World X coordinate for camera center
     * * `center_y` - World Y coordinate for camera center
     * @param {number} width
     * @param {number} height
     * @param {number} zoom
     * @param {number} center_x
     * @param {number} center_y
     */
    prepareFullMapExport(width, height, zoom, center_x, center_y) {
        wasm.rource_prepareFullMapExport(this.__wbg_ptr, width, height, zoom, center_x, center_y);
    }
    /**
     * Attempts to recover from a lost GPU context.
     * @returns {boolean}
     */
    recoverContext() {
        const ret = wasm.rource_recoverContext(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Registers a custom icon color for a file extension.
     *
     * If the extension is already registered, this does nothing.
     * If file icons are not initialized, returns `false`.
     *
     * # Arguments
     *
     * * `extension` - File extension without dot (e.g., "custom", "myext")
     * * `hex_color` - Color as hex string (e.g., "#FF5500" or "FF5500")
     *
     * # Returns
     *
     * `true` if the icon was registered, `false` otherwise.
     *
     * # Example (JavaScript)
     * ```javascript
     * // Register a custom file extension with orange color
     * rource.registerFileIcon("myext", "#FF5500");
     * ```
     * @param {string} extension
     * @param {string} hex_color
     * @returns {boolean}
     */
    registerFileIcon(extension, hex_color) {
        const ptr0 = passStringToWasm0(extension, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(hex_color, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.rource_registerFileIcon(this.__wbg_ptr, ptr0, len0, ptr1, len1);
        return ret !== 0;
    }
    /**
     * Resets the camera to fit all content.
     */
    resetCamera() {
        wasm.rource_resetCamera(this.__wbg_ptr);
    }
    /**
     * Resets all error metrics to zero.
     *
     * Call this when starting a new session or after recovering from errors.
     *
     * # Example
     *
     * ```javascript
     * // Reset metrics for a clean start
     * rource.resetErrorMetrics();
     * ```
     */
    resetErrorMetrics() {
        wasm.rource_resetErrorMetrics(this.__wbg_ptr);
    }
    /**
     * Resizes the canvas and renderer.
     *
     * Should be called when the canvas element size changes.
     * @param {number} width
     * @param {number} height
     */
    resize(width, height) {
        wasm.rource_resize(this.__wbg_ptr, width, height);
    }
    /**
     * Restores the renderer after full map export.
     *
     * Resizes canvas back to normal dimensions and fits camera to content.
     *
     * # Arguments
     * * `width` - Original canvas width
     * * `height` - Original canvas height
     * @param {number} width
     * @param {number} height
     */
    restoreAfterExport(width, height) {
        wasm.rource_restoreAfterExport(this.__wbg_ptr, width, height);
    }
    /**
     * Restores camera state from previously saved values.
     *
     * Use with `getCameraState()` to save/restore view positions.
     * @param {number} x
     * @param {number} y
     * @param {number} zoom
     */
    restoreCameraState(x, y, zoom) {
        wasm.rource_restoreCameraState(this.__wbg_ptr, x, y, zoom);
    }
    /**
     * Seeks to a specific commit index.
     *
     * This rebuilds the scene state by replaying all commits up to the
     * specified index, then pre-warms the physics simulation.
     *
     * # Performance Warning
     *
     * For large repositories, seeking to a distant commit (e.g., commit 50,000
     * in a 100K commit repo) will apply all previous commits synchronously,
     * which may cause brief UI freezing. Consider using incremental playback
     * for very large repositories.
     * @param {number} commit_index
     */
    seek(commit_index) {
        wasm.rource_seek(this.__wbg_ptr, commit_index);
    }
    /**
     * Enables or disables auto-fit mode.
     *
     * When enabled, the camera automatically zooms out to keep all content visible
     * as the visualization grows. Manual zoom/pan operations disable auto-fit.
     *
     * Auto-fit is disabled by default due to coordination issues with LOD culling
     * and spatial indexing. Use `resetCamera()` for one-time camera fitting instead.
     * @param {boolean} enabled
     */
    setAutoFit(enabled) {
        wasm.rource_setAutoFit(this.__wbg_ptr, enabled);
    }
    /**
     * Sets the background color (hex string like "#000000" or "000000").
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setBackgroundColor("#1a1a2e");
     * ```
     * @param {string} hex
     */
    setBackgroundColor(hex) {
        const ptr0 = passStringToWasm0(hex, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_setBackgroundColor(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Sets whether to show bloom effect.
     *
     * Bloom creates a glow around bright elements.
     * Syncs the setting to the active renderer backend.
     * @param {boolean} enabled
     */
    setBloom(enabled) {
        wasm.rource_setBloom(this.__wbg_ptr, enabled);
    }
    /**
     * Sets the branch depth fade rate.
     *
     * Higher values make deep branches fade faster.
     * Range: [0.0, 1.0], Default: 0.3
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setBranchDepthFade(0.7);
     * ```
     * @param {number} fade
     */
    setBranchDepthFade(fade) {
        wasm.rource_setBranchDepthFade(this.__wbg_ptr, fade);
    }
    /**
     * Sets the maximum branch opacity.
     *
     * Controls visibility of directory-to-parent connections.
     * Range: [0.0, 1.0], Default: 0.35
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setBranchOpacityMax(0.15);
     * ```
     * @param {number} opacity
     */
    setBranchOpacityMax(opacity) {
        wasm.rource_setBranchOpacityMax(this.__wbg_ptr, opacity);
    }
    /**
     * Sets a custom watermark with both primary and secondary text.
     *
     * This is a convenience method that enables the watermark and sets both text values.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setCustomWatermark("My Project", "© 2026 My Company");
     * ```
     * @param {string} text
     * @param {string} subtext
     */
    setCustomWatermark(text, subtext) {
        const ptr0 = passStringToWasm0(text, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(subtext, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len1 = WASM_VECTOR_LEN;
        wasm.rource_setCustomWatermark(this.__wbg_ptr, ptr0, len0, ptr1, len1);
    }
    /**
     * Sets the depth distance exponent for non-linear depth scaling.
     *
     * Values > 1.0 add extra spacing at deeper levels.
     * Range: [0.5, 2.0], Default: 1.0 (linear)
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setDepthDistanceExponent(1.3);
     * ```
     * @param {number} exponent
     */
    setDepthDistanceExponent(exponent) {
        wasm.rource_setDepthDistanceExponent(this.__wbg_ptr, exponent);
    }
    /**
     * Sets the font size for labels.
     *
     * Range: [4.0, 200.0]
     * @param {number} size
     */
    setFontSize(size) {
        wasm.rource_setFontSize(this.__wbg_ptr, size);
    }
    /**
     * Sets the entity count threshold for enabling GPU culling.
     *
     * When the total visible entity count exceeds this threshold, GPU culling
     * will be used (if enabled and wgpu backend is active).
     *
     * Set to 0 to always use GPU culling when enabled (ignores entity count).
     *
     * Default: 10000 entities
     *
     * # Arguments
     * * `threshold` - Minimum entity count to trigger GPU culling
     *
     * # Example (JavaScript)
     * ```javascript
     * // Use GPU culling for scenes with 5000+ entities
     * rource.setGPUCullingThreshold(5000);
     *
     * // Always use GPU culling when enabled (no threshold)
     * rource.setGPUCullingThreshold(0);
     * ```
     * @param {number} threshold
     */
    setGPUCullingThreshold(threshold) {
        wasm.rource_setGPUCullingThreshold(this.__wbg_ptr, threshold);
    }
    /**
     * Sets the directory count threshold for enabling GPU physics.
     *
     * When the scene has more directories than this threshold, GPU physics
     * will be used (if enabled and wgpu backend is active).
     *
     * Set to 0 to always use GPU physics when enabled (ignores directory count).
     *
     * Default: 500 directories
     *
     * # Arguments
     * * `threshold` - Minimum directory count to trigger GPU physics
     *
     * # Example (JavaScript)
     * ```javascript
     * // Use GPU physics for repos with 1000+ directories
     * rource.setGPUPhysicsThreshold(1000);
     *
     * // Always use GPU physics when enabled (no threshold)
     * rource.setGPUPhysicsThreshold(0);
     * ```
     * @param {number} threshold
     */
    setGPUPhysicsThreshold(threshold) {
        wasm.rource_setGPUPhysicsThreshold(this.__wbg_ptr, threshold);
    }
    /**
     * Sets the layout preset for different repository sizes.
     *
     * # Presets
     * * "small" - Repos < 1000 files (compact layout)
     * * "medium" - Repos 1000-10000 files (default)
     * * "large" - Repos 10000-50000 files (spread out)
     * * "massive" - Repos 50000+ files (maximum spread)
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setLayoutPreset("massive");
     * ```
     * @param {string} preset
     */
    setLayoutPreset(preset) {
        const ptr0 = passStringToWasm0(preset, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_setLayoutPreset(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Sets the maximum number of commits to load.
     *
     * Call this before `loadGitLog()` or `loadCustomLog()` to change the limit.
     * Default is 100,000 commits.
     *
     * # Arguments
     *
     * * `max` - Maximum commits to load (0 = unlimited, use with caution)
     * @param {number} max
     */
    setMaxCommits(max) {
        wasm.rource_setMaxCommits(this.__wbg_ptr, max);
    }
    /**
     * Sets the radial distance scale for directory positioning.
     *
     * Higher values spread the tree outward more.
     * Range: [40.0, 500.0], Default: 80.0
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setRadialDistanceScale(160.0);
     * ```
     * @param {number} scale
     */
    setRadialDistanceScale(scale) {
        wasm.rource_setRadialDistanceScale(this.__wbg_ptr, scale);
    }
    /**
     * Sets whether to show labels (user names, file names, directory names).
     * @param {boolean} show
     */
    setShowLabels(show) {
        wasm.rource_setShowLabels(this.__wbg_ptr, show);
    }
    /**
     * Sets playback speed (seconds per day of repository history).
     *
     * Lower values = faster playback. Default is 10.0.
     * Range: [0.01, 1000.0]
     * @param {number} seconds_per_day
     */
    setSpeed(seconds_per_day) {
        wasm.rource_setSpeed(this.__wbg_ptr, seconds_per_day);
    }
    /**
     * Enables or disables GPU visibility culling.
     *
     * When enabled and using the wgpu backend, visibility culling runs on
     * the GPU using compute shaders. This is beneficial for extreme-scale
     * scenarios (10,000+ visible entities) where CPU culling becomes a
     * bottleneck.
     *
     * **Note**: GPU culling only works with the wgpu backend. When using
     * WebGL2 or Software renderers, this setting is ignored and CPU culling
     * is always used.
     *
     * For most use cases, the default CPU-side quadtree culling is sufficient.
     *
     * # Arguments
     * * `enabled` - Whether to enable GPU culling
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isWgpu()) {
     *     rource.setUseGPUCulling(true);
     *     console.log('GPU culling enabled');
     * }
     * ```
     * @param {boolean} enabled
     */
    setUseGPUCulling(enabled) {
        wasm.rource_setUseGPUCulling(this.__wbg_ptr, enabled);
    }
    /**
     * Enables or disables GPU physics simulation.
     *
     * When enabled and using the wgpu backend, the force-directed physics
     * simulation runs on the GPU using compute shaders. This provides
     * significant performance improvements for large repositories (500+
     * directories) where CPU physics becomes the bottleneck.
     *
     * **Note**: GPU physics only works with the wgpu backend. When using
     * WebGL2 or Software renderers, this setting is ignored and CPU physics
     * is always used.
     *
     * # Arguments
     * * `enabled` - Whether to enable GPU physics
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isWgpu()) {
     *     rource.setUseGPUPhysics(true);
     *     console.log('GPU physics enabled');
     * }
     * ```
     * @param {boolean} enabled
     */
    setUseGPUPhysics(enabled) {
        wasm.rource_setUseGPUPhysics(this.__wbg_ptr, enabled);
    }
    /**
     * Sets vsync mode for the renderer.
     *
     * This controls whether frames are synchronized to the display refresh rate:
     * - `true` (default): Vsync enabled, frames sync to display refresh (~60 FPS)
     * - `false`: Vsync disabled, uncapped frame rate (300+ FPS possible)
     *
     * **Note:** This only affects the wgpu backend (WebGPU). WebGL2 and software
     * renderers always use requestAnimationFrame timing which is vsync-aligned.
     *
     * **Performance Impact:** Disabling vsync increases GPU utilization and power
     * consumption. Use with caution on battery-powered devices.
     *
     * # Example (JavaScript)
     * ```javascript
     * // Disable vsync for uncapped FPS
     * rource.setVsync(false);
     *
     * // Re-enable vsync for power efficiency
     * rource.setVsync(true);
     * ```
     * @param {boolean} enabled
     */
    setVsync(enabled) {
        wasm.rource_setVsync(this.__wbg_ptr, enabled);
    }
    /**
     * Sets the watermark text color (hex string like "#FFFFFF" or "FFFFFF").
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkColor("#FFFFFF");
     * ```
     * @param {string} hex
     */
    setWatermarkColor(hex) {
        const ptr0 = passStringToWasm0(hex, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_setWatermarkColor(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Sets whether the watermark is enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkEnabled(true);
     * ```
     * @param {boolean} enabled
     */
    setWatermarkEnabled(enabled) {
        wasm.rource_setWatermarkEnabled(this.__wbg_ptr, enabled);
    }
    /**
     * Sets the watermark font size.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkFontSize(16);
     * ```
     * @param {number} size
     */
    setWatermarkFontSize(size) {
        wasm.rource_setWatermarkFontSize(this.__wbg_ptr, size);
    }
    /**
     * Sets the watermark margin from the screen edge in pixels.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkMargin(20);
     * ```
     * @param {number} margin
     */
    setWatermarkMargin(margin) {
        wasm.rource_setWatermarkMargin(this.__wbg_ptr, margin);
    }
    /**
     * Sets the watermark opacity (0.0 = invisible, 1.0 = fully opaque).
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkOpacity(0.5);
     * ```
     * @param {number} opacity
     */
    setWatermarkOpacity(opacity) {
        wasm.rource_setWatermarkOpacity(this.__wbg_ptr, opacity);
    }
    /**
     * Sets the watermark position.
     *
     * Valid positions:
     * - "top-left" or "tl"
     * - "top-right" or "tr"
     * - "bottom-left" or "bl"
     * - "bottom-right" or "br" (default)
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkPosition("bottom-left");
     * ```
     * @param {string} position
     */
    setWatermarkPosition(position) {
        const ptr0 = passStringToWasm0(position, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_setWatermarkPosition(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Sets the secondary watermark text (displayed below the primary text).
     *
     * Pass an empty string to clear the subtext.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkSubtext("© 2026 My Company");
     * ```
     * @param {string} text
     */
    setWatermarkSubtext(text) {
        const ptr0 = passStringToWasm0(text, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_setWatermarkSubtext(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Sets the primary watermark text.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkText("My Project");
     * ```
     * @param {string} text
     */
    setWatermarkText(text) {
        const ptr0 = passStringToWasm0(text, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_setWatermarkText(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Steps backward to the previous commit.
     */
    stepBackward() {
        wasm.rource_stepBackward(this.__wbg_ptr);
    }
    /**
     * Steps forward to the next commit.
     */
    stepForward() {
        wasm.rource_stepForward(this.__wbg_ptr);
    }
    /**
     * Toggles play/pause state.
     */
    togglePlay() {
        wasm.rource_togglePlay(this.__wbg_ptr);
    }
    /**
     * Warms up the GPU visibility culling compute pipeline.
     *
     * Call this during initialization to pre-compile compute shaders
     * and avoid first-frame stuttering when GPU culling is first used.
     *
     * **Note**: Only has an effect when using the wgpu backend.
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isWgpu()) {
     *     rource.warmupGPUCulling();
     *     rource.setUseGPUCulling(true);
     * }
     * ```
     */
    warmupGPUCulling() {
        wasm.rource_warmupGPUCulling(this.__wbg_ptr);
    }
    /**
     * Warms up the GPU physics compute pipeline.
     *
     * Call this during initialization to pre-compile compute shaders
     * and avoid first-frame stuttering when GPU physics is first used.
     *
     * **Note**: Only has an effect when using the wgpu backend.
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isWgpu()) {
     *     rource.warmupGPUPhysics();
     *     rource.setUseGPUPhysics(true);
     * }
     * ```
     */
    warmupGPUPhysics() {
        wasm.rource_warmupGPUPhysics(this.__wbg_ptr);
    }
    /**
     * Returns true if commits were truncated during the last load.
     *
     * When true, only the first `maxCommits` commits were loaded.
     * Use `getOriginalCommitCount()` to see the full count.
     * @returns {boolean}
     */
    wasCommitsTruncated() {
        const ret = wasm.rource_wasCommitsTruncated(this.__wbg_ptr);
        return ret !== 0;
    }
    /**
     * Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
     *
     * Max zoom is 1000.0 to support deep zoom into massive repositories.
     * Min zoom is `AUTO_FIT_MIN_ZOOM` (0.05) to prevent LOD culling all entities.
     * Disables auto-fit when user manually zooms.
     * @param {number} factor
     */
    zoom(factor) {
        wasm.rource_zoom(this.__wbg_ptr, factor);
    }
    /**
     * Zooms the camera toward a specific screen point.
     *
     * This provides intuitive zoom behavior where the point under the cursor
     * stays fixed during zoom operations.
     * Min zoom is `AUTO_FIT_MIN_ZOOM` (0.05) to prevent LOD culling all entities.
     * Disables auto-fit when user manually zooms.
     * @param {number} screen_x
     * @param {number} screen_y
     * @param {number} factor
     */
    zoomToward(screen_x, screen_y, factor) {
        wasm.rource_zoomToward(this.__wbg_ptr, screen_x, screen_y, factor);
    }
}
if (Symbol.dispose) Rource.prototype[Symbol.dispose] = Rource.prototype.free;

/**
 * Set up better panic messages for debugging in browser console.
 */
export function init_panic_hook() {
    wasm.init_panic_hook();
}

function __wbg_get_imports() {
    const import0 = {
        __proto__: null,
        __wbg_Window_7b2011a6368164ef: function(arg0) {
            const ret = getObject(arg0).Window;
            return addHeapObject(ret);
        },
        __wbg_WorkerGlobalScope_4bddbcb12b3f5a28: function(arg0) {
            const ret = getObject(arg0).WorkerGlobalScope;
            return addHeapObject(ret);
        },
        __wbg___wbindgen_boolean_get_bbbb1c18aa2f5e25: function(arg0) {
            const v = getObject(arg0);
            const ret = typeof(v) === 'boolean' ? v : undefined;
            return isLikeNone(ret) ? 0xFFFFFF : ret ? 1 : 0;
        },
        __wbg___wbindgen_debug_string_0bc8482c6e3508ae: function(arg0, arg1) {
            const ret = debugString(getObject(arg1));
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg___wbindgen_is_function_0095a73b8b156f76: function(arg0) {
            const ret = typeof(getObject(arg0)) === 'function';
            return ret;
        },
        __wbg___wbindgen_is_null_ac34f5003991759a: function(arg0) {
            const ret = getObject(arg0) === null;
            return ret;
        },
        __wbg___wbindgen_is_undefined_9e4d92534c42d778: function(arg0) {
            const ret = getObject(arg0) === undefined;
            return ret;
        },
        __wbg___wbindgen_memory_bd1fbcf21fbef3c8: function() {
            const ret = wasm.memory;
            return addHeapObject(ret);
        },
        __wbg___wbindgen_number_get_8ff4255516ccad3e: function(arg0, arg1) {
            const obj = getObject(arg1);
            const ret = typeof(obj) === 'number' ? obj : undefined;
            getDataViewMemory0().setFloat64(arg0 + 8 * 1, isLikeNone(ret) ? 0 : ret, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, !isLikeNone(ret), true);
        },
        __wbg___wbindgen_string_get_72fb696202c56729: function(arg0, arg1) {
            const obj = getObject(arg1);
            const ret = typeof(obj) === 'string' ? obj : undefined;
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg___wbindgen_throw_be289d5034ed271b: function(arg0, arg1) {
            throw new Error(getStringFromWasm0(arg0, arg1));
        },
        __wbg__wbg_cb_unref_d9b87ff7982e3b21: function(arg0) {
            getObject(arg0)._wbg_cb_unref();
        },
        __wbg_activeTexture_6f9a710514686c24: function(arg0, arg1) {
            getObject(arg0).activeTexture(arg1 >>> 0);
        },
        __wbg_activeTexture_7e39cb8fdf4b6d5a: function(arg0, arg1) {
            getObject(arg0).activeTexture(arg1 >>> 0);
        },
        __wbg_apply_2e22c45cb4f12415: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = Reflect.apply(getObject(arg0), getObject(arg1), getObject(arg2));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_attachShader_32114efcf2744eb6: function(arg0, arg1, arg2) {
            getObject(arg0).attachShader(getObject(arg1), getObject(arg2));
        },
        __wbg_attachShader_b36058e5c9eeaf54: function(arg0, arg1, arg2) {
            getObject(arg0).attachShader(getObject(arg1), getObject(arg2));
        },
        __wbg_beginComputePass_8971ad8382254094: function(arg0, arg1) {
            const ret = getObject(arg0).beginComputePass(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_beginQuery_0fdf154e1da0e73d: function(arg0, arg1, arg2) {
            getObject(arg0).beginQuery(arg1 >>> 0, getObject(arg2));
        },
        __wbg_beginRenderPass_599b98d9a6ba5692: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).beginRenderPass(getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_bindAttribLocation_5cfc7fa688df5051: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).bindAttribLocation(getObject(arg1), arg2 >>> 0, getStringFromWasm0(arg3, arg4));
        },
        __wbg_bindAttribLocation_ce78bfb13019dbe6: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).bindAttribLocation(getObject(arg1), arg2 >>> 0, getStringFromWasm0(arg3, arg4));
        },
        __wbg_bindBufferBase_e36c8faca91d77ea: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).bindBufferBase(arg1 >>> 0, arg2 >>> 0, getObject(arg3));
        },
        __wbg_bindBufferRange_009d206fe9e4151e: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).bindBufferRange(arg1 >>> 0, arg2 >>> 0, getObject(arg3), arg4, arg5);
        },
        __wbg_bindBuffer_69a7a0b8f3f9b9cf: function(arg0, arg1, arg2) {
            getObject(arg0).bindBuffer(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindBuffer_c9068e8712a034f5: function(arg0, arg1, arg2) {
            getObject(arg0).bindBuffer(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindFramebuffer_031c73ba501cb8f6: function(arg0, arg1, arg2) {
            getObject(arg0).bindFramebuffer(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindFramebuffer_7815ca611abb057f: function(arg0, arg1, arg2) {
            getObject(arg0).bindFramebuffer(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindRenderbuffer_8a2aa4e3d1fb5443: function(arg0, arg1, arg2) {
            getObject(arg0).bindRenderbuffer(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindRenderbuffer_db37c1bac9ed4da0: function(arg0, arg1, arg2) {
            getObject(arg0).bindRenderbuffer(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindSampler_96f0e90e7bc31da9: function(arg0, arg1, arg2) {
            getObject(arg0).bindSampler(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindTexture_b2b7b1726a83f93e: function(arg0, arg1, arg2) {
            getObject(arg0).bindTexture(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindTexture_ec13ddcb9dc8e032: function(arg0, arg1, arg2) {
            getObject(arg0).bindTexture(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindVertexArrayOES_c2610602f7485b3f: function(arg0, arg1) {
            getObject(arg0).bindVertexArrayOES(getObject(arg1));
        },
        __wbg_bindVertexArray_78220d1edb1d2382: function(arg0, arg1) {
            getObject(arg0).bindVertexArray(getObject(arg1));
        },
        __wbg_blendColor_1d50ac87d9a2794b: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).blendColor(arg1, arg2, arg3, arg4);
        },
        __wbg_blendColor_e799d452ab2a5788: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).blendColor(arg1, arg2, arg3, arg4);
        },
        __wbg_blendEquationSeparate_1b12c43928cc7bc1: function(arg0, arg1, arg2) {
            getObject(arg0).blendEquationSeparate(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_blendEquationSeparate_a8094fbec94cf80e: function(arg0, arg1, arg2) {
            getObject(arg0).blendEquationSeparate(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_blendEquation_82202f34c4c00e50: function(arg0, arg1) {
            getObject(arg0).blendEquation(arg1 >>> 0);
        },
        __wbg_blendEquation_e9b99928ed1494ad: function(arg0, arg1) {
            getObject(arg0).blendEquation(arg1 >>> 0);
        },
        __wbg_blendFuncSeparate_95465944f788a092: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).blendFuncSeparate(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_blendFuncSeparate_f366c170c5097fbe: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).blendFuncSeparate(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_blendFunc_2ef59299d10c662d: function(arg0, arg1, arg2) {
            getObject(arg0).blendFunc(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_blendFunc_446658e7231ab9c8: function(arg0, arg1, arg2) {
            getObject(arg0).blendFunc(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_blitFramebuffer_d730a23ab4db248e: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).blitFramebuffer(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0);
        },
        __wbg_bufferData_037b591220c42be7: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).bufferData(arg1 >>> 0, getArrayU8FromWasm0(arg2, arg3), arg4 >>> 0);
        },
        __wbg_bufferData_1be8450fab534758: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).bufferData(arg1 >>> 0, arg2, arg3 >>> 0);
        },
        __wbg_bufferData_32d26eba0c74a53c: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).bufferData(arg1 >>> 0, arg2, arg3 >>> 0);
        },
        __wbg_bufferData_52235e85894af988: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).bufferData(arg1 >>> 0, getObject(arg2), arg3 >>> 0);
        },
        __wbg_bufferData_98f6c413a8f0f139: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).bufferData(arg1 >>> 0, getObject(arg2), arg3 >>> 0);
        },
        __wbg_bufferSubData_33eebcc173094f6a: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).bufferSubData(arg1 >>> 0, arg2, getObject(arg3));
        },
        __wbg_bufferSubData_3e902f031adf13fd: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).bufferSubData(arg1 >>> 0, arg2, getObject(arg3));
        },
        __wbg_bufferSubData_4edddd9f793fec78: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).bufferSubData(arg1 >>> 0, arg2, getArrayU8FromWasm0(arg3, arg4));
        },
        __wbg_buffer_26d0910f3a5bc899: function(arg0) {
            const ret = getObject(arg0).buffer;
            return addHeapObject(ret);
        },
        __wbg_buffer_7b5f53e46557d8f1: function(arg0) {
            const ret = getObject(arg0).buffer;
            return addHeapObject(ret);
        },
        __wbg_byteLength_7b03c17ff1e4037f: function(arg0) {
            const ret = getObject(arg0).byteLength;
            return ret;
        },
        __wbg_call_389efe28435a9388: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).call(getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_call_4708e0c13bdc8e95: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).call(getObject(arg1), getObject(arg2));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_checkFramebufferStatus_9d9acdb931c7370b: function(arg0, arg1) {
            const ret = getObject(arg0).checkFramebufferStatus(arg1 >>> 0);
            return ret;
        },
        __wbg_clearBufferfv_ac87d92e2f45d80c: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).clearBufferfv(arg1 >>> 0, arg2, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_clearBufferiv_69ff24bb52ec4c88: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).clearBufferiv(arg1 >>> 0, arg2, getArrayI32FromWasm0(arg3, arg4));
        },
        __wbg_clearBufferuiv_8ad59a8219aafaca: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).clearBufferuiv(arg1 >>> 0, arg2, getArrayU32FromWasm0(arg3, arg4));
        },
        __wbg_clearColor_404a3b16d43db93b: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).clearColor(arg1, arg2, arg3, arg4);
        },
        __wbg_clearDepth_2b109f644a783a53: function(arg0, arg1) {
            getObject(arg0).clearDepth(arg1);
        },
        __wbg_clearDepth_670099db422a4f91: function(arg0, arg1) {
            getObject(arg0).clearDepth(arg1);
        },
        __wbg_clearStencil_5d243d0dff03c315: function(arg0, arg1) {
            getObject(arg0).clearStencil(arg1);
        },
        __wbg_clearStencil_aa65955bb39d8c18: function(arg0, arg1) {
            getObject(arg0).clearStencil(arg1);
        },
        __wbg_clear_4d801d0d054c3579: function(arg0, arg1) {
            getObject(arg0).clear(arg1 >>> 0);
        },
        __wbg_clear_7187030f892c5ca0: function(arg0, arg1) {
            getObject(arg0).clear(arg1 >>> 0);
        },
        __wbg_clientWaitSync_21865feaeb76a9a5: function(arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).clientWaitSync(getObject(arg1), arg2 >>> 0, arg3 >>> 0);
            return ret;
        },
        __wbg_colorMask_177d9762658e5e28: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).colorMask(arg1 !== 0, arg2 !== 0, arg3 !== 0, arg4 !== 0);
        },
        __wbg_colorMask_7a8dbc86e7376a9b: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).colorMask(arg1 !== 0, arg2 !== 0, arg3 !== 0, arg4 !== 0);
        },
        __wbg_compileShader_63b824e86bb00b8f: function(arg0, arg1) {
            getObject(arg0).compileShader(getObject(arg1));
        },
        __wbg_compileShader_94718a93495d565d: function(arg0, arg1) {
            getObject(arg0).compileShader(getObject(arg1));
        },
        __wbg_compressedTexSubImage2D_215bb115facd5e48: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) {
            getObject(arg0).compressedTexSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, getObject(arg8));
        },
        __wbg_compressedTexSubImage2D_684350eb62830032: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) {
            getObject(arg0).compressedTexSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, getObject(arg8));
        },
        __wbg_compressedTexSubImage2D_d8fbae93bb8c4cc9: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).compressedTexSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8, arg9);
        },
        __wbg_compressedTexSubImage3D_16afa3a47bf1d979: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).compressedTexSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, getObject(arg10));
        },
        __wbg_compressedTexSubImage3D_778008a6293f15ab: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).compressedTexSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10, arg11);
        },
        __wbg_configure_bee5e0250d8526d5: function() { return handleError(function (arg0, arg1) {
            getObject(arg0).configure(getObject(arg1));
        }, arguments); },
        __wbg_copyBufferSubData_a4f9815861ff0ae9: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).copyBufferSubData(arg1 >>> 0, arg2 >>> 0, arg3, arg4, arg5);
        },
        __wbg_copyBufferToBuffer_3e2b8d1e524281f5: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).copyBufferToBuffer(getObject(arg1), arg2, getObject(arg3), arg4, arg5);
        }, arguments); },
        __wbg_copyBufferToBuffer_6a6449c0e5793f4c: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).copyBufferToBuffer(getObject(arg1), arg2, getObject(arg3), arg4);
        }, arguments); },
        __wbg_copyTexSubImage2D_417a65926e3d2490: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) {
            getObject(arg0).copyTexSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8);
        },
        __wbg_copyTexSubImage2D_91ebcd9cd1908265: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) {
            getObject(arg0).copyTexSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8);
        },
        __wbg_copyTexSubImage3D_f62ef4c4eeb9a7dc: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).copyTexSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9);
        },
        __wbg_createBindGroupLayout_f543b79f894eed2e: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).createBindGroupLayout(getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_createBindGroup_06db01d96df151a7: function(arg0, arg1) {
            const ret = getObject(arg0).createBindGroup(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_createBuffer_26534c05e01b8559: function(arg0) {
            const ret = getObject(arg0).createBuffer();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createBuffer_6e69283608e8f98f: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).createBuffer(getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_createBuffer_c4ec897aacc1b91c: function(arg0) {
            const ret = getObject(arg0).createBuffer();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createCommandEncoder_88e8ef64b19cdb2c: function(arg0, arg1) {
            const ret = getObject(arg0).createCommandEncoder(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_createComputePipeline_d24ca7b211444394: function(arg0, arg1) {
            const ret = getObject(arg0).createComputePipeline(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_createFramebuffer_41512c38358a41c4: function(arg0) {
            const ret = getObject(arg0).createFramebuffer();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createFramebuffer_b88ffa8e0fd262c4: function(arg0) {
            const ret = getObject(arg0).createFramebuffer();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createPipelineLayout_0f960a922b66be56: function(arg0, arg1) {
            const ret = getObject(arg0).createPipelineLayout(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_createProgram_98aaa91f7c81c5e2: function(arg0) {
            const ret = getObject(arg0).createProgram();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createProgram_9b7710a1f2701c2c: function(arg0) {
            const ret = getObject(arg0).createProgram();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createQuery_7988050efd7e4c48: function(arg0) {
            const ret = getObject(arg0).createQuery();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createRenderPipeline_725209221f17f288: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).createRenderPipeline(getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_createRenderbuffer_1e567f2f4d461710: function(arg0) {
            const ret = getObject(arg0).createRenderbuffer();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createRenderbuffer_a601226a6a680dbe: function(arg0) {
            const ret = getObject(arg0).createRenderbuffer();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createSampler_36aca895fb724d8b: function(arg0, arg1) {
            const ret = getObject(arg0).createSampler(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_createSampler_da6bb96c9ffaaa27: function(arg0) {
            const ret = getObject(arg0).createSampler();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createShaderModule_714b17aece65828e: function(arg0, arg1) {
            const ret = getObject(arg0).createShaderModule(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_createShader_e3ac08ed8c5b14b2: function(arg0, arg1) {
            const ret = getObject(arg0).createShader(arg1 >>> 0);
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createShader_f2b928ca9a426b14: function(arg0, arg1) {
            const ret = getObject(arg0).createShader(arg1 >>> 0);
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createTexture_16d2c8a3d7d4a75a: function(arg0) {
            const ret = getObject(arg0).createTexture();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createTexture_63195fd0d63c3a24: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).createTexture(getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_createTexture_f9451a82c7527ce2: function(arg0) {
            const ret = getObject(arg0).createTexture();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createVertexArrayOES_bd76ceee6ab9b95e: function(arg0) {
            const ret = getObject(arg0).createVertexArrayOES();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createVertexArray_ad5294951ae57497: function(arg0) {
            const ret = getObject(arg0).createVertexArray();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createView_79f49fbd3fb5f94f: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).createView(getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_cullFace_39500f654c67a205: function(arg0, arg1) {
            getObject(arg0).cullFace(arg1 >>> 0);
        },
        __wbg_cullFace_e7e711a14d2c3f48: function(arg0, arg1) {
            getObject(arg0).cullFace(arg1 >>> 0);
        },
        __wbg_deleteBuffer_22fcc93912cbf659: function(arg0, arg1) {
            getObject(arg0).deleteBuffer(getObject(arg1));
        },
        __wbg_deleteBuffer_ab099883c168644d: function(arg0, arg1) {
            getObject(arg0).deleteBuffer(getObject(arg1));
        },
        __wbg_deleteFramebuffer_8de1ca41ac87cfd9: function(arg0, arg1) {
            getObject(arg0).deleteFramebuffer(getObject(arg1));
        },
        __wbg_deleteFramebuffer_9738f3bb85c1ab35: function(arg0, arg1) {
            getObject(arg0).deleteFramebuffer(getObject(arg1));
        },
        __wbg_deleteProgram_9298fb3e3c1d3a78: function(arg0, arg1) {
            getObject(arg0).deleteProgram(getObject(arg1));
        },
        __wbg_deleteProgram_f354e79b8cae8076: function(arg0, arg1) {
            getObject(arg0).deleteProgram(getObject(arg1));
        },
        __wbg_deleteQuery_ea8bf1954febd774: function(arg0, arg1) {
            getObject(arg0).deleteQuery(getObject(arg1));
        },
        __wbg_deleteRenderbuffer_096edada57729468: function(arg0, arg1) {
            getObject(arg0).deleteRenderbuffer(getObject(arg1));
        },
        __wbg_deleteRenderbuffer_0f565f0727b341fc: function(arg0, arg1) {
            getObject(arg0).deleteRenderbuffer(getObject(arg1));
        },
        __wbg_deleteSampler_c6b68c4071841afa: function(arg0, arg1) {
            getObject(arg0).deleteSampler(getObject(arg1));
        },
        __wbg_deleteShader_aaf3b520a64d5d9d: function(arg0, arg1) {
            getObject(arg0).deleteShader(getObject(arg1));
        },
        __wbg_deleteShader_ff70ca962883e241: function(arg0, arg1) {
            getObject(arg0).deleteShader(getObject(arg1));
        },
        __wbg_deleteSync_c8e4a9c735f71d18: function(arg0, arg1) {
            getObject(arg0).deleteSync(getObject(arg1));
        },
        __wbg_deleteTexture_2be78224e5584a8b: function(arg0, arg1) {
            getObject(arg0).deleteTexture(getObject(arg1));
        },
        __wbg_deleteTexture_9d411c0e60ffa324: function(arg0, arg1) {
            getObject(arg0).deleteTexture(getObject(arg1));
        },
        __wbg_deleteVertexArrayOES_197df47ef9684195: function(arg0, arg1) {
            getObject(arg0).deleteVertexArrayOES(getObject(arg1));
        },
        __wbg_deleteVertexArray_7bc7f92769862f93: function(arg0, arg1) {
            getObject(arg0).deleteVertexArray(getObject(arg1));
        },
        __wbg_depthFunc_eb3aa05361dd2eaa: function(arg0, arg1) {
            getObject(arg0).depthFunc(arg1 >>> 0);
        },
        __wbg_depthFunc_f670d4cbb9cd0913: function(arg0, arg1) {
            getObject(arg0).depthFunc(arg1 >>> 0);
        },
        __wbg_depthMask_103091329ca1a750: function(arg0, arg1) {
            getObject(arg0).depthMask(arg1 !== 0);
        },
        __wbg_depthMask_75a36d0065471a4b: function(arg0, arg1) {
            getObject(arg0).depthMask(arg1 !== 0);
        },
        __wbg_depthRange_337bf254e67639bb: function(arg0, arg1, arg2) {
            getObject(arg0).depthRange(arg1, arg2);
        },
        __wbg_depthRange_5579d448b9d7de57: function(arg0, arg1, arg2) {
            getObject(arg0).depthRange(arg1, arg2);
        },
        __wbg_destroy_7602e890b930bb90: function(arg0) {
            getObject(arg0).destroy();
        },
        __wbg_disableVertexAttribArray_24a020060006b10f: function(arg0, arg1) {
            getObject(arg0).disableVertexAttribArray(arg1 >>> 0);
        },
        __wbg_disableVertexAttribArray_4bac633c27bae599: function(arg0, arg1) {
            getObject(arg0).disableVertexAttribArray(arg1 >>> 0);
        },
        __wbg_disable_7fe6fb3e97717f88: function(arg0, arg1) {
            getObject(arg0).disable(arg1 >>> 0);
        },
        __wbg_disable_bd37bdcca1764aea: function(arg0, arg1) {
            getObject(arg0).disable(arg1 >>> 0);
        },
        __wbg_dispatchWorkgroups_d63caaf66ad5bbb0: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).dispatchWorkgroups(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0);
        },
        __wbg_document_ee35a3d3ae34ef6c: function(arg0) {
            const ret = getObject(arg0).document;
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_drawArraysInstancedANGLE_9e4cc507eae8b24d: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).drawArraysInstancedANGLE(arg1 >>> 0, arg2, arg3, arg4);
        },
        __wbg_drawArraysInstanced_ec30adc616ec58d5: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).drawArraysInstanced(arg1 >>> 0, arg2, arg3, arg4);
        },
        __wbg_drawArrays_075228181299b824: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).drawArrays(arg1 >>> 0, arg2, arg3);
        },
        __wbg_drawArrays_2be89c369a29f30b: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).drawArrays(arg1 >>> 0, arg2, arg3);
        },
        __wbg_drawBuffersWEBGL_447bc0a21f8ef22d: function(arg0, arg1) {
            getObject(arg0).drawBuffersWEBGL(getObject(arg1));
        },
        __wbg_drawBuffers_5eccfaacc6560299: function(arg0, arg1) {
            getObject(arg0).drawBuffers(getObject(arg1));
        },
        __wbg_drawElementsInstancedANGLE_6f9da0b845ac6c4e: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).drawElementsInstancedANGLE(arg1 >>> 0, arg2, arg3 >>> 0, arg4, arg5);
        },
        __wbg_drawElementsInstanced_d41fc920ae24717c: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).drawElementsInstanced(arg1 >>> 0, arg2, arg3 >>> 0, arg4, arg5);
        },
        __wbg_drawIndirect_fb473a1c2f258da2: function(arg0, arg1, arg2) {
            getObject(arg0).drawIndirect(getObject(arg1), arg2);
        },
        __wbg_draw_3f782f0d09a907da: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).draw(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_enableVertexAttribArray_475e06c31777296d: function(arg0, arg1) {
            getObject(arg0).enableVertexAttribArray(arg1 >>> 0);
        },
        __wbg_enableVertexAttribArray_aa6e40408261eeb9: function(arg0, arg1) {
            getObject(arg0).enableVertexAttribArray(arg1 >>> 0);
        },
        __wbg_enable_d1ac04dfdd2fb3ae: function(arg0, arg1) {
            getObject(arg0).enable(arg1 >>> 0);
        },
        __wbg_enable_fee40f19b7053ea3: function(arg0, arg1) {
            getObject(arg0).enable(arg1 >>> 0);
        },
        __wbg_endQuery_54f0627d4c931318: function(arg0, arg1) {
            getObject(arg0).endQuery(arg1 >>> 0);
        },
        __wbg_end_8bb194afb9988691: function(arg0) {
            getObject(arg0).end();
        },
        __wbg_end_ae98f313507234ce: function(arg0) {
            getObject(arg0).end();
        },
        __wbg_error_7534b8e9a36f1ab4: function(arg0, arg1) {
            let deferred0_0;
            let deferred0_1;
            try {
                deferred0_0 = arg0;
                deferred0_1 = arg1;
                console.error(getStringFromWasm0(arg0, arg1));
            } finally {
                wasm.__wbindgen_export4(deferred0_0, deferred0_1, 1);
            }
        },
        __wbg_error_9a7fe3f932034cde: function(arg0) {
            console.error(getObject(arg0));
        },
        __wbg_fenceSync_c52a4e24eabfa0d3: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).fenceSync(arg1 >>> 0, arg2 >>> 0);
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_finish_08e2d7b08c066b25: function(arg0, arg1) {
            const ret = getObject(arg0).finish(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_finish_5ebfba3167b3092c: function(arg0) {
            const ret = getObject(arg0).finish();
            return addHeapObject(ret);
        },
        __wbg_finish_ee0b71d14fa50456: function(arg0) {
            getObject(arg0).finish();
        },
        __wbg_flush_7777597fd43065db: function(arg0) {
            getObject(arg0).flush();
        },
        __wbg_flush_e322496f5412e567: function(arg0) {
            getObject(arg0).flush();
        },
        __wbg_framebufferRenderbuffer_850811ed6e26475e: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).framebufferRenderbuffer(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, getObject(arg4));
        },
        __wbg_framebufferRenderbuffer_cd9d55a68a2300ea: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).framebufferRenderbuffer(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, getObject(arg4));
        },
        __wbg_framebufferTexture2D_8adf6bdfc3c56dee: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).framebufferTexture2D(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, getObject(arg4), arg5);
        },
        __wbg_framebufferTexture2D_c283e928186aa542: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).framebufferTexture2D(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, getObject(arg4), arg5);
        },
        __wbg_framebufferTextureLayer_c8328828c8d5eb60: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).framebufferTextureLayer(arg1 >>> 0, arg2 >>> 0, getObject(arg3), arg4, arg5);
        },
        __wbg_framebufferTextureMultiviewOVR_16d049b41d692b91: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            getObject(arg0).framebufferTextureMultiviewOVR(arg1 >>> 0, arg2 >>> 0, getObject(arg3), arg4, arg5, arg6);
        },
        __wbg_frontFace_027e2ec7a7bc347c: function(arg0, arg1) {
            getObject(arg0).frontFace(arg1 >>> 0);
        },
        __wbg_frontFace_d4a6507ad2939b5c: function(arg0, arg1) {
            getObject(arg0).frontFace(arg1 >>> 0);
        },
        __wbg_getBufferSubData_4fc54b4fbb1462d7: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).getBufferSubData(arg1 >>> 0, arg2, getObject(arg3));
        },
        __wbg_getContext_2966500392030d63: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).getContext(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_getContext_2a5764d48600bc43: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).getContext(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_getContext_b28d2db7bd648242: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).getContext(getStringFromWasm0(arg1, arg2), getObject(arg3));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_getContext_de810d9f187f29ca: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).getContext(getStringFromWasm0(arg1, arg2), getObject(arg3));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_getCurrentTexture_6dc4d0ea8555e374: function() { return handleError(function (arg0) {
            const ret = getObject(arg0).getCurrentTexture();
            return addHeapObject(ret);
        }, arguments); },
        __wbg_getError_bba8594facbfd5e1: function(arg0) {
            const ret = getObject(arg0).getError();
            return ret;
        },
        __wbg_getExtension_3c0cb5ae01bb4b17: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).getExtension(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_getIndexedParameter_ca1693c768bc4934: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).getIndexedParameter(arg1 >>> 0, arg2 >>> 0);
            return addHeapObject(ret);
        }, arguments); },
        __wbg_getMappedRange_3cb6354f7963e27e: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).getMappedRange(arg1, arg2);
            return addHeapObject(ret);
        }, arguments); },
        __wbg_getParameter_1ecb910cfdd21f88: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).getParameter(arg1 >>> 0);
            return addHeapObject(ret);
        }, arguments); },
        __wbg_getParameter_2e1f97ecaab76274: function() { return handleError(function (arg0, arg1) {
            const ret = getObject(arg0).getParameter(arg1 >>> 0);
            return addHeapObject(ret);
        }, arguments); },
        __wbg_getPreferredCanvasFormat_06854455b835cf40: function(arg0) {
            const ret = getObject(arg0).getPreferredCanvasFormat();
            return (__wbindgen_enum_GpuTextureFormat.indexOf(ret) + 1 || 96) - 1;
        },
        __wbg_getProgramInfoLog_2ffa30e3abb8b5c2: function(arg0, arg1, arg2) {
            const ret = getObject(arg1).getProgramInfoLog(getObject(arg2));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_getProgramInfoLog_dbfda4b6e7eb1b37: function(arg0, arg1, arg2) {
            const ret = getObject(arg1).getProgramInfoLog(getObject(arg2));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_getProgramParameter_43fbc6d2613c08b3: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getProgramParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getProgramParameter_92e4540ca9da06b2: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getProgramParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getQueryParameter_5d6af051438ae479: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getQueryParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getShaderInfoLog_9991e9e77b0c6805: function(arg0, arg1, arg2) {
            const ret = getObject(arg1).getShaderInfoLog(getObject(arg2));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_getShaderInfoLog_9e0b96da4b13ae49: function(arg0, arg1, arg2) {
            const ret = getObject(arg1).getShaderInfoLog(getObject(arg2));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_getShaderParameter_786fd84f85720ca8: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getShaderParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getShaderParameter_afa4a3dd9dd397c1: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getShaderParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getSupportedExtensions_57142a6b598d7787: function(arg0) {
            const ret = getObject(arg0).getSupportedExtensions();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_getSupportedProfiles_1f728bc32003c4d0: function(arg0) {
            const ret = getObject(arg0).getSupportedProfiles();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_getSyncParameter_7d11ab875b41617e: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getSyncParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getUniformBlockIndex_1ee7e922e6d96d7e: function(arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).getUniformBlockIndex(getObject(arg1), getStringFromWasm0(arg2, arg3));
            return ret;
        },
        __wbg_getUniformLocation_71c070e6644669ad: function(arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).getUniformLocation(getObject(arg1), getStringFromWasm0(arg2, arg3));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_getUniformLocation_d06b3a5b3c60e95c: function(arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).getUniformLocation(getObject(arg1), getStringFromWasm0(arg2, arg3));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_get_9b94d73e6221f75c: function(arg0, arg1) {
            const ret = getObject(arg0)[arg1 >>> 0];
            return addHeapObject(ret);
        },
        __wbg_get_b3ed3ad4be2bc8ac: function() { return handleError(function (arg0, arg1) {
            const ret = Reflect.get(getObject(arg0), getObject(arg1));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_get_d8db2ad31d529ff8: function(arg0, arg1) {
            const ret = getObject(arg0)[arg1 >>> 0];
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_gpu_653e59c6ae8028a8: function(arg0) {
            const ret = getObject(arg0).gpu;
            return addHeapObject(ret);
        },
        __wbg_has_d4e53238966c12b6: function() { return handleError(function (arg0, arg1) {
            const ret = Reflect.has(getObject(arg0), getObject(arg1));
            return ret;
        }, arguments); },
        __wbg_height_38750dc6de41ee75: function(arg0) {
            const ret = getObject(arg0).height;
            return ret;
        },
        __wbg_includes_32215c836f1cd3fb: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).includes(getObject(arg1), arg2);
            return ret;
        },
        __wbg_instanceof_ArrayBuffer_c367199e2fa2aa04: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof ArrayBuffer;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_CanvasRenderingContext2d_4bb052fd1c3d134d: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof CanvasRenderingContext2D;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_GpuAdapter_b2c1300e425af95c: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof GPUAdapter;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_GpuCanvasContext_c9b75b4b7dc7555e: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof GPUCanvasContext;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_HtmlCanvasElement_3f2f6e1edb1c9792: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof HTMLCanvasElement;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_Memory_dc8c61e3f831ee37: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof WebAssembly.Memory;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_Navigator_f0c8e3918bc066f3: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof Navigator;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_Promise_0094681e3519d6ec: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof Promise;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_WebGl2RenderingContext_4a08a94517ed5240: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof WebGL2RenderingContext;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_instanceof_Window_ed49b2db8df90359: function(arg0) {
            let result;
            try {
                result = getObject(arg0) instanceof Window;
            } catch (_) {
                result = false;
            }
            const ret = result;
            return ret;
        },
        __wbg_invalidateFramebuffer_b17b7e1da3051745: function() { return handleError(function (arg0, arg1, arg2) {
            getObject(arg0).invalidateFramebuffer(arg1 >>> 0, getObject(arg2));
        }, arguments); },
        __wbg_isContextLost_906412aff09b65f4: function(arg0) {
            const ret = getObject(arg0).isContextLost();
            return ret;
        },
        __wbg_is_f29129f676e5410c: function(arg0, arg1) {
            const ret = Object.is(getObject(arg0), getObject(arg1));
            return ret;
        },
        __wbg_label_f279af9fe090b53f: function(arg0, arg1) {
            const ret = getObject(arg1).label;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_length_32ed9a279acd054c: function(arg0) {
            const ret = getObject(arg0).length;
            return ret;
        },
        __wbg_length_35a7bace40f36eac: function(arg0) {
            const ret = getObject(arg0).length;
            return ret;
        },
        __wbg_limits_486026e4aa69b9b2: function(arg0) {
            const ret = getObject(arg0).limits;
            return addHeapObject(ret);
        },
        __wbg_linkProgram_6600dd2c0863bbfd: function(arg0, arg1) {
            getObject(arg0).linkProgram(getObject(arg1));
        },
        __wbg_linkProgram_be6b825cf66d177b: function(arg0, arg1) {
            getObject(arg0).linkProgram(getObject(arg1));
        },
        __wbg_log_6b5ca2e6124b2808: function(arg0) {
            console.log(getObject(arg0));
        },
        __wbg_mapAsync_e89ffbd0722e6025: function(arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).mapAsync(arg1 >>> 0, arg2, arg3);
            return addHeapObject(ret);
        },
        __wbg_maxBindGroups_52e3144d1d4f3951: function(arg0) {
            const ret = getObject(arg0).maxBindGroups;
            return ret;
        },
        __wbg_maxBindingsPerBindGroup_8e383157db4cfd9d: function(arg0) {
            const ret = getObject(arg0).maxBindingsPerBindGroup;
            return ret;
        },
        __wbg_maxBufferSize_4bed0deb2b5570bc: function(arg0) {
            const ret = getObject(arg0).maxBufferSize;
            return ret;
        },
        __wbg_maxColorAttachmentBytesPerSample_2ded1d176129b49e: function(arg0) {
            const ret = getObject(arg0).maxColorAttachmentBytesPerSample;
            return ret;
        },
        __wbg_maxColorAttachments_a363e1f84136b445: function(arg0) {
            const ret = getObject(arg0).maxColorAttachments;
            return ret;
        },
        __wbg_maxComputeInvocationsPerWorkgroup_8c8259a34a467300: function(arg0) {
            const ret = getObject(arg0).maxComputeInvocationsPerWorkgroup;
            return ret;
        },
        __wbg_maxComputeWorkgroupSizeX_6a123a5258a37c70: function(arg0) {
            const ret = getObject(arg0).maxComputeWorkgroupSizeX;
            return ret;
        },
        __wbg_maxComputeWorkgroupSizeY_212a6e863b315f06: function(arg0) {
            const ret = getObject(arg0).maxComputeWorkgroupSizeY;
            return ret;
        },
        __wbg_maxComputeWorkgroupSizeZ_53a8c06a42e0daa4: function(arg0) {
            const ret = getObject(arg0).maxComputeWorkgroupSizeZ;
            return ret;
        },
        __wbg_maxComputeWorkgroupStorageSize_0940bd6b70d5ee03: function(arg0) {
            const ret = getObject(arg0).maxComputeWorkgroupStorageSize;
            return ret;
        },
        __wbg_maxComputeWorkgroupsPerDimension_155968404880d2bc: function(arg0) {
            const ret = getObject(arg0).maxComputeWorkgroupsPerDimension;
            return ret;
        },
        __wbg_maxDynamicStorageBuffersPerPipelineLayout_7d88fb9026cd8af3: function(arg0) {
            const ret = getObject(arg0).maxDynamicStorageBuffersPerPipelineLayout;
            return ret;
        },
        __wbg_maxDynamicUniformBuffersPerPipelineLayout_146ac1a721fbca9b: function(arg0) {
            const ret = getObject(arg0).maxDynamicUniformBuffersPerPipelineLayout;
            return ret;
        },
        __wbg_maxSampledTexturesPerShaderStage_10ee96b97a701e05: function(arg0) {
            const ret = getObject(arg0).maxSampledTexturesPerShaderStage;
            return ret;
        },
        __wbg_maxSamplersPerShaderStage_7546a712e69839d0: function(arg0) {
            const ret = getObject(arg0).maxSamplersPerShaderStage;
            return ret;
        },
        __wbg_maxStorageBufferBindingSize_6f36ebfc9d4874d1: function(arg0) {
            const ret = getObject(arg0).maxStorageBufferBindingSize;
            return ret;
        },
        __wbg_maxStorageBuffersPerShaderStage_ad3988a66894ccd8: function(arg0) {
            const ret = getObject(arg0).maxStorageBuffersPerShaderStage;
            return ret;
        },
        __wbg_maxStorageTexturesPerShaderStage_3c4b0fd6cdb25d2f: function(arg0) {
            const ret = getObject(arg0).maxStorageTexturesPerShaderStage;
            return ret;
        },
        __wbg_maxTextureArrayLayers_596c959454186b7e: function(arg0) {
            const ret = getObject(arg0).maxTextureArrayLayers;
            return ret;
        },
        __wbg_maxTextureDimension1D_395c7225194787e6: function(arg0) {
            const ret = getObject(arg0).maxTextureDimension1D;
            return ret;
        },
        __wbg_maxTextureDimension2D_1c70c07372595733: function(arg0) {
            const ret = getObject(arg0).maxTextureDimension2D;
            return ret;
        },
        __wbg_maxTextureDimension3D_c2c0b973db2f7087: function(arg0) {
            const ret = getObject(arg0).maxTextureDimension3D;
            return ret;
        },
        __wbg_maxUniformBufferBindingSize_18e95cb371149021: function(arg0) {
            const ret = getObject(arg0).maxUniformBufferBindingSize;
            return ret;
        },
        __wbg_maxUniformBuffersPerShaderStage_e21721df6407d356: function(arg0) {
            const ret = getObject(arg0).maxUniformBuffersPerShaderStage;
            return ret;
        },
        __wbg_maxVertexAttributes_3685d049fb4b9557: function(arg0) {
            const ret = getObject(arg0).maxVertexAttributes;
            return ret;
        },
        __wbg_maxVertexBufferArrayStride_799ce7d416969442: function(arg0) {
            const ret = getObject(arg0).maxVertexBufferArrayStride;
            return ret;
        },
        __wbg_maxVertexBuffers_9e36c1cf99fac3d6: function(arg0) {
            const ret = getObject(arg0).maxVertexBuffers;
            return ret;
        },
        __wbg_minStorageBufferOffsetAlignment_04598b6c2361de5d: function(arg0) {
            const ret = getObject(arg0).minStorageBufferOffsetAlignment;
            return ret;
        },
        __wbg_minUniformBufferOffsetAlignment_0743900952f2cbce: function(arg0) {
            const ret = getObject(arg0).minUniformBufferOffsetAlignment;
            return ret;
        },
        __wbg_navigator_43be698ba96fc088: function(arg0) {
            const ret = getObject(arg0).navigator;
            return addHeapObject(ret);
        },
        __wbg_navigator_4478931f32ebca57: function(arg0) {
            const ret = getObject(arg0).navigator;
            return addHeapObject(ret);
        },
        __wbg_new_1eea5ab661db13e0: function() { return handleError(function (arg0, arg1) {
            const ret = new OffscreenCanvas(arg0 >>> 0, arg1 >>> 0);
            return addHeapObject(ret);
        }, arguments); },
        __wbg_new_361308b2356cecd0: function() {
            const ret = new Object();
            return addHeapObject(ret);
        },
        __wbg_new_3eb36ae241fe6f44: function() {
            const ret = new Array();
            return addHeapObject(ret);
        },
        __wbg_new_8a6f238a6ece86ea: function() {
            const ret = new Error();
            return addHeapObject(ret);
        },
        __wbg_new_b5d9e2fb389fef91: function(arg0, arg1) {
            try {
                var state0 = {a: arg0, b: arg1};
                var cb0 = (arg0, arg1) => {
                    const a = state0.a;
                    state0.a = 0;
                    try {
                        return __wasm_bindgen_func_elem_7946(a, state0.b, arg0, arg1);
                    } finally {
                        state0.a = a;
                    }
                };
                const ret = new Promise(cb0);
                return addHeapObject(ret);
            } finally {
                state0.a = state0.b = 0;
            }
        },
        __wbg_new_from_slice_a3d2629dc1826784: function(arg0, arg1) {
            const ret = new Uint8Array(getArrayU8FromWasm0(arg0, arg1));
            return addHeapObject(ret);
        },
        __wbg_new_no_args_1c7c842f08d00ebb: function(arg0, arg1) {
            const ret = new Function(getStringFromWasm0(arg0, arg1));
            return addHeapObject(ret);
        },
        __wbg_new_with_byte_offset_and_length_aa261d9c9da49eb1: function(arg0, arg1, arg2) {
            const ret = new Uint8Array(getObject(arg0), arg1 >>> 0, arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_new_with_u8_clamped_array_and_sh_0c0b789ceb2eab31: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = new ImageData(getClampedArrayU8FromWasm0(arg0, arg1), arg2 >>> 0, arg3 >>> 0);
            return addHeapObject(ret);
        }, arguments); },
        __wbg_now_ebffdf7e580f210d: function(arg0) {
            const ret = getObject(arg0).now();
            return ret;
        },
        __wbg_of_f915f7cd925b21a5: function(arg0) {
            const ret = Array.of(getObject(arg0));
            return addHeapObject(ret);
        },
        __wbg_onSubmittedWorkDone_babe5ab237e856ff: function(arg0) {
            const ret = getObject(arg0).onSubmittedWorkDone();
            return addHeapObject(ret);
        },
        __wbg_performance_06f12ba62483475d: function(arg0) {
            const ret = getObject(arg0).performance;
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_pixelStorei_2a65936c11b710fe: function(arg0, arg1, arg2) {
            getObject(arg0).pixelStorei(arg1 >>> 0, arg2);
        },
        __wbg_pixelStorei_f7cc498f52d523f1: function(arg0, arg1, arg2) {
            getObject(arg0).pixelStorei(arg1 >>> 0, arg2);
        },
        __wbg_polygonOffset_24a8059deb03be92: function(arg0, arg1, arg2) {
            getObject(arg0).polygonOffset(arg1, arg2);
        },
        __wbg_polygonOffset_4b3158d8ed028862: function(arg0, arg1, arg2) {
            getObject(arg0).polygonOffset(arg1, arg2);
        },
        __wbg_prototypesetcall_bdcdcc5842e4d77d: function(arg0, arg1, arg2) {
            Uint8Array.prototype.set.call(getArrayU8FromWasm0(arg0, arg1), getObject(arg2));
        },
        __wbg_push_8ffdcb2063340ba5: function(arg0, arg1) {
            const ret = getObject(arg0).push(getObject(arg1));
            return ret;
        },
        __wbg_putImageData_78318465ad96c2c3: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            getObject(arg0).putImageData(getObject(arg1), arg2, arg3);
        }, arguments); },
        __wbg_queryCounterEXT_b578f07c30420446: function(arg0, arg1, arg2) {
            getObject(arg0).queryCounterEXT(getObject(arg1), arg2 >>> 0);
        },
        __wbg_querySelectorAll_1283aae52043a951: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).querySelectorAll(getStringFromWasm0(arg1, arg2));
            return addHeapObject(ret);
        }, arguments); },
        __wbg_querySelector_c3b0df2d58eec220: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).querySelector(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_queueMicrotask_0aa0a927f78f5d98: function(arg0) {
            const ret = getObject(arg0).queueMicrotask;
            return addHeapObject(ret);
        },
        __wbg_queueMicrotask_5bb536982f78a56f: function(arg0) {
            queueMicrotask(getObject(arg0));
        },
        __wbg_queue_13a5c48e3c54a28c: function(arg0) {
            const ret = getObject(arg0).queue;
            return addHeapObject(ret);
        },
        __wbg_readBuffer_9eb461d6857295f0: function(arg0, arg1) {
            getObject(arg0).readBuffer(arg1 >>> 0);
        },
        __wbg_readPixels_55b18304384e073d: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7) {
            getObject(arg0).readPixels(arg1, arg2, arg3, arg4, arg5 >>> 0, arg6 >>> 0, getObject(arg7));
        }, arguments); },
        __wbg_readPixels_6ea8e288a8673282: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7) {
            getObject(arg0).readPixels(arg1, arg2, arg3, arg4, arg5 >>> 0, arg6 >>> 0, arg7);
        }, arguments); },
        __wbg_readPixels_95b2464a7bb863a2: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7) {
            getObject(arg0).readPixels(arg1, arg2, arg3, arg4, arg5 >>> 0, arg6 >>> 0, getObject(arg7));
        }, arguments); },
        __wbg_renderbufferStorageMultisample_bc0ae08a7abb887a: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).renderbufferStorageMultisample(arg1 >>> 0, arg2, arg3 >>> 0, arg4, arg5);
        },
        __wbg_renderbufferStorage_1bc02383614b76b2: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).renderbufferStorage(arg1 >>> 0, arg2 >>> 0, arg3, arg4);
        },
        __wbg_renderbufferStorage_6348154d30979c44: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).renderbufferStorage(arg1 >>> 0, arg2 >>> 0, arg3, arg4);
        },
        __wbg_requestAdapter_cc9a9924f72519ab: function(arg0, arg1) {
            const ret = getObject(arg0).requestAdapter(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_requestDevice_295504649d1da14c: function(arg0, arg1) {
            const ret = getObject(arg0).requestDevice(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_resolve_002c4b7d9d8f6b64: function(arg0) {
            const ret = Promise.resolve(getObject(arg0));
            return addHeapObject(ret);
        },
        __wbg_rource_new: function(arg0) {
            const ret = Rource.__wrap(arg0);
            return addHeapObject(ret);
        },
        __wbg_samplerParameterf_f070d2b69b1e2d46: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).samplerParameterf(getObject(arg1), arg2 >>> 0, arg3);
        },
        __wbg_samplerParameteri_8e4c4bcead0ee669: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).samplerParameteri(getObject(arg1), arg2 >>> 0, arg3);
        },
        __wbg_scissor_2ff8f18f05a6d408: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).scissor(arg1, arg2, arg3, arg4);
        },
        __wbg_scissor_b870b1434a9c25b4: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).scissor(arg1, arg2, arg3, arg4);
        },
        __wbg_setBindGroup_9eb2f378626e78b7: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            getObject(arg0).setBindGroup(arg1 >>> 0, getObject(arg2), getArrayU32FromWasm0(arg3, arg4), arg5, arg6 >>> 0);
        }, arguments); },
        __wbg_setBindGroup_ae93a2ba8c665826: function(arg0, arg1, arg2) {
            getObject(arg0).setBindGroup(arg1 >>> 0, getObject(arg2));
        },
        __wbg_setBindGroup_bf7233e51ee0fd56: function(arg0, arg1, arg2) {
            getObject(arg0).setBindGroup(arg1 >>> 0, getObject(arg2));
        },
        __wbg_setBindGroup_c532d9e80c3b863a: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            getObject(arg0).setBindGroup(arg1 >>> 0, getObject(arg2), getArrayU32FromWasm0(arg3, arg4), arg5, arg6 >>> 0);
        }, arguments); },
        __wbg_setPipeline_6d9bb386aa5ee85f: function(arg0, arg1) {
            getObject(arg0).setPipeline(getObject(arg1));
        },
        __wbg_setPipeline_b632e313f54b1cb1: function(arg0, arg1) {
            getObject(arg0).setPipeline(getObject(arg1));
        },
        __wbg_setScissorRect_13be2665184d6e20: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).setScissorRect(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_setVertexBuffer_71f6b6b9f7c32e99: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).setVertexBuffer(arg1 >>> 0, getObject(arg2), arg3);
        },
        __wbg_setVertexBuffer_c8234139ead62a61: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).setVertexBuffer(arg1 >>> 0, getObject(arg2), arg3, arg4);
        },
        __wbg_set_25cf9deff6bf0ea8: function(arg0, arg1, arg2) {
            getObject(arg0).set(getObject(arg1), arg2 >>> 0);
        },
        __wbg_set_6cb8631f80447a67: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = Reflect.set(getObject(arg0), getObject(arg1), getObject(arg2));
            return ret;
        }, arguments); },
        __wbg_set_a_e87a2053d5fccb4c: function(arg0, arg1) {
            getObject(arg0).a = arg1;
        },
        __wbg_set_access_69d91e9d4e4ceac2: function(arg0, arg1) {
            getObject(arg0).access = __wbindgen_enum_GpuStorageTextureAccess[arg1];
        },
        __wbg_set_address_mode_u_17e91ba6701d7cdf: function(arg0, arg1) {
            getObject(arg0).addressModeU = __wbindgen_enum_GpuAddressMode[arg1];
        },
        __wbg_set_address_mode_v_83cff33885b49fd0: function(arg0, arg1) {
            getObject(arg0).addressModeV = __wbindgen_enum_GpuAddressMode[arg1];
        },
        __wbg_set_address_mode_w_2445963d0feae757: function(arg0, arg1) {
            getObject(arg0).addressModeW = __wbindgen_enum_GpuAddressMode[arg1];
        },
        __wbg_set_alpha_a7a68e5ec04efe77: function(arg0, arg1) {
            getObject(arg0).alpha = getObject(arg1);
        },
        __wbg_set_alpha_mode_60f87267fa3d95d0: function(arg0, arg1) {
            getObject(arg0).alphaMode = __wbindgen_enum_GpuCanvasAlphaMode[arg1];
        },
        __wbg_set_alpha_to_coverage_enabled_67782b8fff854d06: function(arg0, arg1) {
            getObject(arg0).alphaToCoverageEnabled = arg1 !== 0;
        },
        __wbg_set_array_layer_count_2bd74e56899b603a: function(arg0, arg1) {
            getObject(arg0).arrayLayerCount = arg1 >>> 0;
        },
        __wbg_set_array_stride_acb85bd3848529a6: function(arg0, arg1) {
            getObject(arg0).arrayStride = arg1;
        },
        __wbg_set_aspect_82ca9caa27a4c533: function(arg0, arg1) {
            getObject(arg0).aspect = __wbindgen_enum_GpuTextureAspect[arg1];
        },
        __wbg_set_aspect_b78bd0b34ebfe19b: function(arg0, arg1) {
            getObject(arg0).aspect = __wbindgen_enum_GpuTextureAspect[arg1];
        },
        __wbg_set_attributes_4d5de6c80e3a7e73: function(arg0, arg1) {
            getObject(arg0).attributes = getObject(arg1);
        },
        __wbg_set_b_87725d82ac69a631: function(arg0, arg1) {
            getObject(arg0).b = arg1;
        },
        __wbg_set_base_array_layer_064977086530f2e7: function(arg0, arg1) {
            getObject(arg0).baseArrayLayer = arg1 >>> 0;
        },
        __wbg_set_base_mip_level_845abe28a57bd901: function(arg0, arg1) {
            getObject(arg0).baseMipLevel = arg1 >>> 0;
        },
        __wbg_set_beginning_of_pass_write_index_18bb7ab9fb16de02: function(arg0, arg1) {
            getObject(arg0).beginningOfPassWriteIndex = arg1 >>> 0;
        },
        __wbg_set_beginning_of_pass_write_index_1d1dcdf984952e54: function(arg0, arg1) {
            getObject(arg0).beginningOfPassWriteIndex = arg1 >>> 0;
        },
        __wbg_set_bind_group_layouts_db65f9787380e242: function(arg0, arg1) {
            getObject(arg0).bindGroupLayouts = getObject(arg1);
        },
        __wbg_set_binding_35fa28beda49ff83: function(arg0, arg1) {
            getObject(arg0).binding = arg1 >>> 0;
        },
        __wbg_set_binding_3b4abee15b11f6ec: function(arg0, arg1) {
            getObject(arg0).binding = arg1 >>> 0;
        },
        __wbg_set_blend_21337ec514ad2280: function(arg0, arg1) {
            getObject(arg0).blend = getObject(arg1);
        },
        __wbg_set_buffer_a9223dfcc0e34853: function(arg0, arg1) {
            getObject(arg0).buffer = getObject(arg1);
        },
        __wbg_set_buffer_d49e95bb5349d827: function(arg0, arg1) {
            getObject(arg0).buffer = getObject(arg1);
        },
        __wbg_set_buffers_68609a5d48c31b27: function(arg0, arg1) {
            getObject(arg0).buffers = getObject(arg1);
        },
        __wbg_set_bytes_per_row_4a52bbf4cdbfe78b: function(arg0, arg1) {
            getObject(arg0).bytesPerRow = arg1 >>> 0;
        },
        __wbg_set_clear_value_8fc3623594df71b2: function(arg0, arg1) {
            getObject(arg0).clearValue = getObject(arg1);
        },
        __wbg_set_code_20093e29960281f8: function(arg0, arg1, arg2) {
            getObject(arg0).code = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_color_64a633bf7b4cf6fe: function(arg0, arg1) {
            getObject(arg0).color = getObject(arg1);
        },
        __wbg_set_color_attachments_4d4c71d7eeba8e2f: function(arg0, arg1) {
            getObject(arg0).colorAttachments = getObject(arg1);
        },
        __wbg_set_compare_0376672b0c0bbfd8: function(arg0, arg1) {
            getObject(arg0).compare = __wbindgen_enum_GpuCompareFunction[arg1];
        },
        __wbg_set_compare_f3fb77a9bf3f0f7e: function(arg0, arg1) {
            getObject(arg0).compare = __wbindgen_enum_GpuCompareFunction[arg1];
        },
        __wbg_set_compute_937f4ee700e465ff: function(arg0, arg1) {
            getObject(arg0).compute = getObject(arg1);
        },
        __wbg_set_count_8cf9a3dd1ffc7b7d: function(arg0, arg1) {
            getObject(arg0).count = arg1 >>> 0;
        },
        __wbg_set_cull_mode_41c12526410d3e05: function(arg0, arg1) {
            getObject(arg0).cullMode = __wbindgen_enum_GpuCullMode[arg1];
        },
        __wbg_set_depth_bias_31554aeaaa675954: function(arg0, arg1) {
            getObject(arg0).depthBias = arg1;
        },
        __wbg_set_depth_bias_clamp_8cf5f4f0d80e8cba: function(arg0, arg1) {
            getObject(arg0).depthBiasClamp = arg1;
        },
        __wbg_set_depth_bias_slope_scale_310ae406f2d3a055: function(arg0, arg1) {
            getObject(arg0).depthBiasSlopeScale = arg1;
        },
        __wbg_set_depth_clear_value_8760aafb583d5312: function(arg0, arg1) {
            getObject(arg0).depthClearValue = arg1;
        },
        __wbg_set_depth_compare_8831904ce3173063: function(arg0, arg1) {
            getObject(arg0).depthCompare = __wbindgen_enum_GpuCompareFunction[arg1];
        },
        __wbg_set_depth_fail_op_62ec602580477afc: function(arg0, arg1) {
            getObject(arg0).depthFailOp = __wbindgen_enum_GpuStencilOperation[arg1];
        },
        __wbg_set_depth_load_op_102d57f3ddf95461: function(arg0, arg1) {
            getObject(arg0).depthLoadOp = __wbindgen_enum_GpuLoadOp[arg1];
        },
        __wbg_set_depth_or_array_layers_d7b93db07c5da69d: function(arg0, arg1) {
            getObject(arg0).depthOrArrayLayers = arg1 >>> 0;
        },
        __wbg_set_depth_read_only_aebc24a542debafd: function(arg0, arg1) {
            getObject(arg0).depthReadOnly = arg1 !== 0;
        },
        __wbg_set_depth_stencil_5627e73aaf33912c: function(arg0, arg1) {
            getObject(arg0).depthStencil = getObject(arg1);
        },
        __wbg_set_depth_stencil_attachment_04b936535778e362: function(arg0, arg1) {
            getObject(arg0).depthStencilAttachment = getObject(arg1);
        },
        __wbg_set_depth_store_op_610b0a50dbb00eb8: function(arg0, arg1) {
            getObject(arg0).depthStoreOp = __wbindgen_enum_GpuStoreOp[arg1];
        },
        __wbg_set_depth_write_enabled_f94217df9ff2d60c: function(arg0, arg1) {
            getObject(arg0).depthWriteEnabled = arg1 !== 0;
        },
        __wbg_set_device_dab18ead7bfc077b: function(arg0, arg1) {
            getObject(arg0).device = getObject(arg1);
        },
        __wbg_set_dimension_2a75a794a0bfcc94: function(arg0, arg1) {
            getObject(arg0).dimension = __wbindgen_enum_GpuTextureViewDimension[arg1];
        },
        __wbg_set_dimension_a3c50fb6d43f6cec: function(arg0, arg1) {
            getObject(arg0).dimension = __wbindgen_enum_GpuTextureDimension[arg1];
        },
        __wbg_set_dst_factor_cf872fec841747ac: function(arg0, arg1) {
            getObject(arg0).dstFactor = __wbindgen_enum_GpuBlendFactor[arg1];
        },
        __wbg_set_end_of_pass_write_index_02ee5189026c1d3a: function(arg0, arg1) {
            getObject(arg0).endOfPassWriteIndex = arg1 >>> 0;
        },
        __wbg_set_end_of_pass_write_index_12c25e0a48d5aa5c: function(arg0, arg1) {
            getObject(arg0).endOfPassWriteIndex = arg1 >>> 0;
        },
        __wbg_set_entries_1472deaee7053fb7: function(arg0, arg1) {
            getObject(arg0).entries = getObject(arg1);
        },
        __wbg_set_entries_b2258b5ef29810b0: function(arg0, arg1) {
            getObject(arg0).entries = getObject(arg1);
        },
        __wbg_set_entry_point_11f912102ade99b1: function(arg0, arg1, arg2) {
            getObject(arg0).entryPoint = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_entry_point_7f546bbf1e63e58d: function(arg0, arg1, arg2) {
            getObject(arg0).entryPoint = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_entry_point_f9224cdb29cbe5df: function(arg0, arg1, arg2) {
            getObject(arg0).entryPoint = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_external_texture_613e4434100d63ee: function(arg0, arg1) {
            getObject(arg0).externalTexture = getObject(arg1);
        },
        __wbg_set_fail_op_73a4e194f4bc914a: function(arg0, arg1) {
            getObject(arg0).failOp = __wbindgen_enum_GpuStencilOperation[arg1];
        },
        __wbg_set_format_1670e760e18ac001: function(arg0, arg1) {
            getObject(arg0).format = __wbindgen_enum_GpuTextureFormat[arg1];
        },
        __wbg_set_format_2141a8a1fd36fb9c: function(arg0, arg1) {
            getObject(arg0).format = __wbindgen_enum_GpuTextureFormat[arg1];
        },
        __wbg_set_format_25e4aacc74949e38: function(arg0, arg1) {
            getObject(arg0).format = __wbindgen_enum_GpuTextureFormat[arg1];
        },
        __wbg_set_format_3f7008e9e568f0fc: function(arg0, arg1) {
            getObject(arg0).format = __wbindgen_enum_GpuVertexFormat[arg1];
        },
        __wbg_set_format_4a4fccdfc45bc409: function(arg0, arg1) {
            getObject(arg0).format = __wbindgen_enum_GpuTextureFormat[arg1];
        },
        __wbg_set_format_7696f8290da8a36b: function(arg0, arg1) {
            getObject(arg0).format = __wbindgen_enum_GpuTextureFormat[arg1];
        },
        __wbg_set_format_974a01725f579c5d: function(arg0, arg1) {
            getObject(arg0).format = __wbindgen_enum_GpuTextureFormat[arg1];
        },
        __wbg_set_fragment_f7ce64feaf1cd7dc: function(arg0, arg1) {
            getObject(arg0).fragment = getObject(arg1);
        },
        __wbg_set_front_face_09e32557f8852301: function(arg0, arg1) {
            getObject(arg0).frontFace = __wbindgen_enum_GpuFrontFace[arg1];
        },
        __wbg_set_g_c31c959457596456: function(arg0, arg1) {
            getObject(arg0).g = arg1;
        },
        __wbg_set_has_dynamic_offset_fbc1bb343939ed0b: function(arg0, arg1) {
            getObject(arg0).hasDynamicOffset = arg1 !== 0;
        },
        __wbg_set_height_710b87344b3d6748: function(arg0, arg1) {
            getObject(arg0).height = arg1 >>> 0;
        },
        __wbg_set_height_b386c0f603610637: function(arg0, arg1) {
            getObject(arg0).height = arg1 >>> 0;
        },
        __wbg_set_height_f21f985387070100: function(arg0, arg1) {
            getObject(arg0).height = arg1 >>> 0;
        },
        __wbg_set_label_0ec13ba975f77124: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_3b658d9ce970552c: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_48883f5f49e4ec47: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_4bbbc289ddddebd7: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_4d609666f09cfdfb: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_4f4264b0041180e2: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_5b46e419b9e88c5e: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_95423cd2e1f4b5dd: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_ad0f2c69b41c3483: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_c3fc0a66f4ecc82b: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_c857f45a8485236a: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_d0fd4d4810525bf2: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_dc8df9969898889c: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_e3709fe3e82429b5: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_label_fb5d28b3ba7af11f: function(arg0, arg1, arg2) {
            getObject(arg0).label = getStringFromWasm0(arg1, arg2);
        },
        __wbg_set_layout_170ec6b8aa37178f: function(arg0, arg1) {
            getObject(arg0).layout = getObject(arg1);
        },
        __wbg_set_layout_7f76289be3294b4a: function(arg0, arg1) {
            getObject(arg0).layout = getObject(arg1);
        },
        __wbg_set_layout_c20d48b352b24c1b: function(arg0, arg1) {
            getObject(arg0).layout = getObject(arg1);
        },
        __wbg_set_load_op_c71d200e998908b0: function(arg0, arg1) {
            getObject(arg0).loadOp = __wbindgen_enum_GpuLoadOp[arg1];
        },
        __wbg_set_lod_max_clamp_aaac5daaecca96d4: function(arg0, arg1) {
            getObject(arg0).lodMaxClamp = arg1;
        },
        __wbg_set_lod_min_clamp_ed2162d4b198abba: function(arg0, arg1) {
            getObject(arg0).lodMinClamp = arg1;
        },
        __wbg_set_mag_filter_c8a8c1218cd38da6: function(arg0, arg1) {
            getObject(arg0).magFilter = __wbindgen_enum_GpuFilterMode[arg1];
        },
        __wbg_set_mapped_at_creation_2d003ce549611385: function(arg0, arg1) {
            getObject(arg0).mappedAtCreation = arg1 !== 0;
        },
        __wbg_set_mask_a933ba2e61c7610a: function(arg0, arg1) {
            getObject(arg0).mask = arg1 >>> 0;
        },
        __wbg_set_max_anisotropy_fb4bae64cb5acf57: function(arg0, arg1) {
            getObject(arg0).maxAnisotropy = arg1;
        },
        __wbg_set_min_binding_size_308360802ae7a9ba: function(arg0, arg1) {
            getObject(arg0).minBindingSize = arg1;
        },
        __wbg_set_min_filter_2dafbdeb188fd817: function(arg0, arg1) {
            getObject(arg0).minFilter = __wbindgen_enum_GpuFilterMode[arg1];
        },
        __wbg_set_mip_level_babe1ff64201f0ea: function(arg0, arg1) {
            getObject(arg0).mipLevel = arg1 >>> 0;
        },
        __wbg_set_mip_level_count_cd3197411f4f2432: function(arg0, arg1) {
            getObject(arg0).mipLevelCount = arg1 >>> 0;
        },
        __wbg_set_mip_level_count_fdc72450a94244ef: function(arg0, arg1) {
            getObject(arg0).mipLevelCount = arg1 >>> 0;
        },
        __wbg_set_mipmap_filter_79f552c459e63aa6: function(arg0, arg1) {
            getObject(arg0).mipmapFilter = __wbindgen_enum_GpuMipmapFilterMode[arg1];
        },
        __wbg_set_module_18d541838665d831: function(arg0, arg1) {
            getObject(arg0).module = getObject(arg1);
        },
        __wbg_set_module_20641353ebb28712: function(arg0, arg1) {
            getObject(arg0).module = getObject(arg1);
        },
        __wbg_set_module_6ece909be28666dd: function(arg0, arg1) {
            getObject(arg0).module = getObject(arg1);
        },
        __wbg_set_multisample_e0f310ea9e40c2d9: function(arg0, arg1) {
            getObject(arg0).multisample = getObject(arg1);
        },
        __wbg_set_multisampled_cd50d8f6709cea1a: function(arg0, arg1) {
            getObject(arg0).multisampled = arg1 !== 0;
        },
        __wbg_set_offset_2e78915f5d65d704: function(arg0, arg1) {
            getObject(arg0).offset = arg1;
        },
        __wbg_set_offset_405017033a936d89: function(arg0, arg1) {
            getObject(arg0).offset = arg1;
        },
        __wbg_set_offset_e7ce8b8eaaf46b95: function(arg0, arg1) {
            getObject(arg0).offset = arg1;
        },
        __wbg_set_operation_b96fabca3716aaa3: function(arg0, arg1) {
            getObject(arg0).operation = __wbindgen_enum_GpuBlendOperation[arg1];
        },
        __wbg_set_origin_c5f017d3f09ad7ff: function(arg0, arg1) {
            getObject(arg0).origin = getObject(arg1);
        },
        __wbg_set_pass_op_765be90bb2f27220: function(arg0, arg1) {
            getObject(arg0).passOp = __wbindgen_enum_GpuStencilOperation[arg1];
        },
        __wbg_set_power_preference_39b347bf0d236ce6: function(arg0, arg1) {
            getObject(arg0).powerPreference = __wbindgen_enum_GpuPowerPreference[arg1];
        },
        __wbg_set_primitive_d6456d7efe6b4fe5: function(arg0, arg1) {
            getObject(arg0).primitive = getObject(arg1);
        },
        __wbg_set_query_set_20ecd7f9a16f3ec6: function(arg0, arg1) {
            getObject(arg0).querySet = getObject(arg1);
        },
        __wbg_set_query_set_3afc955600bc819a: function(arg0, arg1) {
            getObject(arg0).querySet = getObject(arg1);
        },
        __wbg_set_r_07bd987697069496: function(arg0, arg1) {
            getObject(arg0).r = arg1;
        },
        __wbg_set_required_features_650c9e5dafbaa395: function(arg0, arg1) {
            getObject(arg0).requiredFeatures = getObject(arg1);
        },
        __wbg_set_resolve_target_c18cd4048765732a: function(arg0, arg1) {
            getObject(arg0).resolveTarget = getObject(arg1);
        },
        __wbg_set_resource_8cea0fe2c8745c3e: function(arg0, arg1) {
            getObject(arg0).resource = getObject(arg1);
        },
        __wbg_set_rows_per_image_2f7969031c71f0d8: function(arg0, arg1) {
            getObject(arg0).rowsPerImage = arg1 >>> 0;
        },
        __wbg_set_sample_count_07aedd28692aeae8: function(arg0, arg1) {
            getObject(arg0).sampleCount = arg1 >>> 0;
        },
        __wbg_set_sample_type_601a744a4bd6ea07: function(arg0, arg1) {
            getObject(arg0).sampleType = __wbindgen_enum_GpuTextureSampleType[arg1];
        },
        __wbg_set_sampler_1a2729c0aa194081: function(arg0, arg1) {
            getObject(arg0).sampler = getObject(arg1);
        },
        __wbg_set_shader_location_bdcfdc1009d351b1: function(arg0, arg1) {
            getObject(arg0).shaderLocation = arg1 >>> 0;
        },
        __wbg_set_size_7a392ee585f87da8: function(arg0, arg1) {
            getObject(arg0).size = arg1;
        },
        __wbg_set_size_c6bf409f70f4420f: function(arg0, arg1) {
            getObject(arg0).size = getObject(arg1);
        },
        __wbg_set_size_f902b266d636bf6e: function(arg0, arg1) {
            getObject(arg0).size = arg1;
        },
        __wbg_set_src_factor_50cef27aa8aece91: function(arg0, arg1) {
            getObject(arg0).srcFactor = __wbindgen_enum_GpuBlendFactor[arg1];
        },
        __wbg_set_stencil_back_e740415a5c0b637a: function(arg0, arg1) {
            getObject(arg0).stencilBack = getObject(arg1);
        },
        __wbg_set_stencil_clear_value_6be76b512040398d: function(arg0, arg1) {
            getObject(arg0).stencilClearValue = arg1 >>> 0;
        },
        __wbg_set_stencil_front_03185e1c3bafa411: function(arg0, arg1) {
            getObject(arg0).stencilFront = getObject(arg1);
        },
        __wbg_set_stencil_load_op_084f44352b978b3d: function(arg0, arg1) {
            getObject(arg0).stencilLoadOp = __wbindgen_enum_GpuLoadOp[arg1];
        },
        __wbg_set_stencil_read_mask_e2736fc4af9399e4: function(arg0, arg1) {
            getObject(arg0).stencilReadMask = arg1 >>> 0;
        },
        __wbg_set_stencil_read_only_31f3d99299373c12: function(arg0, arg1) {
            getObject(arg0).stencilReadOnly = arg1 !== 0;
        },
        __wbg_set_stencil_store_op_428fb4955e4899d6: function(arg0, arg1) {
            getObject(arg0).stencilStoreOp = __wbindgen_enum_GpuStoreOp[arg1];
        },
        __wbg_set_stencil_write_mask_b1d3e1655305a187: function(arg0, arg1) {
            getObject(arg0).stencilWriteMask = arg1 >>> 0;
        },
        __wbg_set_step_mode_98e49f7877daf1c5: function(arg0, arg1) {
            getObject(arg0).stepMode = __wbindgen_enum_GpuVertexStepMode[arg1];
        },
        __wbg_set_storage_texture_6ee0cbeb50698110: function(arg0, arg1) {
            getObject(arg0).storageTexture = getObject(arg1);
        },
        __wbg_set_store_op_e761080d541a10cc: function(arg0, arg1) {
            getObject(arg0).storeOp = __wbindgen_enum_GpuStoreOp[arg1];
        },
        __wbg_set_strip_index_format_16df9e33c7aa97e6: function(arg0, arg1) {
            getObject(arg0).stripIndexFormat = __wbindgen_enum_GpuIndexFormat[arg1];
        },
        __wbg_set_targets_9fd1ec0b8edc895c: function(arg0, arg1) {
            getObject(arg0).targets = getObject(arg1);
        },
        __wbg_set_texture_f03807916f70dcc6: function(arg0, arg1) {
            getObject(arg0).texture = getObject(arg1);
        },
        __wbg_set_texture_f8ae0bb4bb159354: function(arg0, arg1) {
            getObject(arg0).texture = getObject(arg1);
        },
        __wbg_set_timestamp_writes_3998dbfa21e48dbe: function(arg0, arg1) {
            getObject(arg0).timestampWrites = getObject(arg1);
        },
        __wbg_set_timestamp_writes_de925214f236e575: function(arg0, arg1) {
            getObject(arg0).timestampWrites = getObject(arg1);
        },
        __wbg_set_topology_036632318a24227d: function(arg0, arg1) {
            getObject(arg0).topology = __wbindgen_enum_GpuPrimitiveTopology[arg1];
        },
        __wbg_set_type_0cb4cdb5eff87f31: function(arg0, arg1) {
            getObject(arg0).type = __wbindgen_enum_GpuBufferBindingType[arg1];
        },
        __wbg_set_type_d05fa8415ad0761f: function(arg0, arg1) {
            getObject(arg0).type = __wbindgen_enum_GpuSamplerBindingType[arg1];
        },
        __wbg_set_unclipped_depth_17a5ab83d4e7cadc: function(arg0, arg1) {
            getObject(arg0).unclippedDepth = arg1 !== 0;
        },
        __wbg_set_usage_3d569e7b02227032: function(arg0, arg1) {
            getObject(arg0).usage = arg1 >>> 0;
        },
        __wbg_set_usage_ac222ece73f994b7: function(arg0, arg1) {
            getObject(arg0).usage = arg1 >>> 0;
        },
        __wbg_set_usage_ca00520767c8a475: function(arg0, arg1) {
            getObject(arg0).usage = arg1 >>> 0;
        },
        __wbg_set_usage_fe13088353b65bee: function(arg0, arg1) {
            getObject(arg0).usage = arg1 >>> 0;
        },
        __wbg_set_vertex_76b7ac4bdfbb06f4: function(arg0, arg1) {
            getObject(arg0).vertex = getObject(arg1);
        },
        __wbg_set_view_1ef41eeb26eaf718: function(arg0, arg1) {
            getObject(arg0).view = getObject(arg1);
        },
        __wbg_set_view_46b654a12649c6f6: function(arg0, arg1) {
            getObject(arg0).view = getObject(arg1);
        },
        __wbg_set_view_dimension_12c332494a2697dc: function(arg0, arg1) {
            getObject(arg0).viewDimension = __wbindgen_enum_GpuTextureViewDimension[arg1];
        },
        __wbg_set_view_dimension_31b9fd7126132e82: function(arg0, arg1) {
            getObject(arg0).viewDimension = __wbindgen_enum_GpuTextureViewDimension[arg1];
        },
        __wbg_set_view_formats_152cb995add2ee4e: function(arg0, arg1) {
            getObject(arg0).viewFormats = getObject(arg1);
        },
        __wbg_set_view_formats_cc77650da6c3b25b: function(arg0, arg1) {
            getObject(arg0).viewFormats = getObject(arg1);
        },
        __wbg_set_visibility_6d1fc94552f22ac3: function(arg0, arg1) {
            getObject(arg0).visibility = arg1 >>> 0;
        },
        __wbg_set_width_5ee1e2d4a0fd929b: function(arg0, arg1) {
            getObject(arg0).width = arg1 >>> 0;
        },
        __wbg_set_width_7f07715a20503914: function(arg0, arg1) {
            getObject(arg0).width = arg1 >>> 0;
        },
        __wbg_set_width_d60bc4f2f20c56a4: function(arg0, arg1) {
            getObject(arg0).width = arg1 >>> 0;
        },
        __wbg_set_write_mask_c92743022356850e: function(arg0, arg1) {
            getObject(arg0).writeMask = arg1 >>> 0;
        },
        __wbg_set_x_0771b0f86d56cdf9: function(arg0, arg1) {
            getObject(arg0).x = arg1 >>> 0;
        },
        __wbg_set_y_668d1578881576dd: function(arg0, arg1) {
            getObject(arg0).y = arg1 >>> 0;
        },
        __wbg_set_z_3e24a918a76c816d: function(arg0, arg1) {
            getObject(arg0).z = arg1 >>> 0;
        },
        __wbg_shaderSource_32425cfe6e5a1e52: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).shaderSource(getObject(arg1), getStringFromWasm0(arg2, arg3));
        },
        __wbg_shaderSource_8f4bda03f70359df: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).shaderSource(getObject(arg1), getStringFromWasm0(arg2, arg3));
        },
        __wbg_stack_0ed75d68575b0f3c: function(arg0, arg1) {
            const ret = getObject(arg1).stack;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_static_accessor_GLOBAL_12837167ad935116: function() {
            const ret = typeof global === 'undefined' ? null : global;
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_static_accessor_GLOBAL_THIS_e628e89ab3b1c95f: function() {
            const ret = typeof globalThis === 'undefined' ? null : globalThis;
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_static_accessor_SELF_a621d3dfbb60d0ce: function() {
            const ret = typeof self === 'undefined' ? null : self;
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_static_accessor_WINDOW_f8727f0cf888e0bd: function() {
            const ret = typeof window === 'undefined' ? null : window;
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_stencilFuncSeparate_10d043d0af14366f: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).stencilFuncSeparate(arg1 >>> 0, arg2 >>> 0, arg3, arg4 >>> 0);
        },
        __wbg_stencilFuncSeparate_1798f5cca257f313: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).stencilFuncSeparate(arg1 >>> 0, arg2 >>> 0, arg3, arg4 >>> 0);
        },
        __wbg_stencilMaskSeparate_28d53625c02d9c7f: function(arg0, arg1, arg2) {
            getObject(arg0).stencilMaskSeparate(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_stencilMaskSeparate_c24c1a28b8dd8a63: function(arg0, arg1, arg2) {
            getObject(arg0).stencilMaskSeparate(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_stencilMask_0eca090c4c47f8f7: function(arg0, arg1) {
            getObject(arg0).stencilMask(arg1 >>> 0);
        },
        __wbg_stencilMask_732dcc5aada10e4c: function(arg0, arg1) {
            getObject(arg0).stencilMask(arg1 >>> 0);
        },
        __wbg_stencilOpSeparate_4657523b1d3b184f: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).stencilOpSeparate(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_stencilOpSeparate_de257f3c29e604cd: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).stencilOpSeparate(arg1 >>> 0, arg2 >>> 0, arg3 >>> 0, arg4 >>> 0);
        },
        __wbg_submit_a1850a1cb6baf64a: function(arg0, arg1) {
            getObject(arg0).submit(getObject(arg1));
        },
        __wbg_texImage2D_087ef94df78081f0: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texImage2D_13414a4692836804: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, arg9);
        }, arguments); },
        __wbg_texImage2D_c1bb39f4b3a26e90: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).texImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, arg9 === 0 ? undefined : getArrayU8FromWasm0(arg9, arg10));
        }, arguments); },
        __wbg_texImage2D_e71049312f3172d9: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texImage3D_2082006a8a9b28a7: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).texImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8 >>> 0, arg9 >>> 0, arg10);
        }, arguments); },
        __wbg_texImage3D_bd2b0bd2cfcdb278: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).texImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8 >>> 0, arg9 >>> 0, getObject(arg10));
        }, arguments); },
        __wbg_texParameteri_0d45be2c88d6bad8: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).texParameteri(arg1 >>> 0, arg2 >>> 0, arg3);
        },
        __wbg_texParameteri_ec937d2161018946: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).texParameteri(arg1 >>> 0, arg2 >>> 0, arg3);
        },
        __wbg_texStorage2D_9504743abf5a986a: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).texStorage2D(arg1 >>> 0, arg2, arg3 >>> 0, arg4, arg5);
        },
        __wbg_texStorage3D_e9e1b58fee218abe: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            getObject(arg0).texStorage3D(arg1 >>> 0, arg2, arg3 >>> 0, arg4, arg5, arg6);
        },
        __wbg_texSubImage2D_117d29278542feb0: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texSubImage2D_19ae4cadb809f264: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texSubImage2D_5d270af600a7fc4a: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texSubImage2D_bd034db2e58c352c: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texSubImage2D_bf72e56edeeed376: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texSubImage2D_c0140b758462635d: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, arg9 === 0 ? undefined : getArrayU8FromWasm0(arg9, arg10));
        }, arguments); },
        __wbg_texSubImage2D_d17a39cdec4a3495: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texSubImage2D_e193f1d28439217c: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, getObject(arg9));
        }, arguments); },
        __wbg_texSubImage2D_edf5bd70fda3feaf: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, arg9);
        }, arguments); },
        __wbg_texSubImage3D_0e069c6759e299b8: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, arg11 === 0 ? undefined : getArrayU8FromWasm0(arg11, arg12));
        }, arguments); },
        __wbg_texSubImage3D_1102c12a20bf56d5: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, getObject(arg11));
        }, arguments); },
        __wbg_texSubImage3D_18d7f3c65567c885: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, getObject(arg11));
        }, arguments); },
        __wbg_texSubImage3D_3b653017c4c5d721: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, getObject(arg11));
        }, arguments); },
        __wbg_texSubImage3D_45591e5655d1ed5c: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, getObject(arg11));
        }, arguments); },
        __wbg_texSubImage3D_47643556a8a4bf86: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, getObject(arg11));
        }, arguments); },
        __wbg_texSubImage3D_59b8e24fb05787aa: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, arg11);
        }, arguments); },
        __wbg_texSubImage3D_eff5cd6ab84f44ee: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) {
            getObject(arg0).texSubImage3D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9 >>> 0, arg10 >>> 0, getObject(arg11));
        }, arguments); },
        __wbg_then_0d9fe2c7b1857d32: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).then(getObject(arg1), getObject(arg2));
            return addHeapObject(ret);
        },
        __wbg_then_b9e7b3b5f1a9e1b5: function(arg0, arg1) {
            const ret = getObject(arg0).then(getObject(arg1));
            return addHeapObject(ret);
        },
        __wbg_uniform1f_b500ede5b612bea2: function(arg0, arg1, arg2) {
            getObject(arg0).uniform1f(getObject(arg1), arg2);
        },
        __wbg_uniform1f_c148eeaf4b531059: function(arg0, arg1, arg2) {
            getObject(arg0).uniform1f(getObject(arg1), arg2);
        },
        __wbg_uniform1i_9f3f72dbcb98ada9: function(arg0, arg1, arg2) {
            getObject(arg0).uniform1i(getObject(arg1), arg2);
        },
        __wbg_uniform1i_e9aee4b9e7fe8c4b: function(arg0, arg1, arg2) {
            getObject(arg0).uniform1i(getObject(arg1), arg2);
        },
        __wbg_uniform1ui_a0f911ff174715d0: function(arg0, arg1, arg2) {
            getObject(arg0).uniform1ui(getObject(arg1), arg2 >>> 0);
        },
        __wbg_uniform2f_1887b1268f65bfee: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform2f(getObject(arg1), arg2, arg3);
        },
        __wbg_uniform2fv_04c304b93cbf7f55: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform2fv(getObject(arg1), getArrayF32FromWasm0(arg2, arg3));
        },
        __wbg_uniform2fv_2fb47cfe06330cc7: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform2fv(getObject(arg1), getArrayF32FromWasm0(arg2, arg3));
        },
        __wbg_uniform2iv_095baf208f172131: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform2iv(getObject(arg1), getArrayI32FromWasm0(arg2, arg3));
        },
        __wbg_uniform2iv_ccf2ed44ac8e602e: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform2iv(getObject(arg1), getArrayI32FromWasm0(arg2, arg3));
        },
        __wbg_uniform2uiv_3030d7e769f5e82a: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform2uiv(getObject(arg1), getArrayU32FromWasm0(arg2, arg3));
        },
        __wbg_uniform3fv_aa35ef21e14d5469: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform3fv(getObject(arg1), getArrayF32FromWasm0(arg2, arg3));
        },
        __wbg_uniform3fv_c0872003729939a5: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform3fv(getObject(arg1), getArrayF32FromWasm0(arg2, arg3));
        },
        __wbg_uniform3iv_6aa2b0791e659d14: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform3iv(getObject(arg1), getArrayI32FromWasm0(arg2, arg3));
        },
        __wbg_uniform3iv_e912f444d4ff8269: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform3iv(getObject(arg1), getArrayI32FromWasm0(arg2, arg3));
        },
        __wbg_uniform3uiv_86941e7eeb8ee0a3: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform3uiv(getObject(arg1), getArrayU32FromWasm0(arg2, arg3));
        },
        __wbg_uniform4f_71ec75443e58cecc: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).uniform4f(getObject(arg1), arg2, arg3, arg4, arg5);
        },
        __wbg_uniform4f_f6b5e2024636033a: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).uniform4f(getObject(arg1), arg2, arg3, arg4, arg5);
        },
        __wbg_uniform4fv_498bd80dc5aa16ff: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform4fv(getObject(arg1), getArrayF32FromWasm0(arg2, arg3));
        },
        __wbg_uniform4fv_e6c73702e9a3be5c: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform4fv(getObject(arg1), getArrayF32FromWasm0(arg2, arg3));
        },
        __wbg_uniform4iv_375332584c65e61b: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform4iv(getObject(arg1), getArrayI32FromWasm0(arg2, arg3));
        },
        __wbg_uniform4iv_8a8219fda39dffd5: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform4iv(getObject(arg1), getArrayI32FromWasm0(arg2, arg3));
        },
        __wbg_uniform4uiv_046ee400bb80547d: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform4uiv(getObject(arg1), getArrayU32FromWasm0(arg2, arg3));
        },
        __wbg_uniformBlockBinding_1cf9fd2c49adf0f3: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniformBlockBinding(getObject(arg1), arg2 >>> 0, arg3 >>> 0);
        },
        __wbg_uniformMatrix2fv_24430076c7afb5e3: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix2fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix2fv_e2806601f5b95102: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix2fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix2x3fv_a377326104a8faf4: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix2x3fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix2x4fv_b7a4d810e7a1cf7d: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix2x4fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix3fv_6f822361173d8046: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix3fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix3fv_b94a764c63aa6468: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix3fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix3x2fv_69a4cf0ce5b09f8b: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix3x2fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix3x4fv_cc72e31a1baaf9c9: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix3x4fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix4fv_0e724dbebd372526: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix4fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix4fv_923b55ad503fdc56: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix4fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix4x2fv_8c9fb646f3b90b63: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix4x2fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_uniformMatrix4x3fv_ee0bed9a1330400d: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).uniformMatrix4x3fv(getObject(arg1), arg2 !== 0, getArrayF32FromWasm0(arg3, arg4));
        },
        __wbg_unmap_ab94ab04cfb14bee: function(arg0) {
            getObject(arg0).unmap();
        },
        __wbg_useProgram_e82c1a5f87d81579: function(arg0, arg1) {
            getObject(arg0).useProgram(getObject(arg1));
        },
        __wbg_useProgram_fe720ade4d3b6edb: function(arg0, arg1) {
            getObject(arg0).useProgram(getObject(arg1));
        },
        __wbg_vertexAttribDivisorANGLE_eaa3c29423ea6da4: function(arg0, arg1, arg2) {
            getObject(arg0).vertexAttribDivisorANGLE(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_vertexAttribDivisor_744c0ca468594894: function(arg0, arg1, arg2) {
            getObject(arg0).vertexAttribDivisor(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_vertexAttribIPointer_b9020d0c2e759912: function(arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).vertexAttribIPointer(arg1 >>> 0, arg2, arg3 >>> 0, arg4, arg5);
        },
        __wbg_vertexAttribPointer_75f6ff47f6c9f8cb: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            getObject(arg0).vertexAttribPointer(arg1 >>> 0, arg2, arg3 >>> 0, arg4 !== 0, arg5, arg6);
        },
        __wbg_vertexAttribPointer_adbd1853cce679ad: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            getObject(arg0).vertexAttribPointer(arg1 >>> 0, arg2, arg3 >>> 0, arg4 !== 0, arg5, arg6);
        },
        __wbg_viewport_174ae1c2209344ae: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).viewport(arg1, arg2, arg3, arg4);
        },
        __wbg_viewport_df236eac68bc7467: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).viewport(arg1, arg2, arg3, arg4);
        },
        __wbg_warn_f7ae1b2e66ccb930: function(arg0) {
            console.warn(getObject(arg0));
        },
        __wbg_width_5f66bde2e810fbde: function(arg0) {
            const ret = getObject(arg0).width;
            return ret;
        },
        __wbg_writeBuffer_b203cf79b98d6dd8: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5) {
            getObject(arg0).writeBuffer(getObject(arg1), arg2, getObject(arg3), arg4, arg5);
        }, arguments); },
        __wbg_writeTexture_0466bf7d7d35e04e: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).writeTexture(getObject(arg1), getObject(arg2), getObject(arg3), getObject(arg4));
        }, arguments); },
        __wbindgen_cast_0000000000000001: function(arg0, arg1) {
            // Cast intrinsic for `Closure(Closure { dtor_idx: 801, function: Function { arguments: [Externref], shim_idx: 802, ret: Unit, inner_ret: Some(Unit) }, mutable: true }) -> Externref`.
            const ret = makeMutClosure(arg0, arg1, wasm.__wasm_bindgen_func_elem_3198, __wasm_bindgen_func_elem_3199);
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000002: function(arg0) {
            // Cast intrinsic for `F64 -> Externref`.
            const ret = arg0;
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000003: function(arg0, arg1) {
            // Cast intrinsic for `Ref(Slice(F32)) -> NamedExternref("Float32Array")`.
            const ret = getArrayF32FromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000004: function(arg0, arg1) {
            // Cast intrinsic for `Ref(Slice(I16)) -> NamedExternref("Int16Array")`.
            const ret = getArrayI16FromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000005: function(arg0, arg1) {
            // Cast intrinsic for `Ref(Slice(I32)) -> NamedExternref("Int32Array")`.
            const ret = getArrayI32FromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000006: function(arg0, arg1) {
            // Cast intrinsic for `Ref(Slice(I8)) -> NamedExternref("Int8Array")`.
            const ret = getArrayI8FromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000007: function(arg0, arg1) {
            // Cast intrinsic for `Ref(Slice(U16)) -> NamedExternref("Uint16Array")`.
            const ret = getArrayU16FromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000008: function(arg0, arg1) {
            // Cast intrinsic for `Ref(Slice(U32)) -> NamedExternref("Uint32Array")`.
            const ret = getArrayU32FromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_cast_0000000000000009: function(arg0, arg1) {
            // Cast intrinsic for `Ref(Slice(U8)) -> NamedExternref("Uint8Array")`.
            const ret = getArrayU8FromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_cast_000000000000000a: function(arg0, arg1) {
            // Cast intrinsic for `Ref(String) -> Externref`.
            const ret = getStringFromWasm0(arg0, arg1);
            return addHeapObject(ret);
        },
        __wbindgen_object_clone_ref: function(arg0) {
            const ret = getObject(arg0);
            return addHeapObject(ret);
        },
        __wbindgen_object_drop_ref: function(arg0) {
            takeObject(arg0);
        },
    };
    return {
        __proto__: null,
        "./rource_wasm_bg.js": import0,
    };
}

function __wasm_bindgen_func_elem_3199(arg0, arg1, arg2) {
    wasm.__wasm_bindgen_func_elem_3199(arg0, arg1, addHeapObject(arg2));
}

function __wasm_bindgen_func_elem_7946(arg0, arg1, arg2, arg3) {
    wasm.__wasm_bindgen_func_elem_7946(arg0, arg1, addHeapObject(arg2), addHeapObject(arg3));
}


const __wbindgen_enum_GpuAddressMode = ["clamp-to-edge", "repeat", "mirror-repeat"];


const __wbindgen_enum_GpuBlendFactor = ["zero", "one", "src", "one-minus-src", "src-alpha", "one-minus-src-alpha", "dst", "one-minus-dst", "dst-alpha", "one-minus-dst-alpha", "src-alpha-saturated", "constant", "one-minus-constant", "src1", "one-minus-src1", "src1-alpha", "one-minus-src1-alpha"];


const __wbindgen_enum_GpuBlendOperation = ["add", "subtract", "reverse-subtract", "min", "max"];


const __wbindgen_enum_GpuBufferBindingType = ["uniform", "storage", "read-only-storage"];


const __wbindgen_enum_GpuCanvasAlphaMode = ["opaque", "premultiplied"];


const __wbindgen_enum_GpuCompareFunction = ["never", "less", "equal", "less-equal", "greater", "not-equal", "greater-equal", "always"];


const __wbindgen_enum_GpuCullMode = ["none", "front", "back"];


const __wbindgen_enum_GpuFilterMode = ["nearest", "linear"];


const __wbindgen_enum_GpuFrontFace = ["ccw", "cw"];


const __wbindgen_enum_GpuIndexFormat = ["uint16", "uint32"];


const __wbindgen_enum_GpuLoadOp = ["load", "clear"];


const __wbindgen_enum_GpuMipmapFilterMode = ["nearest", "linear"];


const __wbindgen_enum_GpuPowerPreference = ["low-power", "high-performance"];


const __wbindgen_enum_GpuPrimitiveTopology = ["point-list", "line-list", "line-strip", "triangle-list", "triangle-strip"];


const __wbindgen_enum_GpuSamplerBindingType = ["filtering", "non-filtering", "comparison"];


const __wbindgen_enum_GpuStencilOperation = ["keep", "zero", "replace", "invert", "increment-clamp", "decrement-clamp", "increment-wrap", "decrement-wrap"];


const __wbindgen_enum_GpuStorageTextureAccess = ["write-only", "read-only", "read-write"];


const __wbindgen_enum_GpuStoreOp = ["store", "discard"];


const __wbindgen_enum_GpuTextureAspect = ["all", "stencil-only", "depth-only"];


const __wbindgen_enum_GpuTextureDimension = ["1d", "2d", "3d"];


const __wbindgen_enum_GpuTextureFormat = ["r8unorm", "r8snorm", "r8uint", "r8sint", "r16uint", "r16sint", "r16float", "rg8unorm", "rg8snorm", "rg8uint", "rg8sint", "r32uint", "r32sint", "r32float", "rg16uint", "rg16sint", "rg16float", "rgba8unorm", "rgba8unorm-srgb", "rgba8snorm", "rgba8uint", "rgba8sint", "bgra8unorm", "bgra8unorm-srgb", "rgb9e5ufloat", "rgb10a2uint", "rgb10a2unorm", "rg11b10ufloat", "rg32uint", "rg32sint", "rg32float", "rgba16uint", "rgba16sint", "rgba16float", "rgba32uint", "rgba32sint", "rgba32float", "stencil8", "depth16unorm", "depth24plus", "depth24plus-stencil8", "depth32float", "depth32float-stencil8", "bc1-rgba-unorm", "bc1-rgba-unorm-srgb", "bc2-rgba-unorm", "bc2-rgba-unorm-srgb", "bc3-rgba-unorm", "bc3-rgba-unorm-srgb", "bc4-r-unorm", "bc4-r-snorm", "bc5-rg-unorm", "bc5-rg-snorm", "bc6h-rgb-ufloat", "bc6h-rgb-float", "bc7-rgba-unorm", "bc7-rgba-unorm-srgb", "etc2-rgb8unorm", "etc2-rgb8unorm-srgb", "etc2-rgb8a1unorm", "etc2-rgb8a1unorm-srgb", "etc2-rgba8unorm", "etc2-rgba8unorm-srgb", "eac-r11unorm", "eac-r11snorm", "eac-rg11unorm", "eac-rg11snorm", "astc-4x4-unorm", "astc-4x4-unorm-srgb", "astc-5x4-unorm", "astc-5x4-unorm-srgb", "astc-5x5-unorm", "astc-5x5-unorm-srgb", "astc-6x5-unorm", "astc-6x5-unorm-srgb", "astc-6x6-unorm", "astc-6x6-unorm-srgb", "astc-8x5-unorm", "astc-8x5-unorm-srgb", "astc-8x6-unorm", "astc-8x6-unorm-srgb", "astc-8x8-unorm", "astc-8x8-unorm-srgb", "astc-10x5-unorm", "astc-10x5-unorm-srgb", "astc-10x6-unorm", "astc-10x6-unorm-srgb", "astc-10x8-unorm", "astc-10x8-unorm-srgb", "astc-10x10-unorm", "astc-10x10-unorm-srgb", "astc-12x10-unorm", "astc-12x10-unorm-srgb", "astc-12x12-unorm", "astc-12x12-unorm-srgb"];


const __wbindgen_enum_GpuTextureSampleType = ["float", "unfilterable-float", "depth", "sint", "uint"];


const __wbindgen_enum_GpuTextureViewDimension = ["1d", "2d", "2d-array", "cube", "cube-array", "3d"];


const __wbindgen_enum_GpuVertexFormat = ["uint8", "uint8x2", "uint8x4", "sint8", "sint8x2", "sint8x4", "unorm8", "unorm8x2", "unorm8x4", "snorm8", "snorm8x2", "snorm8x4", "uint16", "uint16x2", "uint16x4", "sint16", "sint16x2", "sint16x4", "unorm16", "unorm16x2", "unorm16x4", "snorm16", "snorm16x2", "snorm16x4", "float16", "float16x2", "float16x4", "float32", "float32x2", "float32x3", "float32x4", "uint32", "uint32x2", "uint32x3", "uint32x4", "sint32", "sint32x2", "sint32x3", "sint32x4", "unorm10-10-10-2", "unorm8x4-bgra"];


const __wbindgen_enum_GpuVertexStepMode = ["vertex", "instance"];
const RourceFinalization = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(ptr => wasm.__wbg_rource_free(ptr >>> 0, 1));

function addHeapObject(obj) {
    if (heap_next === heap.length) heap.push(heap.length + 1);
    const idx = heap_next;
    heap_next = heap[idx];

    heap[idx] = obj;
    return idx;
}

const CLOSURE_DTORS = (typeof FinalizationRegistry === 'undefined')
    ? { register: () => {}, unregister: () => {} }
    : new FinalizationRegistry(state => state.dtor(state.a, state.b));

function debugString(val) {
    // primitive types
    const type = typeof val;
    if (type == 'number' || type == 'boolean' || val == null) {
        return  `${val}`;
    }
    if (type == 'string') {
        return `"${val}"`;
    }
    if (type == 'symbol') {
        const description = val.description;
        if (description == null) {
            return 'Symbol';
        } else {
            return `Symbol(${description})`;
        }
    }
    if (type == 'function') {
        const name = val.name;
        if (typeof name == 'string' && name.length > 0) {
            return `Function(${name})`;
        } else {
            return 'Function';
        }
    }
    // objects
    if (Array.isArray(val)) {
        const length = val.length;
        let debug = '[';
        if (length > 0) {
            debug += debugString(val[0]);
        }
        for(let i = 1; i < length; i++) {
            debug += ', ' + debugString(val[i]);
        }
        debug += ']';
        return debug;
    }
    // Test for built-in
    const builtInMatches = /\[object ([^\]]+)\]/.exec(toString.call(val));
    let className;
    if (builtInMatches && builtInMatches.length > 1) {
        className = builtInMatches[1];
    } else {
        // Failed to match the standard '[object ClassName]'
        return toString.call(val);
    }
    if (className == 'Object') {
        // we're a user defined class or Object
        // JSON.stringify avoids problems with cycles, and is generally much
        // easier than looping through ownProperties of `val`.
        try {
            return 'Object(' + JSON.stringify(val) + ')';
        } catch (_) {
            return 'Object';
        }
    }
    // errors
    if (val instanceof Error) {
        return `${val.name}: ${val.message}\n${val.stack}`;
    }
    // TODO we could test for more things here, like `Set`s and `Map`s.
    return className;
}

function dropObject(idx) {
    if (idx < 132) return;
    heap[idx] = heap_next;
    heap_next = idx;
}

function getArrayF32FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getFloat32ArrayMemory0().subarray(ptr / 4, ptr / 4 + len);
}

function getArrayI16FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getInt16ArrayMemory0().subarray(ptr / 2, ptr / 2 + len);
}

function getArrayI32FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getInt32ArrayMemory0().subarray(ptr / 4, ptr / 4 + len);
}

function getArrayI8FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getInt8ArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
}

function getArrayU16FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getUint16ArrayMemory0().subarray(ptr / 2, ptr / 2 + len);
}

function getArrayU32FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getUint32ArrayMemory0().subarray(ptr / 4, ptr / 4 + len);
}

function getArrayU8FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getUint8ArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
}

function getClampedArrayU8FromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return getUint8ClampedArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
}

let cachedDataViewMemory0 = null;
function getDataViewMemory0() {
    if (cachedDataViewMemory0 === null || cachedDataViewMemory0.buffer.detached === true || (cachedDataViewMemory0.buffer.detached === undefined && cachedDataViewMemory0.buffer !== wasm.memory.buffer)) {
        cachedDataViewMemory0 = new DataView(wasm.memory.buffer);
    }
    return cachedDataViewMemory0;
}

let cachedFloat32ArrayMemory0 = null;
function getFloat32ArrayMemory0() {
    if (cachedFloat32ArrayMemory0 === null || cachedFloat32ArrayMemory0.byteLength === 0) {
        cachedFloat32ArrayMemory0 = new Float32Array(wasm.memory.buffer);
    }
    return cachedFloat32ArrayMemory0;
}

let cachedInt16ArrayMemory0 = null;
function getInt16ArrayMemory0() {
    if (cachedInt16ArrayMemory0 === null || cachedInt16ArrayMemory0.byteLength === 0) {
        cachedInt16ArrayMemory0 = new Int16Array(wasm.memory.buffer);
    }
    return cachedInt16ArrayMemory0;
}

let cachedInt32ArrayMemory0 = null;
function getInt32ArrayMemory0() {
    if (cachedInt32ArrayMemory0 === null || cachedInt32ArrayMemory0.byteLength === 0) {
        cachedInt32ArrayMemory0 = new Int32Array(wasm.memory.buffer);
    }
    return cachedInt32ArrayMemory0;
}

let cachedInt8ArrayMemory0 = null;
function getInt8ArrayMemory0() {
    if (cachedInt8ArrayMemory0 === null || cachedInt8ArrayMemory0.byteLength === 0) {
        cachedInt8ArrayMemory0 = new Int8Array(wasm.memory.buffer);
    }
    return cachedInt8ArrayMemory0;
}

function getStringFromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return decodeText(ptr, len);
}

let cachedUint16ArrayMemory0 = null;
function getUint16ArrayMemory0() {
    if (cachedUint16ArrayMemory0 === null || cachedUint16ArrayMemory0.byteLength === 0) {
        cachedUint16ArrayMemory0 = new Uint16Array(wasm.memory.buffer);
    }
    return cachedUint16ArrayMemory0;
}

let cachedUint32ArrayMemory0 = null;
function getUint32ArrayMemory0() {
    if (cachedUint32ArrayMemory0 === null || cachedUint32ArrayMemory0.byteLength === 0) {
        cachedUint32ArrayMemory0 = new Uint32Array(wasm.memory.buffer);
    }
    return cachedUint32ArrayMemory0;
}

let cachedUint8ArrayMemory0 = null;
function getUint8ArrayMemory0() {
    if (cachedUint8ArrayMemory0 === null || cachedUint8ArrayMemory0.byteLength === 0) {
        cachedUint8ArrayMemory0 = new Uint8Array(wasm.memory.buffer);
    }
    return cachedUint8ArrayMemory0;
}

let cachedUint8ClampedArrayMemory0 = null;
function getUint8ClampedArrayMemory0() {
    if (cachedUint8ClampedArrayMemory0 === null || cachedUint8ClampedArrayMemory0.byteLength === 0) {
        cachedUint8ClampedArrayMemory0 = new Uint8ClampedArray(wasm.memory.buffer);
    }
    return cachedUint8ClampedArrayMemory0;
}

function getObject(idx) { return heap[idx]; }

function handleError(f, args) {
    try {
        return f.apply(this, args);
    } catch (e) {
        wasm.__wbindgen_export3(addHeapObject(e));
    }
}

let heap = new Array(128).fill(undefined);
heap.push(undefined, null, true, false);

let heap_next = heap.length;

function isLikeNone(x) {
    return x === undefined || x === null;
}

function makeMutClosure(arg0, arg1, dtor, f) {
    const state = { a: arg0, b: arg1, cnt: 1, dtor };
    const real = (...args) => {

        // First up with a closure we increment the internal reference
        // count. This ensures that the Rust closure environment won't
        // be deallocated while we're invoking it.
        state.cnt++;
        const a = state.a;
        state.a = 0;
        try {
            return f(a, state.b, ...args);
        } finally {
            state.a = a;
            real._wbg_cb_unref();
        }
    };
    real._wbg_cb_unref = () => {
        if (--state.cnt === 0) {
            state.dtor(state.a, state.b);
            state.a = 0;
            CLOSURE_DTORS.unregister(state);
        }
    };
    CLOSURE_DTORS.register(real, state, state);
    return real;
}

function passArray8ToWasm0(arg, malloc) {
    const ptr = malloc(arg.length * 1, 1) >>> 0;
    getUint8ArrayMemory0().set(arg, ptr / 1);
    WASM_VECTOR_LEN = arg.length;
    return ptr;
}

function passStringToWasm0(arg, malloc, realloc) {
    if (realloc === undefined) {
        const buf = cachedTextEncoder.encode(arg);
        const ptr = malloc(buf.length, 1) >>> 0;
        getUint8ArrayMemory0().subarray(ptr, ptr + buf.length).set(buf);
        WASM_VECTOR_LEN = buf.length;
        return ptr;
    }

    let len = arg.length;
    let ptr = malloc(len, 1) >>> 0;

    const mem = getUint8ArrayMemory0();

    let offset = 0;

    for (; offset < len; offset++) {
        const code = arg.charCodeAt(offset);
        if (code > 0x7F) break;
        mem[ptr + offset] = code;
    }
    if (offset !== len) {
        if (offset !== 0) {
            arg = arg.slice(offset);
        }
        ptr = realloc(ptr, len, len = offset + arg.length * 3, 1) >>> 0;
        const view = getUint8ArrayMemory0().subarray(ptr + offset, ptr + len);
        const ret = cachedTextEncoder.encodeInto(arg, view);

        offset += ret.written;
        ptr = realloc(ptr, len, offset, 1) >>> 0;
    }

    WASM_VECTOR_LEN = offset;
    return ptr;
}

function takeObject(idx) {
    const ret = getObject(idx);
    dropObject(idx);
    return ret;
}

let cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
cachedTextDecoder.decode();
const MAX_SAFARI_DECODE_BYTES = 2146435072;
let numBytesDecoded = 0;
function decodeText(ptr, len) {
    numBytesDecoded += len;
    if (numBytesDecoded >= MAX_SAFARI_DECODE_BYTES) {
        cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
        cachedTextDecoder.decode();
        numBytesDecoded = len;
    }
    return cachedTextDecoder.decode(getUint8ArrayMemory0().subarray(ptr, ptr + len));
}

const cachedTextEncoder = new TextEncoder();

if (!('encodeInto' in cachedTextEncoder)) {
    cachedTextEncoder.encodeInto = function (arg, view) {
        const buf = cachedTextEncoder.encode(arg);
        view.set(buf);
        return {
            read: arg.length,
            written: buf.length
        };
    };
}

let WASM_VECTOR_LEN = 0;

let wasmModule, wasm;
function __wbg_finalize_init(instance, module) {
    wasm = instance.exports;
    wasmModule = module;
    cachedDataViewMemory0 = null;
    cachedFloat32ArrayMemory0 = null;
    cachedInt16ArrayMemory0 = null;
    cachedInt32ArrayMemory0 = null;
    cachedInt8ArrayMemory0 = null;
    cachedUint16ArrayMemory0 = null;
    cachedUint32ArrayMemory0 = null;
    cachedUint8ArrayMemory0 = null;
    cachedUint8ClampedArrayMemory0 = null;
    wasm.__wbindgen_start();
    return wasm;
}

async function __wbg_load(module, imports) {
    if (typeof Response === 'function' && module instanceof Response) {
        if (typeof WebAssembly.instantiateStreaming === 'function') {
            try {
                return await WebAssembly.instantiateStreaming(module, imports);
            } catch (e) {
                const validResponse = module.ok && expectedResponseType(module.type);

                if (validResponse && module.headers.get('Content-Type') !== 'application/wasm') {
                    console.warn("`WebAssembly.instantiateStreaming` failed because your server does not serve Wasm with `application/wasm` MIME type. Falling back to `WebAssembly.instantiate` which is slower. Original error:\n", e);

                } else { throw e; }
            }
        }

        const bytes = await module.arrayBuffer();
        return await WebAssembly.instantiate(bytes, imports);
    } else {
        const instance = await WebAssembly.instantiate(module, imports);

        if (instance instanceof WebAssembly.Instance) {
            return { instance, module };
        } else {
            return instance;
        }
    }

    function expectedResponseType(type) {
        switch (type) {
            case 'basic': case 'cors': case 'default': return true;
        }
        return false;
    }
}

function initSync(module) {
    if (wasm !== undefined) return wasm;


    if (module !== undefined) {
        if (Object.getPrototypeOf(module) === Object.prototype) {
            ({module} = module)
        } else {
            console.warn('using deprecated parameters for `initSync()`; pass a single object instead')
        }
    }

    const imports = __wbg_get_imports();
    if (!(module instanceof WebAssembly.Module)) {
        module = new WebAssembly.Module(module);
    }
    const instance = new WebAssembly.Instance(module, imports);
    return __wbg_finalize_init(instance, module);
}

async function __wbg_init(module_or_path) {
    if (wasm !== undefined) return wasm;


    if (module_or_path !== undefined) {
        if (Object.getPrototypeOf(module_or_path) === Object.prototype) {
            ({module_or_path} = module_or_path)
        } else {
            console.warn('using deprecated parameters for the initialization function; pass a single object instead')
        }
    }

    if (module_or_path === undefined) {
        module_or_path = new URL('rource_wasm_bg.wasm', import.meta.url);
    }
    const imports = __wbg_get_imports();

    if (typeof module_or_path === 'string' || (typeof Request === 'function' && module_or_path instanceof Request) || (typeof URL === 'function' && module_or_path instanceof URL)) {
        module_or_path = fetch(module_or_path);
    }

    const { instance, module } = await __wbg_load(await module_or_path, imports);

    return __wbg_finalize_init(instance, module);
}

export { initSync, __wbg_init as default };
