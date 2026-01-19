/* @ts-self-types="./rource_wasm.d.ts" */

/**
 * The main Rource visualization controller for browser usage.
 */
export class Rource {
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
     * Captures a screenshot and returns it as PNG data (`Uint8Array`).
     *
     * Note: This only works with the software renderer. For WebGL2, returns an error.
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
            wasm.__wbindgen_export3(r0, r1 * 1, 1);
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
     * Returns the current commit index.
     * @returns {number}
     */
    currentCommit() {
        const ret = wasm.rource_currentCommit(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Forces a render without updating simulation (useful for static views).
     */
    forceRender() {
        wasm.rource_forceRender(this.__wbg_ptr);
    }
    /**
     * Updates and renders a single frame.
     *
     * # Arguments
     *
     * * `timestamp` - Current time in milliseconds (from requestAnimationFrame)
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
     * Returns the color for a given author name as a hex string (e.g., "#ff5500").
     *
     * This uses the same deterministic color generation as the visualization,
     * so colors will match what's displayed on screen.
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
            wasm.__wbindgen_export3(deferred2_0, deferred2_1, 1);
        }
    }
    /**
     * Returns author data as a JSON string array.
     *
     * Each entry contains: `{ "name": "Author Name", "color": "#rrggbb", "commits": count }`
     * Sorted by commit count (most active first).
     *
     * # Example (JavaScript)
     *
     * ```javascript,ignore
     * const authorsJson = rource.getAuthors();
     * const authors = JSON.parse(authorsJson);
     * authors.forEach(a => console.log(a.name, a.color, a.commits));
     * ```
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
            wasm.__wbindgen_export3(deferred1_0, deferred1_1, 1);
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
     * Returns the estimated draw call count for the last frame.
     * @returns {number}
     */
    getDrawCalls() {
        const ret = wasm.rource_getDrawCalls(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the current frames per second (rolling average over 60 frames).
     * @returns {number}
     */
    getFps() {
        const ret = wasm.rource_getFps(this.__wbg_ptr);
        return ret;
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
     * Returns the type of renderer being used ("webgl2" or "software").
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
            wasm.__wbindgen_export3(deferred1_0, deferred1_1, 1);
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
     * Returns the total number of entities in the scene.
     * @returns {number}
     */
    getTotalEntities() {
        const ret = wasm.rource_getTotalEntities(this.__wbg_ptr);
        return ret >>> 0;
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
     * Returns the total number of frames rendered since initialization.
     * @returns {bigint}
     */
    getTotalFrames() {
        const ret = wasm.rource_getTotalFrames(this.__wbg_ptr);
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
     * Returns the uptime in seconds since initialization.
     * @returns {number}
     */
    getUptime() {
        const ret = wasm.rource_getUptime(this.__wbg_ptr);
        return ret;
    }
    /**
     * Returns the number of visible directories currently being rendered.
     * @returns {number}
     */
    getVisibleDirectories() {
        const ret = wasm.rource_getVisibleDirectories(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the number of visible files currently being rendered.
     * @returns {number}
     */
    getVisibleFiles() {
        const ret = wasm.rource_getVisibleFiles(this.__wbg_ptr);
        return ret >>> 0;
    }
    /**
     * Returns the number of visible users currently being rendered.
     * @returns {number}
     */
    getVisibleUsers() {
        const ret = wasm.rource_getVisibleUsers(this.__wbg_ptr);
        return ret >>> 0;
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
     * Returns whether playback is active.
     * @returns {boolean}
     */
    isPlaying() {
        const ret = wasm.rource_isPlaying(this.__wbg_ptr);
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
     * Loads commits from custom pipe-delimited format.
     *
     * Format: `timestamp|author|action|path` per line
     * - timestamp: Unix timestamp
     * - author: Committer name
     * - action: A=add, M=modify, D=delete
     * - path: File path
     *
     * # Example (JavaScript)
     *
     * ```javascript,ignore
     * rource.loadCustomLog("1234567890|John Doe|A|src/main.rs\n1234567891|Jane|M|src/lib.rs");
     * ```
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
     * Expected format is `git log --pretty=format:... --name-status`
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
     * Creates a new Rource instance attached to a canvas element.
     *
     * Automatically tries WebGL2 first, falling back to software rendering if unavailable.
     *
     * # Arguments
     *
     * * `canvas` - The HTML canvas element to render to
     * @param {HTMLCanvasElement} canvas
     */
    constructor(canvas) {
        try {
            const retptr = wasm.__wbindgen_add_to_stack_pointer(-16);
            wasm.rource_new(retptr, addHeapObject(canvas));
            var r0 = getDataViewMemory0().getInt32(retptr + 4 * 0, true);
            var r1 = getDataViewMemory0().getInt32(retptr + 4 * 1, true);
            var r2 = getDataViewMemory0().getInt32(retptr + 4 * 2, true);
            if (r2) {
                throw takeObject(r1);
            }
            this.__wbg_ptr = r0 >>> 0;
            RourceFinalization.register(this, this.__wbg_ptr, this);
            return this;
        } finally {
            wasm.__wbindgen_add_to_stack_pointer(16);
        }
    }
    /**
     * Handles keyboard events.
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
     * Checks for entity under cursor first. If an entity is found, starts dragging it.
     * Otherwise, starts camera panning.
     * @param {number} x
     * @param {number} y
     */
    onMouseDown(x, y) {
        wasm.rource_onMouseDown(this.__wbg_ptr, x, y);
    }
    /**
     * Handles mouse move events.
     *
     * If dragging an entity, updates its position and applies force-directed
     * movement to connected entities. Otherwise, pans the camera.
     * @param {number} x
     * @param {number} y
     */
    onMouseMove(x, y) {
        wasm.rource_onMouseMove(this.__wbg_ptr, x, y);
    }
    /**
     * Handles mouse up events.
     */
    onMouseUp() {
        wasm.rource_onMouseUp(this.__wbg_ptr);
    }
    /**
     * Handles mouse wheel events for zooming toward the mouse position.
     *
     * Uses a smooth, proportional zoom based on scroll amount.
     * Zooms toward the mouse position so the content under the cursor stays in place.
     * @param {number} delta_y
     * @param {number} mouse_x
     * @param {number} mouse_y
     */
    onWheel(delta_y, mouse_x, mouse_y) {
        wasm.rource_onWheel(this.__wbg_ptr, delta_y, mouse_x, mouse_y);
    }
    /**
     * Pans the camera by the given delta in screen pixels.
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
     * Resets the camera to fit all content.
     */
    resetCamera() {
        wasm.rource_resetCamera(this.__wbg_ptr);
    }
    /**
     * Resizes the canvas and renderer.
     * @param {number} width
     * @param {number} height
     */
    resize(width, height) {
        wasm.rource_resize(this.__wbg_ptr, width, height);
    }
    /**
     * Seeks to a specific commit index.
     * @param {number} commit_index
     */
    seek(commit_index) {
        wasm.rource_seek(this.__wbg_ptr, commit_index);
    }
    /**
     * Sets the background color (hex string like "#000000" or "000000").
     * @param {string} hex
     */
    setBackgroundColor(hex) {
        const ptr0 = passStringToWasm0(hex, wasm.__wbindgen_export, wasm.__wbindgen_export2);
        const len0 = WASM_VECTOR_LEN;
        wasm.rource_setBackgroundColor(this.__wbg_ptr, ptr0, len0);
    }
    /**
     * Sets whether to show bloom effect.
     * @param {boolean} enabled
     */
    setBloom(enabled) {
        wasm.rource_setBloom(this.__wbg_ptr, enabled);
    }
    /**
     * Sets whether to show labels (user names, file names).
     * @param {boolean} show
     */
    setShowLabels(show) {
        wasm.rource_setShowLabels(this.__wbg_ptr, show);
    }
    /**
     * Sets playback speed (seconds per day of repository history).
     *
     * The speed is clamped between 1.0 (10x, fastest) and 1000.0 (very slow) seconds per day.
     * NaN, infinite, and non-positive values are replaced with the default of 10.0.
     *
     * The formula `seconds_per_commit = seconds_per_day / 10.0` means:
     * - At speed=1.0 (10x): 0.1s per commit = ~6 frames at 60fps (acceptable)
     * - At speed=0.1 (100x): 0.01s per commit = ~1.7 commits/frame (too fast!)
     * @param {number} seconds_per_day
     */
    setSpeed(seconds_per_day) {
        wasm.rource_setSpeed(this.__wbg_ptr, seconds_per_day);
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
     * Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
     * @param {number} factor
     */
    zoom(factor) {
        wasm.rource_zoom(this.__wbg_ptr, factor);
    }
    /**
     * Zooms the camera toward a specific screen point.
     *
     * This keeps the point under the mouse cursor stationary while zooming,
     * making it easier to zoom into specific areas of the visualization.
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
        __wbg___wbindgen_throw_be289d5034ed271b: function(arg0, arg1) {
            throw new Error(getStringFromWasm0(arg0, arg1));
        },
        __wbg_activeTexture_6f9a710514686c24: function(arg0, arg1) {
            getObject(arg0).activeTexture(arg1 >>> 0);
        },
        __wbg_attachShader_b36058e5c9eeaf54: function(arg0, arg1, arg2) {
            getObject(arg0).attachShader(getObject(arg1), getObject(arg2));
        },
        __wbg_bindBuffer_c9068e8712a034f5: function(arg0, arg1, arg2) {
            getObject(arg0).bindBuffer(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindTexture_b2b7b1726a83f93e: function(arg0, arg1, arg2) {
            getObject(arg0).bindTexture(arg1 >>> 0, getObject(arg2));
        },
        __wbg_bindVertexArray_78220d1edb1d2382: function(arg0, arg1) {
            getObject(arg0).bindVertexArray(getObject(arg1));
        },
        __wbg_blendFunc_2ef59299d10c662d: function(arg0, arg1, arg2) {
            getObject(arg0).blendFunc(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_bufferData_037b591220c42be7: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).bufferData(arg1 >>> 0, getArrayU8FromWasm0(arg2, arg3), arg4 >>> 0);
        },
        __wbg_clearColor_404a3b16d43db93b: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).clearColor(arg1, arg2, arg3, arg4);
        },
        __wbg_clear_7187030f892c5ca0: function(arg0, arg1) {
            getObject(arg0).clear(arg1 >>> 0);
        },
        __wbg_compileShader_94718a93495d565d: function(arg0, arg1) {
            getObject(arg0).compileShader(getObject(arg1));
        },
        __wbg_createBuffer_26534c05e01b8559: function(arg0) {
            const ret = getObject(arg0).createBuffer();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createProgram_9b7710a1f2701c2c: function(arg0) {
            const ret = getObject(arg0).createProgram();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createShader_e3ac08ed8c5b14b2: function(arg0, arg1) {
            const ret = getObject(arg0).createShader(arg1 >>> 0);
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createTexture_16d2c8a3d7d4a75a: function(arg0) {
            const ret = getObject(arg0).createTexture();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_createVertexArray_ad5294951ae57497: function(arg0) {
            const ret = getObject(arg0).createVertexArray();
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_deleteBuffer_ab099883c168644d: function(arg0, arg1) {
            getObject(arg0).deleteBuffer(getObject(arg1));
        },
        __wbg_deleteProgram_9298fb3e3c1d3a78: function(arg0, arg1) {
            getObject(arg0).deleteProgram(getObject(arg1));
        },
        __wbg_deleteShader_aaf3b520a64d5d9d: function(arg0, arg1) {
            getObject(arg0).deleteShader(getObject(arg1));
        },
        __wbg_deleteTexture_9d411c0e60ffa324: function(arg0, arg1) {
            getObject(arg0).deleteTexture(getObject(arg1));
        },
        __wbg_deleteVertexArray_7bc7f92769862f93: function(arg0, arg1) {
            getObject(arg0).deleteVertexArray(getObject(arg1));
        },
        __wbg_drawArraysInstanced_ec30adc616ec58d5: function(arg0, arg1, arg2, arg3, arg4) {
            getObject(arg0).drawArraysInstanced(arg1 >>> 0, arg2, arg3, arg4);
        },
        __wbg_enableVertexAttribArray_475e06c31777296d: function(arg0, arg1) {
            getObject(arg0).enableVertexAttribArray(arg1 >>> 0);
        },
        __wbg_enable_d1ac04dfdd2fb3ae: function(arg0, arg1) {
            getObject(arg0).enable(arg1 >>> 0);
        },
        __wbg_error_7534b8e9a36f1ab4: function(arg0, arg1) {
            let deferred0_0;
            let deferred0_1;
            try {
                deferred0_0 = arg0;
                deferred0_1 = arg1;
                console.error(getStringFromWasm0(arg0, arg1));
            } finally {
                wasm.__wbindgen_export3(deferred0_0, deferred0_1, 1);
            }
        },
        __wbg_finish_ee0b71d14fa50456: function(arg0) {
            getObject(arg0).finish();
        },
        __wbg_getContext_2a5764d48600bc43: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = getObject(arg0).getContext(getStringFromWasm0(arg1, arg2));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_getContext_b28d2db7bd648242: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).getContext(getStringFromWasm0(arg1, arg2), getObject(arg3));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        }, arguments); },
        __wbg_getProgramInfoLog_2ffa30e3abb8b5c2: function(arg0, arg1, arg2) {
            const ret = getObject(arg1).getProgramInfoLog(getObject(arg2));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_getProgramParameter_92e4540ca9da06b2: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getProgramParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getShaderInfoLog_9e0b96da4b13ae49: function(arg0, arg1, arg2) {
            const ret = getObject(arg1).getShaderInfoLog(getObject(arg2));
            var ptr1 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            var len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_getShaderParameter_afa4a3dd9dd397c1: function(arg0, arg1, arg2) {
            const ret = getObject(arg0).getShaderParameter(getObject(arg1), arg2 >>> 0);
            return addHeapObject(ret);
        },
        __wbg_getUniformLocation_d06b3a5b3c60e95c: function(arg0, arg1, arg2, arg3) {
            const ret = getObject(arg0).getUniformLocation(getObject(arg1), getStringFromWasm0(arg2, arg3));
            return isLikeNone(ret) ? 0 : addHeapObject(ret);
        },
        __wbg_height_38750dc6de41ee75: function(arg0) {
            const ret = getObject(arg0).height;
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
        __wbg_isContextLost_906412aff09b65f4: function(arg0) {
            const ret = getObject(arg0).isContextLost();
            return ret;
        },
        __wbg_linkProgram_6600dd2c0863bbfd: function(arg0, arg1) {
            getObject(arg0).linkProgram(getObject(arg1));
        },
        __wbg_log_6b5ca2e6124b2808: function(arg0) {
            console.log(getObject(arg0));
        },
        __wbg_new_361308b2356cecd0: function() {
            const ret = new Object();
            return addHeapObject(ret);
        },
        __wbg_new_8a6f238a6ece86ea: function() {
            const ret = new Error();
            return addHeapObject(ret);
        },
        __wbg_new_with_u8_clamped_array_and_sh_0c0b789ceb2eab31: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            const ret = new ImageData(getClampedArrayU8FromWasm0(arg0, arg1), arg2 >>> 0, arg3 >>> 0);
            return addHeapObject(ret);
        }, arguments); },
        __wbg_putImageData_78318465ad96c2c3: function() { return handleError(function (arg0, arg1, arg2, arg3) {
            getObject(arg0).putImageData(getObject(arg1), arg2, arg3);
        }, arguments); },
        __wbg_set_6cb8631f80447a67: function() { return handleError(function (arg0, arg1, arg2) {
            const ret = Reflect.set(getObject(arg0), getObject(arg1), getObject(arg2));
            return ret;
        }, arguments); },
        __wbg_set_height_f21f985387070100: function(arg0, arg1) {
            getObject(arg0).height = arg1 >>> 0;
        },
        __wbg_set_width_d60bc4f2f20c56a4: function(arg0, arg1) {
            getObject(arg0).width = arg1 >>> 0;
        },
        __wbg_shaderSource_32425cfe6e5a1e52: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).shaderSource(getObject(arg1), getStringFromWasm0(arg2, arg3));
        },
        __wbg_stack_0ed75d68575b0f3c: function(arg0, arg1) {
            const ret = getObject(arg1).stack;
            const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_export, wasm.__wbindgen_export2);
            const len1 = WASM_VECTOR_LEN;
            getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
            getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
        },
        __wbg_texImage2D_c1bb39f4b3a26e90: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).texImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, arg9 === 0 ? undefined : getArrayU8FromWasm0(arg9, arg10));
        }, arguments); },
        __wbg_texParameteri_0d45be2c88d6bad8: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).texParameteri(arg1 >>> 0, arg2 >>> 0, arg3);
        },
        __wbg_texSubImage2D_c0140b758462635d: function() { return handleError(function (arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) {
            getObject(arg0).texSubImage2D(arg1 >>> 0, arg2, arg3, arg4, arg5, arg6, arg7 >>> 0, arg8 >>> 0, arg9 === 0 ? undefined : getArrayU8FromWasm0(arg9, arg10));
        }, arguments); },
        __wbg_uniform1i_e9aee4b9e7fe8c4b: function(arg0, arg1, arg2) {
            getObject(arg0).uniform1i(getObject(arg1), arg2);
        },
        __wbg_uniform2f_1887b1268f65bfee: function(arg0, arg1, arg2, arg3) {
            getObject(arg0).uniform2f(getObject(arg1), arg2, arg3);
        },
        __wbg_useProgram_fe720ade4d3b6edb: function(arg0, arg1) {
            getObject(arg0).useProgram(getObject(arg1));
        },
        __wbg_vertexAttribDivisor_744c0ca468594894: function(arg0, arg1, arg2) {
            getObject(arg0).vertexAttribDivisor(arg1 >>> 0, arg2 >>> 0);
        },
        __wbg_vertexAttribPointer_75f6ff47f6c9f8cb: function(arg0, arg1, arg2, arg3, arg4, arg5, arg6) {
            getObject(arg0).vertexAttribPointer(arg1 >>> 0, arg2, arg3 >>> 0, arg4 !== 0, arg5, arg6);
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
        __wbindgen_cast_0000000000000001: function(arg0, arg1) {
            // Cast intrinsic for `Ref(String) -> Externref`.
            const ret = getStringFromWasm0(arg0, arg1);
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

function getStringFromWasm0(ptr, len) {
    ptr = ptr >>> 0;
    return decodeText(ptr, len);
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
        wasm.__wbindgen_export4(addHeapObject(e));
    }
}

let heap = new Array(128).fill(undefined);
heap.push(undefined, null, true, false);

let heap_next = heap.length;

function isLikeNone(x) {
    return x === undefined || x === null;
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
