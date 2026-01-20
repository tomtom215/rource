/* tslint:disable */
/* eslint-disable */

/**
 * The main Rource visualization controller for browser usage.
 */
export class Rource {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Captures a screenshot and returns it as PNG data (`Uint8Array`).
     *
     * Note: This only works with the software renderer. For WebGL2, returns an error.
     */
    captureScreenshot(): Uint8Array;
    /**
     * Returns the number of loaded commits.
     */
    commitCount(): number;
    /**
     * Returns the current commit index.
     */
    currentCommit(): number;
    /**
     * Forces a render without updating simulation (useful for static views).
     *
     * This method ensures the viewport is synchronized with the current canvas
     * dimensions before rendering, which is critical for screenshots and exports.
     *
     * Unlike the normal render path, this also calls `sync()` to ensure all GPU
     * commands complete before returning. This is necessary for `canvas.toBlob()`
     * to capture a complete frame.
     */
    forceRender(): void;
    /**
     * Updates and renders a single frame.
     *
     * # Arguments
     *
     * * `timestamp` - Current time in milliseconds (from requestAnimationFrame)
     *
     * Returns true if there are more frames to render.
     */
    frame(timestamp: number): boolean;
    /**
     * Returns the number of active action beams.
     */
    getActiveActions(): number;
    /**
     * Returns the color for a given author name as a hex string (e.g., "#ff5500").
     *
     * This uses the same deterministic color generation as the visualization,
     * so colors will match what's displayed on screen.
     */
    getAuthorColor(name: string): string;
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
     */
    getAuthors(): string;
    /**
     * Returns the current camera state as JSON for saving/restoring.
     *
     * Returns: `{ "x": f32, "y": f32, "zoom": f32 }`
     */
    getCameraState(): string;
    /**
     * Returns the canvas height in pixels.
     */
    getCanvasHeight(): number;
    /**
     * Returns the canvas width in pixels.
     */
    getCanvasWidth(): number;
    /**
     * Returns the author name for a commit at the given index.
     *
     * Returns empty string if the index is out of bounds.
     */
    getCommitAuthor(index: number): string;
    /**
     * Returns the number of files changed in a commit at the given index.
     *
     * Returns 0 if the index is out of bounds.
     */
    getCommitFileCount(index: number): number;
    /**
     * Returns the timestamp (Unix epoch seconds) for a commit at the given index.
     *
     * Returns 0 if the index is out of bounds.
     * Note: Returns f64 instead of i64 to avoid `BigInt` conversion issues in JavaScript.
     */
    getCommitTimestamp(index: number): number;
    /**
     * Returns the date range of all commits as a JSON object.
     *
     * Returns: `{ "startTimestamp": i64, "endTimestamp": i64 }` or null if no commits.
     */
    getDateRange(): string | undefined;
    /**
     * Returns the estimated draw call count for the last frame.
     */
    getDrawCalls(): number;
    /**
     * Returns the bounding box of all entities as a JSON object.
     *
     * Returns: `{ "minX": f32, "minY": f32, "maxX": f32, "maxY": f32, "width": f32, "height": f32 }`
     *
     * Returns null if no entities exist.
     */
    getEntityBounds(): string | undefined;
    /**
     * Gets the current font size for labels.
     */
    getFontSize(): number;
    /**
     * Returns the current frames per second (rolling average over 60 frames).
     */
    getFps(): number;
    /**
     * Returns the last frame time in milliseconds.
     */
    getFrameTimeMs(): number;
    /**
     * Calculates the required canvas dimensions to render the full map at a readable zoom level.
     *
     * # Arguments
     *
     * * `min_label_font_size` - Minimum font size for labels to be readable (default: 10.0)
     *
     * Returns: `{ "width": u32, "height": u32, "zoom": f32, "centerX": f32, "centerY": f32 }`
     *
     * Returns null if no entities exist.
     */
    getFullMapDimensions(min_label_font_size: number): string | undefined;
    /**
     * Returns the type of renderer being used ("webgl2" or "software").
     */
    getRendererType(): string;
    /**
     * Gets whether labels are being shown.
     */
    getShowLabels(): boolean;
    /**
     * Gets the current playback speed.
     */
    getSpeed(): number;
    /**
     * Returns the total number of entities in the scene.
     */
    getTotalEntities(): number;
    /**
     * Returns the total number of files in the scene.
     */
    getTotalFiles(): number;
    /**
     * Returns the total number of frames rendered since initialization.
     * Note: Returns f64 instead of u64 to avoid `BigInt` conversion issues in JavaScript.
     */
    getTotalFrames(): number;
    /**
     * Returns the total number of users in the scene.
     */
    getTotalUsers(): number;
    /**
     * Returns the uptime in seconds since initialization.
     */
    getUptime(): number;
    /**
     * Returns the number of visible directories currently being rendered.
     */
    getVisibleDirectories(): number;
    /**
     * Returns the number of visible files currently being rendered.
     */
    getVisibleFiles(): number;
    /**
     * Returns the number of visible users currently being rendered.
     */
    getVisibleUsers(): number;
    /**
     * Returns the current zoom level.
     */
    getZoom(): number;
    /**
     * Returns true if the WebGL context is lost.
     *
     * This can happen when the GPU is reset, the browser tab is backgrounded
     * for a long time, or system resources are exhausted. When the context is
     * lost, rendering operations are skipped automatically.
     *
     * Software renderer always returns false (it never loses context).
     */
    isContextLost(): boolean;
    /**
     * Returns whether playback is active.
     */
    isPlaying(): boolean;
    /**
     * Returns true if using WebGL2 renderer.
     */
    isWebGL2(): boolean;
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
     */
    loadCustomLog(log: string): number;
    /**
     * Loads commits from git log format.
     *
     * Expected format is `git log --pretty=format:... --name-status`
     */
    loadGitLog(log: string): number;
    /**
     * Creates a new Rource instance attached to a canvas element.
     *
     * Automatically tries WebGL2 first, falling back to software rendering if unavailable.
     *
     * # Arguments
     *
     * * `canvas` - The HTML canvas element to render to
     */
    constructor(canvas: HTMLCanvasElement);
    /**
     * Handles keyboard events.
     */
    onKeyDown(key: string): void;
    /**
     * Handles mouse down events.
     *
     * Checks for entity under cursor first. If an entity is found, starts dragging it.
     * Otherwise, starts camera panning.
     */
    onMouseDown(x: number, y: number): void;
    /**
     * Handles mouse move events.
     *
     * If dragging an entity, updates its position and applies force-directed
     * movement to connected entities. Otherwise, pans the camera.
     */
    onMouseMove(x: number, y: number): void;
    /**
     * Handles mouse up events.
     */
    onMouseUp(): void;
    /**
     * Handles mouse wheel events for zooming toward the mouse position.
     *
     * Uses a smooth, proportional zoom based on scroll amount.
     * Zooms toward the mouse position so the content under the cursor stays in place.
     */
    onWheel(delta_y: number, mouse_x: number, mouse_y: number): void;
    /**
     * Pans the camera by the given delta in screen pixels.
     */
    pan(dx: number, dy: number): void;
    /**
     * Pauses playback.
     */
    pause(): void;
    /**
     * Starts playback.
     */
    play(): void;
    /**
     * Prepares the renderer for full map export by setting up camera and viewport.
     *
     * # Arguments
     *
     * * `width` - Target canvas width
     * * `height` - Target canvas height
     * * `zoom` - Zoom level to use
     * * `center_x` - World X coordinate to center on
     * * `center_y` - World Y coordinate to center on
     *
     * Call this before resizing canvas and calling `forceRender()`.
     */
    prepareFullMapExport(width: number, height: number, zoom: number, center_x: number, center_y: number): void;
    /**
     * Attempts to recover from a lost WebGL context.
     *
     * Returns true if recovery was successful or if context was not lost.
     * Returns false if recovery failed (e.g., WebGL is permanently unavailable).
     *
     * After a successful recovery, the visualization will continue from where
     * it left off on the next frame.
     */
    recoverContext(): boolean;
    /**
     * Resets the camera to fit all content.
     */
    resetCamera(): void;
    /**
     * Resizes the canvas and renderer.
     */
    resize(width: number, height: number): void;
    /**
     * Restores the renderer after full map export.
     *
     * # Arguments
     *
     * * `width` - Original canvas width
     * * `height` - Original canvas height
     */
    restoreAfterExport(width: number, height: number): void;
    /**
     * Restores camera state from previously saved values.
     */
    restoreCameraState(x: number, y: number, zoom: number): void;
    /**
     * Seeks to a specific commit index.
     */
    seek(commit_index: number): void;
    /**
     * Sets the background color (hex string like "#000000" or "000000").
     */
    setBackgroundColor(hex: string): void;
    /**
     * Sets whether to show bloom effect.
     */
    setBloom(enabled: boolean): void;
    /**
     * Sets the font size for labels (user names, file names, directory names).
     *
     * # Arguments
     *
     * * `size` - Font size in pixels (clamped to 4.0 - 200.0 range)
     */
    setFontSize(size: number): void;
    /**
     * Sets whether to show labels (user names, file names).
     */
    setShowLabels(show: boolean): void;
    /**
     * Sets playback speed (seconds per day of repository history).
     *
     * The speed is clamped between 1.0 (10x, fastest) and 1000.0 (very slow) seconds per day.
     * NaN, infinite, and non-positive values are replaced with the default of 10.0.
     *
     * The formula `seconds_per_commit = seconds_per_day / 10.0` means:
     * - At speed=1.0 (10x): 0.1s per commit = ~6 frames at 60fps (acceptable)
     * - At speed=0.1 (100x): 0.01s per commit = ~1.7 commits/frame (too fast!)
     */
    setSpeed(seconds_per_day: number): void;
    /**
     * Steps backward to the previous commit.
     */
    stepBackward(): void;
    /**
     * Steps forward to the next commit.
     */
    stepForward(): void;
    /**
     * Toggles play/pause state.
     */
    togglePlay(): void;
    /**
     * Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
     */
    zoom(factor: number): void;
    /**
     * Zooms the camera toward a specific screen point.
     *
     * This keeps the point under the mouse cursor stationary while zooming,
     * making it easier to zoom into specific areas of the visualization.
     */
    zoomToward(screen_x: number, screen_y: number, factor: number): void;
}

/**
 * Set up better panic messages for debugging in browser console.
 */
export function init_panic_hook(): void;

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly __wbg_rource_free: (a: number, b: number) => void;
    readonly rource_captureScreenshot: (a: number, b: number) => void;
    readonly rource_commitCount: (a: number) => number;
    readonly rource_currentCommit: (a: number) => number;
    readonly rource_forceRender: (a: number) => void;
    readonly rource_frame: (a: number, b: number) => number;
    readonly rource_getActiveActions: (a: number) => number;
    readonly rource_getAuthorColor: (a: number, b: number, c: number, d: number) => void;
    readonly rource_getAuthors: (a: number, b: number) => void;
    readonly rource_getCameraState: (a: number, b: number) => void;
    readonly rource_getCanvasHeight: (a: number) => number;
    readonly rource_getCanvasWidth: (a: number) => number;
    readonly rource_getCommitAuthor: (a: number, b: number, c: number) => void;
    readonly rource_getCommitFileCount: (a: number, b: number) => number;
    readonly rource_getCommitTimestamp: (a: number, b: number) => number;
    readonly rource_getDateRange: (a: number, b: number) => void;
    readonly rource_getDrawCalls: (a: number) => number;
    readonly rource_getEntityBounds: (a: number, b: number) => void;
    readonly rource_getFontSize: (a: number) => number;
    readonly rource_getFps: (a: number) => number;
    readonly rource_getFrameTimeMs: (a: number) => number;
    readonly rource_getFullMapDimensions: (a: number, b: number, c: number) => void;
    readonly rource_getRendererType: (a: number, b: number) => void;
    readonly rource_getShowLabels: (a: number) => number;
    readonly rource_getSpeed: (a: number) => number;
    readonly rource_getTotalEntities: (a: number) => number;
    readonly rource_getTotalFiles: (a: number) => number;
    readonly rource_getTotalFrames: (a: number) => number;
    readonly rource_getTotalUsers: (a: number) => number;
    readonly rource_getUptime: (a: number) => number;
    readonly rource_getVisibleDirectories: (a: number) => number;
    readonly rource_getVisibleFiles: (a: number) => number;
    readonly rource_getVisibleUsers: (a: number) => number;
    readonly rource_getZoom: (a: number) => number;
    readonly rource_isContextLost: (a: number) => number;
    readonly rource_isPlaying: (a: number) => number;
    readonly rource_isWebGL2: (a: number) => number;
    readonly rource_loadCustomLog: (a: number, b: number, c: number, d: number) => void;
    readonly rource_loadGitLog: (a: number, b: number, c: number, d: number) => void;
    readonly rource_new: (a: number, b: number) => void;
    readonly rource_onKeyDown: (a: number, b: number, c: number) => void;
    readonly rource_onMouseDown: (a: number, b: number, c: number) => void;
    readonly rource_onMouseMove: (a: number, b: number, c: number) => void;
    readonly rource_onMouseUp: (a: number) => void;
    readonly rource_onWheel: (a: number, b: number, c: number, d: number) => void;
    readonly rource_pan: (a: number, b: number, c: number) => void;
    readonly rource_pause: (a: number) => void;
    readonly rource_play: (a: number) => void;
    readonly rource_prepareFullMapExport: (a: number, b: number, c: number, d: number, e: number, f: number) => void;
    readonly rource_recoverContext: (a: number) => number;
    readonly rource_resetCamera: (a: number) => void;
    readonly rource_resize: (a: number, b: number, c: number) => void;
    readonly rource_restoreAfterExport: (a: number, b: number, c: number) => void;
    readonly rource_restoreCameraState: (a: number, b: number, c: number, d: number) => void;
    readonly rource_seek: (a: number, b: number) => void;
    readonly rource_setBackgroundColor: (a: number, b: number, c: number) => void;
    readonly rource_setBloom: (a: number, b: number) => void;
    readonly rource_setFontSize: (a: number, b: number) => void;
    readonly rource_setShowLabels: (a: number, b: number) => void;
    readonly rource_setSpeed: (a: number, b: number) => void;
    readonly rource_stepBackward: (a: number) => void;
    readonly rource_stepForward: (a: number) => void;
    readonly rource_togglePlay: (a: number) => void;
    readonly rource_zoom: (a: number, b: number) => void;
    readonly rource_zoomToward: (a: number, b: number, c: number, d: number) => void;
    readonly init_panic_hook: () => void;
    readonly __wbindgen_export: (a: number, b: number) => number;
    readonly __wbindgen_export2: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_export3: (a: number, b: number, c: number) => void;
    readonly __wbindgen_export4: (a: number) => void;
    readonly __wbindgen_add_to_stack_pointer: (a: number) => number;
    readonly __wbindgen_start: () => void;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
 * Instantiates the given `module`, which can either be bytes or
 * a precompiled `WebAssembly.Module`.
 *
 * @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
 *
 * @returns {InitOutput}
 */
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
