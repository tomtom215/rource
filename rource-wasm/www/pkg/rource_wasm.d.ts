/* tslint:disable */
/* eslint-disable */

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
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Captures a screenshot and returns it as PNG data.
     *
     * Only works with software renderer. WebGL2/wgpu renderers don't support
     * direct pixel readback from JavaScript.
     *
     * # Returns
     * PNG file data as a byte vector, or error message.
     */
    captureScreenshot(): Uint8Array;
    /**
     * Returns the number of loaded commits.
     */
    commitCount(): number;
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
     */
    configureLayoutForRepo(file_count: number, max_depth: number, dir_count: number): void;
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
     */
    static create(canvas: HTMLCanvasElement): Promise<Rource>;
    /**
     * Returns the current commit index.
     */
    currentCommit(): number;
    /**
     * Forces a render without updating simulation.
     */
    forceRender(): void;
    /**
     * Updates and renders a single frame.
     *
     * Returns true if there are more frames to render.
     */
    frame(timestamp: number): boolean;
    /**
     * Returns the number of active action beams.
     */
    getActiveActions(): number;
    /**
     * Returns the color for a given author name as a hex string.
     *
     * Colors are deterministically generated from the author name,
     * so the same name always produces the same color.
     *
     * # Returns
     * Hex color string like "#e94560"
     */
    getAuthorColor(name: string): string;
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
     */
    getAuthors(): string;
    /**
     * Returns the current camera state as JSON.
     *
     * Returns `{"x": <f32>, "y": <f32>, "zoom": <f32>}`
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
     */
    getCommitAuthor(index: number): string;
    /**
     * Returns the total number of unique directories across all loaded commits.
     *
     * This calculates directory count from file paths, independent of
     * playback state. Useful for displaying total stats before playback
     * reaches the end.
     */
    getCommitDirectoryCount(): number;
    /**
     * Returns the number of files changed in a commit at the given index.
     */
    getCommitFileCount(index: number): number;
    /**
     * Returns the timestamp for a commit at the given index.
     */
    getCommitTimestamp(index: number): number;
    /**
     * Returns the date range of all commits as a JSON object.
     *
     * Returns `{"startTimestamp": <unix_ts>, "endTimestamp": <unix_ts>}` or null
     * if no commits are loaded.
     */
    getDateRange(): string | undefined;
    /**
     * Returns the estimated draw call count for the current frame.
     */
    getDrawCalls(): number;
    /**
     * Returns the bounding box of all entities as JSON.
     *
     * Returns `{"minX", "minY", "maxX", "maxY", "width", "height"}` or null
     * if no entities exist.
     */
    getEntityBounds(): string | undefined;
    /**
     * Gets the current font size for labels.
     */
    getFontSize(): number;
    /**
     * Returns the current frames per second.
     */
    getFps(): number;
    /**
     * Returns the last frame time in milliseconds.
     */
    getFrameTimeMs(): number;
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
     */
    getFullMapDimensions(min_label_font_size: number): string | undefined;
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
     */
    getLayoutConfig(): string;
    /**
     * Returns the type of renderer being used ("wgpu", "webgl2", or "software").
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
     * Returns the total number of directories currently in the scene.
     *
     * Note: This only includes directories that have been created so far
     * during playback. For total directories across all commits, use
     * `getCommitDirectoryCount()`.
     */
    getTotalDirectories(): number;
    /**
     * Returns the total number of entities (files + users + dirs + actions).
     */
    getTotalEntities(): number;
    /**
     * Returns the total number of files in the scene.
     */
    getTotalFiles(): number;
    /**
     * Returns the total number of frames rendered.
     */
    getTotalFrames(): number;
    /**
     * Returns the total number of users in the scene.
     */
    getTotalUsers(): number;
    /**
     * Returns the uptime in seconds.
     */
    getUptime(): number;
    /**
     * Returns the number of visible directories (in current viewport).
     */
    getVisibleDirectories(): number;
    /**
     * Returns the number of visible files (in current viewport).
     */
    getVisibleFiles(): number;
    /**
     * Returns the number of visible users (in current viewport).
     */
    getVisibleUsers(): number;
    /**
     * Returns the current zoom level.
     */
    getZoom(): number;
    /**
     * Returns true if the GPU context is lost.
     */
    isContextLost(): boolean;
    /**
     * Returns true if using a GPU-accelerated renderer (wgpu or WebGL2).
     */
    isGPUAccelerated(): boolean;
    /**
     * Returns whether playback is active.
     */
    isPlaying(): boolean;
    /**
     * Returns true if using WebGL2 renderer.
     */
    isWebGL2(): boolean;
    /**
     * Returns true if using wgpu (WebGPU) renderer.
     */
    isWgpu(): boolean;
    /**
     * Loads commits from custom pipe-delimited format.
     *
     * Format: `timestamp|author|action|path` per line
     *
     * Uses lenient parsing by default to skip invalid lines (e.g., lines with
     * pipe characters in author names or unsupported git statuses).
     */
    loadCustomLog(log: string): number;
    /**
     * Loads commits from git log format.
     *
     * Uses lenient parsing to handle malformed lines gracefully.
     */
    loadGitLog(log: string): number;
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
     */
    onKeyDown(key: string): void;
    /**
     * Handles mouse down events.
     *
     * Initiates entity dragging if an entity is clicked, otherwise starts
     * camera panning mode.
     */
    onMouseDown(x: number, y: number): void;
    /**
     * Handles mouse move events.
     *
     * Updates entity position if dragging, or pans camera if no entity is selected.
     */
    onMouseMove(x: number, y: number): void;
    /**
     * Handles mouse up events.
     *
     * Releases any dragged entity and resets drag state.
     */
    onMouseUp(): void;
    /**
     * Handles mouse wheel events for zooming.
     *
     * Zooms toward the mouse cursor position for intuitive navigation.
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
     */
    prepareFullMapExport(width: number, height: number, zoom: number, center_x: number, center_y: number): void;
    /**
     * Attempts to recover from a lost GPU context.
     */
    recoverContext(): boolean;
    /**
     * Resets the camera to fit all content.
     */
    resetCamera(): void;
    /**
     * Resizes the canvas and renderer.
     *
     * Should be called when the canvas element size changes.
     */
    resize(width: number, height: number): void;
    /**
     * Restores the renderer after full map export.
     *
     * Resizes canvas back to normal dimensions and fits camera to content.
     *
     * # Arguments
     * * `width` - Original canvas width
     * * `height` - Original canvas height
     */
    restoreAfterExport(width: number, height: number): void;
    /**
     * Restores camera state from previously saved values.
     *
     * Use with `getCameraState()` to save/restore view positions.
     */
    restoreCameraState(x: number, y: number, zoom: number): void;
    /**
     * Seeks to a specific commit index.
     *
     * This rebuilds the scene state by replaying all commits up to the
     * specified index, then pre-warms the physics simulation.
     */
    seek(commit_index: number): void;
    /**
     * Sets the background color (hex string like "#000000" or "000000").
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setBackgroundColor("#1a1a2e");
     * ```
     */
    setBackgroundColor(hex: string): void;
    /**
     * Sets whether to show bloom effect.
     *
     * Bloom creates a glow around bright elements.
     */
    setBloom(enabled: boolean): void;
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
     */
    setBranchDepthFade(fade: number): void;
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
     */
    setBranchOpacityMax(opacity: number): void;
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
     */
    setDepthDistanceExponent(exponent: number): void;
    /**
     * Sets the font size for labels.
     *
     * Range: [4.0, 200.0]
     */
    setFontSize(size: number): void;
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
     */
    setLayoutPreset(preset: string): void;
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
     */
    setRadialDistanceScale(scale: number): void;
    /**
     * Sets whether to show labels (user names, file names, directory names).
     */
    setShowLabels(show: boolean): void;
    /**
     * Sets playback speed (seconds per day of repository history).
     *
     * Lower values = faster playback. Default is 10.0.
     * Range: [0.01, 1000.0]
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
     *
     * Max zoom is 1000.0 to support deep zoom into massive repositories.
     */
    zoom(factor: number): void;
    /**
     * Zooms the camera toward a specific screen point.
     *
     * This provides intuitive zoom behavior where the point under the cursor
     * stays fixed during zoom operations.
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
    readonly rource_configureLayoutForRepo: (a: number, b: number, c: number, d: number) => void;
    readonly rource_create: (a: number) => number;
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
    readonly rource_getCommitDirectoryCount: (a: number) => number;
    readonly rource_getCommitFileCount: (a: number, b: number) => number;
    readonly rource_getCommitTimestamp: (a: number, b: number) => number;
    readonly rource_getDateRange: (a: number, b: number) => void;
    readonly rource_getDrawCalls: (a: number) => number;
    readonly rource_getEntityBounds: (a: number, b: number) => void;
    readonly rource_getFontSize: (a: number) => number;
    readonly rource_getFps: (a: number) => number;
    readonly rource_getFrameTimeMs: (a: number) => number;
    readonly rource_getFullMapDimensions: (a: number, b: number, c: number) => void;
    readonly rource_getLayoutConfig: (a: number, b: number) => void;
    readonly rource_getRendererType: (a: number, b: number) => void;
    readonly rource_getShowLabels: (a: number) => number;
    readonly rource_getSpeed: (a: number) => number;
    readonly rource_getTotalDirectories: (a: number) => number;
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
    readonly rource_isGPUAccelerated: (a: number) => number;
    readonly rource_isPlaying: (a: number) => number;
    readonly rource_isWebGL2: (a: number) => number;
    readonly rource_isWgpu: (a: number) => number;
    readonly rource_loadCustomLog: (a: number, b: number, c: number, d: number) => void;
    readonly rource_loadGitLog: (a: number, b: number, c: number, d: number) => void;
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
    readonly rource_setBranchDepthFade: (a: number, b: number) => void;
    readonly rource_setBranchOpacityMax: (a: number, b: number) => void;
    readonly rource_setDepthDistanceExponent: (a: number, b: number) => void;
    readonly rource_setFontSize: (a: number, b: number) => void;
    readonly rource_setLayoutPreset: (a: number, b: number, c: number) => void;
    readonly rource_setRadialDistanceScale: (a: number, b: number) => void;
    readonly rource_setShowLabels: (a: number, b: number) => void;
    readonly rource_setSpeed: (a: number, b: number) => void;
    readonly rource_stepBackward: (a: number) => void;
    readonly rource_stepForward: (a: number) => void;
    readonly rource_togglePlay: (a: number) => void;
    readonly rource_zoom: (a: number, b: number) => void;
    readonly rource_zoomToward: (a: number, b: number, c: number, d: number) => void;
    readonly init_panic_hook: () => void;
    readonly __wasm_bindgen_func_elem_6182: (a: number, b: number) => void;
    readonly __wasm_bindgen_func_elem_6237: (a: number, b: number, c: number, d: number) => void;
    readonly __wasm_bindgen_func_elem_6183: (a: number, b: number, c: number) => void;
    readonly __wbindgen_export: (a: number, b: number) => number;
    readonly __wbindgen_export2: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_export3: (a: number) => void;
    readonly __wbindgen_export4: (a: number, b: number, c: number) => void;
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
