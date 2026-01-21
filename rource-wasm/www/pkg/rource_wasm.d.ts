/* tslint:disable */
/* eslint-disable */

/**
 * The main Rource visualization controller for browser usage.
 *
 * This struct manages the entire visualization lifecycle including:
 * - Rendering (WebGL2 or Software backend)
 * - Scene management (files, users, directories)
 * - Camera controls (pan, zoom)
 * - Playback timeline (play, pause, seek)
 * - User interaction (mouse, keyboard)
 */
export class Rource {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Captures a screenshot and returns it as PNG data.
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
     */
    getAuthorColor(name: string): string;
    /**
     * Returns author data as a JSON string array.
     * Iterates over all commits to get complete author statistics,
     * not just users currently visible in the scene.
     */
    getAuthors(): string;
    /**
     * Returns the current camera state as JSON.
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
     * This calculates directory count from file paths, independent of playback state.
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
     */
    getDateRange(): string | undefined;
    /**
     * Returns the estimated draw call count.
     */
    getDrawCalls(): number;
    /**
     * Returns the bounding box of all entities as JSON.
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
     * Returns the total number of directories currently in the scene.
     * Note: This only includes directories that have been created so far during playback.
     * For total directories across all commits, use `getCommitDirectoryCount()`.
     */
    getTotalDirectories(): number;
    /**
     * Returns the total number of entities.
     */
    getTotalEntities(): number;
    /**
     * Returns the total number of files.
     */
    getTotalFiles(): number;
    /**
     * Returns the total number of frames rendered.
     */
    getTotalFrames(): number;
    /**
     * Returns the total number of users.
     */
    getTotalUsers(): number;
    /**
     * Returns the uptime in seconds.
     */
    getUptime(): number;
    /**
     * Returns the number of visible directories.
     */
    getVisibleDirectories(): number;
    /**
     * Returns the number of visible files.
     */
    getVisibleFiles(): number;
    /**
     * Returns the number of visible users.
     */
    getVisibleUsers(): number;
    /**
     * Returns the current zoom level.
     */
    getZoom(): number;
    /**
     * Returns true if the WebGL context is lost.
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
     */
    onMouseDown(x: number, y: number): void;
    /**
     * Handles mouse move events.
     */
    onMouseMove(x: number, y: number): void;
    /**
     * Handles mouse up events.
     */
    onMouseUp(): void;
    /**
     * Handles mouse wheel events for zooming.
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
     */
    prepareFullMapExport(width: number, height: number, zoom: number, center_x: number, center_y: number): void;
    /**
     * Attempts to recover from a lost WebGL context.
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
     * Sets the branch depth fade rate.
     *
     * Higher values make deep branches fade faster (0.0-1.0).
     * Default: 0.3
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
     * Controls visibility of directory-to-parent connections (0.0-1.0).
     * Default: 0.35
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
     * Default: 1.0 (linear), Range: [0.5, 2.0]
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setDepthDistanceExponent(1.3);
     * ```
     */
    setDepthDistanceExponent(exponent: number): void;
    /**
     * Sets the font size for labels.
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
     * Higher values spread the tree outward more. Range: [40.0, 500.0]
     * Default: 80.0
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setRadialDistanceScale(160.0);
     * ```
     */
    setRadialDistanceScale(scale: number): void;
    /**
     * Sets whether to show labels.
     */
    setShowLabels(show: boolean): void;
    /**
     * Sets playback speed (seconds per day of repository history).
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
     * Max zoom increased to 1000.0 to support deep zoom into massive repositories.
     */
    zoom(factor: number): void;
    /**
     * Zooms the camera toward a specific screen point.
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
