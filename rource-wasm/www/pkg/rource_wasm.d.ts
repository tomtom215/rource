/* tslint:disable */
/* eslint-disable */

export class Rource {
  free(): void;
  [Symbol.dispose](): void;
  /**
   * Returns the uptime in seconds since initialization.
   */
  getUptime(): number;
  /**
   * Returns whether playback is active.
   */
  isPlaying(): boolean;
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
   * Handles keyboard events.
   */
  onKeyDown(key: string): void;
  /**
   * Handles mouse up events.
   */
  onMouseUp(): void;
  /**
   * Toggles play/pause state.
   */
  togglePlay(): void;
  /**
   * Returns the number of loaded commits.
   */
  commitCount(): number;
  /**
   * Forces a render without updating simulation (useful for static views).
   */
  forceRender(): void;
  /**
   * Loads commits from git log format.
   *
   * Expected format is `git log --pretty=format:... --name-status`
   */
  loadGitLog(log: string): number;
  /**
   * Resets the camera to fit all content.
   */
  resetCamera(): void;
  /**
   * Steps forward to the next commit.
   */
  stepForward(): void;
  /**
   * Handles mouse down events.
   */
  onMouseDown(x: number, y: number): void;
  /**
   * Handles mouse move events.
   */
  onMouseMove(x: number, y: number): void;
  /**
   * Steps backward to the previous commit.
   */
  stepBackward(): void;
  /**
   * Returns the current commit index.
   */
  currentCommit(): number;
  /**
   * Returns the estimated draw call count for the last frame.
   */
  getDrawCalls(): number;
  /**
   * Gets whether labels are being shown.
   */
  getShowLabels(): boolean;
  /**
   * Returns the total number of files in the scene.
   */
  getTotalFiles(): number;
  /**
   * Returns the total number of users in the scene.
   */
  getTotalUsers(): number;
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
   * Sets whether to show labels (user names, file names).
   */
  setShowLabels(show: boolean): void;
  /**
   * Returns the color for a given author name as a hex string (e.g., "#ff5500").
   *
   * This uses the same deterministic color generation as the visualization,
   * so colors will match what's displayed on screen.
   */
  getAuthorColor(name: string): string;
  /**
   * Returns the canvas width in pixels.
   */
  getCanvasWidth(): number;
  /**
   * Returns the total number of frames rendered since initialization.
   */
  getTotalFrames(): bigint;
  /**
   * Returns the canvas height in pixels.
   */
  getCanvasHeight(): number;
  /**
   * Returns the last frame time in milliseconds.
   */
  getFrameTimeMs(): number;
  /**
   * Returns the type of renderer being used ("webgl2" or "software").
   */
  getRendererType(): string;
  /**
   * Returns the number of visible files currently being rendered.
   */
  getVisibleFiles(): number;
  /**
   * Returns the number of visible users currently being rendered.
   */
  getVisibleUsers(): number;
  /**
   * Captures a screenshot and returns it as PNG data (`Uint8Array`).
   *
   * Note: This only works with the software renderer. For WebGL2, returns an error.
   */
  captureScreenshot(): Uint8Array;
  /**
   * Returns the number of active action beams.
   */
  getActiveActions(): number;
  /**
   * Returns the total number of entities in the scene.
   */
  getTotalEntities(): number;
  /**
   * Sets the background color (hex string like "#000000" or "000000").
   */
  setBackgroundColor(hex: string): void;
  /**
   * Returns the number of visible directories currently being rendered.
   */
  getVisibleDirectories(): number;
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
   * Pans the camera by the given delta in screen pixels.
   */
  pan(dx: number, dy: number): void;
  /**
   * Starts playback.
   */
  play(): void;
  /**
   * Seeks to a specific commit index.
   */
  seek(commit_index: number): void;
  /**
   * Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
   */
  zoom(factor: number): void;
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
   * Pauses playback.
   */
  pause(): void;
  /**
   * Resizes the canvas and renderer.
   */
  resize(width: number, height: number): void;
  /**
   * Returns the current frames per second (rolling average over 60 frames).
   */
  getFps(): number;
  /**
   * Returns the current zoom level.
   */
  getZoom(): number;
  /**
   * Handles mouse wheel events for zooming.
   *
   * Uses a smooth, proportional zoom based on scroll amount.
   */
  onWheel(delta_y: number): void;
  /**
   * Gets the current playback speed.
   */
  getSpeed(): number;
  /**
   * Returns true if using WebGL2 renderer.
   */
  isWebGL2(): boolean;
  /**
   * Sets whether to show bloom effect.
   */
  setBloom(enabled: boolean): void;
  /**
   * Sets playback speed (seconds per day of repository history).
   */
  setSpeed(seconds_per_day: number): void;
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
  readonly rource_getCanvasHeight: (a: number) => number;
  readonly rource_getCanvasWidth: (a: number) => number;
  readonly rource_getDrawCalls: (a: number) => number;
  readonly rource_getFps: (a: number) => number;
  readonly rource_getFrameTimeMs: (a: number) => number;
  readonly rource_getRendererType: (a: number, b: number) => void;
  readonly rource_getShowLabels: (a: number) => number;
  readonly rource_getSpeed: (a: number) => number;
  readonly rource_getTotalEntities: (a: number) => number;
  readonly rource_getTotalFiles: (a: number) => number;
  readonly rource_getTotalFrames: (a: number) => bigint;
  readonly rource_getTotalUsers: (a: number) => number;
  readonly rource_getUptime: (a: number) => number;
  readonly rource_getVisibleDirectories: (a: number) => number;
  readonly rource_getVisibleFiles: (a: number) => number;
  readonly rource_getVisibleUsers: (a: number) => number;
  readonly rource_getZoom: (a: number) => number;
  readonly rource_isPlaying: (a: number) => number;
  readonly rource_isWebGL2: (a: number) => number;
  readonly rource_loadCustomLog: (a: number, b: number, c: number, d: number) => void;
  readonly rource_loadGitLog: (a: number, b: number, c: number, d: number) => void;
  readonly rource_new: (a: number, b: number) => void;
  readonly rource_onKeyDown: (a: number, b: number, c: number) => void;
  readonly rource_onMouseDown: (a: number, b: number, c: number) => void;
  readonly rource_onMouseMove: (a: number, b: number, c: number) => void;
  readonly rource_onMouseUp: (a: number) => void;
  readonly rource_onWheel: (a: number, b: number) => void;
  readonly rource_pan: (a: number, b: number, c: number) => void;
  readonly rource_pause: (a: number) => void;
  readonly rource_play: (a: number) => void;
  readonly rource_resetCamera: (a: number) => void;
  readonly rource_resize: (a: number, b: number, c: number) => void;
  readonly rource_seek: (a: number, b: number) => void;
  readonly rource_setBackgroundColor: (a: number, b: number, c: number) => void;
  readonly rource_setBloom: (a: number, b: number) => void;
  readonly rource_setShowLabels: (a: number, b: number) => void;
  readonly rource_setSpeed: (a: number, b: number) => void;
  readonly rource_stepBackward: (a: number) => void;
  readonly rource_stepForward: (a: number) => void;
  readonly rource_togglePlay: (a: number) => void;
  readonly rource_zoom: (a: number, b: number) => void;
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
