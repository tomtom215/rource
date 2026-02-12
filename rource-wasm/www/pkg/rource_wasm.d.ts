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
     * Returns debug information about hit testing at the given coordinates.
     *
     * Use this to diagnose why drag might not be working:
     * - Check if `screen_to_world` conversion is correct
     * - Check if entities are in the spatial index
     * - Check if entities are within hit radius
     */
    debugHitTest(x: number, y: number): string;
    /**
     * Disables the watermark.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.disableWatermark();
     * ```
     */
    disableWatermark(): void;
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
    dispose(): void;
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
    enableRourceWatermark(): void;
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
     */
    errorRateExceedsThreshold(threshold_percent: number): boolean;
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
     */
    exportCacheBytes(): Uint8Array | undefined;
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
     */
    exportCacheBytesWithRepoId(repo_id: string): Uint8Array | undefined;
    /**
     * Forces a render without updating simulation.
     *
     * Guards against zero-dimension canvas (e.g., when `#viz-panel` is hidden
     * and `resizeCanvas()` hasn't run yet). WebGPU cannot create swapchain
     * textures with 0×0 dimensions, so we skip the render entirely.
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
     * Returns commit activity heatmap (day-of-week × hour-of-day grid).
     */
    getActivityHeatmap(): string | undefined;
    /**
     * Returns all per-file metrics as a JSON array.
     *
     * Each element contains the file path and its aggregated academic metrics.
     * Useful for bulk visualization (e.g., coloring all files by hotspot score).
     */
    getAllFileMetrics(): string | undefined;
    /**
     * Returns all per-user metrics as a JSON array.
     *
     * Each element contains the author name and their aggregated academic metrics.
     */
    getAllUserMetrics(): string | undefined;
    /**
     * Returns architectural drift index analysis as JSON.
     *
     * Measures divergence between directory structure and co-change clusters
     * using Normalized Mutual Information (NMI).
     *
     * # Academic Citations
     * - Garcia et al. (WICSA 2009): drift detection
     * - Maqbool & Babri (JSS 2007): hierarchical clustering comparison
     * - Raghavan et al. (Phys Rev 2007): label propagation
     */
    getArchitecturalDrift(): string | undefined;
    /**
     * Returns the error count for asset loading operations.
     *
     * Asset errors occur when loading images, fonts, or other resources.
     */
    getAssetErrorCount(): bigint;
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
     * Returns bus factor analysis per directory as JSON.
     *
     * The bus factor is the minimum number of contributors who must leave
     * before a directory becomes unmaintained. Low values (1-2) indicate
     * critical key-person risk.
     */
    getBusFactors(): string | undefined;
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
     */
    getCacheStats(): string | undefined;
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
     */
    static getCacheVersion(): number;
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
     * Returns per-file change burst detection as JSON.
     *
     * Detects rapid consecutive changes to individual files.
     * Files with many bursts are significantly more defect-prone
     * (Nagappan et al. 2010).
     */
    getChangeBursts(): string | undefined;
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
     */
    getChangeCoupling(limit?: number | null): string | undefined;
    /**
     * Returns sliding-window change entropy analysis as JSON.
     *
     * Measures Shannon entropy of file modification distribution within
     * time windows for defect risk prediction (Hassan ICSE 2009).
     */
    getChangeEntropy(): string | undefined;
    /**
     * Returns change propagation prediction as JSON.
     *
     * Predicts which files need concurrent modification based on
     * historical co-change patterns and transitive cascade analysis.
     *
     * # Academic Citations
     * - Ying et al. (MSR 2004): change propagation
     * - Hassan & Holt (ICSM 2004): predictive change coupling
     */
    getChangePropagation(): string | undefined;
    /**
     * Returns code churn volatility per file (Nagappan & Ball 2005).
     */
    getChurnVolatility(): string | undefined;
    /**
     * Returns circadian (time-of-day) risk patterns as JSON.
     *
     * Assigns risk scores based on hour-of-day and day-of-week.
     * Commits between midnight–4AM UTC are significantly buggier
     * (Eyolfson et al. 2011).
     */
    getCircadianRisk(): string | undefined;
    /**
     * Returns codebase growth trajectory as JSON.
     *
     * Tracks active file count over time, growth rate, and trend
     * classification (Lehman 1996 Laws of Software Evolution).
     */
    getCodebaseGrowth(): string | undefined;
    /**
     * Returns the author name for a commit at the given index.
     */
    getCommitAuthor(index: number): string;
    /**
     * Returns commit cadence analysis per developer as JSON.
     *
     * Analyzes inter-commit intervals to classify contributors as
     * regular, moderate, or bursty (Eyolfson et al. 2014).
     */
    getCommitCadence(): string | undefined;
    /**
     * Returns commit cohesion index analysis as JSON.
     *
     * Measures whether commits are atomic (tightly related changes) or tangled.
     *
     * # Academic Citations
     * - Herzig & Zeller (ICSE 2013): tangled commits
     * - Kirinuki et al. (SANER 2014): untangling changes
     */
    getCommitCohesion(): string | undefined;
    /**
     * Returns per-commit complexity / tangled change scores (Herzig & Zeller 2013).
     */
    getCommitComplexity(): string | undefined;
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
     */
    getCommitDirectoryCount(): number;
    /**
     * Returns the number of files changed in a commit at the given index.
     */
    getCommitFileCount(index: number): number;
    /**
     * Returns commit message entropy analysis as JSON.
     *
     * Measures the information density and quality of commit messages
     * using Shannon entropy and cross-entropy.
     *
     * # Academic Citations
     * - Dyer et al. (MSR 2013): commit message mining
     * - Hindle et al. (ICSE 2012): naturalness of code
     */
    getCommitMessageEntropy(): string | undefined;
    /**
     * Returns the timestamp for a commit at the given index.
     */
    getCommitTimestamp(index: number): number;
    /**
     * Returns the error count for configuration operations.
     *
     * Config errors occur when invalid settings are provided.
     */
    getConfigErrorCount(): bigint;
    /**
     * Returns sociotechnical congruence analysis as JSON.
     *
     * Measures alignment between who SHOULD coordinate (from technical
     * dependencies) and who ACTUALLY does (from shared files).
     * Conway's Law quantified (Cataldo et al. 2008).
     */
    getCongruence(): string | undefined;
    /**
     * Returns contextual complexity (working set size) analysis as JSON.
     *
     * For each file, computes the number of other files a developer must
     * simultaneously understand to safely modify it.
     *
     * # Academic Citations
     * - Bavota et al. (ICSM 2013): structural-semantic coupling
     * - Gall et al. (ICSE 1998): logical coupling from co-changes
     * - Denning (CACM 1968): working set model
     */
    getContextualComplexity(): string | undefined;
    /**
     * Returns contribution inequality / Gini coefficient analysis as JSON.
     *
     * Measures how unevenly commits are distributed using the Gini coefficient.
     * Includes Lorenz curve, top-K% share, and windowed trend analysis
     * (Chelkowski et al. 2016).
     */
    getContributionInequality(): string | undefined;
    /**
     * Returns the date range of all commits as a JSON object.
     *
     * Returns `{"startTimestamp": <unix_ts>, "endTimestamp": <unix_ts>}` or null
     * if no commits are loaded.
     */
    getDateRange(): string | undefined;
    /**
     * Returns defect-introducing change patterns (Kim et al. 2008).
     */
    getDefectPatterns(): string | undefined;
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
     */
    getDetailedErrorMetrics(): string;
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
     */
    getDetailedFrameStats(): string;
    /**
     * Returns developer experience scores (Mockus & Votta 2000).
     */
    getDeveloperExperience(): string | undefined;
    /**
     * Returns developer focus and file diffusion analysis as JSON.
     *
     * Measures how concentrated developers' activity is (focus) and
     * how spread out files' contributors are (diffusion).
     * More focused developers introduce fewer defects (Posnett et al. 2013).
     */
    getDeveloperFocus(): string | undefined;
    /**
     * Returns developer collaboration network analysis as JSON.
     *
     * Builds and analyzes the co-authorship network: density, components,
     * betweenness centrality, and clustering (Begel et al. 2023).
     */
    getDeveloperNetwork(): string | undefined;
    /**
     * Returns developer activity profiles as JSON.
     *
     * Classifies contributors as core, peripheral, or drive-by based
     * on commit share and recency (Mockus et al. 2002).
     */
    getDeveloperProfiles(): string | undefined;
    /**
     * Returns the estimated draw call count for the current frame.
     */
    getDrawCalls(): number;
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
     */
    getEntityAtCursor(x: number, y: number): string | undefined;
    /**
     * Returns the bounding box of all entities as JSON.
     *
     * Returns `{"minX", "minY", "maxX", "maxY", "width", "height"}` or null
     * if no entities exist.
     */
    getEntityBounds(): string | undefined;
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
     */
    getErrorMetrics(): string;
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
     */
    getErrorRate(): number;
    /**
     * Returns the number of registered file icon types.
     *
     * # Example (JavaScript)
     * ```javascript
     * const count = rource.getFileIconCount();
     * console.log(`${count} file types registered`);
     * ```
     */
    getFileIconCount(): number;
    /**
     * Returns file lifecycle analysis as JSON.
     *
     * Tracks file creation, modification, and deletion patterns to
     * identify ephemeral, dead, and actively maintained files
     * (Godfrey & Tu 2000, Gall et al. 1998).
     */
    getFileLifecycles(): string | undefined;
    /**
     * Returns aggregated academic metrics for a specific file as JSON.
     *
     * Performs O(1) lookup from the cached insights index (computed at load time).
     * Returns `null` if no commits are loaded or the file is not found.
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
     */
    getFileMetrics(path: string): string | undefined;
    /**
     * Returns file survival analysis (Kaplan-Meier estimator) as JSON.
     *
     * Estimates how long files survive before deletion using the
     * gold-standard survival analysis technique from biostatistics
     * (Cito et al. 2021).
     */
    getFileSurvival(): string | undefined;
    /**
     * Gets the current font size for labels.
     */
    getFontSize(): number;
    /**
     * Returns the current frames per second.
     */
    getFps(): number;
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
     */
    getFrameStats(): string;
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
     */
    getGPUCullingStats(): string | undefined;
    /**
     * Returns the current GPU culling threshold.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU culling threshold:', rource.getGPUCullingThreshold());
     * ```
     */
    getGPUCullingThreshold(): number;
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
     */
    getGPUInfo(): string | undefined;
    /**
     * Returns the current GPU physics threshold.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU physics threshold:', rource.getGPUPhysicsThreshold());
     * ```
     */
    getGPUPhysicsThreshold(): number;
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
     */
    getHotspots(limit?: number | null): string | undefined;
    /**
     * Returns comprehensive repository insights as JSON from the cached report.
     *
     * Includes research-backed metrics:
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
     * Report is cached at load time (Phase 89). This method only serializes.
     */
    getInsights(): string | undefined;
    /**
     * Returns the complete insights index summary as JSON.
     *
     * Contains aggregate counts: total files, total users, knowledge silos,
     * contributor profile distribution, max hotspot score.
     */
    getInsightsIndexSummary(): string | undefined;
    /**
     * Returns a summary of repository health metrics as JSON.
     *
     * Quick overview suitable for dashboard display:
     * - Total commits, files, authors
     * - Time span
     * - Average commit entropy (change scatter)
     * - Top 5 hotspots
     * - Lowest bus factors
     */
    getInsightsSummary(): string | undefined;
    /**
     * Returns the error count for I/O operations.
     *
     * I/O errors occur during file reads or network operations.
     */
    getIoErrorCount(): bigint;
    /**
     * Returns per-directory knowledge distribution entropy (Constantinou & Mens 2017).
     */
    getKnowledgeDistribution(): string | undefined;
    /**
     * Returns knowledge half-life analysis as JSON.
     *
     * Models exponential knowledge decay with per-file adaptive decay rates.
     *
     * # Academic Citations
     * - Fritz et al. (ICSE 2010): degree-of-knowledge model
     * - Robillard et al. (IEEE Software 2014): developer memory
     * - Ebbinghaus (1885): forgetting curve
     */
    getKnowledgeHalfLife(): string | undefined;
    /**
     * Returns knowledge map and silo analysis as JSON.
     *
     * Computes Shannon entropy of ownership distribution per file to
     * identify knowledge silos (Rigby & Bird 2013, Fritz et al. 2014).
     */
    getKnowledgeMap(): string | undefined;
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
     * Returns the current maximum commits limit.
     */
    getMaxCommits(): number;
    /**
     * Returns co-change modularity / DSM analysis as JSON.
     *
     * Measures whether co-changing files respect directory boundaries.
     * High cross-module coupling indicates architectural erosion
     * (Silva et al. 2014).
     */
    getModularity(): string | undefined;
    /**
     * Gets the current mouse position in screen coordinates.
     *
     * Returns an array `[x, y]` of the last known mouse position.
     */
    getMousePosition(): Float32Array;
    /**
     * Gets the current mouse position in world coordinates.
     *
     * Returns an array `[x, y]` of the mouse position in world space.
     */
    getMouseWorldPosition(): Float32Array;
    /**
     * Returns the original commit count before any truncation.
     *
     * This is useful for displaying "Showing X of Y commits" in the UI.
     */
    getOriginalCommitCount(): number;
    /**
     * Returns per-file ownership fragmentation / Gini (Bird et al. 2011).
     */
    getOwnershipFragmentation(): string | undefined;
    /**
     * Returns the error count for parse operations.
     *
     * Parse errors occur when loading git logs or custom log formats
     * with invalid or malformed content.
     */
    getParseErrorCount(): bigint;
    /**
     * Returns the parse error rate as a percentage (0.0-100.0).
     *
     * Parse errors should be below 0.5% for healthy operation.
     */
    getParseErrorRate(): number;
    /**
     * Returns release rhythm analysis (Khomh et al. 2012).
     */
    getReleaseRhythm(): string | undefined;
    /**
     * Returns the error count for render operations.
     *
     * Render errors occur during frame rendering, such as buffer allocation
     * failures or texture upload issues.
     */
    getRenderErrorCount(): bigint;
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
     * Returns the length of the stats buffer (number of `f32` elements).
     */
    getStatsBufferLen(): number;
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
     */
    getStatsBufferPtr(): number;
    /**
     * Returns succession readiness analysis as JSON.
     *
     * For each file, scores how prepared the team is for the primary
     * contributor to become unavailable.
     *
     * # Academic Citations
     * - Ricca et al. (JSS 2011): developer succession
     * - Rigby & Bird (FSE 2013): knowledge distribution
     */
    getSuccessionReadiness(): string | undefined;
    /**
     * Returns language/technology distribution by file extension.
     */
    getTechDistribution(): string | undefined;
    /**
     * Returns developer technology expertise profiles.
     */
    getTechExpertise(): string | undefined;
    /**
     * Returns temporal activity patterns as JSON.
     *
     * Includes:
     * - Activity heatmap (7 days x 24 hours)
     * - Peak activity times
     * - Change burst detection
     * - Average files per commit during/outside bursts
     */
    getTemporalPatterns(): string | undefined;
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
     * Returns the total number of errors recorded across all categories.
     *
     * # Example
     *
     * ```javascript
     * const totalErrors = rource.getTotalErrors();
     * console.log(`Total errors: ${totalErrors}`);
     * ```
     */
    getTotalErrors(): bigint;
    /**
     * Returns the total number of files in the scene.
     */
    getTotalFiles(): number;
    /**
     * Returns the total number of frames rendered.
     */
    getTotalFrames(): number;
    /**
     * Returns the total number of operations recorded across all categories.
     *
     * This is the denominator for error rate calculations.
     */
    getTotalOperations(): bigint;
    /**
     * Returns the total number of users in the scene.
     */
    getTotalUsers(): number;
    /**
     * Returns enhanced truck factor via DOA model (Avelino et al. 2016).
     */
    getTruckFactor(): string | undefined;
    /**
     * Returns developer turnover impact analysis (Mockus 2009).
     */
    getTurnoverImpact(): string | undefined;
    /**
     * Returns the uptime in seconds.
     */
    getUptime(): number;
    /**
     * Returns aggregated academic metrics for a specific developer as JSON.
     *
     * Performs O(1) lookup from the cached insights index (computed at load time).
     * Returns `null` if no commits are loaded or the author is not found.
     *
     * # Academic Citations
     *
     * The returned metrics aggregate findings from:
     * - Mockus et al. (TSE 2002): developer profiles (core/peripheral)
     * - Eyolfson et al. (MSR 2014): commit cadence
     * - Meneely & Williams (FSE 2009): network centrality
     * - Posnett et al. (ICSE 2013): developer focus
     */
    getUserMetrics(author: string): string | undefined;
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
     * Returns a reference to the WASM linear memory.
     *
     * JS needs this to construct a `Float32Array` view over the stats buffer.
     * The `ArrayBuffer` backing this memory may be detached if WASM memory
     * grows; JS code must handle this by recreating the view.
     */
    getWasmMemory(): any;
    /**
     * Gets the current watermark opacity.
     */
    getWatermarkOpacity(): number;
    /**
     * Returns the error count for WebGL/wgpu operations.
     *
     * WebGL errors include shader compilation failures, context lost events,
     * and program linking issues.
     */
    getWebGlErrorCount(): bigint;
    /**
     * Returns work-type mix analysis as JSON.
     *
     * Classifies commits by Create/Modify/Delete ratio to reveal whether
     * the team is building features, maintaining code, or cleaning up
     * (Hindle et al. 2008, Mockus & Votta 2000).
     */
    getWorkTypeMix(): string | undefined;
    /**
     * Returns the current zoom level.
     */
    getZoom(): number;
    /**
     * Returns debug information about zoom and entity visibility.
     *
     * Returns JSON with zoom level, entity radii, and screen radii to help
     * diagnose visibility issues.
     */
    getZoomDebugInfo(): string;
    /**
     * Returns whether file icons are initialized.
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.hasFileIcons()) {
     *     console.log('File icons ready');
     * }
     * ```
     */
    hasFileIcons(): boolean;
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
     */
    static hasValidCacheMagic(bytes: Uint8Array): boolean;
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
     */
    static hashRepoId(repo_id: string): string;
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
     */
    importCacheBytes(bytes: Uint8Array): number;
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
     */
    importCacheBytesWithRepoId(bytes: Uint8Array, repo_id: string): number;
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
     */
    initFileIcons(): boolean;
    /**
     * Returns whether auto-fit mode is currently enabled.
     */
    isAutoFit(): boolean;
    /**
     * Returns true if the GPU context is lost.
     */
    isContextLost(): boolean;
    /**
     * Returns true if using a GPU-accelerated renderer (wgpu or WebGL2).
     */
    isGPUAccelerated(): boolean;
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
     */
    isGPUCullingActive(): boolean;
    /**
     * Returns whether GPU visibility culling is currently enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU culling:', rource.isGPUCullingEnabled());
     * ```
     */
    isGPUCullingEnabled(): boolean;
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
     */
    isGPUPhysicsActive(): boolean;
    /**
     * Returns whether GPU physics is currently enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * console.log('GPU physics:', rource.isGPUPhysicsEnabled());
     * ```
     */
    isGPUPhysicsEnabled(): boolean;
    /**
     * Returns whether playback is active.
     */
    isPlaying(): boolean;
    /**
     * Returns true if the `profiling` feature is enabled.
     *
     * When true, Performance API marks are added to frames for Chrome `DevTools`.
     */
    isProfilingEnabled(): boolean;
    /**
     * Returns true if the `tracing` feature is enabled.
     *
     * When true, Rust tracing spans are routed to browser console.
     */
    isTracingEnabled(): boolean;
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
     */
    isVsyncEnabled(): boolean;
    /**
     * Returns whether the watermark is enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * if (rource.isWatermarkEnabled()) {
     *     console.log('Watermark is visible');
     * }
     * ```
     */
    isWatermarkEnabled(): boolean;
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
     *
     * # Commit Limit
     *
     * If the log contains more commits than `maxCommits` (default 100,000),
     * only the first `maxCommits` commits are loaded. Check `wasCommitsTruncated()`
     * to detect if truncation occurred.
     */
    loadCustomLog(log: string): number;
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
     * Disables auto-fit when user manually pans.
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
     */
    registerFileIcon(extension: string, hex_color: string): boolean;
    /**
     * Resets the camera to fit all content.
     */
    resetCamera(): void;
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
    resetErrorMetrics(): void;
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
     *
     * # Performance Warning
     *
     * For large repositories, seeking to a distant commit (e.g., commit 50,000
     * in a 100K commit repo) will apply all previous commits synchronously,
     * which may cause brief UI freezing. Consider using incremental playback
     * for very large repositories.
     */
    seek(commit_index: number): void;
    /**
     * Enables or disables auto-fit mode.
     *
     * When enabled, the camera automatically zooms out to keep all content visible
     * as the visualization grows. Manual zoom/pan operations disable auto-fit.
     *
     * Auto-fit is disabled by default due to coordination issues with LOD culling
     * and spatial indexing. Use `resetCamera()` for one-time camera fitting instead.
     */
    setAutoFit(enabled: boolean): void;
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
     * Syncs the setting to the active renderer backend.
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
     * Sets a custom watermark with both primary and secondary text.
     *
     * This is a convenience method that enables the watermark and sets both text values.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setCustomWatermark("My Project", "© 2026 My Company");
     * ```
     */
    setCustomWatermark(text: string, subtext: string): void;
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
     */
    setGPUCullingThreshold(threshold: number): void;
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
     */
    setGPUPhysicsThreshold(threshold: number): void;
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
     * Sets the maximum number of commits to load.
     *
     * Call this before `loadGitLog()` or `loadCustomLog()` to change the limit.
     * Default is 100,000 commits.
     *
     * # Arguments
     *
     * * `max` - Maximum commits to load (0 = unlimited, use with caution)
     */
    setMaxCommits(max: number): void;
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
     */
    setUseGPUCulling(enabled: boolean): void;
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
     */
    setUseGPUPhysics(enabled: boolean): void;
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
     */
    setVsync(enabled: boolean): void;
    /**
     * Sets the watermark text color (hex string like "#FFFFFF" or "FFFFFF").
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkColor("#FFFFFF");
     * ```
     */
    setWatermarkColor(hex: string): void;
    /**
     * Sets whether the watermark is enabled.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkEnabled(true);
     * ```
     */
    setWatermarkEnabled(enabled: boolean): void;
    /**
     * Sets the watermark font size.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkFontSize(16);
     * ```
     */
    setWatermarkFontSize(size: number): void;
    /**
     * Sets the watermark margin from the screen edge in pixels.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkMargin(20);
     * ```
     */
    setWatermarkMargin(margin: number): void;
    /**
     * Sets the watermark opacity (0.0 = invisible, 1.0 = fully opaque).
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkOpacity(0.5);
     * ```
     */
    setWatermarkOpacity(opacity: number): void;
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
     */
    setWatermarkPosition(position: string): void;
    /**
     * Sets the secondary watermark text (displayed below the primary text).
     *
     * Pass an empty string to clear the subtext.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkSubtext("© 2026 My Company");
     * ```
     */
    setWatermarkSubtext(text: string): void;
    /**
     * Sets the primary watermark text.
     *
     * # Example (JavaScript)
     * ```javascript
     * rource.setWatermarkText("My Project");
     * ```
     */
    setWatermarkText(text: string): void;
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
     * Resets the render cooldown to ensure the next `frame()` calls `render()`.
     *
     * Called by WASM API methods that change visual state (camera, settings,
     * input, playback) so the GPU render phase is not skipped while the user
     * is interacting with the visualization.
     *
     * Part of Level 3 power management: dirty-flag rendering.
     */
    wakeRenderer(): void;
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
    warmupGPUCulling(): void;
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
    warmupGPUPhysics(): void;
    /**
     * Returns true if commits were truncated during the last load.
     *
     * When true, only the first `maxCommits` commits were loaded.
     * Use `getOriginalCommitCount()` to see the full count.
     */
    wasCommitsTruncated(): boolean;
    /**
     * Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
     *
     * Max zoom is 1000.0 to support deep zoom into massive repositories.
     * Min zoom is `AUTO_FIT_MIN_ZOOM` (0.05) to prevent LOD culling all entities.
     * Disables auto-fit when user manually zooms.
     */
    zoom(factor: number): void;
    /**
     * Zooms the camera toward a specific screen point.
     *
     * This provides intuitive zoom behavior where the point under the cursor
     * stays fixed during zoom operations.
     * Min zoom is `AUTO_FIT_MIN_ZOOM` (0.05) to prevent LOD culling all entities.
     * Disables auto-fit when user manually zooms.
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
    readonly rource_debugHitTest: (a: number, b: number, c: number, d: number) => void;
    readonly rource_disableWatermark: (a: number) => void;
    readonly rource_dispose: (a: number) => void;
    readonly rource_enableRourceWatermark: (a: number) => void;
    readonly rource_errorRateExceedsThreshold: (a: number, b: number) => number;
    readonly rource_exportCacheBytes: (a: number, b: number) => void;
    readonly rource_exportCacheBytesWithRepoId: (a: number, b: number, c: number, d: number) => void;
    readonly rource_forceRender: (a: number) => void;
    readonly rource_frame: (a: number, b: number) => number;
    readonly rource_getActiveActions: (a: number) => number;
    readonly rource_getActivityHeatmap: (a: number, b: number) => void;
    readonly rource_getAllFileMetrics: (a: number, b: number) => void;
    readonly rource_getAllUserMetrics: (a: number, b: number) => void;
    readonly rource_getArchitecturalDrift: (a: number, b: number) => void;
    readonly rource_getAssetErrorCount: (a: number) => bigint;
    readonly rource_getAuthorColor: (a: number, b: number, c: number, d: number) => void;
    readonly rource_getAuthors: (a: number, b: number) => void;
    readonly rource_getBusFactors: (a: number, b: number) => void;
    readonly rource_getCacheStats: (a: number, b: number) => void;
    readonly rource_getCacheVersion: () => number;
    readonly rource_getCameraState: (a: number, b: number) => void;
    readonly rource_getCanvasHeight: (a: number) => number;
    readonly rource_getCanvasWidth: (a: number) => number;
    readonly rource_getChangeBursts: (a: number, b: number) => void;
    readonly rource_getChangeCoupling: (a: number, b: number, c: number) => void;
    readonly rource_getChangeEntropy: (a: number, b: number) => void;
    readonly rource_getChangePropagation: (a: number, b: number) => void;
    readonly rource_getChurnVolatility: (a: number, b: number) => void;
    readonly rource_getCircadianRisk: (a: number, b: number) => void;
    readonly rource_getCodebaseGrowth: (a: number, b: number) => void;
    readonly rource_getCommitAuthor: (a: number, b: number, c: number) => void;
    readonly rource_getCommitCadence: (a: number, b: number) => void;
    readonly rource_getCommitCohesion: (a: number, b: number) => void;
    readonly rource_getCommitComplexity: (a: number, b: number) => void;
    readonly rource_getCommitDirectoryCount: (a: number) => number;
    readonly rource_getCommitFileCount: (a: number, b: number) => number;
    readonly rource_getCommitMessageEntropy: (a: number, b: number) => void;
    readonly rource_getCommitTimestamp: (a: number, b: number) => number;
    readonly rource_getConfigErrorCount: (a: number) => bigint;
    readonly rource_getCongruence: (a: number, b: number) => void;
    readonly rource_getContextualComplexity: (a: number, b: number) => void;
    readonly rource_getContributionInequality: (a: number, b: number) => void;
    readonly rource_getDateRange: (a: number, b: number) => void;
    readonly rource_getDefectPatterns: (a: number, b: number) => void;
    readonly rource_getDetailedErrorMetrics: (a: number, b: number) => void;
    readonly rource_getDetailedFrameStats: (a: number, b: number) => void;
    readonly rource_getDeveloperExperience: (a: number, b: number) => void;
    readonly rource_getDeveloperFocus: (a: number, b: number) => void;
    readonly rource_getDeveloperNetwork: (a: number, b: number) => void;
    readonly rource_getDeveloperProfiles: (a: number, b: number) => void;
    readonly rource_getDrawCalls: (a: number) => number;
    readonly rource_getEntityAtCursor: (a: number, b: number, c: number, d: number) => void;
    readonly rource_getEntityBounds: (a: number, b: number) => void;
    readonly rource_getErrorMetrics: (a: number, b: number) => void;
    readonly rource_getErrorRate: (a: number) => number;
    readonly rource_getFileIconCount: (a: number) => number;
    readonly rource_getFileLifecycles: (a: number, b: number) => void;
    readonly rource_getFileMetrics: (a: number, b: number, c: number, d: number) => void;
    readonly rource_getFileSurvival: (a: number, b: number) => void;
    readonly rource_getFontSize: (a: number) => number;
    readonly rource_getFps: (a: number) => number;
    readonly rource_getFrameStats: (a: number, b: number) => void;
    readonly rource_getFrameTimeMs: (a: number) => number;
    readonly rource_getFullMapDimensions: (a: number, b: number, c: number) => void;
    readonly rource_getGPUCullingStats: (a: number, b: number) => void;
    readonly rource_getGPUCullingThreshold: (a: number) => number;
    readonly rource_getGPUInfo: (a: number, b: number) => void;
    readonly rource_getGPUPhysicsThreshold: (a: number) => number;
    readonly rource_getHotspots: (a: number, b: number, c: number) => void;
    readonly rource_getInsights: (a: number, b: number) => void;
    readonly rource_getInsightsIndexSummary: (a: number, b: number) => void;
    readonly rource_getInsightsSummary: (a: number, b: number) => void;
    readonly rource_getIoErrorCount: (a: number) => bigint;
    readonly rource_getKnowledgeDistribution: (a: number, b: number) => void;
    readonly rource_getKnowledgeHalfLife: (a: number, b: number) => void;
    readonly rource_getKnowledgeMap: (a: number, b: number) => void;
    readonly rource_getLayoutConfig: (a: number, b: number) => void;
    readonly rource_getMaxCommits: (a: number) => number;
    readonly rource_getModularity: (a: number, b: number) => void;
    readonly rource_getMousePosition: (a: number, b: number) => void;
    readonly rource_getMouseWorldPosition: (a: number, b: number) => void;
    readonly rource_getOriginalCommitCount: (a: number) => number;
    readonly rource_getOwnershipFragmentation: (a: number, b: number) => void;
    readonly rource_getParseErrorCount: (a: number) => bigint;
    readonly rource_getParseErrorRate: (a: number) => number;
    readonly rource_getReleaseRhythm: (a: number, b: number) => void;
    readonly rource_getRenderErrorCount: (a: number) => bigint;
    readonly rource_getRendererType: (a: number, b: number) => void;
    readonly rource_getShowLabels: (a: number) => number;
    readonly rource_getSpeed: (a: number) => number;
    readonly rource_getStatsBufferLen: (a: number) => number;
    readonly rource_getStatsBufferPtr: (a: number) => number;
    readonly rource_getSuccessionReadiness: (a: number, b: number) => void;
    readonly rource_getTechDistribution: (a: number, b: number) => void;
    readonly rource_getTechExpertise: (a: number, b: number) => void;
    readonly rource_getTemporalPatterns: (a: number, b: number) => void;
    readonly rource_getTotalDirectories: (a: number) => number;
    readonly rource_getTotalEntities: (a: number) => number;
    readonly rource_getTotalErrors: (a: number) => bigint;
    readonly rource_getTotalFiles: (a: number) => number;
    readonly rource_getTotalFrames: (a: number) => number;
    readonly rource_getTotalOperations: (a: number) => bigint;
    readonly rource_getTotalUsers: (a: number) => number;
    readonly rource_getTruckFactor: (a: number, b: number) => void;
    readonly rource_getTurnoverImpact: (a: number, b: number) => void;
    readonly rource_getUptime: (a: number) => number;
    readonly rource_getUserMetrics: (a: number, b: number, c: number, d: number) => void;
    readonly rource_getVisibleDirectories: (a: number) => number;
    readonly rource_getVisibleFiles: (a: number) => number;
    readonly rource_getVisibleUsers: (a: number) => number;
    readonly rource_getWasmMemory: (a: number) => number;
    readonly rource_getWatermarkOpacity: (a: number) => number;
    readonly rource_getWebGlErrorCount: (a: number) => bigint;
    readonly rource_getWorkTypeMix: (a: number, b: number) => void;
    readonly rource_getZoom: (a: number) => number;
    readonly rource_getZoomDebugInfo: (a: number, b: number) => void;
    readonly rource_hasFileIcons: (a: number) => number;
    readonly rource_hasValidCacheMagic: (a: number, b: number) => number;
    readonly rource_hashRepoId: (a: number, b: number, c: number) => void;
    readonly rource_importCacheBytes: (a: number, b: number, c: number) => number;
    readonly rource_importCacheBytesWithRepoId: (a: number, b: number, c: number, d: number, e: number) => number;
    readonly rource_initFileIcons: (a: number) => number;
    readonly rource_isAutoFit: (a: number) => number;
    readonly rource_isContextLost: (a: number) => number;
    readonly rource_isGPUAccelerated: (a: number) => number;
    readonly rource_isGPUCullingActive: (a: number) => number;
    readonly rource_isGPUCullingEnabled: (a: number) => number;
    readonly rource_isGPUPhysicsActive: (a: number) => number;
    readonly rource_isGPUPhysicsEnabled: (a: number) => number;
    readonly rource_isPlaying: (a: number) => number;
    readonly rource_isProfilingEnabled: (a: number) => number;
    readonly rource_isVsyncEnabled: (a: number) => number;
    readonly rource_isWatermarkEnabled: (a: number) => number;
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
    readonly rource_registerFileIcon: (a: number, b: number, c: number, d: number, e: number) => number;
    readonly rource_resetCamera: (a: number) => void;
    readonly rource_resetErrorMetrics: (a: number) => void;
    readonly rource_resize: (a: number, b: number, c: number) => void;
    readonly rource_restoreAfterExport: (a: number, b: number, c: number) => void;
    readonly rource_restoreCameraState: (a: number, b: number, c: number, d: number) => void;
    readonly rource_seek: (a: number, b: number) => void;
    readonly rource_setAutoFit: (a: number, b: number) => void;
    readonly rource_setBackgroundColor: (a: number, b: number, c: number) => void;
    readonly rource_setBloom: (a: number, b: number) => void;
    readonly rource_setBranchDepthFade: (a: number, b: number) => void;
    readonly rource_setBranchOpacityMax: (a: number, b: number) => void;
    readonly rource_setCustomWatermark: (a: number, b: number, c: number, d: number, e: number) => void;
    readonly rource_setDepthDistanceExponent: (a: number, b: number) => void;
    readonly rource_setFontSize: (a: number, b: number) => void;
    readonly rource_setGPUCullingThreshold: (a: number, b: number) => void;
    readonly rource_setGPUPhysicsThreshold: (a: number, b: number) => void;
    readonly rource_setLayoutPreset: (a: number, b: number, c: number) => void;
    readonly rource_setMaxCommits: (a: number, b: number) => void;
    readonly rource_setRadialDistanceScale: (a: number, b: number) => void;
    readonly rource_setShowLabels: (a: number, b: number) => void;
    readonly rource_setSpeed: (a: number, b: number) => void;
    readonly rource_setUseGPUCulling: (a: number, b: number) => void;
    readonly rource_setUseGPUPhysics: (a: number, b: number) => void;
    readonly rource_setVsync: (a: number, b: number) => void;
    readonly rource_setWatermarkColor: (a: number, b: number, c: number) => void;
    readonly rource_setWatermarkEnabled: (a: number, b: number) => void;
    readonly rource_setWatermarkFontSize: (a: number, b: number) => void;
    readonly rource_setWatermarkMargin: (a: number, b: number) => void;
    readonly rource_setWatermarkOpacity: (a: number, b: number) => void;
    readonly rource_setWatermarkPosition: (a: number, b: number, c: number) => void;
    readonly rource_setWatermarkSubtext: (a: number, b: number, c: number) => void;
    readonly rource_setWatermarkText: (a: number, b: number, c: number) => void;
    readonly rource_stepBackward: (a: number) => void;
    readonly rource_stepForward: (a: number) => void;
    readonly rource_togglePlay: (a: number) => void;
    readonly rource_wakeRenderer: (a: number) => void;
    readonly rource_warmupGPUCulling: (a: number) => void;
    readonly rource_warmupGPUPhysics: (a: number) => void;
    readonly rource_wasCommitsTruncated: (a: number) => number;
    readonly rource_zoom: (a: number, b: number) => void;
    readonly rource_zoomToward: (a: number, b: number, c: number, d: number) => void;
    readonly init_panic_hook: () => void;
    readonly rource_isTracingEnabled: (a: number) => number;
    readonly __wasm_bindgen_func_elem_3346: (a: number, b: number) => void;
    readonly __wasm_bindgen_func_elem_8091: (a: number, b: number, c: number, d: number) => void;
    readonly __wasm_bindgen_func_elem_3347: (a: number, b: number, c: number) => void;
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
