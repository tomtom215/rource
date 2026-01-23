// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Rource WASM
//!
//! WebAssembly bindings for Rource - software version control visualization.
//!
//! This crate provides JavaScript/TypeScript bindings to run Rource in a web browser.
//!
//! ## Rendering Backends
//!
//! Rource WASM supports three rendering backends (in priority order):
//!
//! 1. **wgpu (WebGPU)**: Best performance, modern GPU API (Chrome 113+, Edge 113+, Firefox 128+)
//! 2. **WebGL2**: Good performance, widely supported in all modern browsers
//! 3. **Software**: Pure CPU rendering via `Canvas2D` for maximum compatibility
//!
//! The async constructor automatically tries wgpu first, then WebGL2, and finally
//! falls back to software rendering.
//!
//! ## Module Structure
//!
//! ### Internal Modules
//! - `backend`: Renderer backend abstraction (wgpu/WebGL2/Software)
//! - `metrics`: Performance tracking and render statistics
//! - `playback`: Timeline and commit playback management
//! - `interaction`: Mouse/touch input handling
//! - `render_phases`: Phased rendering pipeline
//! - `rendering`: Low-level rendering utilities
//!
//! ### WASM API Modules (JavaScript-facing)
//! - `wasm_api::input`: Mouse and keyboard event handlers
//! - `wasm_api::playback`: Timeline control (play, pause, seek, speed)
//! - `wasm_api::camera`: View control (zoom, pan, resize)
//! - `wasm_api::layout`: Layout algorithm configuration
//! - `wasm_api::settings`: Visual settings (bloom, background, labels)
//! - `wasm_api::export`: Screenshot and full-map export
//! - `wasm_api::stats`: Render statistics and entity counts
//! - `wasm_api::authors`: Author information and colors
//!
//! ## Usage
//!
//! ```javascript
//! import init, { Rource } from 'rource-wasm';
//!
//! async function main() {
//!     await init();
//!
//!     const canvas = document.getElementById('canvas');
//!     // Use the async factory method Rource.create()
//!     const rource = await Rource.create(canvas);
//!
//!     // Check which backend is being used
//!     console.log('Renderer:', rource.getRendererType());
//!     // Possible values: "wgpu", "webgl2", or "software"
//!
//!     // Check if GPU-accelerated
//!     if (rource.isGPUAccelerated()) {
//!         console.log('Using GPU acceleration');
//!     }
//!
//!     // Load a git log
//!     const log = `1234567890|John Doe|A|src/main.rs
//! 1234567891|Jane Smith|M|src/lib.rs`;
//!     rource.loadCustomLog(log);
//!
//!     rource.play();
//! }
//! ```

// Allow multiple versions of dependencies from workspace dependencies
#![allow(clippy::multiple_crate_versions)]

// ============================================================================
// Module Declarations
// ============================================================================

mod backend;
mod interaction;
mod metrics;
mod playback;
mod png;
mod render_phases;
mod rendering;

// WASM API modules - each contains an impl block for Rource with related methods
mod wasm_api;

// ============================================================================
// Imports
// ============================================================================

use wasm_bindgen::prelude::*;
use web_sys::HtmlCanvasElement;

use rource_core::camera::Camera;
use rource_core::config::Settings;
use rource_core::entity::{DirId, FileId, UserId};
use rource_core::scene::Scene;
use rource_math::{Bounds, Vec2};
use rource_render::backend::wgpu::ComputeEntity;
use rource_render::{default_font, FontId};
use rource_vcs::parser::{CustomParser, GitParser, ParseOptions, Parser};
use rource_vcs::Commit;

// Internal re-exports for submodules
use backend::{RendererBackend, RendererType};
use interaction::DragTarget;
use metrics::{PerformanceMetrics, RenderStats};
use playback::{apply_vcs_commit, calculate_seconds_per_commit, prewarm_scene, PlaybackState};
use render_phases::{
    render_actions, render_directories, render_directory_labels, render_file_labels, render_files,
    render_user_labels, render_users, render_watermark, RenderContext, AUTO_FIT_MIN_ZOOM,
};

// ============================================================================
// Pure Helper Functions (testable without Rource instance)
// ============================================================================

// ---- Frame Timing Helpers ----

/// Computes the frame delta time from timestamps (in seconds).
///
/// Returns a reasonable default (1/60s) if `last_frame_time` is 0.
#[inline]
#[must_use]
pub fn compute_frame_dt(timestamp: f64, last_frame_time: f64) -> f32 {
    if last_frame_time > 0.0 {
        ((timestamp - last_frame_time) / 1000.0) as f32
    } else {
        1.0 / 60.0
    }
}

/// Clamps delta time to avoid huge jumps (e.g., after tab switch).
#[inline]
#[must_use]
pub fn clamp_dt(dt: f32, max_dt: f32) -> f32 {
    dt.min(max_dt)
}

/// Default maximum delta time (100ms = 10 FPS minimum).
pub const MAX_FRAME_DT: f32 = 0.1;

// ---- Auto-Fit Camera Helpers ----

/// Padding factor for bounds when fitting camera (1.2 = 20% padding).
pub const AUTO_FIT_PADDING: f32 = 1.2;

/// Threshold for zoom adjustment (5% = only zoom out if needed by more than 5%).
pub const ZOOM_ADJUSTMENT_THRESHOLD: f32 = 0.95;

/// Threshold distance for panning (in world units).
pub const PAN_THRESHOLD: f32 = 10.0;

/// Rate of smooth zoom adjustment per second.
pub const ZOOM_RATE: f32 = 2.0;

/// Rate of smooth pan adjustment per second.
pub const PAN_RATE: f32 = 2.0;

/// Maximum interpolation factor per frame (caps adjustment speed).
pub const MAX_INTERPOLATION_FACTOR: f32 = 0.15;

/// Computes the target zoom to fit bounds within screen.
///
/// Returns the minimum of x and y zoom ratios, clamped to the specified range.
#[inline]
#[must_use]
pub fn compute_target_zoom(
    bounds_width: f32,
    bounds_height: f32,
    screen_width: f32,
    screen_height: f32,
    min_zoom: f32,
    max_zoom: f32,
) -> f32 {
    if bounds_width <= 0.0 || bounds_height <= 0.0 {
        return min_zoom;
    }
    let zoom_x = screen_width / bounds_width;
    let zoom_y = screen_height / bounds_height;
    zoom_x.min(zoom_y).clamp(min_zoom, max_zoom)
}

/// Determines if zooming out is needed (only zoom out, never auto zoom in).
#[inline]
#[must_use]
pub fn is_zoom_out_needed(target_zoom: f32, current_zoom: f32, threshold: f32) -> bool {
    target_zoom < current_zoom * threshold
}

/// Computes the interpolation factor for smooth animation.
#[inline]
#[must_use]
pub fn compute_interpolation_factor(rate: f32, dt: f32, max_t: f32) -> f32 {
    (rate * dt).min(max_t)
}

/// Computes a smoothly interpolated zoom value.
#[inline]
#[must_use]
pub fn compute_smooth_zoom(current: f32, target: f32, rate: f32, dt: f32, max_t: f32) -> f32 {
    let t = compute_interpolation_factor(rate, dt, max_t);
    current + (target - current) * t
}

/// Determines if panning is needed (distance exceeds threshold).
#[inline]
#[must_use]
pub fn is_pan_needed(distance: f32, threshold: f32) -> bool {
    distance > threshold
}

/// Computes a smoothly interpolated position.
#[inline]
#[must_use]
pub fn compute_smooth_position(
    current: Vec2,
    target: Vec2,
    rate: f32,
    dt: f32,
    max_t: f32,
) -> Vec2 {
    let t = compute_interpolation_factor(rate, dt, max_t);
    current + (target - current) * t
}

/// Computes padded bounds dimensions.
#[inline]
#[must_use]
pub fn compute_padded_dimensions(width: f32, height: f32, padding: f32) -> (f32, f32) {
    (width * padding, height * padding)
}

// ---- GPU Feature Decision Helpers ----

/// Determines if GPU physics should be used based on configuration and scene size.
///
/// Returns true if:
/// 1. GPU physics is enabled
/// 2. The renderer type supports compute (wgpu only)
/// 3. Directory count meets or exceeds the threshold (0 = always use)
#[inline]
#[must_use]
pub fn should_enable_gpu_physics(
    enabled: bool,
    is_wgpu: bool,
    directory_count: usize,
    threshold: usize,
) -> bool {
    if !enabled || !is_wgpu {
        return false;
    }
    threshold == 0 || directory_count >= threshold
}

/// Determines if GPU culling should be used based on configuration and entity count.
///
/// Returns true if:
/// 1. GPU culling is enabled
/// 2. The renderer type supports compute (wgpu only)
/// 3. Entity count meets or exceeds the threshold (0 = always use)
#[inline]
#[must_use]
pub fn should_enable_gpu_culling(
    enabled: bool,
    is_wgpu: bool,
    entity_count: usize,
    threshold: usize,
) -> bool {
    if !enabled || !is_wgpu {
        return false;
    }
    threshold == 0 || entity_count >= threshold
}

/// Computes the total entity count for GPU culling threshold check.
#[inline]
#[must_use]
pub fn compute_total_entity_count(file_count: usize, user_count: usize, dir_count: usize) -> usize {
    file_count + user_count + dir_count
}

// ---- Playback Helpers ----

/// Determines if playback has more frames to process.
#[inline]
#[must_use]
pub fn has_more_frames(is_playing: bool, current_commit: usize, total_commits: usize) -> bool {
    is_playing || current_commit < total_commits
}

/// Determines if a commit should be applied (handles initial commit case).
#[inline]
#[must_use]
pub fn should_apply_commit(current_commit: usize, last_applied: usize) -> bool {
    current_commit > last_applied || (last_applied == 0 && current_commit == 0)
}

/// Determines if playback should stop (reached end).
#[inline]
#[must_use]
pub fn should_stop_playback(current_commit: usize, total_commits: usize) -> bool {
    current_commit >= total_commits
}

// ============================================================================
// WASM Initialization
// ============================================================================

/// Set up better panic messages for debugging in browser console.
#[wasm_bindgen(start)]
pub fn init_panic_hook() {
    console_error_panic_hook::set_once();
}

// ============================================================================
// Main Rource WASM API
// ============================================================================

/// The main Rource visualization controller for browser usage.
///
/// This struct manages the entire visualization lifecycle including:
/// - Rendering (wgpu, WebGL2, or Software backend)
/// - Scene management (files, users, directories)
/// - Camera controls (pan, zoom)
/// - Playback timeline (play, pause, seek)
/// - User interaction (mouse, keyboard)
///
/// ## API Organization
///
/// The public API is organized into focused modules:
/// - **Constructor/Renderer**: `create()`, `getRendererType()`, `isGPUAccelerated()`
/// - **Data Loading**: `loadCustomLog()`, `loadGitLog()`, `commitCount()`
/// - **Playback**: `play()`, `pause()`, `seek()`, `setSpeed()` (see `wasm_api::playback`)
/// - **Camera**: `zoom()`, `pan()`, `resize()` (see `wasm_api::camera`)
/// - **Input**: `onMouseDown()`, `onKeyDown()` (see `wasm_api::input`)
/// - **Layout**: `setLayoutPreset()`, `configureLayoutForRepo()` (see `wasm_api::layout`)
/// - **Settings**: `setBloom()`, `setShowLabels()` (see `wasm_api::settings`)
/// - **Export**: `captureScreenshot()`, `getFullMapDimensions()` (see `wasm_api::export`)
/// - **Stats**: `getTotalFiles()`, `getVisibleEntities()` (see `wasm_api::stats`)
/// - **Authors**: `getAuthors()`, `getAuthorColor()` (see `wasm_api::authors`)
#[wasm_bindgen]
#[allow(clippy::struct_excessive_bools)]
pub struct Rource {
    // ---- Canvas & Rendering ----
    /// Canvas element.
    canvas: HtmlCanvasElement,

    /// Renderer backend (wgpu, WebGL2, or Software).
    backend: RendererBackend,

    /// Type of renderer being used.
    renderer_type: RendererType,

    // ---- Scene & State ----
    /// Scene graph containing all entities.
    scene: Scene,

    /// Camera for view control.
    camera: Camera,

    /// Visualization settings.
    settings: Settings,

    /// Loaded commits.
    commits: Vec<Commit>,

    /// Playback state (timeline position, play/pause).
    playback: PlaybackState,

    // ---- Input State ----
    /// Mouse X position (screen coordinates).
    mouse_x: f32,
    /// Mouse Y position (screen coordinates).
    mouse_y: f32,
    /// Whether mouse button is currently pressed.
    mouse_down: bool,
    /// X position where drag started.
    drag_start_x: f32,
    /// Y position where drag started.
    drag_start_y: f32,
    /// Camera X position when drag started (for panning).
    camera_start_x: f32,
    /// Camera Y position when drag started (for panning).
    camera_start_y: f32,

    // ---- Entity Dragging ----
    /// Currently dragged entity (if any).
    drag_target: Option<DragTarget>,

    /// Offset from drag start to entity center (for smooth dragging).
    drag_offset: Vec2,

    /// Last position of dragged entity (for calculating movement delta).
    drag_last_pos: Vec2,

    // ---- Display ----
    /// Font ID for text rendering.
    font_id: Option<FontId>,

    /// Whether to show labels (user names, file names).
    show_labels: bool,

    /// Whether to automatically adjust camera to keep all content visible.
    /// When enabled, the camera smoothly zooms out as the visualization grows.
    auto_fit: bool,

    // ---- Metrics ----
    /// Performance metrics (FPS tracking, frame timing).
    perf_metrics: PerformanceMetrics,

    /// Render statistics for the current frame.
    render_stats: RenderStats,

    // ---- Visibility Buffers (zero-allocation rendering) ----
    /// Reusable buffer for visible directory IDs.
    visible_dirs_buf: Vec<DirId>,

    /// Reusable buffer for visible file IDs.
    visible_files_buf: Vec<FileId>,

    /// Reusable buffer for visible user IDs.
    visible_users_buf: Vec<UserId>,

    /// Reusable buffer for file label candidates (avoids per-frame allocation).
    /// Stores (`FileId`, `screen_pos`, `radius`, `alpha`, `priority`) tuples.
    file_label_candidates_buf: Vec<(FileId, Vec2, f32, f32, f32)>,

    /// Reusable label placer for collision avoidance (avoids per-frame Vec allocation).
    label_placer: render_phases::LabelPlacer,

    // ---- GPU Physics (wgpu only) ----
    /// Whether to use GPU physics (only available with wgpu backend).
    /// When enabled and directory count exceeds the threshold, physics
    /// simulation runs on the GPU for better performance.
    use_gpu_physics: bool,

    /// Threshold for auto-enabling GPU physics (directory count).
    gpu_physics_threshold: usize,

    /// Reusable buffer for GPU physics entities (wasm32 only).
    #[cfg_attr(not(target_arch = "wasm32"), allow(dead_code))]
    compute_entities_buf: Vec<ComputeEntity>,

    // ---- GPU Visibility Culling (wgpu only) ----
    /// Whether to use GPU visibility culling.
    /// When enabled, instances are culled on the GPU using compute shaders.
    /// This is beneficial for extreme-scale scenarios (10,000+ instances).
    use_gpu_culling: bool,

    /// Threshold for auto-enabling GPU culling (total visible entity count).
    /// Set to 0 to always use GPU culling when enabled.
    gpu_culling_threshold: usize,
}

// ============================================================================
// Constructor and Renderer Info
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Creates a new Rource instance attached to a canvas element (async factory method).
    ///
    /// Automatically tries wgpu (WebGPU) first, then WebGL2, falling back to
    /// software rendering if neither is available.
    ///
    /// # Arguments
    ///
    /// * `canvas` - The HTML canvas element to render to
    ///
    /// # Backend Selection Priority
    ///
    /// 1. **wgpu (WebGPU)**: Best performance, modern GPU API (Chrome 113+, Edge 113+)
    /// 2. **WebGL2**: Good performance, widely supported
    /// 3. **Software**: Maximum compatibility, CPU-based
    ///
    /// # JavaScript Usage
    ///
    /// ```javascript
    /// const rource = await Rource.create(canvas);
    /// ```
    ///
    /// # Note on Send
    ///
    /// This future is not `Send` because JavaScript/browser APIs are single-threaded.
    /// This is expected and safe for WASM usage.
    #[wasm_bindgen(js_name = create)]
    #[allow(clippy::future_not_send)]
    pub async fn create(canvas: HtmlCanvasElement) -> Result<Self, JsValue> {
        let width = canvas.width();
        let height = canvas.height();

        // Use async initialization to try wgpu (WebGPU) first
        let (mut backend, renderer_type) = RendererBackend::new_async(&canvas).await?;

        // Load the default font for text rendering
        let font_id = backend.load_font(default_font::ROBOTO_MONO);
        if font_id.is_none() {
            web_sys::console::warn_1(
                &"Rource: Failed to load font, labels will be disabled".into(),
            );
        }

        // Initialize file icons for GPU-accelerated rendering (wgpu only)
        // Falls back to colored disc rendering if not supported
        if backend.init_file_icons() {
            web_sys::console::log_1(&"Rource: File icons initialized".into());
        }

        let scene = Scene::new();

        let mut settings = Settings::default();
        settings.display.width = width;
        settings.display.height = height;

        let mut camera = Camera::new(width as f32, height as f32);
        // Use AUTO_FIT_MIN_ZOOM (0.03) as minimum to prevent LOD culling all entities
        camera.set_zoom_limits(AUTO_FIT_MIN_ZOOM, 1000.0);
        camera.jump_to(Vec2::ZERO);

        Ok(Self {
            canvas,
            backend,
            renderer_type,
            scene,
            camera,
            settings,
            commits: Vec::new(),
            playback: PlaybackState::new(),
            mouse_x: 0.0,
            mouse_y: 0.0,
            mouse_down: false,
            drag_start_x: 0.0,
            drag_start_y: 0.0,
            camera_start_x: 0.0,
            camera_start_y: 0.0,
            drag_target: None,
            drag_offset: Vec2::ZERO,
            drag_last_pos: Vec2::ZERO,
            font_id,
            show_labels: true,
            auto_fit: true, // Auto-zoom to fit all content (MIN_ZOOM=0.05 prevents LOD culling)
            perf_metrics: PerformanceMetrics::new(),
            render_stats: RenderStats::default(),
            // Pre-allocate visibility buffers for zero-allocation rendering
            visible_dirs_buf: Vec::with_capacity(1024),
            visible_files_buf: Vec::with_capacity(4096),
            visible_users_buf: Vec::with_capacity(256),
            file_label_candidates_buf: Vec::with_capacity(256),
            // Reusable label placer (avoids per-frame Vec allocation)
            label_placer: render_phases::LabelPlacer::new(1.0),
            // GPU physics (wgpu only) - default threshold 500 directories
            use_gpu_physics: false,
            gpu_physics_threshold: 500,
            compute_entities_buf: Vec::with_capacity(1024),
            // GPU culling (wgpu only) - default threshold 10000 entities
            use_gpu_culling: false,
            gpu_culling_threshold: 10000,
        })
    }

    /// Returns the type of renderer being used ("wgpu", "webgl2", or "software").
    #[wasm_bindgen(js_name = getRendererType)]
    pub fn get_renderer_type(&self) -> String {
        self.renderer_type.as_str().to_string()
    }

    /// Returns true if using a GPU-accelerated renderer (wgpu or WebGL2).
    #[wasm_bindgen(js_name = isGPUAccelerated)]
    pub fn is_gpu_accelerated(&self) -> bool {
        self.renderer_type.is_gpu_accelerated()
    }

    /// Returns true if using wgpu (WebGPU) renderer.
    #[wasm_bindgen(js_name = isWgpu)]
    pub fn is_wgpu(&self) -> bool {
        self.renderer_type == RendererType::Wgpu
    }

    /// Returns true if using WebGL2 renderer.
    #[wasm_bindgen(js_name = isWebGL2)]
    pub fn is_webgl2(&self) -> bool {
        self.renderer_type == RendererType::WebGl2
    }

    /// Returns true if the GPU context is lost.
    #[wasm_bindgen(js_name = isContextLost)]
    pub fn is_context_lost(&self) -> bool {
        self.backend.is_context_lost()
    }

    /// Attempts to recover from a lost GPU context.
    #[wasm_bindgen(js_name = recoverContext)]
    pub fn recover_context(&mut self) -> bool {
        self.backend.recover_context().is_ok()
    }

    /// Releases GPU resources immediately.
    ///
    /// Call this method before the page unloads to prevent GPU resource
    /// contention when the page is refreshed quickly. This is especially
    /// important for WebGPU which may hold onto adapter resources.
    ///
    /// After calling `dispose()`, the Rource instance should not be used again.
    ///
    /// # Example
    ///
    /// ```javascript
    /// window.addEventListener('beforeunload', () => {
    ///     if (rource) {
    ///         rource.dispose();
    ///     }
    /// });
    /// ```
    #[wasm_bindgen]
    pub fn dispose(&mut self) {
        // Log for debugging
        web_sys::console::log_1(&"Rource: Disposing GPU resources...".into());

        // Clear scene to release any entity-related resources
        self.scene = Scene::new();

        // Clear all buffers
        self.commits.clear();
        self.visible_dirs_buf.clear();
        self.visible_files_buf.clear();
        self.visible_users_buf.clear();
        self.compute_entities_buf.clear();

        // The backend will be dropped when self is dropped, but we log this
        // to help with debugging. The actual GPU resource release happens
        // when JavaScript nullifies the reference to this object.
        web_sys::console::log_1(&"Rource: Resources cleared, awaiting garbage collection".into());
    }
}

// ============================================================================
// Data Loading
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Loads commits from custom pipe-delimited format.
    ///
    /// Format: `timestamp|author|action|path` per line
    ///
    /// Uses lenient parsing by default to skip invalid lines (e.g., lines with
    /// pipe characters in author names or unsupported git statuses).
    #[wasm_bindgen(js_name = loadCustomLog)]
    pub fn load_custom_log(&mut self, log: &str) -> Result<usize, JsValue> {
        // Use lenient parsing to handle malformed lines gracefully
        let parser = CustomParser::with_options(ParseOptions::lenient());
        let commits = parser
            .parse_str(log)
            .map_err(|e| JsValue::from_str(&format!("Parse error: {e}")))?;

        let count = commits.len();
        self.commits = commits;
        self.reset_playback();
        Ok(count)
    }

    /// Loads commits from git log format.
    ///
    /// Uses lenient parsing to handle malformed lines gracefully.
    #[wasm_bindgen(js_name = loadGitLog)]
    pub fn load_git_log(&mut self, log: &str) -> Result<usize, JsValue> {
        // Use lenient parsing to handle malformed lines gracefully
        let parser = GitParser::with_options(ParseOptions::lenient());
        let commits = parser
            .parse_str(log)
            .map_err(|e| JsValue::from_str(&format!("Parse error: {e}")))?;

        let count = commits.len();
        self.commits = commits;
        self.reset_playback();
        Ok(count)
    }

    /// Returns the number of loaded commits.
    #[wasm_bindgen(js_name = commitCount)]
    pub fn commit_count(&self) -> usize {
        self.commits.len()
    }
}

// ============================================================================
// Frame Update and Rendering
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Updates and renders a single frame.
    ///
    /// Returns true if there are more frames to render.
    pub fn frame(&mut self, timestamp: f64) -> bool {
        // Initialize start time on first frame
        if self.perf_metrics.start_time() == 0.0 {
            self.perf_metrics.set_start_time(timestamp);
        }

        // Calculate delta time (raw measurement)
        let raw_dt = if self.playback.last_frame_time() > 0.0 {
            ((timestamp - self.playback.last_frame_time()) / 1000.0) as f32
        } else {
            1.0 / 60.0
        };
        self.playback.set_last_frame_time(timestamp);

        // Record UNCLAMPED frame time for accurate performance measurement
        // This is critical: we must display the actual frame time, not a clamped value.
        // Clamping would hide stutters and make performance claims dishonest.
        self.perf_metrics.record_frame(raw_dt);

        // Clamp dt for SIMULATION ONLY to avoid physics instability
        // (e.g., when tab is backgrounded, we don't want entities to fly off screen)
        let dt = raw_dt.min(0.1);

        // Update simulation if playing
        if self.playback.is_playing() && !self.commits.is_empty() {
            self.playback.add_time(dt);

            let seconds_per_commit =
                calculate_seconds_per_commit(self.settings.playback.seconds_per_day);

            while self.playback.accumulated_time() >= seconds_per_commit
                && self.playback.current_commit() < self.commits.len()
            {
                let current = self.playback.current_commit();
                let last_applied = self.playback.last_applied_commit();

                if current > last_applied || (last_applied == 0 && current == 0) {
                    apply_vcs_commit(&mut self.scene, &self.commits[current]);
                    self.playback.set_last_applied_commit(current);
                }
                self.playback.subtract_time(seconds_per_commit);
                self.playback.advance_commit();
            }

            // Check if we're done
            if self.playback.current_commit() >= self.commits.len() {
                self.playback.stop();
            }
        }

        // Update scene physics and animations
        // Use GPU physics when enabled and conditions are met (wgpu backend, threshold)
        if self.should_use_gpu_physics() {
            self.update_physics_gpu(dt);
        } else {
            self.scene.update(dt);
        }

        // Auto-fit camera to keep content visible (if enabled)
        if self.auto_fit {
            self.auto_fit_camera(dt);
        }

        // Update camera
        self.camera.update(dt);

        // Render the frame
        self.render();

        // Return true if there's more to show
        self.playback.is_playing() || self.playback.current_commit() < self.commits.len()
    }

    /// Forces a render without updating simulation.
    #[wasm_bindgen(js_name = forceRender)]
    pub fn force_render(&mut self) {
        let canvas_width = self.canvas.width();
        let canvas_height = self.canvas.height();

        if self.backend.width() != canvas_width || self.backend.height() != canvas_height {
            self.backend.resize(canvas_width, canvas_height);
        }

        self.render();
        self.backend.sync();
    }
}

// ============================================================================
// Performance Metrics API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns the current frames per second.
    #[wasm_bindgen(js_name = getFps)]
    pub fn get_fps(&self) -> f32 {
        self.perf_metrics.fps()
    }

    /// Returns the last frame time in milliseconds.
    #[wasm_bindgen(js_name = getFrameTimeMs)]
    pub fn get_frame_time_ms(&self) -> f32 {
        self.perf_metrics.frame_time_ms()
    }

    /// Returns the total number of frames rendered.
    #[wasm_bindgen(js_name = getTotalFrames)]
    pub fn get_total_frames(&self) -> f64 {
        self.perf_metrics.total_frames() as f64
    }

    /// Returns the uptime in seconds.
    #[wasm_bindgen(js_name = getUptime)]
    pub fn get_uptime(&self) -> f64 {
        self.perf_metrics.uptime(self.playback.last_frame_time())
    }
}

// ============================================================================
// Private Implementation
// ============================================================================

impl Rource {
    /// Collects directory data into `ComputeEntity` buffer for GPU physics.
    ///
    /// Returns the number of entities collected.
    #[cfg(target_arch = "wasm32")]
    #[inline]
    fn collect_compute_entities(&mut self) -> usize {
        self.compute_entities_buf.clear();

        for dir in self.scene.directories().iter() {
            // Skip root - it's anchored at origin
            if dir.is_root() {
                continue;
            }

            let pos = dir.position();
            let vel = dir.velocity();

            self.compute_entities_buf
                .push(ComputeEntity::new(pos.x, pos.y, dir.radius()).with_velocity(vel.x, vel.y));
        }

        self.compute_entities_buf.len()
    }

    /// Applies GPU physics results back to scene directories.
    ///
    /// The entities must be in the same order as collected by `collect_compute_entities`.
    #[cfg(target_arch = "wasm32")]
    fn apply_compute_results(&mut self, entities: &[ComputeEntity]) {
        // Skip root (index 0 in directories), so entities align with directories[1..]
        let mut entity_idx = 0;

        for dir in self.scene.directories_mut().iter_mut() {
            if dir.is_root() {
                continue;
            }

            if entity_idx >= entities.len() {
                break;
            }

            let entity = &entities[entity_idx];
            let (x, y) = entity.position();
            let (vx, vy) = entity.velocity();

            dir.set_position(Vec2::new(x, y));
            dir.set_velocity(Vec2::new(vx, vy));

            entity_idx += 1;
        }
    }

    /// Returns whether GPU physics should be used for the current scene.
    ///
    /// Conditions:
    /// 1. `use_gpu_physics` is enabled
    /// 2. wgpu backend is active
    /// 3. Directory count exceeds threshold (auto mode)
    #[inline]
    fn should_use_gpu_physics(&self) -> bool {
        if !self.use_gpu_physics {
            return false;
        }

        // Only wgpu supports compute shaders
        if self.renderer_type != RendererType::Wgpu {
            return false;
        }

        // Check threshold (0 = always use GPU physics when enabled)
        if self.gpu_physics_threshold > 0
            && self.scene.directories().len() < self.gpu_physics_threshold
        {
            return false;
        }

        true
    }

    /// Returns whether GPU culling should be used for the current scene.
    ///
    /// Conditions:
    /// 1. `use_gpu_culling` is enabled
    /// 2. wgpu backend is active
    /// 3. Entity count exceeds threshold (auto mode)
    #[inline]
    fn should_use_gpu_culling(&self) -> bool {
        if !self.use_gpu_culling {
            return false;
        }

        // Only wgpu supports compute shaders
        if self.renderer_type != RendererType::Wgpu {
            return false;
        }

        // Calculate total entity count
        let total_entities =
            self.scene.file_count() + self.scene.user_count() + self.scene.directories().len();

        // Check threshold (0 = always use GPU culling when enabled)
        if self.gpu_culling_threshold > 0 && total_entities < self.gpu_culling_threshold {
            return false;
        }

        true
    }

    /// Updates physics simulation using the GPU compute pipeline.
    ///
    /// This method:
    /// 1. Collects directory data into `ComputeEntity` format
    /// 2. Dispatches GPU physics simulation
    /// 3. Applies results back to scene directories
    /// 4. Updates file and user animations (CPU, same as normal update)
    #[cfg(target_arch = "wasm32")]
    fn update_physics_gpu(&mut self, dt: f32) {
        // Collect entities from scene
        let entity_count = self.collect_compute_entities();

        if entity_count == 0 {
            // No non-root directories, just update the scene normally
            self.scene.update(dt);
            return;
        }

        // Get mutable reference to wgpu renderer and dispatch physics
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            let updated = wgpu_renderer.dispatch_physics_sync(&self.compute_entities_buf, dt);

            // Apply GPU physics results back to scene directories
            self.apply_compute_results(&updated);
        }

        // Update file/user animations and other scene state (CPU)
        // This handles file fade-in, user positioning, action beams, etc.
        self.scene.update_animations(dt);
    }

    /// Fallback for non-WASM targets (GPU physics not supported).
    #[cfg(not(target_arch = "wasm32"))]
    fn update_physics_gpu(&mut self, dt: f32) {
        // GPU physics only available on WASM with wgpu backend
        self.scene.update(dt);
    }

    /// Resets playback to the beginning.
    fn reset_playback(&mut self) {
        self.scene = Scene::new();
        self.playback.reset();

        if !self.commits.is_empty() {
            apply_vcs_commit(&mut self.scene, &self.commits[0]);
            self.playback.set_last_applied_commit(0);

            prewarm_scene(&mut self.scene, 30, 1.0 / 60.0);
            self.fit_camera_to_content();
        }
    }

    /// Fits the camera to show all content.
    pub(crate) fn fit_camera_to_content(&mut self) {
        if let Some(entity_bounds) = self.scene.compute_entity_bounds() {
            if entity_bounds.width() > 0.0 && entity_bounds.height() > 0.0 {
                let padded_bounds = Bounds::from_center_size(
                    entity_bounds.center(),
                    Vec2::new(entity_bounds.width() * 1.2, entity_bounds.height() * 1.2),
                );

                let screen_width = self.backend.width() as f32;
                let screen_height = self.backend.height() as f32;

                let zoom_x = screen_width / padded_bounds.width();
                let zoom_y = screen_height / padded_bounds.height();
                // Use AUTO_FIT_MIN_ZOOM to prevent zooming out so far that
                // LOD culling removes all entities from the visualization
                let zoom = zoom_x.min(zoom_y).clamp(AUTO_FIT_MIN_ZOOM, 1000.0);

                self.camera.jump_to(padded_bounds.center());
                self.camera.set_zoom(zoom);
            }
        }
    }

    /// Smoothly adjusts camera to keep all content visible (called each frame when `auto_fit` is on).
    fn auto_fit_camera(&mut self, dt: f32) {
        let Some(entity_bounds) = self.scene.compute_entity_bounds() else {
            return;
        };

        if entity_bounds.width() <= 0.0 || entity_bounds.height() <= 0.0 {
            return;
        }

        // Add padding around content (20%)
        let padded_bounds = Bounds::from_center_size(
            entity_bounds.center(),
            Vec2::new(entity_bounds.width() * 1.2, entity_bounds.height() * 1.2),
        );

        let screen_width = self.backend.width() as f32;
        let screen_height = self.backend.height() as f32;

        // Calculate the zoom needed to fit all content
        // Use AUTO_FIT_MIN_ZOOM to prevent zooming out so far that
        // LOD culling removes all entities from the visualization
        let zoom_x = screen_width / padded_bounds.width();
        let zoom_y = screen_height / padded_bounds.height();
        let target_zoom = zoom_x.min(zoom_y).clamp(AUTO_FIT_MIN_ZOOM, 1000.0);

        let current_zoom = self.camera.zoom();

        // Only zoom out, never zoom in automatically (let user control zoom in)
        // Also only adjust if we need to zoom out significantly (5% threshold)
        if target_zoom < current_zoom * 0.95 {
            // Smooth interpolation toward target zoom
            // Use a rate that feels natural - faster when far from target
            let zoom_rate = 2.0; // How fast to adjust
            let t = (zoom_rate * dt).min(0.15); // Cap max adjustment per frame
            let new_zoom = current_zoom + (target_zoom - current_zoom) * t;
            self.camera.set_zoom(new_zoom);
        }

        // Smoothly pan toward content center
        let target_center = padded_bounds.center();
        let current_center = self.camera.position();
        let distance = (target_center - current_center).length();

        // Only pan if content center is significantly off-screen
        if distance > 10.0 {
            let pan_rate = 2.0;
            let t = (pan_rate * dt).min(0.15);
            let new_center = current_center + (target_center - current_center) * t;
            self.camera.jump_to(new_center);
        }
    }

    /// Renders the current frame to the canvas.
    fn render(&mut self) {
        if self.backend.is_context_lost() {
            return;
        }

        let visible_bounds = self.camera.visible_bounds();

        // Update GPU culling bounds if enabled (wgpu only)
        #[cfg(target_arch = "wasm32")]
        if self.should_use_gpu_culling() {
            if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
                wgpu_renderer.set_cull_bounds(
                    visible_bounds.min.x,
                    visible_bounds.min.y,
                    visible_bounds.max.x,
                    visible_bounds.max.y,
                );
            }
        }

        // Get dimensions before borrowing renderer mutably (for watermark)
        let screen_width = self.backend.width() as f32;
        let screen_height = self.backend.height() as f32;

        let renderer = self.backend.as_renderer_mut();
        renderer.begin_frame();
        renderer.clear(self.settings.display.background_color);
        let camera_zoom = self.camera.zoom();

        // Populate visibility buffers using spatial culling for O(log n) query instead of O(n).
        // Use expanded bounds (200 world units margin) to ensure entities near screen edges
        // don't pop in/out during zoom/pan. LOD culling in render_* functions handles
        // sub-pixel entities for additional performance gains at extreme zoom levels.
        let expanded_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 200.0);
        self.scene.visible_entities_into(
            &expanded_bounds,
            &mut self.visible_dirs_buf,
            &mut self.visible_files_buf,
            &mut self.visible_users_buf,
        );

        // O(1) active action count instead of O(n) filtering
        let active_actions = self.scene.active_action_count();

        self.render_stats.update(
            self.visible_files_buf.len(),
            self.visible_users_buf.len(),
            self.visible_dirs_buf.len(),
            active_actions,
            self.scene.file_count()
                + self.scene.user_count()
                + self.scene.directories().len()
                + self.scene.actions().len(),
            if self.renderer_type == RendererType::WebGl2 {
                6
            } else {
                self.visible_dirs_buf.len() * 2
                    + self.visible_files_buf.len()
                    + active_actions * 2
                    + self.visible_users_buf.len() * 3
            },
        );

        let ctx = RenderContext {
            visible_bounds,
            camera_zoom,
            use_curves: camera_zoom < 0.8,
            visible_dirs: &self.visible_dirs_buf,
            visible_files: &self.visible_files_buf,
            visible_users: &self.visible_users_buf,
            show_labels: self.show_labels,
            font_id: self.font_id,
            font_size: self.settings.display.font_size,
            // Branch rendering settings from layout config
            branch_depth_fade: self.settings.layout.branch_depth_fade,
            branch_opacity_max: self.settings.layout.branch_opacity_max,
        };

        render_directories(renderer, &ctx, &self.scene, &self.camera);
        render_directory_labels(renderer, &ctx, &self.scene, &self.camera);
        render_files(renderer, &ctx, &self.scene, &self.camera);
        render_actions(renderer, &ctx, &self.scene, &self.camera);
        render_users(renderer, &ctx, &self.scene, &self.camera);
        render_user_labels(renderer, &ctx, &self.scene, &self.camera);
        render_file_labels(
            renderer,
            &ctx,
            &self.scene,
            &self.camera,
            &mut self.file_label_candidates_buf,
            &mut self.label_placer,
        );

        // Render watermark overlay (screen-space, rendered last to be on top)
        render_watermark(
            renderer,
            &self.settings.overlay.watermark,
            self.font_id,
            screen_width,
            screen_height,
        );

        renderer.end_frame();
        self.backend.present();
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rource_math::Color;

    // ========================================================================
    // Existing Color Tests
    // ========================================================================

    #[test]
    fn test_color_from_hex() {
        let color = Color::from_hex(0x00FF_0000);
        assert!((color.r - 1.0).abs() < 0.01);
        assert!(color.g < 0.01);
        assert!(color.b < 0.01);
    }

    #[test]
    fn test_color_from_hex_green() {
        let color = Color::from_hex(0x0000_FF00);
        assert!(color.r < 0.01);
        assert!((color.g - 1.0).abs() < 0.01);
        assert!(color.b < 0.01);
    }

    #[test]
    fn test_color_from_hex_blue() {
        let color = Color::from_hex(0x0000_00FF);
        assert!(color.r < 0.01);
        assert!(color.g < 0.01);
        assert!((color.b - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_color_from_hex_white() {
        let color = Color::from_hex(0x00FF_FFFF);
        assert!((color.r - 1.0).abs() < 0.01);
        assert!((color.g - 1.0).abs() < 0.01);
        assert!((color.b - 1.0).abs() < 0.01);
    }

    // ========================================================================
    // Frame Timing Tests
    // ========================================================================

    #[test]
    fn test_compute_frame_dt_normal() {
        // 16.67ms between frames = 60 FPS
        let dt = compute_frame_dt(1016.67, 1000.0);
        assert!((dt - 0.01667).abs() < 0.001);
    }

    #[test]
    fn test_compute_frame_dt_first_frame() {
        // First frame (last_frame_time = 0) should return default 1/60
        let dt = compute_frame_dt(1000.0, 0.0);
        assert!((dt - 1.0 / 60.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_frame_dt_slow() {
        // 100ms between frames = 10 FPS
        let dt = compute_frame_dt(1100.0, 1000.0);
        assert!((dt - 0.1).abs() < 0.001);
    }

    #[test]
    fn test_clamp_dt_normal() {
        assert!((clamp_dt(0.016, 0.1) - 0.016).abs() < 0.001);
    }

    #[test]
    fn test_clamp_dt_clamped() {
        assert!((clamp_dt(0.5, 0.1) - 0.1).abs() < 0.001);
    }

    #[test]
    fn test_max_frame_dt_constant() {
        assert!((MAX_FRAME_DT - 0.1).abs() < 0.001);
    }

    // ========================================================================
    // Auto-Fit Camera Tests
    // ========================================================================

    #[test]
    fn test_compute_target_zoom_fit_width() {
        // Bounds: 1000x500, Screen: 800x600
        // zoom_x = 800/1000 = 0.8, zoom_y = 600/500 = 1.2
        // Should use min (0.8)
        let zoom = compute_target_zoom(1000.0, 500.0, 800.0, 600.0, 0.01, 10.0);
        assert!((zoom - 0.8).abs() < 0.001);
    }

    #[test]
    fn test_compute_target_zoom_fit_height() {
        // Bounds: 500x1000, Screen: 800x600
        // zoom_x = 800/500 = 1.6, zoom_y = 600/1000 = 0.6
        // Should use min (0.6)
        let zoom = compute_target_zoom(500.0, 1000.0, 800.0, 600.0, 0.01, 10.0);
        assert!((zoom - 0.6).abs() < 0.001);
    }

    #[test]
    fn test_compute_target_zoom_clamped_min() {
        // Very large bounds, zoom would be very small
        let zoom = compute_target_zoom(100_000.0, 100_000.0, 800.0, 600.0, 0.01, 10.0);
        assert!((zoom - 0.01).abs() < 0.001);
    }

    #[test]
    fn test_compute_target_zoom_clamped_max() {
        // Very small bounds, zoom would be very large
        let zoom = compute_target_zoom(1.0, 1.0, 800.0, 600.0, 0.01, 10.0);
        assert!((zoom - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_target_zoom_zero_bounds() {
        // Invalid bounds should return min_zoom
        let zoom = compute_target_zoom(0.0, 0.0, 800.0, 600.0, 0.03, 10.0);
        assert!((zoom - 0.03).abs() < 0.001);
    }

    #[test]
    fn test_is_zoom_out_needed_yes() {
        // Target 0.5, current 1.0, threshold 0.95
        // 0.5 < 1.0 * 0.95 = 0.95 -> true
        assert!(is_zoom_out_needed(0.5, 1.0, 0.95));
    }

    #[test]
    fn test_is_zoom_out_needed_no() {
        // Target 0.96, current 1.0, threshold 0.95
        // 0.96 < 1.0 * 0.95 = 0.95 -> false
        assert!(!is_zoom_out_needed(0.96, 1.0, 0.95));
    }

    #[test]
    fn test_is_zoom_out_needed_equal() {
        // Target equals threshold boundary
        assert!(!is_zoom_out_needed(0.95, 1.0, 0.95));
    }

    #[test]
    fn test_compute_interpolation_factor_normal() {
        let t = compute_interpolation_factor(2.0, 0.016, 0.15);
        assert!((t - 0.032).abs() < 0.001);
    }

    #[test]
    fn test_compute_interpolation_factor_capped() {
        let t = compute_interpolation_factor(2.0, 0.5, 0.15);
        assert!((t - 0.15).abs() < 0.001);
    }

    #[test]
    fn test_compute_smooth_zoom() {
        // current=1.0, target=0.5, interpolating toward target
        let new_zoom = compute_smooth_zoom(1.0, 0.5, 2.0, 0.016, 0.15);
        // t = 0.032, new = 1.0 + (0.5 - 1.0) * 0.032 = 1.0 - 0.016 = 0.984
        assert!((new_zoom - 0.984).abs() < 0.001);
    }

    #[test]
    fn test_is_pan_needed_yes() {
        assert!(is_pan_needed(15.0, 10.0));
    }

    #[test]
    fn test_is_pan_needed_no() {
        assert!(!is_pan_needed(5.0, 10.0));
    }

    #[test]
    fn test_is_pan_needed_boundary() {
        assert!(!is_pan_needed(10.0, 10.0));
    }

    #[test]
    fn test_compute_smooth_position() {
        let current = Vec2::new(100.0, 100.0);
        let target = Vec2::new(200.0, 150.0);
        let new_pos = compute_smooth_position(current, target, 2.0, 0.016, 0.15);
        // t = 0.032
        // new_x = 100 + (200-100) * 0.032 = 103.2
        // new_y = 100 + (150-100) * 0.032 = 101.6
        assert!((new_pos.x - 103.2).abs() < 0.1);
        assert!((new_pos.y - 101.6).abs() < 0.1);
    }

    #[test]
    fn test_compute_padded_dimensions() {
        let (w, h) = compute_padded_dimensions(100.0, 50.0, 1.2);
        assert!((w - 120.0).abs() < 0.001);
        assert!((h - 60.0).abs() < 0.001);
    }

    #[test]
    fn test_auto_fit_padding_constant() {
        assert!((AUTO_FIT_PADDING - 1.2).abs() < 0.001);
    }

    #[test]
    fn test_zoom_adjustment_threshold_constant() {
        assert!((ZOOM_ADJUSTMENT_THRESHOLD - 0.95).abs() < 0.001);
    }

    #[test]
    fn test_pan_threshold_constant() {
        assert!((PAN_THRESHOLD - 10.0).abs() < 0.001);
    }

    // ========================================================================
    // GPU Feature Decision Tests
    // ========================================================================

    #[test]
    fn test_should_enable_gpu_physics_disabled() {
        assert!(!should_enable_gpu_physics(false, true, 1000, 500));
    }

    #[test]
    fn test_should_enable_gpu_physics_not_wgpu() {
        assert!(!should_enable_gpu_physics(true, false, 1000, 500));
    }

    #[test]
    fn test_should_enable_gpu_physics_below_threshold() {
        assert!(!should_enable_gpu_physics(true, true, 100, 500));
    }

    #[test]
    fn test_should_enable_gpu_physics_at_threshold() {
        assert!(should_enable_gpu_physics(true, true, 500, 500));
    }

    #[test]
    fn test_should_enable_gpu_physics_above_threshold() {
        assert!(should_enable_gpu_physics(true, true, 1000, 500));
    }

    #[test]
    fn test_should_enable_gpu_physics_zero_threshold() {
        // Zero threshold means always use when enabled
        assert!(should_enable_gpu_physics(true, true, 1, 0));
    }

    #[test]
    fn test_should_enable_gpu_culling_disabled() {
        assert!(!should_enable_gpu_culling(false, true, 15000, 10000));
    }

    #[test]
    fn test_should_enable_gpu_culling_not_wgpu() {
        assert!(!should_enable_gpu_culling(true, false, 15000, 10000));
    }

    #[test]
    fn test_should_enable_gpu_culling_below_threshold() {
        assert!(!should_enable_gpu_culling(true, true, 5000, 10000));
    }

    #[test]
    fn test_should_enable_gpu_culling_at_threshold() {
        assert!(should_enable_gpu_culling(true, true, 10000, 10000));
    }

    #[test]
    fn test_should_enable_gpu_culling_above_threshold() {
        assert!(should_enable_gpu_culling(true, true, 15000, 10000));
    }

    #[test]
    fn test_should_enable_gpu_culling_zero_threshold() {
        assert!(should_enable_gpu_culling(true, true, 1, 0));
    }

    #[test]
    fn test_compute_total_entity_count() {
        let total = compute_total_entity_count(1000, 50, 200);
        assert_eq!(total, 1250);
    }

    #[test]
    fn test_compute_total_entity_count_zero() {
        let total = compute_total_entity_count(0, 0, 0);
        assert_eq!(total, 0);
    }

    // ========================================================================
    // Playback Helper Tests
    // ========================================================================

    #[test]
    fn test_has_more_frames_playing() {
        assert!(has_more_frames(true, 0, 100));
    }

    #[test]
    fn test_has_more_frames_not_playing_more_commits() {
        assert!(has_more_frames(false, 50, 100));
    }

    #[test]
    fn test_has_more_frames_done() {
        assert!(!has_more_frames(false, 100, 100));
    }

    #[test]
    fn test_should_apply_commit_first() {
        // First commit (both 0)
        assert!(should_apply_commit(0, 0));
    }

    #[test]
    fn test_should_apply_commit_new() {
        assert!(should_apply_commit(5, 4));
    }

    #[test]
    fn test_should_apply_commit_already_applied() {
        assert!(!should_apply_commit(5, 5));
    }

    #[test]
    fn test_should_apply_commit_earlier() {
        // Current is before last_applied (e.g., seeking backward)
        assert!(!should_apply_commit(3, 5));
    }

    #[test]
    fn test_should_stop_playback_end() {
        assert!(should_stop_playback(100, 100));
    }

    #[test]
    fn test_should_stop_playback_past_end() {
        assert!(should_stop_playback(150, 100));
    }

    #[test]
    fn test_should_stop_playback_not_yet() {
        assert!(!should_stop_playback(50, 100));
    }
}
