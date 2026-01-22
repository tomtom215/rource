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
    render_user_labels, render_users, RenderContext, AUTO_FIT_MIN_ZOOM,
};

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

        let scene = Scene::new();

        let mut settings = Settings::default();
        settings.display.width = width;
        settings.display.height = height;

        let mut camera = Camera::new(width as f32, height as f32);
        camera.set_zoom_limits(0.01, 1000.0); // Support deep zoom for massive repos
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
            auto_fit: true, // Enabled by default for better UX
            perf_metrics: PerformanceMetrics::new(),
            render_stats: RenderStats::default(),
            // Pre-allocate visibility buffers for zero-allocation rendering
            visible_dirs_buf: Vec::with_capacity(1024),
            visible_files_buf: Vec::with_capacity(4096),
            visible_users_buf: Vec::with_capacity(256),
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

        // Calculate delta time
        let dt = if self.playback.last_frame_time() > 0.0 {
            ((timestamp - self.playback.last_frame_time()) / 1000.0) as f32
        } else {
            1.0 / 60.0
        };
        self.playback.set_last_frame_time(timestamp);

        // Clamp dt to avoid huge jumps
        let dt = dt.min(0.1);

        // Record frame time for FPS calculation
        self.perf_metrics.record_frame(dt);

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
        self.scene.update(dt);

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

        let renderer = self.backend.as_renderer_mut();
        renderer.begin_frame();
        renderer.clear(self.settings.display.background_color);

        let visible_bounds = self.camera.visible_bounds();
        let camera_zoom = self.camera.zoom();
        // Zero-allocation visibility query - reuses pre-allocated buffers
        self.scene.visible_entities_into(
            &visible_bounds,
            &mut self.visible_dirs_buf,
            &mut self.visible_files_buf,
            &mut self.visible_users_buf,
        );

        let active_actions = self
            .scene
            .actions()
            .iter()
            .filter(|a| !a.is_complete())
            .count();

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
        render_file_labels(renderer, &ctx, &self.scene, &self.camera);

        renderer.end_frame();
        self.backend.present();
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use rource_math::Color;

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
}
