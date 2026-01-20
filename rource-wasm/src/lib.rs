// Allow multiple versions of dependencies from workspace dependencies
#![allow(clippy::multiple_crate_versions)]

//! # Rource WASM
//!
//! WebAssembly bindings for Rource - software version control visualization.
//!
//! This crate provides JavaScript/TypeScript bindings to run Rource in a web browser.
//!
//! ## Rendering Backends
//!
//! Rource WASM supports two rendering backends:
//!
//! - **WebGL2** (default): GPU-accelerated rendering for best performance
//! - **Software**: Pure CPU rendering via `Canvas2D` for maximum compatibility
//!
//! The constructor automatically tries WebGL2 first and falls back to software
//! rendering if WebGL2 is unavailable.
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
//!     const rource = new Rource(canvas);
//!
//!     // Check which backend is being used
//!     console.log('Renderer:', rource.getRendererType());
//!
//!     // Load a git log
//!     const log = `1234567890|John Doe|A|src/main.rs
//! 1234567891|Jane Smith|M|src/lib.rs`;
//!     rource.loadCustomLog(log);
//!
//!     rource.play();
//! }
//! ```

mod interaction;
mod png;
mod rendering;

use std::fmt::Write as FmtWrite;
use std::path::PathBuf;

use interaction::{
    hit_test_directory, hit_test_file, hit_test_user, move_connected_entities_for_directory,
    move_connected_entities_for_file, move_connected_entities_for_user, DragTarget,
    ENTITY_HIT_RADIUS,
};
use png::write_png;
use rendering::{draw_action_beam, draw_avatar_shape, draw_curved_branch};

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement, ImageData};

use rource_core::camera::Camera;
use rource_core::config::Settings;
use rource_core::scene::{ActionType, Scene};
use rource_math::{Bounds, Color, Vec2};
use rource_render::{
    default_font, estimate_text_width, FontId, LabelPlacer, Renderer, SoftwareRenderer,
    WebGl2Renderer,
};
use rource_vcs::parser::{CustomParser, GitParser, Parser};
use rource_vcs::{Commit, FileAction};

/// Set up better panic messages for debugging in browser console.
#[wasm_bindgen(start)]
pub fn init_panic_hook() {
    console_error_panic_hook::set_once();
}

/// Convert VCS `FileAction` to Scene `ActionType`.
fn file_action_to_action_type(action: FileAction) -> ActionType {
    match action {
        FileAction::Create => ActionType::Create,
        FileAction::Modify => ActionType::Modify,
        FileAction::Delete => ActionType::Delete,
    }
}

// ============================================================================
// Renderer Backend Abstraction
// ============================================================================

/// The type of renderer being used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RendererType {
    /// WebGL2 GPU-accelerated renderer.
    WebGl2,
    /// Software CPU renderer with `Canvas2D` output.
    Software,
}

impl RendererType {
    fn as_str(self) -> &'static str {
        match self {
            Self::WebGl2 => "webgl2",
            Self::Software => "software",
        }
    }
}

/// Unified renderer backend that can be either WebGL2 or Software.
#[allow(clippy::large_enum_variant)] // WebGl2Renderer is larger, but boxing adds complexity for little gain
enum RendererBackend {
    WebGl2(WebGl2Renderer),
    Software {
        renderer: SoftwareRenderer,
        context: CanvasRenderingContext2d,
    },
}

impl RendererBackend {
    /// Creates a new renderer backend, trying WebGL2 first then falling back to Software.
    fn new(canvas: &HtmlCanvasElement) -> Result<(Self, RendererType), JsValue> {
        let width = canvas.width();
        let height = canvas.height();

        // Try WebGL2 first
        if let Ok(webgl2) = WebGl2Renderer::new(canvas) {
            web_sys::console::log_1(&"Rource: Using WebGL2 renderer".into());
            return Ok((Self::WebGl2(webgl2), RendererType::WebGl2));
        }

        // Fall back to software rendering
        web_sys::console::log_1(
            &"Rource: WebGL2 not available, falling back to software renderer".into(),
        );

        let context = canvas
            .get_context("2d")
            .map_err(|e| JsValue::from_str(&format!("Failed to get 2D context: {e:?}")))?
            .ok_or_else(|| JsValue::from_str("Canvas 2D context not available"))?
            .dyn_into::<CanvasRenderingContext2d>()?;

        let renderer = SoftwareRenderer::new(width, height);

        Ok((Self::Software { renderer, context }, RendererType::Software))
    }

    /// Returns the width of the renderer.
    fn width(&self) -> u32 {
        match self {
            Self::WebGl2(r) => r.width(),
            Self::Software { renderer, .. } => renderer.width(),
        }
    }

    /// Returns the height of the renderer.
    fn height(&self) -> u32 {
        match self {
            Self::WebGl2(r) => r.height(),
            Self::Software { renderer, .. } => renderer.height(),
        }
    }

    /// Resizes the renderer.
    fn resize(&mut self, width: u32, height: u32) {
        match self {
            Self::WebGl2(r) => r.resize(width, height),
            Self::Software { renderer, .. } => renderer.resize(width, height),
        }
    }

    /// Gets mutable reference to the underlying Renderer trait object.
    fn as_renderer_mut(&mut self) -> &mut dyn Renderer {
        match self {
            Self::WebGl2(r) => r,
            Self::Software { renderer, .. } => renderer,
        }
    }

    /// Called after `end_frame()` to copy software buffer to canvas (no-op for WebGL2).
    fn present(&self) {
        if let Self::Software { renderer, context } = self {
            let width = renderer.width();
            let height = renderer.height();
            let pixels = renderer.pixels();

            // Convert ARGB to RGBA for ImageData
            let mut rgba = vec![0u8; (width * height * 4) as usize];
            for (i, &pixel) in pixels.iter().enumerate() {
                let offset = i * 4;
                rgba[offset] = ((pixel >> 16) & 0xFF) as u8; // R
                rgba[offset + 1] = ((pixel >> 8) & 0xFF) as u8; // G
                rgba[offset + 2] = (pixel & 0xFF) as u8; // B
                rgba[offset + 3] = ((pixel >> 24) & 0xFF) as u8; // A
            }

            // Create ImageData and put it on the canvas
            if let Ok(image_data) = ImageData::new_with_u8_clamped_array_and_sh(
                wasm_bindgen::Clamped(&rgba),
                width,
                height,
            ) {
                let _ = context.put_image_data(&image_data, 0.0, 0.0);
            }
        }
        // WebGL2 renders directly to canvas, no copy needed
    }

    /// Returns true if the WebGL context is lost (always false for software renderer).
    ///
    /// When the context is lost, rendering operations should be skipped until
    /// the context is restored.
    fn is_context_lost(&self) -> bool {
        match self {
            Self::WebGl2(r) => r.is_context_lost(),
            Self::Software { .. } => false, // Software renderer never loses context
        }
    }

    /// Returns pixel data for screenshot (software only).
    fn pixels(&self) -> Option<&[u32]> {
        if let Self::Software { renderer, .. } = self {
            Some(renderer.pixels())
        } else {
            None
        }
    }

    /// Loads a font and returns its ID.
    fn load_font(&mut self, data: &[u8]) -> Option<FontId> {
        match self {
            Self::WebGl2(r) => r.load_font(data),
            Self::Software { renderer, .. } => renderer.load_font(data),
        }
    }

    /// Synchronizes CPU with GPU by waiting for all pending commands to complete.
    ///
    /// For WebGL2: calls `gl.finish()` to block until GPU is done.
    /// For Software: no-op (CPU rendering is inherently synchronous).
    ///
    /// Call this ONLY when you need to read from the canvas (screenshots, exports).
    /// Do NOT call every frame as it hurts performance.
    fn sync(&self) {
        if let Self::WebGl2(r) = self {
            r.sync();
        }
        // Software renderer is synchronous - no sync needed
    }
}

// ============================================================================
// Main Rource WASM API
// ============================================================================

/// Number of frame samples for FPS averaging.
const FRAME_SAMPLE_COUNT: usize = 60;

/// Performance metrics for FPS tracking and profiling.
#[derive(Debug, Clone)]
struct PerformanceMetrics {
    /// Rolling average of frame times (in seconds).
    frame_times: [f32; FRAME_SAMPLE_COUNT],
    /// Index into `frame_times` for ring buffer.
    frame_time_index: usize,
    /// Number of valid frame time samples.
    frame_time_count: usize,
    /// Last calculated FPS value.
    fps: f32,
    /// Last frame duration in milliseconds.
    frame_time_ms: f32,
    /// Total frames rendered.
    total_frames: u64,
    /// Time of initialization (for uptime tracking).
    start_time: f64,
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceMetrics {
    /// Creates a new performance metrics tracker.
    fn new() -> Self {
        Self {
            frame_times: [0.0; FRAME_SAMPLE_COUNT],
            frame_time_index: 0,
            frame_time_count: 0,
            fps: 0.0,
            frame_time_ms: 0.0,
            total_frames: 0,
            start_time: 0.0,
        }
    }

    /// Records a frame time sample and updates FPS calculation.
    fn record_frame(&mut self, dt: f32) {
        self.frame_times[self.frame_time_index] = dt;
        self.frame_time_index = (self.frame_time_index + 1) % FRAME_SAMPLE_COUNT;
        self.frame_time_count = (self.frame_time_count + 1).min(FRAME_SAMPLE_COUNT);
        self.total_frames += 1;
        self.frame_time_ms = dt * 1000.0;

        // Calculate rolling average FPS
        if self.frame_time_count > 0 {
            let sum: f32 = self.frame_times[..self.frame_time_count].iter().sum();
            let avg_dt = sum / self.frame_time_count as f32;
            self.fps = if avg_dt > 0.0 { 1.0 / avg_dt } else { 0.0 };
        }
    }
}

/// Render statistics for the current frame.
#[derive(Debug, Clone, Default)]
struct RenderStats {
    /// Number of visible files being rendered.
    visible_files: usize,
    /// Number of visible users being rendered.
    visible_users: usize,
    /// Number of visible directories being rendered.
    visible_directories: usize,
    /// Number of active action beams.
    active_actions: usize,
    /// Total entities in the scene.
    total_entities: usize,
    /// Estimated draw call count.
    draw_calls: usize,
}

/// The main Rource visualization controller for browser usage.
#[wasm_bindgen]
pub struct Rource {
    /// Canvas element
    canvas: HtmlCanvasElement,

    /// Renderer backend (WebGL2 or Software)
    backend: RendererBackend,

    /// Type of renderer being used
    renderer_type: RendererType,

    /// Scene graph containing all entities
    scene: Scene,

    /// Camera for view control
    camera: Camera,

    /// Visualization settings
    settings: Settings,

    /// Loaded commits
    commits: Vec<Commit>,

    /// Current commit index
    current_commit: usize,

    /// Accumulated time since last commit
    accumulated_time: f32,

    /// Is playback active
    playing: bool,

    /// Last frame timestamp (ms)
    last_frame_time: f64,

    /// Last applied commit index
    last_applied_commit: usize,

    /// Mouse state for interaction
    mouse_x: f32,
    mouse_y: f32,
    mouse_down: bool,
    drag_start_x: f32,
    drag_start_y: f32,
    camera_start_x: f32,
    camera_start_y: f32,

    /// Currently dragged entity (if any).
    drag_target: Option<DragTarget>,

    /// Offset from drag start to entity center (for smooth dragging).
    drag_offset: Vec2,

    /// Last position of dragged entity (for calculating movement delta).
    drag_last_pos: Vec2,

    /// Font ID for text rendering
    font_id: Option<FontId>,

    /// Whether to show labels (user names, file names)
    show_labels: bool,

    /// Performance metrics (FPS tracking, frame timing).
    perf_metrics: PerformanceMetrics,

    /// Render statistics for the current frame.
    render_stats: RenderStats,
}

#[wasm_bindgen]
impl Rource {
    /// Creates a new Rource instance attached to a canvas element.
    ///
    /// Automatically tries WebGL2 first, falling back to software rendering if unavailable.
    ///
    /// # Arguments
    ///
    /// * `canvas` - The HTML canvas element to render to
    #[wasm_bindgen(constructor)]
    pub fn new(canvas: HtmlCanvasElement) -> Result<Self, JsValue> {
        let width = canvas.width();
        let height = canvas.height();

        let (mut backend, renderer_type) = RendererBackend::new(&canvas)?;

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
        camera.jump_to(Vec2::ZERO);

        Ok(Self {
            canvas,
            backend,
            renderer_type,
            scene,
            camera,
            settings,
            commits: Vec::new(),
            current_commit: 0,
            accumulated_time: 0.0,
            playing: false,
            last_frame_time: 0.0,
            last_applied_commit: 0,
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
            show_labels: true, // Labels enabled by default
            perf_metrics: PerformanceMetrics::new(),
            render_stats: RenderStats::default(),
        })
    }

    /// Returns the type of renderer being used ("webgl2" or "software").
    #[wasm_bindgen(js_name = getRendererType)]
    pub fn get_renderer_type(&self) -> String {
        self.renderer_type.as_str().to_string()
    }

    /// Returns true if using WebGL2 renderer.
    #[wasm_bindgen(js_name = isWebGL2)]
    pub fn is_webgl2(&self) -> bool {
        self.renderer_type == RendererType::WebGl2
    }

    /// Returns true if the WebGL context is lost.
    ///
    /// This can happen when the GPU is reset, the browser tab is backgrounded
    /// for a long time, or system resources are exhausted. When the context is
    /// lost, rendering operations are skipped automatically.
    ///
    /// Software renderer always returns false (it never loses context).
    #[wasm_bindgen(js_name = isContextLost)]
    pub fn is_context_lost(&self) -> bool {
        self.backend.is_context_lost()
    }

    /// Attempts to recover from a lost WebGL context.
    ///
    /// Returns true if recovery was successful or if context was not lost.
    /// Returns false if recovery failed (e.g., WebGL is permanently unavailable).
    ///
    /// After a successful recovery, the visualization will continue from where
    /// it left off on the next frame.
    #[wasm_bindgen(js_name = recoverContext)]
    pub fn recover_context(&mut self) -> bool {
        if let RendererBackend::WebGl2(ref mut renderer) = self.backend {
            renderer.recover_context().is_ok()
        } else {
            // Software renderer never loses context
            true
        }
    }

    /// Loads commits from custom pipe-delimited format.
    ///
    /// Format: `timestamp|author|action|path` per line
    /// - timestamp: Unix timestamp
    /// - author: Committer name
    /// - action: A=add, M=modify, D=delete
    /// - path: File path
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript,ignore
    /// rource.loadCustomLog("1234567890|John Doe|A|src/main.rs\n1234567891|Jane|M|src/lib.rs");
    /// ```
    #[wasm_bindgen(js_name = loadCustomLog)]
    pub fn load_custom_log(&mut self, log: &str) -> Result<usize, JsValue> {
        let parser = CustomParser::new();
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
    /// Expected format is `git log --pretty=format:... --name-status`
    #[wasm_bindgen(js_name = loadGitLog)]
    pub fn load_git_log(&mut self, log: &str) -> Result<usize, JsValue> {
        let parser = GitParser::new();
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

    /// Starts playback.
    pub fn play(&mut self) {
        self.playing = true;
        self.last_frame_time = 0.0;
    }

    /// Pauses playback.
    pub fn pause(&mut self) {
        self.playing = false;
    }

    /// Returns whether playback is active.
    #[wasm_bindgen(js_name = isPlaying)]
    pub fn is_playing(&self) -> bool {
        self.playing
    }

    /// Toggles play/pause state.
    #[wasm_bindgen(js_name = togglePlay)]
    pub fn toggle_play(&mut self) {
        if self.playing {
            self.pause();
        } else {
            self.play();
        }
    }

    /// Seeks to a specific commit index.
    pub fn seek(&mut self, commit_index: usize) {
        if commit_index < self.commits.len() {
            // Reset scene and replay commits up to the target
            self.scene = Scene::new();
            self.current_commit = 0;
            self.last_applied_commit = 0;

            for i in 0..=commit_index {
                if i < self.commits.len() {
                    self.apply_vcs_commit(&self.commits[i].clone());
                }
            }

            self.current_commit = commit_index;
            self.last_applied_commit = commit_index;
            self.accumulated_time = 0.0;

            // Pre-warm the scene
            for _ in 0..30 {
                self.scene.update(1.0 / 60.0);
            }

            // Position camera
            self.fit_camera_to_content();
        }
    }

    /// Returns the current commit index.
    #[wasm_bindgen(js_name = currentCommit)]
    pub fn current_commit(&self) -> usize {
        self.current_commit
    }

    /// Returns the timestamp (Unix epoch seconds) for a commit at the given index.
    ///
    /// Returns 0 if the index is out of bounds.
    /// Note: Returns f64 instead of i64 to avoid `BigInt` conversion issues in JavaScript.
    #[wasm_bindgen(js_name = getCommitTimestamp)]
    pub fn get_commit_timestamp(&self, index: usize) -> f64 {
        self.commits.get(index).map_or(0.0, |c| c.timestamp as f64)
    }

    /// Returns the author name for a commit at the given index.
    ///
    /// Returns empty string if the index is out of bounds.
    #[wasm_bindgen(js_name = getCommitAuthor)]
    pub fn get_commit_author(&self, index: usize) -> String {
        self.commits
            .get(index)
            .map_or_else(String::new, |c| c.author.clone())
    }

    /// Returns the number of files changed in a commit at the given index.
    ///
    /// Returns 0 if the index is out of bounds.
    #[wasm_bindgen(js_name = getCommitFileCount)]
    pub fn get_commit_file_count(&self, index: usize) -> usize {
        self.commits.get(index).map_or(0, |c| c.files.len())
    }

    /// Returns the date range of all commits as a JSON object.
    ///
    /// Returns: `{ "startTimestamp": i64, "endTimestamp": i64 }` or null if no commits.
    #[wasm_bindgen(js_name = getDateRange)]
    pub fn get_date_range(&self) -> Option<String> {
        if self.commits.is_empty() {
            return None;
        }

        let start = self.commits.first().map_or(0, |c| c.timestamp);
        let end = self.commits.last().map_or(0, |c| c.timestamp);

        Some(format!(
            r#"{{"startTimestamp":{start},"endTimestamp":{end}}}"#
        ))
    }

    /// Sets playback speed (seconds per day of repository history).
    ///
    /// The speed is clamped between 1.0 (10x, fastest) and 1000.0 (very slow) seconds per day.
    /// NaN, infinite, and non-positive values are replaced with the default of 10.0.
    ///
    /// The formula `seconds_per_commit = seconds_per_day / 10.0` means:
    /// - At speed=1.0 (10x): 0.1s per commit = ~6 frames at 60fps (acceptable)
    /// - At speed=0.1 (100x): 0.01s per commit = ~1.7 commits/frame (too fast!)
    #[wasm_bindgen(js_name = setSpeed)]
    pub fn set_speed(&mut self, seconds_per_day: f32) {
        // Handle NaN, infinity, and non-positive values by using default speed
        let speed = if seconds_per_day.is_finite() && seconds_per_day > 0.0 {
            seconds_per_day
        } else {
            10.0 // Default speed
        };
        // Clamp to reasonable range: 1.0 (10x fastest) to 1000 (0.01x slowest) seconds per day
        // Minimum of 1.0 ensures at least ~6 frames per commit at 60fps
        self.settings.playback.seconds_per_day = speed.clamp(1.0, 1000.0);
    }

    /// Gets the current playback speed.
    #[wasm_bindgen(js_name = getSpeed)]
    pub fn get_speed(&self) -> f32 {
        self.settings.playback.seconds_per_day
    }

    /// Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
    pub fn zoom(&mut self, factor: f32) {
        let new_zoom = (self.camera.zoom() * factor).clamp(0.01, 100.0);
        self.camera.set_zoom(new_zoom);
    }

    /// Zooms the camera toward a specific screen point.
    ///
    /// This keeps the point under the mouse cursor stationary while zooming,
    /// making it easier to zoom into specific areas of the visualization.
    #[wasm_bindgen(js_name = zoomToward)]
    pub fn zoom_toward(&mut self, screen_x: f32, screen_y: f32, factor: f32) {
        let screen_point = Vec2::new(screen_x, screen_y);

        // Get world position before zoom
        let world_before = self.camera.screen_to_world(screen_point);

        // Apply zoom
        let new_zoom = (self.camera.zoom() * factor).clamp(0.01, 100.0);
        self.camera.set_zoom(new_zoom);

        // Get world position after zoom
        let world_after = self.camera.screen_to_world(screen_point);

        // Adjust camera position so the world point stays at the same screen position
        let diff = world_before - world_after;
        let new_pos = self.camera.position() + diff;
        self.camera.jump_to(new_pos);
    }

    /// Pans the camera by the given delta in screen pixels.
    pub fn pan(&mut self, dx: f32, dy: f32) {
        let world_delta = Vec2::new(dx, dy) / self.camera.zoom();
        let new_pos = self.camera.position() - world_delta;
        self.camera.jump_to(new_pos);
    }

    /// Resets the camera to fit all content.
    #[wasm_bindgen(js_name = resetCamera)]
    pub fn reset_camera(&mut self) {
        self.fit_camera_to_content();
    }

    /// Resizes the canvas and renderer.
    pub fn resize(&mut self, width: u32, height: u32) {
        self.canvas.set_width(width);
        self.canvas.set_height(height);
        self.backend.resize(width, height);
        self.camera = Camera::new(width as f32, height as f32);
        self.settings.display.width = width;
        self.settings.display.height = height;
    }

    /// Sets whether to show bloom effect.
    #[wasm_bindgen(js_name = setBloom)]
    pub fn set_bloom(&mut self, enabled: bool) {
        self.settings.display.bloom_enabled = enabled;
    }

    /// Sets the background color (hex string like "#000000" or "000000").
    #[wasm_bindgen(js_name = setBackgroundColor)]
    pub fn set_background_color(&mut self, hex: &str) {
        // Strip leading # if present
        let hex = hex.trim_start_matches('#');
        if hex.len() == 6 {
            if let Ok(val) = u32::from_str_radix(hex, 16) {
                self.settings.display.background_color = Color::from_hex(val);
            }
        }
    }

    /// Sets whether to show labels (user names, file names).
    #[wasm_bindgen(js_name = setShowLabels)]
    pub fn set_show_labels(&mut self, show: bool) {
        self.show_labels = show;
    }

    /// Gets whether labels are being shown.
    #[wasm_bindgen(js_name = getShowLabels)]
    pub fn get_show_labels(&self) -> bool {
        self.show_labels
    }

    /// Handles mouse down events.
    ///
    /// Checks for entity under cursor first. If an entity is found, starts dragging it.
    /// Otherwise, starts camera panning.
    #[wasm_bindgen(js_name = onMouseDown)]
    pub fn on_mouse_down(&mut self, x: f32, y: f32) {
        self.mouse_down = true;
        self.drag_start_x = x;
        self.drag_start_y = y;
        self.mouse_x = x;
        self.mouse_y = y;

        // Convert screen position to world position
        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);

        // Try to find an entity at this position (users have priority over files)
        let hit_radius = ENTITY_HIT_RADIUS / self.camera.zoom();

        // Check users first (they're larger and more important to interact with)
        if let Some(drag_target) = hit_test_user(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
            // Calculate offset from click point to entity center
            if let DragTarget::User(user_id) = drag_target {
                if let Some(user) = self.scene.get_user(user_id) {
                    self.drag_offset = user.position() - world_pos;
                    self.drag_last_pos = user.position();
                }
            }
            return;
        }

        // Check files
        if let Some(drag_target) = hit_test_file(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
            // Calculate offset from click point to entity center
            if let DragTarget::File(file_id) = drag_target {
                if let Some(file) = self.scene.get_file_mut(file_id) {
                    self.drag_offset = file.position() - world_pos;
                    self.drag_last_pos = file.position();
                    // Pin the file to prevent layout updates from moving it
                    file.set_pinned(true);
                }
            }
            return;
        }

        // Check directories (lowest priority - users and files are easier to target)
        if let Some(drag_target) = hit_test_directory(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
            // Calculate offset from click point to entity center
            if let DragTarget::Directory(dir_id) = drag_target {
                if let Some(dir) = self.scene.directories().get(dir_id) {
                    self.drag_offset = dir.position() - world_pos;
                    self.drag_last_pos = dir.position();
                }
            }
            return;
        }

        // No entity hit, set up for camera panning
        self.drag_target = None;
        self.camera_start_x = self.camera.position().x;
        self.camera_start_y = self.camera.position().y;
    }

    /// Handles mouse up events.
    #[wasm_bindgen(js_name = onMouseUp)]
    pub fn on_mouse_up(&mut self) {
        // Unpin file if we were dragging one
        if let Some(DragTarget::File(file_id)) = self.drag_target {
            if let Some(file) = self.scene.get_file_mut(file_id) {
                file.set_pinned(false);
            }
        }

        self.mouse_down = false;
        self.drag_target = None;
        self.drag_offset = Vec2::ZERO;
        self.drag_last_pos = Vec2::ZERO;
    }

    /// Handles mouse move events.
    ///
    /// If dragging an entity, updates its position and applies force-directed
    /// movement to connected entities. Otherwise, pans the camera.
    #[wasm_bindgen(js_name = onMouseMove)]
    pub fn on_mouse_move(&mut self, x: f32, y: f32) {
        self.mouse_x = x;
        self.mouse_y = y;

        if !self.mouse_down {
            return;
        }

        // Convert screen position to world position
        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);

        // If dragging an entity, move it and connected entities
        if let Some(drag_target) = self.drag_target {
            let new_entity_pos = world_pos + self.drag_offset;

            // Calculate movement delta from last position
            let delta = new_entity_pos - self.drag_last_pos;

            match drag_target {
                DragTarget::User(user_id) => {
                    // Move the user and clear its target so it doesn't snap back
                    if let Some(user) = self.scene.get_user_mut(user_id) {
                        user.set_position(new_entity_pos);
                        user.clear_target();
                    }

                    // Move connected files (files with active actions from this user)
                    move_connected_entities_for_user(&mut self.scene, user_id, delta);
                }
                DragTarget::File(file_id) => {
                    // Get file info before moving
                    let dir_id = self
                        .scene
                        .get_file(file_id)
                        .map(rource_core::scene::FileNode::directory);

                    // Move the file and update its target so it doesn't snap back
                    if let Some(file) = self.scene.get_file_mut(file_id) {
                        file.set_position(new_entity_pos);
                        file.set_target(new_entity_pos);
                    }

                    // Move connected entities (siblings and parent directory)
                    if let Some(dir_id) = dir_id {
                        move_connected_entities_for_file(&mut self.scene, file_id, dir_id, delta);
                    }
                }
                DragTarget::Directory(dir_id) => {
                    // Move the directory and zero its velocity so physics doesn't fight
                    if let Some(dir) = self.scene.directories_mut().get_mut(dir_id) {
                        dir.set_position(new_entity_pos);
                        dir.set_velocity(Vec2::ZERO);
                    }

                    // Move connected entities (children and files in this directory)
                    move_connected_entities_for_directory(&mut self.scene, dir_id, delta);
                }
            }

            // Update last position for next delta calculation
            self.drag_last_pos = new_entity_pos;

            // Mark bounds dirty since entities moved
            self.scene.invalidate_bounds_cache();
        } else {
            // Camera panning
            let dx = x - self.drag_start_x;
            let dy = y - self.drag_start_y;
            let world_delta = Vec2::new(dx, dy) / self.camera.zoom();
            let new_pos = Vec2::new(self.camera_start_x, self.camera_start_y) - world_delta;
            self.camera.jump_to(new_pos);
        }
    }

    /// Handles mouse wheel events for zooming toward the mouse position.
    ///
    /// Uses a smooth, proportional zoom based on scroll amount.
    /// Zooms toward the mouse position so the content under the cursor stays in place.
    #[wasm_bindgen(js_name = onWheel)]
    pub fn on_wheel(&mut self, delta_y: f32, mouse_x: f32, mouse_y: f32) {
        // Normalize delta_y - different browsers/devices report different ranges
        // Typical values: ~100 for line mode, ~3 for pixel mode (trackpad)
        let normalized_delta = delta_y / 100.0;

        // Clamp to reasonable range to prevent huge jumps
        let clamped_delta = normalized_delta.clamp(-2.0, 2.0);

        // Convert to zoom factor: negative delta = zoom in, positive = zoom out
        // Use a gentler factor for smoother zooming
        let factor = 1.0 - (clamped_delta * 0.08);

        // Zoom toward the mouse position
        self.zoom_toward(mouse_x, mouse_y, factor);
    }

    /// Steps forward to the next commit.
    #[wasm_bindgen(js_name = stepForward)]
    pub fn step_forward(&mut self) {
        if self.current_commit < self.commits.len().saturating_sub(1) {
            self.seek(self.current_commit + 1);
        }
    }

    /// Steps backward to the previous commit.
    #[wasm_bindgen(js_name = stepBackward)]
    pub fn step_backward(&mut self) {
        if self.current_commit > 0 {
            self.seek(self.current_commit - 1);
        }
    }

    /// Handles keyboard events.
    #[wasm_bindgen(js_name = onKeyDown)]
    pub fn on_key_down(&mut self, key: &str) {
        match key {
            " " | "Space" => self.toggle_play(),
            "+" | "=" => self.zoom(1.2),
            "-" | "_" => self.zoom(0.8),
            "ArrowUp" => self.pan(0.0, -50.0),
            "ArrowDown" => self.pan(0.0, 50.0),
            "ArrowLeft" => self.pan(-50.0, 0.0),
            "ArrowRight" => self.pan(50.0, 0.0),
            "r" | "R" => self.reset_camera(),
            "l" | "L" => self.show_labels = !self.show_labels,
            "[" => self.set_speed(self.settings.playback.seconds_per_day * 0.5),
            "]" => self.set_speed(self.settings.playback.seconds_per_day * 2.0),
            "," | "<" => self.step_backward(),
            "." | ">" => self.step_forward(),
            "Home" => self.seek(0),
            "End" => {
                if !self.commits.is_empty() {
                    let last = self.commits.len().saturating_sub(1);
                    self.seek(last);
                }
            }
            _ => {}
        }
    }

    /// Updates and renders a single frame.
    ///
    /// # Arguments
    ///
    /// * `timestamp` - Current time in milliseconds (from requestAnimationFrame)
    ///
    /// Returns true if there are more frames to render.
    pub fn frame(&mut self, timestamp: f64) -> bool {
        // Initialize start time on first frame
        if self.perf_metrics.start_time == 0.0 {
            self.perf_metrics.start_time = timestamp;
        }

        // Calculate delta time
        let dt = if self.last_frame_time > 0.0 {
            ((timestamp - self.last_frame_time) / 1000.0) as f32
        } else {
            1.0 / 60.0
        };
        self.last_frame_time = timestamp;

        // Clamp dt to avoid huge jumps
        let dt = dt.min(0.1);

        // Record frame time for FPS calculation
        self.perf_metrics.record_frame(dt);

        // Update simulation if playing
        if self.playing && !self.commits.is_empty() {
            self.accumulated_time += dt;

            // Calculate time per commit based on seconds_per_day
            let seconds_per_commit = self.settings.playback.seconds_per_day / 10.0;

            // Apply commits based on accumulated time
            while self.accumulated_time >= seconds_per_commit
                && self.current_commit < self.commits.len()
            {
                if self.current_commit > self.last_applied_commit
                    || (self.last_applied_commit == 0 && self.current_commit == 0)
                {
                    let commit = self.commits[self.current_commit].clone();
                    self.apply_vcs_commit(&commit);
                    self.last_applied_commit = self.current_commit;
                }
                self.accumulated_time -= seconds_per_commit;
                self.current_commit += 1;
            }

            // Check if we're done
            if self.current_commit >= self.commits.len() {
                self.playing = false;
            }
        }

        // Update scene physics and animations
        self.scene.update(dt);

        // Update camera
        self.camera.update(dt);

        // Render the frame
        self.render();

        // Return true if there's more to show
        self.playing || self.current_commit < self.commits.len()
    }

    // ========================================================================
    // Performance Metrics API
    // ========================================================================

    /// Returns the current frames per second (rolling average over 60 frames).
    #[wasm_bindgen(js_name = getFps)]
    pub fn get_fps(&self) -> f32 {
        self.perf_metrics.fps
    }

    /// Returns the last frame time in milliseconds.
    #[wasm_bindgen(js_name = getFrameTimeMs)]
    pub fn get_frame_time_ms(&self) -> f32 {
        self.perf_metrics.frame_time_ms
    }

    /// Returns the total number of frames rendered since initialization.
    /// Note: Returns f64 instead of u64 to avoid `BigInt` conversion issues in JavaScript.
    #[wasm_bindgen(js_name = getTotalFrames)]
    pub fn get_total_frames(&self) -> f64 {
        self.perf_metrics.total_frames as f64
    }

    /// Returns the uptime in seconds since initialization.
    #[wasm_bindgen(js_name = getUptime)]
    pub fn get_uptime(&self) -> f64 {
        if self.perf_metrics.start_time > 0.0 {
            (self.last_frame_time - self.perf_metrics.start_time) / 1000.0
        } else {
            0.0
        }
    }

    // ========================================================================
    // Render Statistics API
    // ========================================================================

    /// Returns the number of visible files currently being rendered.
    #[wasm_bindgen(js_name = getVisibleFiles)]
    pub fn get_visible_files(&self) -> usize {
        self.render_stats.visible_files
    }

    /// Returns the number of visible users currently being rendered.
    #[wasm_bindgen(js_name = getVisibleUsers)]
    pub fn get_visible_users(&self) -> usize {
        self.render_stats.visible_users
    }

    /// Returns the number of visible directories currently being rendered.
    #[wasm_bindgen(js_name = getVisibleDirectories)]
    pub fn get_visible_directories(&self) -> usize {
        self.render_stats.visible_directories
    }

    /// Returns the number of active action beams.
    #[wasm_bindgen(js_name = getActiveActions)]
    pub fn get_active_actions(&self) -> usize {
        self.render_stats.active_actions
    }

    /// Returns the total number of entities in the scene.
    #[wasm_bindgen(js_name = getTotalEntities)]
    pub fn get_total_entities(&self) -> usize {
        self.render_stats.total_entities
    }

    /// Returns the estimated draw call count for the last frame.
    #[wasm_bindgen(js_name = getDrawCalls)]
    pub fn get_draw_calls(&self) -> usize {
        self.render_stats.draw_calls
    }

    /// Returns the canvas width in pixels.
    #[wasm_bindgen(js_name = getCanvasWidth)]
    pub fn get_canvas_width(&self) -> u32 {
        self.backend.width()
    }

    /// Returns the canvas height in pixels.
    #[wasm_bindgen(js_name = getCanvasHeight)]
    pub fn get_canvas_height(&self) -> u32 {
        self.backend.height()
    }

    /// Returns the current zoom level.
    #[wasm_bindgen(js_name = getZoom)]
    pub fn get_zoom(&self) -> f32 {
        self.camera.zoom()
    }

    /// Returns the total number of files in the scene.
    #[wasm_bindgen(js_name = getTotalFiles)]
    pub fn get_total_files(&self) -> usize {
        self.scene.file_count()
    }

    /// Returns the total number of users in the scene.
    #[wasm_bindgen(js_name = getTotalUsers)]
    pub fn get_total_users(&self) -> usize {
        self.scene.user_count()
    }

    /// Returns author data as a JSON string array.
    ///
    /// Each entry contains: `{ "name": "Author Name", "color": "#rrggbb", "commits": count }`
    /// Sorted by commit count (most active first).
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript,ignore
    /// const authorsJson = rource.getAuthors();
    /// const authors = JSON.parse(authorsJson);
    /// authors.forEach(a => console.log(a.name, a.color, a.commits));
    /// ```
    #[wasm_bindgen(js_name = getAuthors)]
    pub fn get_authors(&self) -> String {
        let mut authors: Vec<(&str, Color, usize)> = self
            .scene
            .users()
            .values()
            .map(|user| {
                // Count commits by this author
                let commit_count = self
                    .commits
                    .iter()
                    .filter(|c| c.author == user.name())
                    .count();
                (user.name(), user.color(), commit_count)
            })
            .collect();

        // Sort by commit count descending
        authors.sort_by(|a, b| b.2.cmp(&a.2));

        // Build JSON manually to avoid serde dependency
        let mut json = String::from("[");
        for (i, (name, color, commits)) in authors.iter().enumerate() {
            if i > 0 {
                json.push(',');
            }
            let r = (color.r * 255.0) as u8;
            let g = (color.g * 255.0) as u8;
            let b = (color.b * 255.0) as u8;
            // Escape quotes in name for JSON safety
            let escaped_name = name.replace('\\', "\\\\").replace('"', "\\\"");
            let _ = FmtWrite::write_fmt(
                &mut json,
                format_args!("{{\"name\":\"{escaped_name}\",\"color\":\"#{r:02x}{g:02x}{b:02x}\",\"commits\":{commits}}}")
            );
        }
        json.push(']');
        json
    }

    /// Returns the color for a given author name as a hex string (e.g., "#ff5500").
    ///
    /// This uses the same deterministic color generation as the visualization,
    /// so colors will match what's displayed on screen.
    #[wasm_bindgen(js_name = getAuthorColor)]
    pub fn get_author_color(&self, name: &str) -> String {
        use rource_core::scene::User;
        let color = User::color_from_name(name);
        format!(
            "#{:02x}{:02x}{:02x}",
            (color.r * 255.0) as u8,
            (color.g * 255.0) as u8,
            (color.b * 255.0) as u8
        )
    }

    /// Forces a render without updating simulation (useful for static views).
    ///
    /// This method ensures the viewport is synchronized with the current canvas
    /// dimensions before rendering, which is critical for screenshots and exports.
    ///
    /// Unlike the normal render path, this also calls `sync()` to ensure all GPU
    /// commands complete before returning. This is necessary for `canvas.toBlob()`
    /// to capture a complete frame.
    #[wasm_bindgen(js_name = forceRender)]
    pub fn force_render(&mut self) {
        // Ensure the backend dimensions match the canvas dimensions
        // This is critical after canvas resize operations
        let canvas_width = self.canvas.width();
        let canvas_height = self.canvas.height();

        // Sync backend if dimensions don't match
        if self.backend.width() != canvas_width || self.backend.height() != canvas_height {
            self.backend.resize(canvas_width, canvas_height);
        }

        self.render();

        // Synchronize GPU to ensure frame is complete before returning.
        // This is critical for screenshot/export operations that read from canvas.
        self.backend.sync();
    }

    /// Captures a screenshot and returns it as PNG data (`Uint8Array`).
    ///
    /// Note: This only works with the software renderer. For WebGL2, returns an error.
    #[wasm_bindgen(js_name = captureScreenshot)]
    pub fn capture_screenshot(&self) -> Result<Vec<u8>, JsValue> {
        if let Some(pixels) = self.backend.pixels() {
            let width = self.backend.width();
            let height = self.backend.height();

            let mut png_data = Vec::new();
            write_png(&mut png_data, pixels, width, height)
                .map_err(|e| JsValue::from_str(&format!("Failed to create PNG: {e}")))?;

            Ok(png_data)
        } else {
            Err(JsValue::from_str(
                "Screenshot not supported with WebGL2 renderer",
            ))
        }
    }

    // ========================================================================
    // Font Size Control
    // ========================================================================

    /// Sets the font size for labels (user names, file names, directory names).
    ///
    /// # Arguments
    ///
    /// * `size` - Font size in pixels (clamped to 4.0 - 200.0 range)
    #[wasm_bindgen(js_name = setFontSize)]
    pub fn set_font_size(&mut self, size: f32) {
        self.settings.display.font_size = size.clamp(4.0, 200.0);
    }

    /// Gets the current font size for labels.
    #[wasm_bindgen(js_name = getFontSize)]
    pub fn get_font_size(&self) -> f32 {
        self.settings.display.font_size
    }

    // ========================================================================
    // Entity Bounds & Full Map Export
    // ========================================================================

    /// Returns the bounding box of all entities as a JSON object.
    ///
    /// Returns: `{ "minX": f32, "minY": f32, "maxX": f32, "maxY": f32, "width": f32, "height": f32 }`
    ///
    /// Returns null if no entities exist.
    #[wasm_bindgen(js_name = getEntityBounds)]
    pub fn get_entity_bounds(&mut self) -> Option<String> {
        self.scene.compute_entity_bounds().map(|bounds| {
            format!(
                r#"{{"minX":{},"minY":{},"maxX":{},"maxY":{},"width":{},"height":{}}}"#,
                bounds.min.x,
                bounds.min.y,
                bounds.max.x,
                bounds.max.y,
                bounds.width(),
                bounds.height()
            )
        })
    }

    /// Calculates the required canvas dimensions to render the full map at a readable zoom level.
    ///
    /// # Arguments
    ///
    /// * `min_label_font_size` - Minimum font size for labels to be readable (default: 10.0)
    ///
    /// Returns: `{ "width": u32, "height": u32, "zoom": f32, "centerX": f32, "centerY": f32 }`
    ///
    /// Returns null if no entities exist.
    #[wasm_bindgen(js_name = getFullMapDimensions)]
    pub fn get_full_map_dimensions(&mut self, min_label_font_size: f32) -> Option<String> {
        let bounds = self.scene.compute_entity_bounds()?;

        // Add padding around the bounds (20% on each side)
        let padding = 0.2;
        let padded_width = bounds.width() * (1.0 + padding * 2.0);
        let padded_height = bounds.height() * (1.0 + padding * 2.0);

        if padded_width <= 0.0 || padded_height <= 0.0 {
            return None;
        }

        // Calculate zoom level where labels are readable
        // Base font size is settings.display.font_size (default 12.0)
        // We want: base_font_size * zoom >= min_label_font_size
        let base_font_size = self.settings.display.font_size;
        let readable_zoom = (min_label_font_size / base_font_size).max(0.5);

        // Calculate canvas dimensions
        // world_size * zoom = canvas_size
        let canvas_width = (padded_width * readable_zoom).ceil() as u32;
        let canvas_height = (padded_height * readable_zoom).ceil() as u32;

        // Cap at reasonable maximum (browser limits, typically 16384x16384)
        let max_dimension = 16384_u32;
        let (final_width, final_height, final_zoom) =
            if canvas_width > max_dimension || canvas_height > max_dimension {
                // Scale down to fit within limits
                let scale = (max_dimension as f32) / (canvas_width.max(canvas_height) as f32);
                let scaled_width = ((canvas_width as f32) * scale).ceil() as u32;
                let scaled_height = ((canvas_height as f32) * scale).ceil() as u32;
                let scaled_zoom = readable_zoom * scale;
                (scaled_width, scaled_height, scaled_zoom)
            } else {
                (canvas_width, canvas_height, readable_zoom)
            };

        // Center point
        let center = bounds.center();

        Some(format!(
            r#"{{"width":{},"height":{},"zoom":{},"centerX":{},"centerY":{}}}"#,
            final_width, final_height, final_zoom, center.x, center.y
        ))
    }

    /// Prepares the renderer for full map export by setting up camera and viewport.
    ///
    /// # Arguments
    ///
    /// * `width` - Target canvas width
    /// * `height` - Target canvas height
    /// * `zoom` - Zoom level to use
    /// * `center_x` - World X coordinate to center on
    /// * `center_y` - World Y coordinate to center on
    ///
    /// Call this before resizing canvas and calling `forceRender()`.
    #[wasm_bindgen(js_name = prepareFullMapExport)]
    pub fn prepare_full_map_export(
        &mut self,
        width: u32,
        height: u32,
        zoom: f32,
        center_x: f32,
        center_y: f32,
    ) {
        // Update canvas dimensions
        self.canvas.set_width(width);
        self.canvas.set_height(height);

        // Update backend renderer (viewport and internal dimensions)
        self.backend.resize(width, height);

        // Update camera viewport size and position
        self.camera = Camera::new(width as f32, height as f32);
        self.camera.jump_to(Vec2::new(center_x, center_y));
        self.camera.set_zoom(zoom);

        // Update settings
        self.settings.display.width = width;
        self.settings.display.height = height;
    }

    /// Restores the renderer after full map export.
    ///
    /// # Arguments
    ///
    /// * `width` - Original canvas width
    /// * `height` - Original canvas height
    #[wasm_bindgen(js_name = restoreAfterExport)]
    pub fn restore_after_export(&mut self, width: u32, height: u32) {
        // Restore canvas dimensions
        self.canvas.set_width(width);
        self.canvas.set_height(height);

        // Restore backend renderer dimensions
        self.backend.resize(width, height);

        // Restore camera
        self.camera = Camera::new(width as f32, height as f32);
        self.settings.display.width = width;
        self.settings.display.height = height;

        // Fit camera to content
        self.fit_camera_to_content();
    }

    /// Returns the current camera state as JSON for saving/restoring.
    ///
    /// Returns: `{ "x": f32, "y": f32, "zoom": f32 }`
    #[wasm_bindgen(js_name = getCameraState)]
    pub fn get_camera_state(&self) -> String {
        format!(
            r#"{{"x":{},"y":{},"zoom":{}}}"#,
            self.camera.position().x,
            self.camera.position().y,
            self.camera.zoom()
        )
    }

    /// Restores camera state from previously saved values.
    #[wasm_bindgen(js_name = restoreCameraState)]
    pub fn restore_camera_state(&mut self, x: f32, y: f32, zoom: f32) {
        self.camera.jump_to(Vec2::new(x, y));
        self.camera.set_zoom(zoom);
    }
}

// Private implementation
impl Rource {
    /// Applies a VCS commit to the scene.
    fn apply_vcs_commit(&mut self, commit: &Commit) {
        let files: Vec<(PathBuf, ActionType)> = commit
            .files
            .iter()
            .map(|fc| (fc.path.clone(), file_action_to_action_type(fc.action)))
            .collect();

        self.scene.apply_commit(&commit.author, &files);
    }

    /// Resets playback to the beginning.
    fn reset_playback(&mut self) {
        self.scene = Scene::new();
        self.current_commit = 0;
        self.last_applied_commit = 0;
        self.accumulated_time = 0.0;

        // Apply first commit and pre-warm if we have commits
        if !self.commits.is_empty() {
            let commit = self.commits[0].clone();
            self.apply_vcs_commit(&commit);
            self.last_applied_commit = 0;

            // Pre-warm the scene so files are visible
            for _ in 0..30 {
                self.scene.update(1.0 / 60.0);
            }

            self.fit_camera_to_content();
        }
    }

    /// Fits the camera to show all content.
    fn fit_camera_to_content(&mut self) {
        if let Some(entity_bounds) = self.scene.compute_entity_bounds() {
            if entity_bounds.width() > 0.0 && entity_bounds.height() > 0.0 {
                // Add padding
                let padded_bounds = Bounds::from_center_size(
                    entity_bounds.center(),
                    Vec2::new(entity_bounds.width() * 1.2, entity_bounds.height() * 1.2),
                );

                // Calculate zoom to fit bounds
                let screen_width = self.backend.width() as f32;
                let screen_height = self.backend.height() as f32;

                let zoom_x = screen_width / padded_bounds.width();
                let zoom_y = screen_height / padded_bounds.height();
                let zoom = zoom_x.min(zoom_y).clamp(0.01, 100.0);

                self.camera.jump_to(padded_bounds.center());
                self.camera.set_zoom(zoom);
            }
        }
    }

    /// Renders the current frame to the canvas.
    #[allow(clippy::too_many_lines)]
    fn render(&mut self) {
        // Skip rendering if WebGL context is lost
        // This prevents errors and allows graceful recovery
        if self.backend.is_context_lost() {
            return;
        }

        let renderer = self.backend.as_renderer_mut();

        // Begin frame
        renderer.begin_frame();

        // Clear with background color
        renderer.clear(self.settings.display.background_color);

        // Compute visible bounds in world space
        let visible_bounds = self.camera.visible_bounds();
        let camera_zoom = self.camera.zoom();

        // Get visible entities
        let visible_dirs = self.scene.visible_directory_ids(&visible_bounds);
        let visible_files = self.scene.visible_file_ids(&visible_bounds);
        let visible_users = self.scene.visible_user_ids(&visible_bounds);

        // Collect render statistics
        let active_actions = self
            .scene
            .actions()
            .iter()
            .filter(|a| !a.is_complete())
            .count();
        self.render_stats = RenderStats {
            visible_files: visible_files.len(),
            visible_users: visible_users.len(),
            visible_directories: visible_dirs.len(),
            active_actions,
            total_entities: self.scene.file_count()
                + self.scene.user_count()
                + self.scene.directories().len()
                + self.scene.actions().len(),
            // Estimate draw calls: directories (lines + circles) + files + actions (lines + circles) + users (2 circles + ring)
            draw_calls: if self.renderer_type == RendererType::WebGl2 {
                // WebGL2 batches by primitive type: ~6 draw calls typically
                6
            } else {
                // Software renderer: one per primitive
                visible_dirs.len() * 2
                    + visible_files.len()
                    + active_actions * 2
                    + visible_users.len() * 3
            },
        };

        // Use curves when zoomed out (better visual, acceptable perf)
        let use_curves = camera_zoom < 0.8;

        // Draw directories with enhanced styling
        for dir_id in &visible_dirs {
            if let Some(dir) = self.scene.directories().get(*dir_id) {
                if !dir.is_visible() {
                    continue;
                }

                let screen_pos = self.camera.world_to_screen(dir.position());
                let radius = dir.radius() * camera_zoom;

                // Enhanced directory styling based on depth
                let depth = dir.depth() as f32;
                let depth_factor = (depth / 6.0).min(1.0);

                // Gradient color with depth
                let base_brightness = 0.25 + 0.1 * (1.0 - depth_factor);
                let dir_color = Color::new(
                    base_brightness * 0.9,
                    base_brightness,
                    base_brightness * 1.1 + 0.05,
                    0.55,
                );

                // Draw soft glow behind directory node
                let glow_color = dir_color.with_alpha(0.1);
                renderer.draw_disc(screen_pos, radius * 1.5, glow_color);

                // Draw directory as a hollow circle
                renderer.draw_circle(screen_pos, radius, 1.5, dir_color);

                // Small filled center dot
                let center_color = dir_color.with_alpha(0.4);
                renderer.draw_disc(screen_pos, radius * 0.25, center_color);

                // Draw connection to parent with curved branches
                if let Some(parent_pos) = dir.parent_position() {
                    let parent_screen = self.camera.world_to_screen(parent_pos);

                    // Branch width based on depth
                    let branch_width = (1.5 - depth_factor * 0.5).max(0.8);

                    // Branch color with gradient effect
                    let branch_color = Color::new(
                        dir_color.r * 1.1,
                        dir_color.g * 1.1,
                        dir_color.b * 1.2,
                        0.35,
                    );

                    draw_curved_branch(
                        renderer,
                        parent_screen,
                        screen_pos,
                        branch_width,
                        branch_color,
                        use_curves,
                    );
                }

                // Draw directory name label if labels are enabled
                // Only show for shallow directories (depth <= 2) to avoid clutter
                if self.show_labels && dir.depth() <= 2 {
                    if let Some(fid) = self.font_id {
                        let name = dir.name();
                        // Skip empty names (root directory)
                        if !name.is_empty() {
                            let dir_font_size = self.settings.display.font_size * 0.75;
                            let label_pos = Vec2::new(
                                screen_pos.x + radius + 4.0,
                                screen_pos.y - dir_font_size * 0.3,
                            );

                            // Shadow for better readability
                            let shadow_color = Color::new(0.0, 0.0, 0.0, 0.4);
                            renderer.draw_text(
                                name,
                                label_pos + Vec2::new(1.0, 1.0),
                                fid,
                                dir_font_size,
                                shadow_color,
                            );

                            // Main label in soft blue-gray
                            let label_color = Color::new(0.75, 0.78, 0.85, 0.7);
                            renderer.draw_text(name, label_pos, fid, dir_font_size, label_color);
                        }
                    }
                }
            }
        }

        // Draw files with enhanced styling
        for file_id in &visible_files {
            if let Some(file) = self.scene.get_file(*file_id) {
                if file.alpha() < 0.01 {
                    continue;
                }

                let screen_pos = self.camera.world_to_screen(file.position());
                let radius = file.radius() * camera_zoom;
                let color = file.current_color().with_alpha(file.alpha());
                let effective_radius = radius.max(2.0);

                // Draw connection to parent directory first (behind file)
                if let Some(dir) = self.scene.directories().get(file.directory()) {
                    let dir_screen = self.camera.world_to_screen(dir.position());

                    // Branch color matches file color for visual cohesion
                    let branch_color = Color::new(
                        color.r * 0.7,
                        color.g * 0.7,
                        color.b * 0.7,
                        0.25 * file.alpha(),
                    );

                    draw_curved_branch(
                        renderer,
                        dir_screen,
                        screen_pos,
                        0.8,
                        branch_color,
                        use_curves,
                    );
                }

                // Draw soft glow behind file
                let is_touched = file.touch_time() > 0.0;
                let glow_intensity = if is_touched { 0.25 } else { 0.08 };
                let glow_color = color.with_alpha(glow_intensity * file.alpha());
                renderer.draw_disc(screen_pos, effective_radius * 2.0, glow_color);

                // Outer ring (darker border)
                let border_color = Color::new(color.r * 0.6, color.g * 0.6, color.b * 0.6, color.a);
                renderer.draw_disc(screen_pos, effective_radius + 0.5, border_color);

                // Main file disc
                renderer.draw_disc(screen_pos, effective_radius, color);

                // Bright highlight for active/touched files
                if is_touched {
                    let highlight = Color::new(1.0, 1.0, 1.0, 0.3 * file.alpha());
                    renderer.draw_disc(screen_pos, effective_radius * 0.5, highlight);
                }
            }
        }

        // Draw actions (beams from users to files) with enhanced glow effects
        for action in self.scene.actions() {
            if action.is_complete() {
                continue;
            }

            let user_opt = self.scene.get_user(action.user());
            let file_opt = self.scene.get_file(action.file());

            if let (Some(user), Some(file)) = (user_opt, file_opt) {
                let user_screen = self.camera.world_to_screen(user.position());
                let file_screen = self.camera.world_to_screen(file.position());
                let beam_color = action.beam_color();

                // Use enhanced beam drawing with glow
                draw_action_beam(
                    renderer,
                    user_screen,
                    file_screen,
                    action.progress(),
                    beam_color,
                    camera_zoom,
                );
            }
        }

        // Draw users with stylized avatar shapes
        for user_id in &visible_users {
            if let Some(user) = self.scene.get_user(*user_id) {
                if user.alpha() < 0.01 {
                    continue;
                }

                let screen_pos = self.camera.world_to_screen(user.position());
                let radius = (user.radius() * camera_zoom).max(5.0);
                let color = user.display_color();

                // Draw stylized avatar shape (modern person silhouette)
                draw_avatar_shape(
                    renderer,
                    screen_pos,
                    radius,
                    color,
                    user.is_active(),
                    user.alpha(),
                );
            }
        }

        // Draw labels if enabled and font is loaded
        if self.show_labels {
            if let Some(font_id) = self.font_id {
                let font_size = self.settings.display.font_size;

                // Draw user name labels with shadows
                for user_id in &visible_users {
                    if let Some(user) = self.scene.get_user(*user_id) {
                        if user.alpha() < 0.01 {
                            continue;
                        }

                        let screen_pos = self.camera.world_to_screen(user.position());
                        let radius = (user.radius() * camera_zoom).max(5.0);

                        // Position label to the right of the user
                        let label_pos =
                            Vec2::new(screen_pos.x + radius + 5.0, screen_pos.y - font_size * 0.3);
                        let alpha = user.alpha();

                        // Shadow for better readability
                        let shadow_color = Color::new(0.0, 0.0, 0.0, 0.5 * alpha);
                        renderer.draw_text(
                            user.name(),
                            label_pos + Vec2::new(1.0, 1.0),
                            font_id,
                            font_size,
                            shadow_color,
                        );

                        let label_color = Color::new(1.0, 1.0, 1.0, 0.9 * alpha);
                        renderer.draw_text(user.name(), label_pos, font_id, font_size, label_color);
                    }
                }

                // Draw file name labels with collision avoidance and adaptive visibility
                if camera_zoom > 0.15 {
                    let file_font_size = font_size * 0.8;

                    // Collect label candidates with priority
                    let mut label_candidates: Vec<(Vec2, f32, f32, &str, f32)> = Vec::new();
                    for file_id in &visible_files {
                        if let Some(file) = self.scene.get_file(*file_id) {
                            if file.alpha() < 0.3 {
                                continue;
                            }

                            let screen_pos = self.camera.world_to_screen(file.position());
                            let radius = (file.radius() * camera_zoom).max(2.0);
                            let is_touched = file.touch_time() > 0.0;

                            // Priority based on visibility and activity
                            let activity_bonus = if is_touched { 100.0 } else { 0.0 };
                            let priority = file.radius() * file.alpha() * 10.0 + activity_bonus;

                            label_candidates.push((
                                screen_pos,
                                radius,
                                file.alpha(),
                                file.name(),
                                priority,
                            ));
                        }
                    }

                    // Sort by priority (highest first)
                    label_candidates
                        .sort_by(|a, b| b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal));

                    // Use label placer for collision avoidance
                    let mut placer = LabelPlacer::new(camera_zoom);

                    for (screen_pos, radius, alpha, name, _priority) in &label_candidates {
                        if !placer.can_place_more() {
                            break;
                        }

                        // Calculate label dimensions
                        let text_width = estimate_text_width(name, file_font_size);
                        let text_height = file_font_size;

                        // Primary position: right of the file
                        let primary_pos = Vec2::new(
                            screen_pos.x + radius + 3.0,
                            screen_pos.y - file_font_size * 0.3,
                        );

                        // Try to place with fallback positions
                        if let Some(label_pos) = placer.try_place_with_fallback(
                            primary_pos,
                            text_width,
                            text_height,
                            *screen_pos,
                            *radius,
                        ) {
                            // Shadow for better readability
                            let shadow_color = Color::new(0.0, 0.0, 0.0, 0.5 * alpha);
                            renderer.draw_text(
                                name,
                                label_pos + Vec2::new(1.0, 1.0),
                                font_id,
                                file_font_size,
                                shadow_color,
                            );

                            let label_color = Color::new(0.95, 0.95, 0.95, 0.8 * alpha);
                            renderer.draw_text(
                                name,
                                label_pos,
                                font_id,
                                file_font_size,
                                label_color,
                            );
                        }
                    }
                }
            }
        }

        // End frame
        renderer.end_frame();

        // Present (copy to canvas for software renderer)
        self.backend.present();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // File Action Conversion Tests
    // ========================================================================

    #[test]
    fn test_file_action_conversion() {
        assert!(matches!(
            file_action_to_action_type(FileAction::Create),
            ActionType::Create
        ));
        assert!(matches!(
            file_action_to_action_type(FileAction::Modify),
            ActionType::Modify
        ));
        assert!(matches!(
            file_action_to_action_type(FileAction::Delete),
            ActionType::Delete
        ));
    }

    // ========================================================================
    // Color Tests
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
    // Renderer Type Tests
    // ========================================================================

    #[test]
    fn test_renderer_type_as_str() {
        assert_eq!(RendererType::WebGl2.as_str(), "webgl2");
        assert_eq!(RendererType::Software.as_str(), "software");
    }

    #[test]
    fn test_renderer_type_equality() {
        assert_eq!(RendererType::WebGl2, RendererType::WebGl2);
        assert_eq!(RendererType::Software, RendererType::Software);
        assert_ne!(RendererType::WebGl2, RendererType::Software);
    }

    // ========================================================================
    // Performance Metrics Tests
    // ========================================================================

    #[test]
    fn test_performance_metrics_new() {
        let metrics = PerformanceMetrics::new();
        assert_eq!(metrics.fps, 0.0);
        assert_eq!(metrics.total_frames, 0);
        assert_eq!(metrics.frame_time_count, 0);
    }

    #[test]
    fn test_performance_metrics_record_frame() {
        let mut metrics = PerformanceMetrics::new();

        // Record a frame at 60fps (16.67ms)
        metrics.record_frame(1.0 / 60.0);

        assert_eq!(metrics.total_frames, 1);
        assert_eq!(metrics.frame_time_count, 1);
        assert!(metrics.fps > 59.0 && metrics.fps < 61.0);
    }

    #[test]
    fn test_performance_metrics_rolling_average() {
        let mut metrics = PerformanceMetrics::new();

        // Record 60 frames at consistent 60fps
        for _ in 0..60 {
            metrics.record_frame(1.0 / 60.0);
        }

        assert_eq!(metrics.total_frames, 60);
        assert_eq!(metrics.frame_time_count, FRAME_SAMPLE_COUNT);
        // Should show approximately 60 FPS
        assert!(metrics.fps > 59.0 && metrics.fps < 61.0);
    }

    #[test]
    fn test_performance_metrics_varying_framerate() {
        let mut metrics = PerformanceMetrics::new();

        // Mix of fast and slow frames
        for _ in 0..30 {
            metrics.record_frame(1.0 / 30.0); // 30fps
        }
        for _ in 0..30 {
            metrics.record_frame(1.0 / 60.0); // 60fps
        }

        // Average should be between 30 and 60
        assert!(metrics.fps > 30.0 && metrics.fps < 60.0);
    }

    // ========================================================================
    // Render Stats Tests
    // ========================================================================

    #[test]
    fn test_render_stats_default() {
        let stats = RenderStats::default();
        assert_eq!(stats.visible_files, 0);
        assert_eq!(stats.visible_users, 0);
        assert_eq!(stats.visible_directories, 0);
        assert_eq!(stats.active_actions, 0);
        assert_eq!(stats.total_entities, 0);
        assert_eq!(stats.draw_calls, 0);
    }

    // ========================================================================
    // File Action Conversion Tests
    // ========================================================================

    #[test]
    fn test_file_action_to_action_type_create() {
        let action = file_action_to_action_type(FileAction::Create);
        assert!(matches!(action, ActionType::Create));
    }

    #[test]
    fn test_file_action_to_action_type_modify() {
        let action = file_action_to_action_type(FileAction::Modify);
        assert!(matches!(action, ActionType::Modify));
    }

    #[test]
    fn test_file_action_to_action_type_delete() {
        let action = file_action_to_action_type(FileAction::Delete);
        assert!(matches!(action, ActionType::Delete));
    }

    // ========================================================================
    // Additional PerformanceMetrics Tests
    // ========================================================================

    #[test]
    fn test_performance_metrics_zero_dt() {
        let mut metrics = PerformanceMetrics::new();
        // Recording a zero-duration frame should not crash
        metrics.record_frame(0.0);
        assert_eq!(metrics.total_frames, 1);
    }

    #[test]
    fn test_performance_metrics_very_slow_frame() {
        let mut metrics = PerformanceMetrics::new();
        // Very slow frame (1 second = 1 FPS)
        metrics.record_frame(1.0);
        assert!(metrics.fps > 0.9 && metrics.fps < 1.1);
    }

    #[test]
    fn test_performance_metrics_reset() {
        let mut metrics = PerformanceMetrics::new();
        for _ in 0..100 {
            metrics.record_frame(1.0 / 60.0);
        }
        assert!(metrics.total_frames > 0);
        // Create new metrics to "reset"
        let fresh = PerformanceMetrics::new();
        assert_eq!(fresh.total_frames, 0);
        assert_eq!(fresh.fps, 0.0);
    }

    // ========================================================================
    // RenderStats Tests
    // ========================================================================

    #[test]
    fn test_render_stats_with_values() {
        let stats = RenderStats {
            visible_files: 100,
            visible_users: 5,
            visible_directories: 20,
            active_actions: 10,
            total_entities: 125,
            draw_calls: 50,
        };
        assert_eq!(stats.visible_files, 100);
        assert_eq!(stats.visible_users, 5);
        assert_eq!(stats.visible_directories, 20);
        assert_eq!(stats.active_actions, 10);
        assert_eq!(stats.total_entities, 125);
        assert_eq!(stats.draw_calls, 50);
    }
}
