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
//! ## Module Structure
//!
//! - `backend`: Renderer backend abstraction (WebGL2/Software)
//! - `metrics`: Performance tracking and render statistics
//! - `playback`: Timeline and commit playback management
//! - `interaction`: Mouse/touch input handling
//! - `render_phases`: Phased rendering pipeline
//! - `rendering`: Low-level rendering utilities
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

// ============================================================================
// Imports
// ============================================================================

use std::fmt::Write as FmtWrite;

use wasm_bindgen::prelude::*;
use web_sys::HtmlCanvasElement;

use rource_core::camera::Camera;
use rource_core::config::Settings;
use rource_core::scene::Scene;
use rource_math::{Bounds, Color, Vec2};
use rource_render::{default_font, FontId};
use rource_vcs::parser::{CustomParser, GitParser, ParseOptions, Parser};
use rource_vcs::Commit;

// Re-exports for internal use
use backend::{RendererBackend, RendererType};
use interaction::{
    hit_test_directory, hit_test_file, hit_test_user, move_connected_entities_for_directory,
    move_connected_entities_for_file, move_connected_entities_for_user, DragTarget,
    ENTITY_HIT_RADIUS,
};
use metrics::{PerformanceMetrics, RenderStats};
use playback::{apply_vcs_commit, prewarm_scene, PlaybackState};
use png::write_png;
use render_phases::{
    render_actions, render_directories, render_directory_labels, render_file_labels, render_files,
    render_user_labels, render_users, RenderContext,
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
/// - Rendering (WebGL2 or Software backend)
/// - Scene management (files, users, directories)
/// - Camera controls (pan, zoom)
/// - Playback timeline (play, pause, seek)
/// - User interaction (mouse, keyboard)
#[wasm_bindgen]
pub struct Rource {
    /// Canvas element.
    canvas: HtmlCanvasElement,

    /// Renderer backend (WebGL2 or Software).
    backend: RendererBackend,

    /// Type of renderer being used.
    renderer_type: RendererType,

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

    /// Mouse state for interaction.
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

    /// Font ID for text rendering.
    font_id: Option<FontId>,

    /// Whether to show labels (user names, file names).
    show_labels: bool,

    /// Performance metrics (FPS tracking, frame timing).
    perf_metrics: PerformanceMetrics,

    /// Render statistics for the current frame.
    render_stats: RenderStats,
}

// ============================================================================
// Constructor and Renderer Info
// ============================================================================

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
    #[wasm_bindgen(js_name = isContextLost)]
    pub fn is_context_lost(&self) -> bool {
        self.backend.is_context_lost()
    }

    /// Attempts to recover from a lost WebGL context.
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
// Playback Control
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Starts playback.
    pub fn play(&mut self) {
        self.playback.play();
    }

    /// Pauses playback.
    pub fn pause(&mut self) {
        self.playback.pause();
    }

    /// Returns whether playback is active.
    #[wasm_bindgen(js_name = isPlaying)]
    pub fn is_playing(&self) -> bool {
        self.playback.is_playing()
    }

    /// Toggles play/pause state.
    #[wasm_bindgen(js_name = togglePlay)]
    pub fn toggle_play(&mut self) {
        self.playback.toggle_play();
    }

    /// Seeks to a specific commit index.
    pub fn seek(&mut self, commit_index: usize) {
        if commit_index < self.commits.len() {
            // Reset scene and replay commits up to the target
            self.scene = Scene::new();
            self.playback.set_current_commit(0);
            self.playback.set_last_applied_commit(0);

            for i in 0..=commit_index {
                if i < self.commits.len() {
                    apply_vcs_commit(&mut self.scene, &self.commits[i]);
                }
            }

            self.playback.set_current_commit(commit_index);
            self.playback.set_last_applied_commit(commit_index);
            self.playback.reset_accumulated_time();

            // Pre-warm the scene
            prewarm_scene(&mut self.scene, 30, 1.0 / 60.0);

            // Position camera
            self.fit_camera_to_content();
        }
    }

    /// Returns the current commit index.
    #[wasm_bindgen(js_name = currentCommit)]
    pub fn current_commit(&self) -> usize {
        self.playback.current_commit()
    }

    /// Returns the timestamp for a commit at the given index.
    #[wasm_bindgen(js_name = getCommitTimestamp)]
    pub fn get_commit_timestamp(&self, index: usize) -> f64 {
        self.commits.get(index).map_or(0.0, |c| c.timestamp as f64)
    }

    /// Returns the author name for a commit at the given index.
    #[wasm_bindgen(js_name = getCommitAuthor)]
    pub fn get_commit_author(&self, index: usize) -> String {
        self.commits
            .get(index)
            .map_or_else(String::new, |c| c.author.clone())
    }

    /// Returns the number of files changed in a commit at the given index.
    #[wasm_bindgen(js_name = getCommitFileCount)]
    pub fn get_commit_file_count(&self, index: usize) -> usize {
        self.commits.get(index).map_or(0, |c| c.files.len())
    }

    /// Returns the date range of all commits as a JSON object.
    #[wasm_bindgen(js_name = getDateRange)]
    pub fn get_date_range(&self) -> Option<String> {
        playback::get_date_range(&self.commits)
            .map(|(start, end)| format!(r#"{{"startTimestamp":{start},"endTimestamp":{end}}}"#))
    }

    /// Sets playback speed (seconds per day of repository history).
    #[wasm_bindgen(js_name = setSpeed)]
    pub fn set_speed(&mut self, seconds_per_day: f32) {
        let speed = if seconds_per_day.is_finite() && seconds_per_day > 0.0 {
            seconds_per_day
        } else {
            10.0
        };
        self.settings.playback.seconds_per_day = speed.clamp(1.0, 1000.0);
    }

    /// Gets the current playback speed.
    #[wasm_bindgen(js_name = getSpeed)]
    pub fn get_speed(&self) -> f32 {
        self.settings.playback.seconds_per_day
    }

    /// Steps forward to the next commit.
    #[wasm_bindgen(js_name = stepForward)]
    pub fn step_forward(&mut self) {
        let current = self.playback.current_commit();
        if current < self.commits.len().saturating_sub(1) {
            self.seek(current + 1);
        }
    }

    /// Steps backward to the previous commit.
    #[wasm_bindgen(js_name = stepBackward)]
    pub fn step_backward(&mut self) {
        let current = self.playback.current_commit();
        if current > 0 {
            self.seek(current - 1);
        }
    }
}

// ============================================================================
// Camera Control
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
    /// Max zoom increased to 1000.0 to support deep zoom into massive repositories.
    pub fn zoom(&mut self, factor: f32) {
        let new_zoom = (self.camera.zoom() * factor).clamp(0.01, 1000.0);
        self.camera.set_zoom(new_zoom);
    }

    /// Zooms the camera toward a specific screen point.
    #[wasm_bindgen(js_name = zoomToward)]
    pub fn zoom_toward(&mut self, screen_x: f32, screen_y: f32, factor: f32) {
        let screen_point = Vec2::new(screen_x, screen_y);
        let world_before = self.camera.screen_to_world(screen_point);

        // Max zoom increased to 1000.0 to support deep zoom into massive repositories
        let new_zoom = (self.camera.zoom() * factor).clamp(0.01, 1000.0);
        self.camera.set_zoom(new_zoom);

        let world_after = self.camera.screen_to_world(screen_point);
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

    /// Returns the current zoom level.
    #[wasm_bindgen(js_name = getZoom)]
    pub fn get_zoom(&self) -> f32 {
        self.camera.zoom()
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

    /// Returns the current camera state as JSON.
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

// ============================================================================
// Settings
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Sets whether to show bloom effect.
    #[wasm_bindgen(js_name = setBloom)]
    pub fn set_bloom(&mut self, enabled: bool) {
        self.settings.display.bloom_enabled = enabled;
    }

    /// Sets the background color (hex string like "#000000" or "000000").
    #[wasm_bindgen(js_name = setBackgroundColor)]
    pub fn set_background_color(&mut self, hex: &str) {
        let hex = hex.trim_start_matches('#');
        if hex.len() == 6 {
            if let Ok(val) = u32::from_str_radix(hex, 16) {
                self.settings.display.background_color = Color::from_hex(val);
            }
        }
    }

    /// Sets whether to show labels.
    #[wasm_bindgen(js_name = setShowLabels)]
    pub fn set_show_labels(&mut self, show: bool) {
        self.show_labels = show;
    }

    /// Gets whether labels are being shown.
    #[wasm_bindgen(js_name = getShowLabels)]
    pub fn get_show_labels(&self) -> bool {
        self.show_labels
    }

    /// Sets the font size for labels.
    #[wasm_bindgen(js_name = setFontSize)]
    pub fn set_font_size(&mut self, size: f32) {
        self.settings.display.font_size = size.clamp(4.0, 200.0);
    }

    /// Gets the current font size for labels.
    #[wasm_bindgen(js_name = getFontSize)]
    pub fn get_font_size(&self) -> f32 {
        self.settings.display.font_size
    }
}

// ============================================================================
// Input Handling
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Handles mouse down events.
    #[wasm_bindgen(js_name = onMouseDown)]
    pub fn on_mouse_down(&mut self, x: f32, y: f32) {
        self.mouse_down = true;
        self.drag_start_x = x;
        self.drag_start_y = y;
        self.mouse_x = x;
        self.mouse_y = y;

        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);
        let hit_radius = ENTITY_HIT_RADIUS / self.camera.zoom();

        // Check users first
        if let Some(drag_target) = hit_test_user(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
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
            if let DragTarget::File(file_id) = drag_target {
                if let Some(file) = self.scene.get_file_mut(file_id) {
                    self.drag_offset = file.position() - world_pos;
                    self.drag_last_pos = file.position();
                    file.set_pinned(true);
                }
            }
            return;
        }

        // Check directories
        if let Some(drag_target) = hit_test_directory(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
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
    #[wasm_bindgen(js_name = onMouseMove)]
    pub fn on_mouse_move(&mut self, x: f32, y: f32) {
        self.mouse_x = x;
        self.mouse_y = y;

        if !self.mouse_down {
            return;
        }

        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);

        if let Some(drag_target) = self.drag_target {
            let new_entity_pos = world_pos + self.drag_offset;
            let delta = new_entity_pos - self.drag_last_pos;

            match drag_target {
                DragTarget::User(user_id) => {
                    if let Some(user) = self.scene.get_user_mut(user_id) {
                        user.set_position(new_entity_pos);
                        user.clear_target();
                    }
                    move_connected_entities_for_user(&mut self.scene, user_id, delta);
                }
                DragTarget::File(file_id) => {
                    let dir_id = self
                        .scene
                        .get_file(file_id)
                        .map(rource_core::scene::FileNode::directory);

                    if let Some(file) = self.scene.get_file_mut(file_id) {
                        file.set_position(new_entity_pos);
                        file.set_target(new_entity_pos);
                    }

                    if let Some(dir_id) = dir_id {
                        move_connected_entities_for_file(&mut self.scene, file_id, dir_id, delta);
                    }
                }
                DragTarget::Directory(dir_id) => {
                    if let Some(dir) = self.scene.directories_mut().get_mut(dir_id) {
                        dir.set_position(new_entity_pos);
                        dir.set_velocity(Vec2::ZERO);
                    }
                    move_connected_entities_for_directory(&mut self.scene, dir_id, delta);
                }
            }

            self.drag_last_pos = new_entity_pos;
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

    /// Handles mouse wheel events for zooming.
    #[wasm_bindgen(js_name = onWheel)]
    pub fn on_wheel(&mut self, delta_y: f32, mouse_x: f32, mouse_y: f32) {
        let normalized_delta = delta_y / 100.0;
        let clamped_delta = normalized_delta.clamp(-2.0, 2.0);
        let factor = 1.0 - (clamped_delta * 0.08);
        self.zoom_toward(mouse_x, mouse_y, factor);
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
                playback::calculate_seconds_per_commit(self.settings.playback.seconds_per_day);

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
// Render Statistics API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns the number of visible files.
    #[wasm_bindgen(js_name = getVisibleFiles)]
    pub fn get_visible_files(&self) -> usize {
        self.render_stats.visible_files
    }

    /// Returns the number of visible users.
    #[wasm_bindgen(js_name = getVisibleUsers)]
    pub fn get_visible_users(&self) -> usize {
        self.render_stats.visible_users
    }

    /// Returns the number of visible directories.
    #[wasm_bindgen(js_name = getVisibleDirectories)]
    pub fn get_visible_directories(&self) -> usize {
        self.render_stats.visible_directories
    }

    /// Returns the number of active action beams.
    #[wasm_bindgen(js_name = getActiveActions)]
    pub fn get_active_actions(&self) -> usize {
        self.render_stats.active_actions
    }

    /// Returns the total number of entities.
    #[wasm_bindgen(js_name = getTotalEntities)]
    pub fn get_total_entities(&self) -> usize {
        self.render_stats.total_entities
    }

    /// Returns the estimated draw call count.
    #[wasm_bindgen(js_name = getDrawCalls)]
    pub fn get_draw_calls(&self) -> usize {
        self.render_stats.draw_calls
    }

    /// Returns the total number of files.
    #[wasm_bindgen(js_name = getTotalFiles)]
    pub fn get_total_files(&self) -> usize {
        self.scene.file_count()
    }

    /// Returns the total number of users.
    #[wasm_bindgen(js_name = getTotalUsers)]
    pub fn get_total_users(&self) -> usize {
        self.scene.user_count()
    }
}

// ============================================================================
// Author Information API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns author data as a JSON string array.
    #[wasm_bindgen(js_name = getAuthors)]
    pub fn get_authors(&self) -> String {
        let mut authors: Vec<(&str, Color, usize)> = self
            .scene
            .users()
            .values()
            .map(|user| {
                let commit_count = self
                    .commits
                    .iter()
                    .filter(|c| c.author == user.name())
                    .count();
                (user.name(), user.color(), commit_count)
            })
            .collect();

        authors.sort_by(|a, b| b.2.cmp(&a.2));

        let mut json = String::from("[");
        for (i, (name, color, commits)) in authors.iter().enumerate() {
            if i > 0 {
                json.push(',');
            }
            let r = (color.r * 255.0) as u8;
            let g = (color.g * 255.0) as u8;
            let b = (color.b * 255.0) as u8;
            let escaped_name = name.replace('\\', "\\\\").replace('"', "\\\"");
            let _ = FmtWrite::write_fmt(
                &mut json,
                format_args!("{{\"name\":\"{escaped_name}\",\"color\":\"#{r:02x}{g:02x}{b:02x}\",\"commits\":{commits}}}")
            );
        }
        json.push(']');
        json
    }

    /// Returns the color for a given author name as a hex string.
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
}

// ============================================================================
// Export / Screenshot API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns the bounding box of all entities as JSON.
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

    /// Calculates the required canvas dimensions for full map export.
    #[wasm_bindgen(js_name = getFullMapDimensions)]
    pub fn get_full_map_dimensions(&mut self, min_label_font_size: f32) -> Option<String> {
        let bounds = self.scene.compute_entity_bounds()?;

        let padding = 0.2;
        let padded_width = bounds.width() * (1.0 + padding * 2.0);
        let padded_height = bounds.height() * (1.0 + padding * 2.0);

        if padded_width <= 0.0 || padded_height <= 0.0 {
            return None;
        }

        let base_font_size = self.settings.display.font_size;
        let readable_zoom = (min_label_font_size / base_font_size).max(0.5);

        let canvas_width = (padded_width * readable_zoom).ceil() as u32;
        let canvas_height = (padded_height * readable_zoom).ceil() as u32;

        let max_dimension = 16384_u32;
        let (final_width, final_height, final_zoom) =
            if canvas_width > max_dimension || canvas_height > max_dimension {
                let scale = (max_dimension as f32) / (canvas_width.max(canvas_height) as f32);
                let scaled_width = ((canvas_width as f32) * scale).ceil() as u32;
                let scaled_height = ((canvas_height as f32) * scale).ceil() as u32;
                let scaled_zoom = readable_zoom * scale;
                (scaled_width, scaled_height, scaled_zoom)
            } else {
                (canvas_width, canvas_height, readable_zoom)
            };

        let center = bounds.center();

        Some(format!(
            r#"{{"width":{},"height":{},"zoom":{},"centerX":{},"centerY":{}}}"#,
            final_width, final_height, final_zoom, center.x, center.y
        ))
    }

    /// Prepares the renderer for full map export.
    #[wasm_bindgen(js_name = prepareFullMapExport)]
    pub fn prepare_full_map_export(
        &mut self,
        width: u32,
        height: u32,
        zoom: f32,
        center_x: f32,
        center_y: f32,
    ) {
        self.canvas.set_width(width);
        self.canvas.set_height(height);
        self.backend.resize(width, height);
        self.camera = Camera::new(width as f32, height as f32);
        self.camera.jump_to(Vec2::new(center_x, center_y));
        self.camera.set_zoom(zoom);
        self.settings.display.width = width;
        self.settings.display.height = height;
    }

    /// Restores the renderer after full map export.
    #[wasm_bindgen(js_name = restoreAfterExport)]
    pub fn restore_after_export(&mut self, width: u32, height: u32) {
        self.canvas.set_width(width);
        self.canvas.set_height(height);
        self.backend.resize(width, height);
        self.camera = Camera::new(width as f32, height as f32);
        self.settings.display.width = width;
        self.settings.display.height = height;
        self.fit_camera_to_content();
    }

    /// Captures a screenshot and returns it as PNG data.
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
    fn fit_camera_to_content(&mut self) {
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
                let zoom = zoom_x.min(zoom_y).clamp(0.01, 1000.0);

                self.camera.jump_to(padded_bounds.center());
                self.camera.set_zoom(zoom);
            }
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
        let (visible_dirs, visible_files, visible_users) =
            self.scene.visible_entities(&visible_bounds);

        let active_actions = self
            .scene
            .actions()
            .iter()
            .filter(|a| !a.is_complete())
            .count();

        self.render_stats.update(
            visible_files.len(),
            visible_users.len(),
            visible_dirs.len(),
            active_actions,
            self.scene.file_count()
                + self.scene.user_count()
                + self.scene.directories().len()
                + self.scene.actions().len(),
            if self.renderer_type == RendererType::WebGl2 {
                6
            } else {
                visible_dirs.len() * 2
                    + visible_files.len()
                    + active_actions * 2
                    + visible_users.len() * 3
            },
        );

        let ctx = RenderContext {
            visible_bounds,
            camera_zoom,
            use_curves: camera_zoom < 0.8,
            visible_dirs,
            visible_files,
            visible_users,
            show_labels: self.show_labels,
            font_id: self.font_id,
            font_size: self.settings.display.font_size,
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
