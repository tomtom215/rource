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
//! - **Software**: Pure CPU rendering via Canvas2D for maximum compatibility
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

use std::path::PathBuf;

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement, ImageData};

use rource_core::camera::Camera;
use rource_core::config::Settings;
use rource_core::scene::{ActionType, Scene};
use rource_math::{Bounds, Color, Vec2};
use rource_render::{Renderer, SoftwareRenderer, WebGl2Renderer};
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
// PNG Export (minimal, dependency-free implementation)
// ============================================================================

use std::io::{self, Write};

/// Writes a frame buffer to PNG format.
fn write_png<W: Write>(writer: &mut W, pixels: &[u32], width: u32, height: u32) -> io::Result<()> {
    // PNG signature
    writer.write_all(&[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A])?;

    // IHDR chunk
    let ihdr_data = {
        let mut data = Vec::with_capacity(13);
        data.extend_from_slice(&width.to_be_bytes());
        data.extend_from_slice(&height.to_be_bytes());
        data.push(8); // Bit depth
        data.push(2); // Color type: RGB
        data.push(0); // Compression method
        data.push(0); // Filter method
        data.push(0); // Interlace method
        data
    };
    write_png_chunk(writer, *b"IHDR", &ihdr_data)?;

    // Prepare raw image data (1 filter byte + 3 RGB bytes per pixel per row)
    let raw_size = (1 + (width as usize) * 3) * height as usize;
    let mut raw_data = Vec::with_capacity(raw_size);

    for y in 0..height as usize {
        raw_data.push(0); // Filter type: None
        for x in 0..width as usize {
            let pixel = pixels[y * width as usize + x];
            raw_data.push(((pixel >> 16) & 0xFF) as u8); // R
            raw_data.push(((pixel >> 8) & 0xFF) as u8); // G
            raw_data.push((pixel & 0xFF) as u8); // B
        }
    }

    // Compress and write IDAT
    let compressed = deflate_compress(&raw_data);
    write_png_chunk(writer, *b"IDAT", &compressed)?;

    // IEND chunk
    write_png_chunk(writer, *b"IEND", &[])?;

    writer.flush()
}

/// Writes a PNG chunk.
fn write_png_chunk<W: Write>(writer: &mut W, chunk_type: [u8; 4], data: &[u8]) -> io::Result<()> {
    writer.write_all(&(data.len() as u32).to_be_bytes())?;
    writer.write_all(&chunk_type)?;
    writer.write_all(data)?;
    let crc = crc32(&chunk_type, data);
    writer.write_all(&crc.to_be_bytes())?;
    Ok(())
}

/// Computes CRC-32 for PNG chunks.
fn crc32(chunk_type: &[u8], data: &[u8]) -> u32 {
    const CRC_TABLE: [u32; 256] = {
        let mut table = [0u32; 256];
        let mut i = 0;
        while i < 256 {
            let mut crc = i as u32;
            let mut j = 0;
            while j < 8 {
                if crc & 1 != 0 {
                    crc = 0xEDB8_8320 ^ (crc >> 1);
                } else {
                    crc >>= 1;
                }
                j += 1;
            }
            table[i] = crc;
            i += 1;
        }
        table
    };

    let mut crc = 0xFFFF_FFFF_u32;
    for &byte in chunk_type.iter().chain(data.iter()) {
        let index = ((crc ^ u32::from(byte)) & 0xFF) as usize;
        crc = CRC_TABLE[index] ^ (crc >> 8);
    }
    !crc
}

/// Maximum bytes per uncompressed DEFLATE block.
const MAX_DEFLATE_BLOCK: usize = 65535;

/// Simple DEFLATE compression with zlib wrapper (uncompressed blocks).
fn deflate_compress(data: &[u8]) -> Vec<u8> {
    let mut output = Vec::new();
    output.push(0x78); // CMF
    output.push(0x01); // FLG

    let mut offset = 0;
    while offset < data.len() {
        let remaining = data.len() - offset;
        let block_len = remaining.min(MAX_DEFLATE_BLOCK);
        let is_final = offset + block_len >= data.len();

        output.push(u8::from(is_final));
        let len = block_len as u16;
        output.push((len & 0xFF) as u8);
        output.push((len >> 8) as u8);
        output.push((!len & 0xFF) as u8);
        output.push((!len >> 8) as u8);
        output.extend_from_slice(&data[offset..offset + block_len]);

        offset += block_len;
    }

    // Adler-32
    let mut a: u32 = 1;
    let mut b: u32 = 0;
    for &byte in data {
        a = (a + u32::from(byte)) % 65521;
        b = (b + a) % 65521;
    }
    let adler = (b << 16) | a;
    output.extend_from_slice(&adler.to_be_bytes());

    output
}

// ============================================================================
// Renderer Backend Abstraction
// ============================================================================

/// The type of renderer being used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RendererType {
    /// WebGL2 GPU-accelerated renderer.
    WebGl2,
    /// Software CPU renderer with Canvas2D output.
    Software,
}

impl RendererType {
    fn as_str(&self) -> &'static str {
        match self {
            Self::WebGl2 => "webgl2",
            Self::Software => "software",
        }
    }
}

/// Unified renderer backend that can be either WebGL2 or Software.
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

    /// Returns the renderer type.
    fn renderer_type(&self) -> RendererType {
        match self {
            Self::WebGl2(_) => RendererType::WebGl2,
            Self::Software { .. } => RendererType::Software,
        }
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

    /// Called after end_frame() to copy software buffer to canvas (no-op for WebGL2).
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

    /// Returns pixel data for screenshot (software only).
    fn pixels(&self) -> Option<&[u32]> {
        if let Self::Software { renderer, .. } = self {
            Some(renderer.pixels())
        } else {
            None
        }
    }
}

// ============================================================================
// Main Rource WASM API
// ============================================================================

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

        let (backend, renderer_type) = RendererBackend::new(&canvas)?;

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

    /// Sets playback speed (seconds per day of repository history).
    #[wasm_bindgen(js_name = setSpeed)]
    pub fn set_speed(&mut self, seconds_per_day: f32) {
        self.settings.playback.seconds_per_day = seconds_per_day.max(0.01);
    }

    /// Gets the current playback speed.
    #[wasm_bindgen(js_name = getSpeed)]
    pub fn get_speed(&self) -> f32 {
        self.settings.playback.seconds_per_day
    }

    /// Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
    pub fn zoom(&mut self, factor: f32) {
        let new_zoom = (self.camera.zoom() * factor).clamp(0.1, 10.0);
        self.camera.set_zoom(new_zoom);
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

    /// Handles mouse down events.
    #[wasm_bindgen(js_name = onMouseDown)]
    pub fn on_mouse_down(&mut self, x: f32, y: f32) {
        self.mouse_down = true;
        self.drag_start_x = x;
        self.drag_start_y = y;
        self.camera_start_x = self.camera.position().x;
        self.camera_start_y = self.camera.position().y;
    }

    /// Handles mouse up events.
    #[wasm_bindgen(js_name = onMouseUp)]
    pub fn on_mouse_up(&mut self) {
        self.mouse_down = false;
    }

    /// Handles mouse move events.
    #[wasm_bindgen(js_name = onMouseMove)]
    pub fn on_mouse_move(&mut self, x: f32, y: f32) {
        self.mouse_x = x;
        self.mouse_y = y;

        if self.mouse_down {
            let dx = x - self.drag_start_x;
            let dy = y - self.drag_start_y;
            let world_delta = Vec2::new(dx, dy) / self.camera.zoom();
            let new_pos = Vec2::new(self.camera_start_x, self.camera_start_y) - world_delta;
            self.camera.jump_to(new_pos);
        }
    }

    /// Handles mouse wheel events for zooming.
    #[wasm_bindgen(js_name = onWheel)]
    pub fn on_wheel(&mut self, delta_y: f32) {
        let factor = if delta_y > 0.0 { 0.9 } else { 1.1 };
        self.zoom(factor);
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
        // Calculate delta time
        let dt = if self.last_frame_time > 0.0 {
            ((timestamp - self.last_frame_time) / 1000.0) as f32
        } else {
            1.0 / 60.0
        };
        self.last_frame_time = timestamp;

        // Clamp dt to avoid huge jumps
        let dt = dt.min(0.1);

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

    /// Forces a render without updating simulation (useful for static views).
    #[wasm_bindgen(js_name = forceRender)]
    pub fn force_render(&mut self) {
        self.render();
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
                let zoom = zoom_x.min(zoom_y).clamp(0.1, 5.0);

                self.camera.jump_to(padded_bounds.center());
                self.camera.set_zoom(zoom);
            }
        }
    }

    /// Renders the current frame to the canvas.
    fn render(&mut self) {
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

        // Draw directories (lines from parent to children)
        for dir_id in &visible_dirs {
            if let Some(dir) = self.scene.directories().get(*dir_id) {
                let screen_pos = self.camera.world_to_screen(dir.position());

                // Draw connections to children
                for child_id in dir.children() {
                    if let Some(child) = self.scene.directories().get(*child_id) {
                        let child_screen = self.camera.world_to_screen(child.position());
                        let color = Color::new(0.3, 0.3, 0.4, 0.5);
                        renderer.draw_line(screen_pos, child_screen, 1.0, color);
                    }
                }

                // Draw directory node
                let radius = (dir.radius() * camera_zoom).min(20.0);
                let color = Color::new(0.4, 0.4, 0.5, 0.8);
                renderer.draw_disc(screen_pos, radius.max(2.0), color);
            }
        }

        // Draw files
        for file_id in &visible_files {
            if let Some(file) = self.scene.get_file(*file_id) {
                let screen_pos = self.camera.world_to_screen(file.position());
                let radius = file.radius() * camera_zoom;
                let mut color = file.color();
                color.a = file.alpha();

                if color.a > 0.01 {
                    renderer.draw_disc(screen_pos, radius.max(1.0), color);
                }
            }
        }

        // Draw actions (beams from users to files)
        for action in self.scene.actions() {
            if action.is_complete() {
                continue;
            }

            let user_opt = self.scene.get_user(action.user());
            let file_opt = self.scene.get_file(action.file());

            if let (Some(user), Some(file)) = (user_opt, file_opt) {
                let user_screen = self.camera.world_to_screen(user.position());
                let file_screen = self.camera.world_to_screen(file.position());
                let beam_end = user_screen.lerp(file_screen, action.progress());

                let beam_color = action.beam_color();
                renderer.draw_line(user_screen, beam_end, 2.0, beam_color);

                // Draw beam head
                let head_radius = (3.0 * camera_zoom).max(2.0);
                renderer.draw_disc(beam_end, head_radius, beam_color);
            }
        }

        // Draw users
        for user_id in &visible_users {
            if let Some(user) = self.scene.get_user(*user_id) {
                if user.alpha() < 0.01 {
                    continue;
                }

                let screen_pos = self.camera.world_to_screen(user.position());
                let radius = (user.radius() * camera_zoom).max(5.0);
                let color = user.display_color();

                // Draw border/outline (darker version of user color)
                let border_color = Color::new(color.r * 0.4, color.g * 0.4, color.b * 0.4, color.a);
                renderer.draw_disc(screen_pos, radius + 2.0, border_color);

                // Draw user circle
                renderer.draw_disc(screen_pos, radius, color);

                // Draw a highlight ring if active
                if user.is_active() {
                    renderer.draw_circle(
                        screen_pos,
                        radius * 1.3,
                        2.0,
                        color.with_alpha(0.5 * user.alpha()),
                    );
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

    #[test]
    fn test_color_from_hex() {
        let color = Color::from_hex(0xff0000);
        assert!((color.r - 1.0).abs() < 0.01);
        assert!(color.g < 0.01);
        assert!(color.b < 0.01);
    }

    #[test]
    fn test_renderer_type_as_str() {
        assert_eq!(RendererType::WebGl2.as_str(), "webgl2");
        assert_eq!(RendererType::Software.as_str(), "software");
    }
}
