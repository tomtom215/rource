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

use std::fmt::Write as FmtWrite;
use std::path::PathBuf;

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{CanvasRenderingContext2d, HtmlCanvasElement, ImageData};

use rource_core::camera::Camera;
use rource_core::config::Settings;
use rource_core::entity::{DirId, FileId, UserId};
use rource_core::scene::{ActionType, EntityType, Scene};
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
// Enhanced Visual Rendering
// ============================================================================

/// Number of segments for Catmull-Rom spline interpolation
const SPLINE_SEGMENTS: usize = 12;

/// Curve tension for branch splines (0.0 = straight, 0.5 = natural curves)
const BRANCH_CURVE_TENSION: f32 = 0.4;

/// Glow intensity multiplier for action beams
const BEAM_GLOW_INTENSITY: f32 = 0.4;

/// Number of glow layers for beams
const BEAM_GLOW_LAYERS: usize = 3;

/// Generates Catmull-Rom spline points between control points.
fn catmull_rom_spline(points: &[Vec2], segments_per_span: usize) -> Vec<Vec2> {
    if points.len() < 2 {
        return points.to_vec();
    }

    if points.len() == 2 {
        return points.to_vec();
    }

    let mut result = Vec::with_capacity(points.len() * segments_per_span);

    for i in 0..points.len() - 1 {
        let p0 = if i == 0 { points[0] } else { points[i - 1] };
        let p1 = points[i];
        let p2 = points[i + 1];
        let p3 = if i + 2 >= points.len() {
            points[points.len() - 1]
        } else {
            points[i + 2]
        };

        for j in 0..segments_per_span {
            let t = j as f32 / segments_per_span as f32;
            let point = catmull_rom_interpolate(p0, p1, p2, p3, t);
            result.push(point);
        }
    }

    result.push(*points.last().unwrap());
    result
}

/// Performs Catmull-Rom interpolation between p1 and p2.
#[inline]
fn catmull_rom_interpolate(p0: Vec2, p1: Vec2, p2: Vec2, p3: Vec2, t: f32) -> Vec2 {
    let t2 = t * t;
    let t3 = t2 * t;

    let c0 = -0.5 * t3 + t2 - 0.5 * t;
    let c1 = 1.5 * t3 - 2.5 * t2 + 1.0;
    let c2 = -1.5 * t3 + 2.0 * t2 + 0.5 * t;
    let c3 = 0.5 * t3 - 0.5 * t2;

    Vec2::new(
        c0 * p0.x + c1 * p1.x + c2 * p2.x + c3 * p3.x,
        c0 * p0.y + c1 * p1.y + c2 * p2.y + c3 * p3.y,
    )
}

/// Creates a curved path between two points with natural-looking curvature.
fn create_branch_curve(start: Vec2, end: Vec2, tension: f32) -> Vec<Vec2> {
    let mid = start.lerp(end, 0.5);
    let dir = end - start;
    let length = dir.length();

    if length < 1.0 {
        return vec![start, end];
    }

    let perp = Vec2::new(-dir.y, dir.x).normalized();
    let offset = perp * length * tension * 0.15;

    let ctrl1 = start.lerp(mid, 0.33) + offset * 0.5;
    let ctrl2 = start.lerp(mid, 0.66) + offset;
    let ctrl3 = mid.lerp(end, 0.33) + offset * 0.5;
    let ctrl4 = mid.lerp(end, 0.66);

    catmull_rom_spline(
        &[start, ctrl1, ctrl2, ctrl3, ctrl4, end],
        SPLINE_SEGMENTS / 2,
    )
}

/// Draws a stylized avatar shape (modern person silhouette).
fn draw_avatar_shape<R: Renderer + ?Sized>(
    renderer: &mut R,
    center: Vec2,
    radius: f32,
    color: Color,
    is_active: bool,
    alpha: f32,
) {
    let effective_alpha = color.a * alpha;
    if effective_alpha < 0.01 {
        return;
    }

    let head_radius = radius * 0.42;
    let body_width = radius * 0.7;
    let body_height = radius * 0.65;

    let head_center = Vec2::new(center.x, center.y - radius * 0.28);
    let body_center = Vec2::new(center.x, center.y + radius * 0.32);

    // Draw outer glow for active users
    if is_active {
        for i in 0..4 {
            let glow_radius = radius * (1.4 + i as f32 * 0.15);
            let glow_alpha = effective_alpha * 0.12 * (1.0 - i as f32 * 0.2);
            let glow_color = color.with_alpha(glow_alpha);
            renderer.draw_disc(center, glow_radius, glow_color);
        }
    }

    // Draw shadow/base layer
    let shadow_color = Color::new(
        color.r * 0.2,
        color.g * 0.2,
        color.b * 0.2,
        effective_alpha * 0.6,
    );
    renderer.draw_disc(center, radius * 1.05, shadow_color);

    // Draw body (pill shape approximated with overlapping discs)
    let body_color = Color::new(
        color.r * 0.85,
        color.g * 0.85,
        color.b * 0.85,
        effective_alpha,
    );

    let body_top = body_center.y - body_height * 0.4;
    let body_bottom = body_center.y + body_height * 0.4;
    let steps = 6;
    for i in 0..=steps {
        let t = i as f32 / steps as f32;
        let y = body_top + t * (body_bottom - body_top);
        let taper = 1.0 - (t - 0.5).abs() * 0.3;
        let w = body_width * taper * 0.5;
        renderer.draw_disc(Vec2::new(center.x, y), w, body_color);
    }

    // Draw head
    let head_color = color.with_alpha(effective_alpha);
    renderer.draw_disc(head_center, head_radius, head_color);

    // Head highlight
    let highlight_offset = Vec2::new(-head_radius * 0.25, -head_radius * 0.25);
    let highlight_color = Color::new(1.0, 1.0, 1.0, effective_alpha * 0.25);
    renderer.draw_disc(
        head_center + highlight_offset,
        head_radius * 0.35,
        highlight_color,
    );

    // Active indicator ring
    if is_active {
        let ring_color = Color::new(1.0, 1.0, 1.0, effective_alpha * 0.4);
        renderer.draw_circle(center, radius * 1.15, 1.5, ring_color);
    }
}

/// Draws an action beam with glow effect.
fn draw_action_beam<R: Renderer + ?Sized>(
    renderer: &mut R,
    start: Vec2,
    end: Vec2,
    progress: f32,
    color: Color,
    zoom: f32,
) {
    let beam_end = start.lerp(end, progress);

    // Draw glow layers
    for i in 0..BEAM_GLOW_LAYERS {
        let layer = i as f32;
        let width = (2.0 + layer * 2.0) * zoom.max(0.5);
        let alpha = color.a * BEAM_GLOW_INTENSITY * (1.0 - layer * 0.25);
        let glow_color = color.with_alpha(alpha);
        renderer.draw_line(start, beam_end, width, glow_color);
    }

    // Draw core beam (brightest)
    let core_color = Color::new(
        (color.r + 0.3).min(1.0),
        (color.g + 0.3).min(1.0),
        (color.b + 0.3).min(1.0),
        color.a,
    );
    renderer.draw_line(start, beam_end, 1.5 * zoom.max(0.5), core_color);

    // Draw beam head with glow
    let head_radius = (4.0 * zoom).max(2.5);

    for i in 0..2 {
        let glow_r = head_radius * (1.5 + i as f32 * 0.5);
        let glow_a = color.a * 0.3 * (1.0 - i as f32 * 0.3);
        renderer.draw_disc(beam_end, glow_r, color.with_alpha(glow_a));
    }

    renderer.draw_disc(beam_end, head_radius, core_color);

    // Tiny bright center
    let center_color = Color::new(1.0, 1.0, 1.0, color.a * 0.8);
    renderer.draw_disc(beam_end, head_radius * 0.4, center_color);
}

/// Draws a curved branch line with gradient effect.
fn draw_curved_branch<R: Renderer + ?Sized>(
    renderer: &mut R,
    start: Vec2,
    end: Vec2,
    width: f32,
    color: Color,
    use_curve: bool,
) {
    if color.a < 0.01 {
        return;
    }

    if use_curve {
        let curve_points = create_branch_curve(start, end, BRANCH_CURVE_TENSION);
        renderer.draw_spline(&curve_points, width, color);

        // Subtle glow along the curve
        let glow_color = color.with_alpha(color.a * 0.15);
        renderer.draw_spline(&curve_points, width * 2.5, glow_color);
    } else {
        renderer.draw_line(start, end, width, color);
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
}

// ============================================================================
// Main Rource WASM API
// ============================================================================

/// Number of frame samples for FPS averaging.
const FRAME_SAMPLE_COUNT: usize = 60;

/// Hit radius for entity picking (in world units).
const ENTITY_HIT_RADIUS: f32 = 15.0;

/// Draggable entity type.
#[derive(Debug, Clone, Copy)]
enum DragTarget {
    /// Dragging a file entity.
    File(FileId),
    /// Dragging a user entity.
    User(UserId),
}

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
        if let Some(drag_target) = self.hit_test_user(world_pos, hit_radius) {
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
        if let Some(drag_target) = self.hit_test_file(world_pos, hit_radius) {
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
                    self.move_connected_entities_for_user(user_id, delta);
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
                        self.move_connected_entities_for_file(file_id, dir_id, delta);
                    }
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
    #[wasm_bindgen(js_name = getTotalFrames)]
    pub fn get_total_frames(&self) -> u64 {
        self.perf_metrics.total_frames
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
    /// Tests if a user is within the hit radius of the given world position.
    ///
    /// Returns the drag target if a user is found.
    fn hit_test_user(&self, world_pos: Vec2, hit_radius: f32) -> Option<DragTarget> {
        // Query entities in the hit area
        let entities = self.scene.query_entities_circle(world_pos, hit_radius);

        // Find the closest user
        let mut closest_user: Option<(UserId, f32)> = None;

        for entity in entities {
            if let EntityType::User(user_id) = entity {
                if let Some(user) = self.scene.get_user(user_id) {
                    let dist = (user.position() - world_pos).length();
                    // Check if within the user's radius (with some tolerance)
                    let effective_radius = user.radius() + hit_radius * 0.5;
                    if dist <= effective_radius
                        && (closest_user.is_none() || dist < closest_user.unwrap().1)
                    {
                        closest_user = Some((user_id, dist));
                    }
                }
            }
        }

        closest_user.map(|(id, _)| DragTarget::User(id))
    }

    /// Tests if a file is within the hit radius of the given world position.
    ///
    /// Returns the drag target if a file is found.
    fn hit_test_file(&self, world_pos: Vec2, hit_radius: f32) -> Option<DragTarget> {
        // Query entities in the hit area
        let entities = self.scene.query_entities_circle(world_pos, hit_radius);

        // Find the closest file
        let mut closest_file: Option<(FileId, f32)> = None;

        for entity in entities {
            if let EntityType::File(file_id) = entity {
                if let Some(file) = self.scene.get_file(file_id) {
                    // Skip files that are faded out
                    if file.alpha() < 0.1 {
                        continue;
                    }
                    let dist = (file.position() - world_pos).length();
                    // Check if within the file's radius (with some tolerance)
                    let effective_radius = file.radius() + hit_radius * 0.5;
                    if dist <= effective_radius
                        && (closest_file.is_none() || dist < closest_file.unwrap().1)
                    {
                        closest_file = Some((file_id, dist));
                    }
                }
            }
        }

        closest_file.map(|(id, _)| DragTarget::File(id))
    }

    /// Drag coupling strength for connected entities (0.0 = no coupling, 1.0 = full coupling).
    /// Lower values create a more elastic, spring-like effect.
    const DRAG_COUPLING_STRENGTH: f32 = 0.6;

    /// Distance threshold beyond which coupling decreases (in world units).
    const DRAG_COUPLING_DISTANCE_THRESHOLD: f32 = 150.0;

    /// Moves entities connected to a dragged file.
    ///
    /// Connected entities include:
    /// - Sibling files in the same directory
    /// - The parent directory
    /// - Child directories (if dragging a directory)
    fn move_connected_entities_for_file(
        &mut self,
        dragged_file_id: FileId,
        dir_id: DirId,
        delta: Vec2,
    ) {
        // Skip if delta is negligible
        if delta.length() < 0.1 {
            return;
        }

        // Get the dragged file's position for distance-based coupling
        let dragged_pos = self
            .scene
            .get_file(dragged_file_id)
            .map_or(Vec2::ZERO, rource_core::scene::FileNode::position);

        // Move sibling files in the same directory
        let sibling_ids: Vec<FileId> = self
            .scene
            .directories()
            .get(dir_id)
            .map(|dir| dir.files().to_vec())
            .unwrap_or_default();

        for sibling_id in sibling_ids {
            if sibling_id == dragged_file_id {
                continue; // Skip the dragged file itself
            }

            if let Some(sibling) = self.scene.get_file_mut(sibling_id) {
                // Calculate distance-based coupling (closer = stronger)
                let distance = (sibling.position() - dragged_pos).length();
                let distance_factor =
                    (1.0 - distance / Self::DRAG_COUPLING_DISTANCE_THRESHOLD).clamp(0.0, 1.0);
                let coupling = Self::DRAG_COUPLING_STRENGTH * distance_factor;

                if coupling > 0.01 {
                    let new_pos = sibling.position() + delta * coupling;
                    sibling.set_position(new_pos);
                    sibling.set_target(new_pos);
                }
            }
        }

        // Move the parent directory (with reduced coupling)
        // Also zero velocity so physics doesn't fight the drag
        if let Some(dir) = self.scene.directories_mut().get_mut(dir_id) {
            let distance = (dir.position() - dragged_pos).length();
            let distance_factor =
                (1.0 - distance / Self::DRAG_COUPLING_DISTANCE_THRESHOLD).clamp(0.0, 1.0);
            let coupling = Self::DRAG_COUPLING_STRENGTH * 0.5 * distance_factor;

            if coupling > 0.01 {
                let new_pos = dir.position() + delta * coupling;
                dir.set_position(new_pos);
                dir.set_velocity(Vec2::ZERO);
            }
        }
    }

    /// Moves entities connected to a dragged user.
    ///
    /// Connected entities include files that have active action beams from this user.
    fn move_connected_entities_for_user(&mut self, user_id: UserId, delta: Vec2) {
        // Skip if delta is negligible
        if delta.length() < 0.1 {
            return;
        }

        // Get the dragged user's position for distance-based coupling
        let dragged_pos = self
            .scene
            .get_user(user_id)
            .map_or(Vec2::ZERO, rource_core::scene::User::position);

        // Collect file IDs that have active actions from this user
        let connected_file_ids: Vec<FileId> = self
            .scene
            .actions()
            .iter()
            .filter(|action| action.user() == user_id && !action.is_complete())
            .map(rource_core::scene::Action::file)
            .collect();

        // Move connected files and update their targets so they don't snap back
        for file_id in connected_file_ids {
            if let Some(file) = self.scene.get_file_mut(file_id) {
                // Calculate distance-based coupling
                let distance = (file.position() - dragged_pos).length();
                let distance_factor =
                    (1.0 - distance / Self::DRAG_COUPLING_DISTANCE_THRESHOLD).clamp(0.0, 1.0);
                let coupling = Self::DRAG_COUPLING_STRENGTH * distance_factor;

                if coupling > 0.01 {
                    let new_pos = file.position() + delta * coupling;
                    file.set_position(new_pos);
                    file.set_target(new_pos);
                }
            }
        }
    }

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
    // PNG/CRC32 Tests
    // ========================================================================

    #[test]
    fn test_crc32_empty() {
        let result = crc32(b"IEND", &[]);
        // Known CRC32 for empty IEND chunk
        assert_eq!(result, 0xAE42_6082);
    }

    #[test]
    fn test_crc32_ihdr() {
        // Test with a known IHDR chunk (1x1 RGB image)
        let ihdr_data = [
            0, 0, 0, 1, // width = 1
            0, 0, 0, 1, // height = 1
            8, // bit depth
            2, // color type (RGB)
            0, // compression
            0, // filter
            0, // interlace
        ];
        let crc = crc32(b"IHDR", &ihdr_data);
        // Should be a valid non-zero CRC
        assert_ne!(crc, 0);
    }

    #[test]
    fn test_deflate_compress_empty() {
        let result = deflate_compress(&[]);
        // Compressed empty data should have zlib header + empty block + adler32
        assert!(!result.is_empty());
        // Check zlib header
        assert_eq!(result[0], 0x78);
        assert_eq!(result[1], 0x01);
    }

    #[test]
    fn test_deflate_compress_small() {
        let data = b"Hello, World!";
        let result = deflate_compress(data);
        // Compressed data should be larger than original for small data
        // (uncompressed storage adds overhead)
        assert!(!result.is_empty());
        // Should contain the original data
        assert!(result.windows(data.len()).any(|w| w == data));
    }

    #[test]
    fn test_write_png_small_image() {
        // Create a 2x2 red image
        let pixels: Vec<u32> = vec![
            0xFFFF_0000,
            0xFFFF_0000, // Red, Red
            0xFFFF_0000,
            0xFFFF_0000, // Red, Red
        ];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 2, 2).unwrap();

        // Check PNG signature
        assert_eq!(
            &output[0..8],
            &[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
        );

        // Check IHDR chunk type
        assert_eq!(&output[12..16], b"IHDR");

        // Output should contain IEND
        assert!(output.windows(4).any(|w| w == b"IEND"));
    }

    #[test]
    fn test_write_png_1x1_pixel() {
        let pixels: Vec<u32> = vec![0xFF00_FF00]; // Green
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 1, 1).unwrap();

        // Should produce valid PNG with signature
        assert!(output.len() > 8);
        assert_eq!(
            &output[0..8],
            &[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
        );
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
    // Catmull-Rom Spline Tests
    // ========================================================================

    #[test]
    fn test_catmull_rom_spline_empty() {
        let points: Vec<Vec2> = vec![];
        let result = catmull_rom_spline(&points, 10);
        assert!(result.is_empty());
    }

    #[test]
    fn test_catmull_rom_spline_single_point() {
        let points = vec![Vec2::new(1.0, 2.0)];
        let result = catmull_rom_spline(&points, 10);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Vec2::new(1.0, 2.0));
    }

    #[test]
    fn test_catmull_rom_spline_two_points() {
        let points = vec![Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        let result = catmull_rom_spline(&points, 10);
        // With only 2 points, returns the original points
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], Vec2::new(0.0, 0.0));
        assert_eq!(result[1], Vec2::new(10.0, 10.0));
    }

    #[test]
    fn test_catmull_rom_spline_three_points() {
        let points = vec![
            Vec2::new(0.0, 0.0),
            Vec2::new(5.0, 5.0),
            Vec2::new(10.0, 0.0),
        ];
        let result = catmull_rom_spline(&points, 4);
        // Should have segments + 1 points per span, plus final point
        assert!(result.len() > 3);
        // First and last should match original
        assert_eq!(result[0], Vec2::new(0.0, 0.0));
        assert_eq!(*result.last().unwrap(), Vec2::new(10.0, 0.0));
    }

    #[test]
    fn test_catmull_rom_spline_many_points() {
        let points = vec![
            Vec2::new(0.0, 0.0),
            Vec2::new(2.0, 4.0),
            Vec2::new(4.0, 0.0),
            Vec2::new(6.0, 4.0),
            Vec2::new(8.0, 0.0),
        ];
        let result = catmull_rom_spline(&points, 8);
        // Should produce smooth interpolation
        assert!(result.len() > points.len());
        // Endpoints preserved
        assert_eq!(result[0], points[0]);
        assert_eq!(*result.last().unwrap(), *points.last().unwrap());
    }

    #[test]
    fn test_catmull_rom_interpolate_at_zero() {
        let p0 = Vec2::new(-1.0, 0.0);
        let p1 = Vec2::new(0.0, 0.0);
        let p2 = Vec2::new(1.0, 0.0);
        let p3 = Vec2::new(2.0, 0.0);
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 0.0);
        // At t=0, should be at p1
        assert!((result.x - p1.x).abs() < 0.001);
        assert!((result.y - p1.y).abs() < 0.001);
    }

    #[test]
    fn test_catmull_rom_interpolate_at_one() {
        let p0 = Vec2::new(-1.0, 0.0);
        let p1 = Vec2::new(0.0, 0.0);
        let p2 = Vec2::new(1.0, 0.0);
        let p3 = Vec2::new(2.0, 0.0);
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 1.0);
        // At t=1, should be at p2
        assert!((result.x - p2.x).abs() < 0.001);
        assert!((result.y - p2.y).abs() < 0.001);
    }

    #[test]
    fn test_catmull_rom_interpolate_midpoint() {
        let p0 = Vec2::new(0.0, 0.0);
        let p1 = Vec2::new(0.0, 0.0);
        let p2 = Vec2::new(4.0, 0.0);
        let p3 = Vec2::new(4.0, 0.0);
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 0.5);
        // At t=0.5, should be roughly in the middle
        assert!(result.x > 1.0 && result.x < 3.0);
    }

    // ========================================================================
    // Branch Curve Tests
    // ========================================================================

    #[test]
    fn test_create_branch_curve_very_short() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.1, 0.1);
        let result = create_branch_curve(start, end, 0.5);
        // Very short distance returns just start and end
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_create_branch_curve_horizontal() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 0.0);
        let result = create_branch_curve(start, end, 0.5);
        // Should have multiple points for a proper curve
        assert!(result.len() >= 2);
        // Start and end preserved
        assert_eq!(result[0], start);
        assert_eq!(*result.last().unwrap(), end);
    }

    #[test]
    fn test_create_branch_curve_vertical() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.0, 100.0);
        let result = create_branch_curve(start, end, 0.5);
        assert!(result.len() >= 2);
        assert_eq!(result[0], start);
        assert_eq!(*result.last().unwrap(), end);
    }

    #[test]
    fn test_create_branch_curve_diagonal() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let result = create_branch_curve(start, end, 0.4);
        assert!(result.len() >= 2);
        // The curve should have control points that add natural curvature
    }

    #[test]
    fn test_create_branch_curve_zero_tension() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(50.0, 50.0);
        let result = create_branch_curve(start, end, 0.0);
        // With zero tension, should still produce a valid curve
        assert!(result.len() >= 2);
    }

    // ========================================================================
    // DragTarget Tests
    // ========================================================================

    #[test]
    fn test_drag_target_user() {
        let user_id = UserId::from_index(42);
        let target = DragTarget::User(user_id);
        assert!(matches!(target, DragTarget::User(_)));
    }

    #[test]
    fn test_drag_target_file() {
        let file_id = FileId::from_index(123);
        let target = DragTarget::File(file_id);
        assert!(matches!(target, DragTarget::File(_)));
    }

    #[test]
    fn test_drag_target_copy() {
        let file_id = FileId::from_index(5);
        let target1 = DragTarget::File(file_id);
        let target2 = target1;
        assert!(matches!(target2, DragTarget::File(_)));
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

    // ========================================================================
    // PNG Writing Edge Cases
    // ========================================================================

    #[test]
    fn test_write_png_transparent_pixel() {
        let pixels: Vec<u32> = vec![0x0000_0000]; // Fully transparent
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 1, 1).unwrap();
        // Should still produce valid PNG
        assert!(output.len() > 8);
    }

    #[test]
    fn test_write_png_various_colors() {
        // 4 pixels: red, green, blue, white
        let pixels: Vec<u32> = vec![
            0xFFFF_0000, // Red
            0xFF00_FF00, // Green
            0xFF00_00FF, // Blue
            0xFFFF_FFFF, // White
        ];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 2, 2).unwrap();
        // Check valid PNG signature
        assert_eq!(
            &output[0..8],
            &[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
        );
    }

    #[test]
    fn test_write_png_wide_image() {
        // 10x1 image
        let pixels: Vec<u32> = vec![0xFFFF_FFFF; 10];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 10, 1).unwrap();
        assert!(output.windows(4).any(|w| w == b"IHDR"));
        assert!(output.windows(4).any(|w| w == b"IEND"));
    }

    #[test]
    fn test_write_png_tall_image() {
        // 1x10 image
        let pixels: Vec<u32> = vec![0xFF00_0000; 10];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 1, 10).unwrap();
        assert!(output.windows(4).any(|w| w == b"IHDR"));
        assert!(output.windows(4).any(|w| w == b"IEND"));
    }

    // ========================================================================
    // Deflate Compression Tests
    // ========================================================================

    #[test]
    fn test_deflate_compress_repeated_data() {
        // Highly compressible data
        let data = vec![0xAA; 1000];
        let result = deflate_compress(&data);
        // Should still produce valid output
        assert!(!result.is_empty());
    }

    #[test]
    fn test_deflate_compress_random_like_data() {
        // Less compressible data
        let data: Vec<u8> = (0..=255).collect();
        let result = deflate_compress(&data);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_deflate_compress_single_byte() {
        let data = vec![0x42];
        let result = deflate_compress(&data);
        assert!(!result.is_empty());
        // Should contain the original byte
        assert!(result.windows(1).any(|w| w[0] == 0x42));
    }
}
