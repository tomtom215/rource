// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Software rasterizer backend.
//!
//! A pure-CPU rendering backend that works on any platform without GPU.
//! Uses anti-aliased drawing algorithms for high-quality output.

// Allow casts that could wrap on 32-bit platforms - dimensions won't overflow
#![allow(clippy::cast_possible_wrap)]
// Allow lossless casts written as `as` for brevity in numeric code
#![allow(clippy::cast_lossless)]

use std::collections::HashMap;

use rource_math::{Bounds, Color, Mat4, Vec2, Vec3};

use crate::{FontCache, FontId, Renderer, Texture, TextureId};

// ============================================================================
// Free Functions for Split Borrow Pattern
// ============================================================================
//
// These free functions enable split borrowing of SoftwareRenderer fields,
// avoiding the need to clone texture data in draw_quad(). The borrow checker
// can't see that self.textures and self.pixels are disjoint, so we pass them
// as separate parameters to these functions.

/// Helper function to check if a point is clipped (free function for split borrow pattern).
#[inline]
fn is_clipped_inner(x: i32, y: i32, width: u32, height: u32, clips: &[Bounds]) -> bool {
    if x < 0 || y < 0 || x >= width as i32 || y >= height as i32 {
        return true;
    }
    for clip in clips {
        if x < clip.min.x as i32
            || x > clip.max.x as i32
            || y < clip.min.y as i32
            || y > clip.max.y as i32
        {
            return true;
        }
    }
    false
}

/// Helper function to get pixel index (free function for split borrow pattern).
#[inline]
fn pixel_index_inner(x: i32, y: i32, width: u32, height: u32) -> Option<usize> {
    if x < 0 || y < 0 || x >= width as i32 || y >= height as i32 {
        return None;
    }
    Some((y as usize) * (width as usize) + (x as usize))
}

/// Helper function to plot a pixel with premultiplied alpha (free function for split borrow pattern).
#[inline]
#[allow(clippy::too_many_arguments)] // Explicit parameters needed for split borrow pattern
fn plot_premultiplied_inner(
    pixels: &mut [u32],
    x: i32,
    y: i32,
    width: u32,
    height: u32,
    clips: &[Bounds],
    r: u8,
    g: u8,
    b: u8,
    a: u8,
) {
    if is_clipped_inner(x, y, width, height, clips) {
        return;
    }
    let Some(idx) = pixel_index_inner(x, y, width, height) else {
        return;
    };

    if a == 0 {
        return;
    }

    let existing = pixels[idx];

    if a == 255 {
        pixels[idx] = 0xFF00_0000 | ((r as u32) << 16) | ((g as u32) << 8) | (b as u32);
        return;
    }

    let alpha = a as f32 / 255.0;
    let inv_alpha = 1.0 - alpha;

    let dst_r = ((existing >> 16) & 0xFF) as f32;
    let dst_g = ((existing >> 8) & 0xFF) as f32;
    let dst_b = (existing & 0xFF) as f32;

    let new_r = ((r as f32 * alpha + dst_r * inv_alpha) as u32).min(255);
    let new_g = ((g as f32 * alpha + dst_g * inv_alpha) as u32).min(255);
    let new_b = ((b as f32 * alpha + dst_b * inv_alpha) as u32).min(255);

    pixels[idx] = 0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b;
}

/// Draws a single glyph using explicit split borrows (free function).
///
/// This avoids cloning the glyph bitmap by accepting pixels and the glyph reference
/// as separate parameters, allowing the borrow checker to see they are disjoint from
/// the font_cache borrow.
#[inline]
#[allow(clippy::too_many_arguments)] // Explicit parameters needed for split borrow pattern
fn draw_glyph_inner(
    pixels: &mut [u32],
    width: u32,
    height: u32,
    clips: &[Bounds],
    x: i32,
    y: i32,
    glyph: &crate::font::CachedGlyph,
    color: Color,
) {
    let glyph_width = glyph.metrics.width;
    let glyph_height = glyph.metrics.height;

    for gy in 0..glyph_height {
        for gx in 0..glyph_width {
            let coverage = glyph.bitmap[gy * glyph_width + gx] as f32 / 255.0;
            if coverage > 0.0 {
                let px = x + gx as i32;
                let py = y + gy as i32;
                plot_inner(pixels, width, height, clips, px, py, coverage, color);
            }
        }
    }
}

/// Plots a pixel with coverage blending (free function for split borrow pattern).
#[inline]
fn plot_inner(
    pixels: &mut [u32],
    width: u32,
    height: u32,
    clips: &[Bounds],
    x: i32,
    y: i32,
    brightness: f32,
    color: Color,
) {
    if is_clipped_inner(x, y, width, height, clips) {
        return;
    }

    let Some(idx) = pixel_index_inner(x, y, width, height) else {
        return;
    };

    let existing = pixels[idx];

    // Calculate effective alpha
    let alpha = color.a * brightness;
    if alpha < 0.001 {
        return;
    }

    let inv_alpha = 1.0 - alpha;

    // Extract existing RGB
    let dst_r = ((existing >> 16) & 0xFF) as f32;
    let dst_g = ((existing >> 8) & 0xFF) as f32;
    let dst_b = (existing & 0xFF) as f32;

    // Blend colors
    let new_r = ((color.r * 255.0 * alpha + dst_r * inv_alpha) as u32).min(255);
    let new_g = ((color.g * 255.0 * alpha + dst_g * inv_alpha) as u32).min(255);
    let new_b = ((color.b * 255.0 * alpha + dst_b * inv_alpha) as u32).min(255);

    pixels[idx] = 0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b;
}

/// Draws a textured quad using explicit split borrows (free function).
///
/// This avoids the need to clone the entire texture by accepting pixels and textures
/// as separate parameters, allowing the borrow checker to see they are disjoint.
///
/// # Performance
///
/// This function eliminates the texture clone that was previously required in `draw_quad()`.
/// For a typical 32x32 icon texture, this saves 4KB per textured quad per frame.
/// For larger textures (e.g., 512x512), the savings are over 1MB per quad.
#[inline]
#[allow(clippy::too_many_arguments)] // Explicit parameters needed for split borrow pattern
fn draw_textured_quad_with_textures(
    pixels: &mut [u32],
    width: u32,
    height: u32,
    clips: &[Bounds],
    textures: &HashMap<TextureId, Texture>,
    tex_id: TextureId,
    bounds: Bounds,
    tint: Color,
) {
    let Some(texture) = textures.get(&tex_id) else {
        return;
    };

    let min_x = bounds.min.x.floor() as i32;
    let max_x = bounds.max.x.ceil() as i32;
    let min_y = bounds.min.y.floor() as i32;
    let max_y = bounds.max.y.ceil() as i32;

    let w = bounds.max.x - bounds.min.x;
    let h = bounds.max.y - bounds.min.y;

    if w <= 0.0 || h <= 0.0 {
        return;
    }

    for y in min_y..max_y {
        for x in min_x..max_x {
            let u = (x as f32 - bounds.min.x) / w;
            let v = (y as f32 - bounds.min.y) / h;

            let (tr, tg, tb, ta) = texture.sample(u, v);

            let r = ((tr as f32 / 255.0) * tint.r * 255.0) as u8;
            let g = ((tg as f32 / 255.0) * tint.g * 255.0) as u8;
            let b = ((tb as f32 / 255.0) * tint.b * 255.0) as u8;
            let a = ((ta as f32 / 255.0) * tint.a * 255.0) as u8;

            plot_premultiplied_inner(pixels, x, y, width, height, clips, r, g, b, a);
        }
    }
}

/// Software renderer using CPU-based rasterization.
///
/// This renderer provides:
/// - Anti-aliased line drawing using Xiaolin Wu's algorithm
/// - Anti-aliased circle/disc drawing with sub-pixel accuracy
/// - Alpha blending for transparency
/// - Font rendering via fontdue
/// - Optional Z-buffer for 3D depth testing
///
/// # Performance
///
/// For best performance:
/// - Draw opaque objects first, transparent last
/// - Batch similar operations together
/// - Use smaller viewport sizes when possible
#[derive(Debug)]
pub struct SoftwareRenderer {
    /// Pixel buffer (ARGB8 format: 0xAARRGGBB)
    pixels: Vec<u32>,

    /// Z-buffer for depth testing (optional, None when 3D disabled)
    z_buffer: Option<Vec<f32>>,

    /// Whether depth testing is enabled
    depth_test_enabled: bool,

    /// Viewport width
    width: u32,

    /// Viewport height
    height: u32,

    /// Current transformation matrix
    transform: Mat4,

    /// Clip rectangle stack
    clips: Vec<Bounds>,

    /// Font cache
    font_cache: FontCache,

    /// Loaded textures
    textures: HashMap<TextureId, Texture>,

    /// Next texture ID
    next_texture_id: u32,

    /// Reusable buffer for text glyph positioning (avoids per-draw_text allocation and glyph cloning).
    /// Stores (x, y, char, font_id, size_key) tuples for each character in a text string.
    /// Glyphs are looked up again during drawing to avoid cloning bitmap data.
    glyph_buffer: Vec<(i32, i32, char, FontId, u32)>,

    /// File icon extension to texture ID mapping.
    /// Used for file icon rendering in CPU software mode.
    file_icon_textures: HashMap<String, TextureId>,
}

impl SoftwareRenderer {
    /// Creates a new software renderer with the given dimensions.
    ///
    /// # Example
    ///
    /// ```
    /// use rource_render::{Renderer, SoftwareRenderer};
    ///
    /// let renderer = SoftwareRenderer::new(1920, 1080);
    /// assert_eq!(renderer.width(), 1920);
    /// assert_eq!(renderer.height(), 1080);
    /// ```
    pub fn new(width: u32, height: u32) -> Self {
        let size = (width * height) as usize;
        Self {
            pixels: vec![0xFF00_0000; size], // Opaque black
            z_buffer: None,
            depth_test_enabled: false,
            width,
            height,
            transform: Mat4::IDENTITY,
            clips: Vec::new(),
            font_cache: FontCache::new(),
            textures: HashMap::new(),
            next_texture_id: 1,
            // Pre-allocate glyph buffer with capacity for typical text lengths
            glyph_buffer: Vec::with_capacity(256),
            file_icon_textures: HashMap::new(),
        }
    }

    /// Enables 3D depth testing with a Z-buffer.
    ///
    /// When enabled, pixels are only drawn if their depth value is closer
    /// than the existing value in the Z-buffer.
    pub fn enable_depth_test(&mut self) {
        let size = (self.width * self.height) as usize;
        if self.z_buffer.is_none() {
            // Initialize Z-buffer with far plane value (1.0)
            self.z_buffer = Some(vec![1.0; size]);
        }
        self.depth_test_enabled = true;
    }

    /// Disables 3D depth testing.
    pub fn disable_depth_test(&mut self) {
        self.depth_test_enabled = false;
    }

    /// Returns whether depth testing is enabled.
    #[inline]
    #[must_use]
    pub const fn depth_test_enabled(&self) -> bool {
        self.depth_test_enabled
    }

    /// Clears the Z-buffer to the far plane value.
    ///
    /// This should be called at the start of each frame when using depth testing.
    pub fn clear_depth(&mut self) {
        if let Some(ref mut z_buffer) = self.z_buffer {
            z_buffer.fill(1.0);
        }
    }

    /// Tests and writes a depth value at the given pixel position.
    ///
    /// Returns `true` if the depth test passes and the pixel should be drawn.
    /// When depth testing is disabled, always returns `true`.
    #[inline]
    fn depth_test(&mut self, x: u32, y: u32, depth: f32) -> bool {
        if !self.depth_test_enabled {
            return true;
        }

        if let Some(ref mut z_buffer) = self.z_buffer {
            let idx = (y * self.width + x) as usize;
            if idx < z_buffer.len() && depth < z_buffer[idx] {
                z_buffer[idx] = depth;
                return true;
            }
        }
        false
    }

    /// Blends a source color onto an existing pixel value using alpha blending.
    #[inline]
    fn blend_color(existing: u32, src: Color) -> u32 {
        let alpha = src.a;
        if alpha < 0.001 {
            return existing;
        }

        let inv_alpha = 1.0 - alpha;

        // Extract existing RGB
        let dst_r = ((existing >> 16) & 0xFF) as f32;
        let dst_g = ((existing >> 8) & 0xFF) as f32;
        let dst_b = (existing & 0xFF) as f32;

        // Source RGB (0-1 in Color)
        let src_r = src.r * 255.0;
        let src_g = src.g * 255.0;
        let src_b = src.b * 255.0;

        // Blend
        let new_r = ((src_r * alpha + dst_r * inv_alpha) as u32).min(255);
        let new_g = ((src_g * alpha + dst_g * inv_alpha) as u32).min(255);
        let new_b = ((src_b * alpha + dst_b * inv_alpha) as u32).min(255);

        0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b
    }

    /// Draws a disc (filled circle) with depth testing.
    ///
    /// The depth value is used for Z-buffer testing when depth testing is enabled.
    /// This is useful for 3D rendering where screen-space coordinates and depth
    /// are computed by projecting 3D world positions.
    ///
    /// # Performance Optimization
    ///
    /// This function uses squared distance comparisons where possible to avoid
    /// expensive `sqrt()` calls. The disc is divided into three regions:
    ///
    /// 1. **Inner region** (`dist² <= inner_sq`): Full opacity, no sqrt needed
    /// 2. **Edge region** (`inner_sq < dist² <= outer_sq`): Anti-aliased, requires sqrt
    /// 3. **Outer region** (`dist² > outer_sq`): Invisible, early exit
    ///
    /// For a typical disc, ~78% of pixels are in the inner region (no sqrt),
    /// ~18% are in the edge region (sqrt needed), and ~4% are outside.
    ///
    /// # Arguments
    /// * `center` - Screen-space center position
    /// * `radius` - Disc radius in pixels
    /// * `depth` - Depth value (0.0 = near, 1.0 = far)
    /// * `color` - Fill color
    pub fn draw_disc_3d(&mut self, center: Vec2, radius: f32, depth: f32, color: Color) {
        let cx = center.x;
        let cy = center.y;

        // Bounding box
        let min_x = (cx - radius).floor().max(0.0) as i32;
        let max_x = (cx + radius).ceil().min(self.width as f32 - 1.0) as i32;
        let min_y = (cy - radius).floor().max(0.0) as i32;
        let max_y = (cy + radius).ceil().min(self.height as f32 - 1.0) as i32;

        let aa_width = 1.0; // Anti-aliasing edge width

        // Pre-compute squared thresholds to avoid sqrt() in inner loop
        // inner_radius = radius - aa_width (pixels inside this are fully opaque)
        // outer_radius = radius + aa_width (pixels outside this are invisible)
        let inner_radius = (radius - aa_width).max(0.0);
        let inner_sq = inner_radius * inner_radius;
        let outer_radius = radius + aa_width;
        let outer_sq = outer_radius * outer_radius;

        // Pre-compute inverse for anti-aliasing interpolation
        let aa_range = 2.0 * aa_width;

        for py in min_y..=max_y {
            for px in min_x..=max_x {
                let dx = px as f32 + 0.5 - cx;
                let dy = py as f32 + 0.5 - cy;
                let dist2 = dx * dx + dy * dy;

                // Early exit: pixel is outside the outer radius
                if dist2 > outer_sq {
                    continue;
                }

                // Perform depth test
                if !self.depth_test(px as u32, py as u32, depth) {
                    continue;
                }

                // Determine alpha based on region using squared distance comparison
                let alpha = if dist2 <= inner_sq {
                    // Inner region: fully opaque, no sqrt needed
                    color.a
                } else {
                    // Edge region: anti-aliased, sqrt needed for smooth gradient
                    // This branch is taken for ~18% of pixels in a typical disc
                    let dist = dist2.sqrt();
                    let t = (outer_radius - dist) / aa_range;
                    color.a * t
                };

                let idx = (py as u32 * self.width + px as u32) as usize;
                if idx < self.pixels.len() {
                    let src = Color::new(color.r, color.g, color.b, alpha);
                    self.pixels[idx] = Self::blend_color(self.pixels[idx], src);
                }
            }
        }
    }

    /// Draws a line with depth testing.
    ///
    /// Depth is linearly interpolated between start and end points.
    ///
    /// # Arguments
    /// * `start` - Screen-space start position
    /// * `start_depth` - Depth at start (0.0 = near, 1.0 = far)
    /// * `end` - Screen-space end position
    /// * `end_depth` - Depth at end (0.0 = near, 1.0 = far)
    /// * `width` - Line width in pixels
    /// * `color` - Line color
    pub fn draw_line_3d(
        &mut self,
        start: Vec2,
        start_depth: f32,
        end: Vec2,
        end_depth: f32,
        width: f32,
        color: Color,
    ) {
        // For now, use the average depth for the entire line
        // A more accurate implementation would interpolate per-pixel
        let avg_depth = (start_depth + end_depth) * 0.5;

        // Use existing thick line drawing with depth testing
        self.draw_thick_line_with_depth(start, end, width, avg_depth, color);
    }

    /// Draws an anti-aliased thick line with uniform depth testing.
    fn draw_thick_line_with_depth(
        &mut self,
        start: Vec2,
        end: Vec2,
        width: f32,
        depth: f32,
        color: Color,
    ) {
        let dx = end.x - start.x;
        let dy = end.y - start.y;
        let length = dx.hypot(dy);

        if length < 0.001 {
            return;
        }

        let length_sq = length * length;

        let half_width = width * 0.5;

        // Line bounding box
        let min_x = start
            .x
            .min(end.x)
            .floor()
            .max(0.0)
            .min(self.width as f32 - 1.0) as i32
            - (half_width + 1.0) as i32;
        let max_x = start
            .x
            .max(end.x)
            .ceil()
            .max(0.0)
            .min(self.width as f32 - 1.0) as i32
            + (half_width + 1.0) as i32;
        let min_y = start
            .y
            .min(end.y)
            .floor()
            .max(0.0)
            .min(self.height as f32 - 1.0) as i32
            - (half_width + 1.0) as i32;
        let max_y = start
            .y
            .max(end.y)
            .ceil()
            .max(0.0)
            .min(self.height as f32 - 1.0) as i32
            + (half_width + 1.0) as i32;

        // Clamp to viewport
        let min_x = min_x.max(0);
        let max_x = max_x.min(self.width as i32 - 1);
        let min_y = min_y.max(0);
        let max_y = max_y.min(self.height as i32 - 1);

        // Pre-compute squared thresholds to avoid sqrt in the inner loop
        let outer_threshold_sq = (half_width + 1.0) * (half_width + 1.0);
        let inner_threshold_sq = (half_width - 0.5) * (half_width - 0.5);
        let outer_edge_sq = (half_width + 0.5) * (half_width + 0.5);

        for py_int in min_y..=max_y {
            for px_int in min_x..=max_x {
                let point_x = px_int as f32 + 0.5;
                let point_y = py_int as f32 + 0.5;

                // Distance from point to line segment
                let to_start_x = point_x - start.x;
                let to_start_y = point_y - start.y;

                let t = ((to_start_x * dx + to_start_y * dy) / length_sq).clamp(0.0, 1.0);

                let closest_x = start.x + t * dx;
                let closest_y = start.y + t * dy;

                let dist_x = point_x - closest_x;
                let dist_y = point_y - closest_y;
                // Use squared distance to avoid sqrt in most cases
                let dist_sq = dist_x * dist_x + dist_y * dist_y;

                if dist_sq <= outer_threshold_sq {
                    // Perform depth test
                    if !self.depth_test(px_int as u32, py_int as u32, depth) {
                        continue;
                    }

                    // Anti-aliased edge using squared comparisons for inner region
                    let alpha = if dist_sq <= inner_threshold_sq {
                        // Inner region: full opacity, no sqrt needed
                        color.a
                    } else if dist_sq >= outer_edge_sq {
                        // Outside edge: skip, no sqrt needed
                        continue;
                    } else {
                        // Edge region: need actual distance for smooth blending
                        let dist = dist_sq.sqrt();
                        let edge_t = (half_width + 0.5 - dist) / 1.0;
                        color.a * edge_t
                    };

                    let idx = (py_int as u32 * self.width + px_int as u32) as usize;
                    if idx < self.pixels.len() {
                        let src = Color::new(color.r, color.g, color.b, alpha);
                        self.pixels[idx] = Self::blend_color(self.pixels[idx], src);
                    }
                }
            }
        }
    }

    /// Returns a reference to the pixel buffer.
    ///
    /// Pixels are in ARGB8 format (0xAARRGGBB).
    #[inline]
    pub fn pixels(&self) -> &[u32] {
        &self.pixels
    }

    /// Returns a mutable reference to the pixel buffer.
    #[inline]
    pub fn pixels_mut(&mut self) -> &mut [u32] {
        &mut self.pixels
    }

    /// Returns the pixel buffer as raw bytes (ARGB8).
    pub fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.pixels.len() * 4);
        for &pixel in &self.pixels {
            bytes.push(((pixel >> 16) & 0xFF) as u8); // R
            bytes.push(((pixel >> 8) & 0xFF) as u8); // G
            bytes.push((pixel & 0xFF) as u8); // B
            bytes.push(((pixel >> 24) & 0xFF) as u8); // A
        }
        bytes
    }

    /// Returns access to the font cache.
    #[inline]
    pub fn font_cache(&self) -> &FontCache {
        &self.font_cache
    }

    /// Returns mutable access to the font cache.
    #[inline]
    pub fn font_cache_mut(&mut self) -> &mut FontCache {
        &mut self.font_cache
    }

    /// Registers a texture and returns its ID.
    ///
    /// Use this to add custom textures (like user avatars) to the renderer.
    pub fn register_texture(&mut self, texture: Texture) -> TextureId {
        let id = TextureId::new(self.next_texture_id);
        self.next_texture_id += 1;
        self.textures.insert(id, texture);
        id
    }

    /// Unregisters a texture by its ID.
    pub fn unregister_texture(&mut self, id: TextureId) {
        self.textures.remove(&id);
    }

    /// Returns a reference to a registered texture.
    pub fn get_texture(&self, id: TextureId) -> Option<&Texture> {
        self.textures.get(&id)
    }

    /// Transforms a point from world to screen coordinates.
    #[inline]
    fn transform_point(&self, point: Vec2) -> Vec2 {
        let p = self.transform.transform_point(Vec3::from_vec2(point, 0.0));
        Vec2::new(p.x, p.y)
    }

    /// Checks if a point is within the current clip bounds.
    #[inline]
    fn is_clipped(&self, x: i32, y: i32) -> bool {
        if x < 0 || y < 0 || x >= self.width as i32 || y >= self.height as i32 {
            return true;
        }

        for clip in &self.clips {
            if x < clip.min.x as i32
                || x > clip.max.x as i32
                || y < clip.min.y as i32
                || y > clip.max.y as i32
            {
                return true;
            }
        }

        false
    }

    /// Gets the pixel index for screen coordinates.
    #[inline]
    fn pixel_index(&self, x: i32, y: i32) -> Option<usize> {
        if x < 0 || y < 0 || x >= self.width as i32 || y >= self.height as i32 {
            return None;
        }
        Some((y as usize) * (self.width as usize) + (x as usize))
    }

    /// Plots a pixel with alpha blending.
    ///
    /// # Arguments
    /// * `x`, `y` - Screen coordinates
    /// * `brightness` - Coverage/brightness factor (0.0-1.0) for anti-aliasing
    /// * `color` - Source color
    fn plot(&mut self, x: i32, y: i32, brightness: f32, color: Color) {
        if self.is_clipped(x, y) {
            return;
        }

        let Some(idx) = self.pixel_index(x, y) else {
            return;
        };

        let existing = self.pixels[idx];

        // Calculate effective alpha
        let alpha = color.a * brightness;
        if alpha < 0.001 {
            return;
        }

        let inv_alpha = 1.0 - alpha;

        // Extract existing RGB
        let dst_r = ((existing >> 16) & 0xFF) as f32;
        let dst_g = ((existing >> 8) & 0xFF) as f32;
        let dst_b = (existing & 0xFF) as f32;

        // Source RGB (already 0-255 in Color)
        let src_r = color.r * 255.0;
        let src_g = color.g * 255.0;
        let src_b = color.b * 255.0;

        // Blend
        let new_r = ((src_r * alpha + dst_r * inv_alpha) as u32).min(255);
        let new_g = ((src_g * alpha + dst_g * inv_alpha) as u32).min(255);
        let new_b = ((src_b * alpha + dst_b * inv_alpha) as u32).min(255);

        self.pixels[idx] = 0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b;
    }

    /// Anti-aliased line drawing using Xiaolin Wu's algorithm.
    fn draw_line_aa(&mut self, x0: f32, y0: f32, x1: f32, y1: f32, color: Color) {
        let steep = (y1 - y0).abs() > (x1 - x0).abs();

        let (x0, y0, x1, y1) = if steep {
            (y0, x0, y1, x1)
        } else {
            (x0, y0, x1, y1)
        };

        let (x0, y0, x1, y1) = if x0 > x1 {
            (x1, y1, x0, y0)
        } else {
            (x0, y0, x1, y1)
        };

        let dx = x1 - x0;
        let dy = y1 - y0;
        let gradient = if dx.abs() < 0.0001 { 1.0 } else { dy / dx };

        // Handle first endpoint
        let xend = x0.round();
        let yend = y0 + gradient * (xend - x0);
        let xgap = 1.0 - (x0 + 0.5).fract();
        let xpxl1 = xend as i32;
        let ypxl1 = yend.floor() as i32;

        if steep {
            self.plot(ypxl1, xpxl1, (1.0 - yend.fract()) * xgap, color);
            self.plot(ypxl1 + 1, xpxl1, yend.fract() * xgap, color);
        } else {
            self.plot(xpxl1, ypxl1, (1.0 - yend.fract()) * xgap, color);
            self.plot(xpxl1, ypxl1 + 1, yend.fract() * xgap, color);
        }

        let mut intery = yend + gradient;

        // Handle second endpoint
        let xend = x1.round();
        let yend = y1 + gradient * (xend - x1);
        let xgap = (x1 + 0.5).fract();
        let xpxl2 = xend as i32;
        let ypxl2 = yend.floor() as i32;

        if steep {
            self.plot(ypxl2, xpxl2, (1.0 - yend.fract()) * xgap, color);
            self.plot(ypxl2 + 1, xpxl2, yend.fract() * xgap, color);
        } else {
            self.plot(xpxl2, ypxl2, (1.0 - yend.fract()) * xgap, color);
            self.plot(xpxl2, ypxl2 + 1, yend.fract() * xgap, color);
        }

        // Main loop
        for x in (xpxl1 + 1)..xpxl2 {
            if steep {
                self.plot(intery.floor() as i32, x, 1.0 - intery.fract(), color);
                self.plot(intery.floor() as i32 + 1, x, intery.fract(), color);
            } else {
                self.plot(x, intery.floor() as i32, 1.0 - intery.fract(), color);
                self.plot(x, intery.floor() as i32 + 1, intery.fract(), color);
            }
            intery += gradient;
        }
    }

    /// Draws a thick anti-aliased line by drawing multiple parallel lines.
    fn draw_thick_line_aa(&mut self, start: Vec2, end: Vec2, width: f32, color: Color) {
        if width <= 1.0 {
            self.draw_line_aa(start.x, start.y, end.x, end.y, color);
            return;
        }

        // Calculate perpendicular direction
        let dir = (end - start).normalized();
        let perp = Vec2::new(-dir.y, dir.x);

        // Draw multiple parallel lines
        let half_width = width / 2.0;
        let steps = (width.ceil() as i32).max(1);

        for i in 0..steps {
            let offset = (i as f32 - (steps - 1) as f32 / 2.0) * (width / steps as f32);
            let p = perp * offset;

            // Calculate coverage for edge lines
            let coverage = if offset.abs() < half_width - 0.5 {
                1.0
            } else {
                1.0 - (offset.abs() - (half_width - 0.5)).min(1.0)
            };

            if coverage > 0.0 {
                let c = color.with_alpha(color.a * coverage);
                self.draw_line_aa(start.x + p.x, start.y + p.y, end.x + p.x, end.y + p.y, c);
            }
        }
    }

    /// Draws a filled circle with anti-aliased edges.
    fn draw_disc_aa(&mut self, cx: f32, cy: f32, radius: f32, color: Color) {
        let min_x = (cx - radius - 1.0).floor() as i32;
        let max_x = (cx + radius + 1.0).ceil() as i32;
        let min_y = (cy - radius - 1.0).floor() as i32;
        let max_y = (cy + radius + 1.0).ceil() as i32;

        let inner_r2 = (radius - 1.0).max(0.0) * (radius - 1.0).max(0.0);

        for y in min_y..=max_y {
            for x in min_x..=max_x {
                let dx = x as f32 - cx;
                let dy = y as f32 - cy;
                let dist2 = dx * dx + dy * dy;

                if dist2 <= inner_r2 {
                    // Fully inside
                    self.plot(x, y, 1.0, color);
                } else if dist2 <= (radius + 1.0) * (radius + 1.0) {
                    // Edge - calculate coverage
                    let dist = dist2.sqrt();
                    let coverage = (radius + 0.5 - dist).clamp(0.0, 1.0);
                    if coverage > 0.0 {
                        self.plot(x, y, coverage, color);
                    }
                }
            }
        }
    }

    /// Draws an outlined circle with anti-aliased edges.
    fn draw_circle_aa(&mut self, cx: f32, cy: f32, radius: f32, width: f32, color: Color) {
        let half_width = width / 2.0;
        let outer_radius = radius + half_width;
        let inner_radius = (radius - half_width).max(0.0);

        let min_x = (cx - outer_radius - 1.0).floor() as i32;
        let max_x = (cx + outer_radius + 1.0).ceil() as i32;
        let min_y = (cy - outer_radius - 1.0).floor() as i32;
        let max_y = (cy + outer_radius + 1.0).ceil() as i32;

        // Pre-compute squared thresholds to avoid sqrt in most cases
        let inner_test_sq = (inner_radius - 0.5) * (inner_radius - 0.5);
        let outer_test_sq = (outer_radius + 0.5) * (outer_radius + 0.5);

        for y in min_y..=max_y {
            for x in min_x..=max_x {
                let dx = x as f32 - cx;
                let dy = y as f32 - cy;
                let dist_sq = dx * dx + dy * dy;

                // Quick rejection using squared distance (no sqrt)
                if dist_sq < inner_test_sq || dist_sq > outer_test_sq {
                    continue;
                }

                // Only compute sqrt for pixels that might be in the ring
                let dist = dist_sq.sqrt();

                // Check if in ring
                if dist >= inner_radius - 0.5 && dist <= outer_radius + 0.5 {
                    // Calculate coverage based on distance from ring center
                    let ring_dist = (dist - radius).abs();
                    let coverage = (half_width + 0.5 - ring_dist).clamp(0.0, 1.0);
                    if coverage > 0.0 {
                        self.plot(x, y, coverage, color);
                    }
                }
            }
        }
    }

    /// Draws a solid colored quad.
    fn draw_solid_quad(&mut self, bounds: Bounds, color: Color) {
        let min_x = bounds.min.x.floor() as i32;
        let max_x = bounds.max.x.ceil() as i32;
        let min_y = bounds.min.y.floor() as i32;
        let max_y = bounds.max.y.ceil() as i32;

        for y in min_y..max_y {
            for x in min_x..max_x {
                // Calculate coverage for edge anti-aliasing
                let coverage_x = {
                    let left = (x as f32 - bounds.min.x + 0.5).clamp(0.0, 1.0);
                    let right = (bounds.max.x - x as f32 + 0.5).clamp(0.0, 1.0);
                    left.min(right)
                };

                let coverage_y = {
                    let top = (y as f32 - bounds.min.y + 0.5).clamp(0.0, 1.0);
                    let bottom = (bounds.max.y - y as f32 + 0.5).clamp(0.0, 1.0);
                    top.min(bottom)
                };

                let coverage = coverage_x * coverage_y;
                if coverage > 0.0 {
                    self.plot(x, y, coverage, color);
                }
            }
        }
    }

    // Note: draw_glyph has been replaced by draw_glyph_inner free function
    // to enable split borrow pattern (avoid cloning glyph bitmap data).

    // ========================================================================
    // File Icon Methods
    // ========================================================================

    /// Initializes file icons for common extensions.
    ///
    /// This pre-generates icons for common file extensions and stores them
    /// as CPU textures for software rendering.
    ///
    /// # Returns
    ///
    /// `true` if initialization succeeded (always succeeds for software renderer).
    pub fn init_file_icons(&mut self) -> bool {
        use crate::backend::icons::{
            common_extensions, generate_default_icon, generate_icon, ICON_SIZE,
        };

        // Register common file extensions
        for (ext, color) in common_extensions() {
            let icon_data = generate_icon(color);
            let texture = Texture::new(ICON_SIZE as u32, ICON_SIZE as u32, icon_data);
            let tex_id = TextureId::new(self.next_texture_id);
            self.next_texture_id += 1;
            self.textures.insert(tex_id, texture);
            self.file_icon_textures.insert(ext.to_lowercase(), tex_id);
        }

        // Register default icon for unknown extensions
        let default_icon = generate_default_icon();
        let texture = Texture::new(ICON_SIZE as u32, ICON_SIZE as u32, default_icon);
        let tex_id = TextureId::new(self.next_texture_id);
        self.next_texture_id += 1;
        self.textures.insert(tex_id, texture);
        self.file_icon_textures
            .insert("_default".to_string(), tex_id);

        true
    }

    /// Returns whether file icons are initialized.
    #[inline]
    pub fn has_file_icons(&self) -> bool {
        !self.file_icon_textures.is_empty()
    }

    /// Returns the number of registered file icon types.
    #[inline]
    pub fn file_icon_count(&self) -> u32 {
        self.file_icon_textures.len() as u32
    }

    /// Returns the texture ID for a file extension.
    ///
    /// If the extension is not registered, returns the default icon.
    /// If file icons are not initialized, returns `None`.
    ///
    /// Note: Uses stack-allocated buffer for ASCII lowercase to avoid heap allocation.
    pub fn get_file_icon_texture(&self, extension: &str) -> Option<TextureId> {
        if self.file_icon_textures.is_empty() {
            return None;
        }

        // Fast path: Use stack buffer for common short extensions (< 16 chars)
        // This avoids heap allocation for `to_lowercase()` on every lookup
        let mut stack_buf = [0u8; 16];
        let ext_lower: Option<&str> = if extension.len() <= 16 && extension.is_ascii() {
            for (i, b) in extension.bytes().enumerate() {
                stack_buf[i] = b.to_ascii_lowercase();
            }
            // Safe: ASCII bytes are always valid UTF-8
            std::str::from_utf8(&stack_buf[..extension.len()]).ok()
        } else {
            None
        };

        if let Some(ext_lower) = ext_lower {
            self.file_icon_textures
                .get(ext_lower)
                .copied()
                .or_else(|| self.file_icon_textures.get("_default").copied())
        } else {
            // Fallback for rare long/non-ASCII extensions (heap allocates)
            self.file_icon_textures
                .get(&extension.to_lowercase())
                .copied()
                .or_else(|| self.file_icon_textures.get("_default").copied())
        }
    }

    /// Registers a custom icon for a file extension.
    ///
    /// If the extension is already registered, this does nothing.
    /// If file icons are not initialized, this initializes them first.
    ///
    /// # Arguments
    ///
    /// * `extension` - File extension (e.g., "custom")
    /// * `color` - Color for the icon
    ///
    /// # Returns
    ///
    /// `true` if the icon was registered.
    pub fn register_file_icon(&mut self, extension: &str, color: rource_math::Color) -> bool {
        use crate::backend::icons::{generate_icon, ICON_SIZE};

        let ext_lower = extension.to_lowercase();

        // Check if already registered
        if self.file_icon_textures.contains_key(&ext_lower) {
            return true;
        }

        // Generate and register icon
        let icon_data = generate_icon(color);
        let texture = Texture::new(ICON_SIZE as u32, ICON_SIZE as u32, icon_data);
        let tex_id = TextureId::new(self.next_texture_id);
        self.next_texture_id += 1;
        self.textures.insert(tex_id, texture);
        self.file_icon_textures.insert(ext_lower, tex_id);

        true
    }
}

impl Renderer for SoftwareRenderer {
    fn begin_frame(&mut self) {
        // Nothing special needed for software renderer
    }

    fn end_frame(&mut self) {
        // Nothing special needed for software renderer
    }

    fn clear(&mut self, color: Color) {
        let r = (color.r * 255.0) as u32;
        let g = (color.g * 255.0) as u32;
        let b = (color.b * 255.0) as u32;
        let pixel = 0xFF00_0000 | (r << 16) | (g << 8) | b;

        self.pixels.fill(pixel);

        // Clear Z-buffer when depth testing is enabled
        if self.depth_test_enabled {
            self.clear_depth();
        }
    }

    #[inline]
    fn draw_circle(&mut self, center: Vec2, radius: f32, width: f32, color: Color) {
        let center = self.transform_point(center);
        self.draw_circle_aa(center.x, center.y, radius, width, color);
    }

    #[inline]
    fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color) {
        let center = self.transform_point(center);
        self.draw_disc_aa(center.x, center.y, radius, color);
    }

    #[inline]
    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color) {
        let start = self.transform_point(start);
        let end = self.transform_point(end);
        self.draw_thick_line_aa(start, end, width, color);
    }

    #[inline]
    fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color) {
        if points.len() < 2 {
            return;
        }

        // Zero-allocation streaming: transform and draw each segment immediately
        let mut prev_point = self.transform_point(points[0]);

        for &point in &points[1..] {
            let curr_point = self.transform_point(point);
            self.draw_thick_line_aa(prev_point, curr_point, width, color);
            prev_point = curr_point;
        }
    }

    #[inline]
    fn draw_quad(&mut self, bounds: Bounds, texture: Option<TextureId>, color: Color) {
        // Transform bounds corners
        let min = self.transform_point(bounds.min);
        let max = self.transform_point(bounds.max);
        let transformed = Bounds::new(min, max);

        if let Some(tex_id) = texture {
            // Use split borrow pattern to avoid cloning the entire texture.
            // By passing &mut self.pixels and &self.textures separately to a free function,
            // the borrow checker can see these are disjoint borrows of different struct fields.
            draw_textured_quad_with_textures(
                &mut self.pixels,
                self.width,
                self.height,
                &self.clips,
                &self.textures,
                tex_id,
                transformed,
                color,
            );
        } else {
            self.draw_solid_quad(transformed, color);
        }
    }

    #[inline]
    fn draw_text(&mut self, text: &str, position: Vec2, font: FontId, size: f32, color: Color) {
        let position = self.transform_point(position);

        let mut x = position.x as i32;
        let y = position.y as i32;
        let size_key = (size * 10.0) as u32;

        // Clear and reuse pre-allocated glyph buffer (zero-allocation hot path)
        // First pass: compute positions, store only (x, y, char, font_id, size_key)
        // This avoids cloning glyph bitmap data for every character
        self.glyph_buffer.clear();

        for ch in text.chars() {
            if let Some(glyph) = self.font_cache.rasterize(font, ch, size) {
                let gx = x + glyph.metrics.xmin;
                let gy = y - glyph.metrics.ymin - glyph.metrics.height as i32 + (size * 0.8) as i32; // Baseline adjustment

                // Store only positioning info, no glyph clone
                self.glyph_buffer.push((gx, gy, ch, font, size_key));
                x += glyph.metrics.advance_width as i32;
            }
        }

        // Draw all glyphs using split borrow pattern
        // Second pass: look up glyphs again (just HashMap lookup since cached) and draw
        // We swap the buffer out temporarily to avoid borrow conflicts while drawing
        let mut glyph_positions = std::mem::take(&mut self.glyph_buffer);
        for &(gx, gy, ch, font_id, sz_key) in &glyph_positions {
            // Glyph is already cached, this is just a HashMap lookup (no re-rasterization)
            if let Some(glyph) = self.font_cache.rasterize(font_id, ch, sz_key as f32 / 10.0) {
                // Use split borrow pattern: separate borrows of font_cache and pixels
                draw_glyph_inner(
                    &mut self.pixels,
                    self.width,
                    self.height,
                    &self.clips,
                    gx,
                    gy,
                    glyph,
                    color,
                );
            }
        }
        // Put the buffer back (preserves capacity for next call)
        glyph_positions.clear();
        self.glyph_buffer = glyph_positions;
    }

    fn set_transform(&mut self, transform: Mat4) {
        self.transform = transform;
    }

    fn transform(&self) -> Mat4 {
        self.transform
    }

    fn push_clip(&mut self, bounds: Bounds) {
        let min = self.transform_point(bounds.min);
        let max = self.transform_point(bounds.max);
        self.clips.push(Bounds::new(min, max));
    }

    fn pop_clip(&mut self) {
        self.clips.pop();
    }

    fn width(&self) -> u32 {
        self.width
    }

    fn height(&self) -> u32 {
        self.height
    }

    fn resize(&mut self, width: u32, height: u32) {
        let size = (width * height) as usize;
        self.pixels.resize(size, 0xFF00_0000);
        self.width = width;
        self.height = height;

        // Resize Z-buffer if it exists
        if let Some(ref mut z_buffer) = self.z_buffer {
            z_buffer.resize(size, 1.0);
        }
    }

    fn load_texture(&mut self, width: u32, height: u32, data: &[u8]) -> TextureId {
        let id = TextureId::new(self.next_texture_id);
        self.next_texture_id += 1;

        let texture = Texture::new(width, height, data.to_vec());
        self.textures.insert(id, texture);

        id
    }

    fn unload_texture(&mut self, texture: TextureId) {
        self.textures.remove(&texture);
    }

    fn load_font(&mut self, data: &[u8]) -> Option<FontId> {
        self.font_cache.load(data)
    }

    // =========================================================================
    // File Icon Methods
    // =========================================================================
    // The SoftwareRenderer uses the default trait implementations which
    // render colored discs as fallback. No GPU texture arrays available.
    // init_file_icons() returns false, has_file_icons() returns false,
    // and draw_file_icon() draws a colored disc.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_software_renderer_new() {
        let renderer = SoftwareRenderer::new(100, 100);
        assert_eq!(renderer.width(), 100);
        assert_eq!(renderer.height(), 100);
        assert_eq!(renderer.pixels().len(), 10000);
    }

    #[test]
    fn test_software_renderer_clear() {
        let mut renderer = SoftwareRenderer::new(10, 10);
        renderer.clear(Color::WHITE);

        // Check all pixels are white (0xFFFF_FFFF but we store as 0xFFRRGGBB)
        for &pixel in renderer.pixels() {
            assert_eq!(pixel, 0xFFFF_FFFF);
        }
    }

    #[test]
    fn test_software_renderer_clear_color() {
        let mut renderer = SoftwareRenderer::new(10, 10);
        let red = Color::new(1.0, 0.0, 0.0, 1.0);
        renderer.clear(red);

        // Check all pixels are red
        for &pixel in renderer.pixels() {
            assert_eq!(pixel, 0xFFFF_0000);
        }
    }

    #[test]
    fn test_software_renderer_resize() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.resize(200, 150);

        assert_eq!(renderer.width(), 200);
        assert_eq!(renderer.height(), 150);
        assert_eq!(renderer.pixels().len(), 30000);
    }

    #[test]
    fn test_software_renderer_draw_disc() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);
        renderer.draw_disc(Vec2::new(50.0, 50.0), 10.0, Color::WHITE);

        // Check center pixel is white
        let center_idx = 50 * 100 + 50;
        assert_eq!(renderer.pixels()[center_idx], 0xFFFF_FFFF);
    }

    #[test]
    fn test_software_renderer_draw_line() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);
        renderer.draw_line(
            Vec2::new(10.0, 50.0),
            Vec2::new(90.0, 50.0),
            1.0,
            Color::WHITE,
        );

        // Check some pixels along the line are modified
        let line_idx = 50 * 100 + 50;
        let pixel = renderer.pixels()[line_idx];
        // Should have some white component
        let r = (pixel >> 16) & 0xFF;
        assert!(r > 0, "Line should affect pixels");
    }

    #[test]
    fn test_software_renderer_draw_circle() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);
        renderer.draw_circle(Vec2::new(50.0, 50.0), 20.0, 2.0, Color::WHITE);

        // Check a pixel on the circle edge is modified
        // At radius 20, the top of the circle is at y=30
        let circle_edge_idx = 30 * 100 + 50;
        let pixel = renderer.pixels()[circle_edge_idx];
        let r = (pixel >> 16) & 0xFF;
        assert!(r > 0, "Circle edge should affect pixels");
    }

    #[test]
    fn test_software_renderer_transform() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        assert_eq!(renderer.transform(), Mat4::IDENTITY);

        let translation = Mat4::translation(10.0, 20.0, 0.0);
        renderer.set_transform(translation);
        assert_eq!(renderer.transform(), translation);
    }

    #[test]
    fn test_software_renderer_clip() {
        let mut renderer = SoftwareRenderer::new(100, 100);

        // Push a clip
        let clip = Bounds::new(Vec2::new(10.0, 10.0), Vec2::new(50.0, 50.0));
        renderer.push_clip(clip);
        assert_eq!(renderer.clips.len(), 1);

        // Pop the clip
        renderer.pop_clip();
        assert_eq!(renderer.clips.len(), 0);
    }

    #[test]
    fn test_software_renderer_load_texture() {
        let mut renderer = SoftwareRenderer::new(100, 100);

        // Create a 2x2 white texture
        let data = vec![255u8; 2 * 2 * 4];
        let id = renderer.load_texture(2, 2, &data);

        assert!(renderer.textures.contains_key(&id));
    }

    #[test]
    fn test_software_renderer_unload_texture() {
        let mut renderer = SoftwareRenderer::new(100, 100);

        let data = vec![255u8; 2 * 2 * 4];
        let id = renderer.load_texture(2, 2, &data);
        assert!(renderer.textures.contains_key(&id));

        renderer.unload_texture(id);
        assert!(!renderer.textures.contains_key(&id));
    }

    #[test]
    fn test_software_renderer_draw_quad() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);

        let bounds = Bounds::new(Vec2::new(20.0, 20.0), Vec2::new(40.0, 40.0));
        renderer.draw_quad(bounds, None, Color::WHITE);

        // Check center of quad is white
        let center_idx = 30 * 100 + 30;
        assert_eq!(renderer.pixels()[center_idx], 0xFFFF_FFFF);
    }

    #[test]
    fn test_software_renderer_as_bytes() {
        let mut renderer = SoftwareRenderer::new(2, 2);
        renderer.clear(Color::new(1.0, 0.5, 0.25, 1.0));

        let bytes = renderer.as_bytes();
        assert_eq!(bytes.len(), 2 * 2 * 4);

        // Check first pixel (RGBA format)
        // Note: 0.5 * 255 = 127.5 truncates to 127, 0.25 * 255 = 63.75 truncates to 63
        assert_eq!(bytes[0], 255); // R
        assert_eq!(bytes[1], 127); // G (0.5 * 255 = 127.5 -> 127 when cast to u32)
        assert_eq!(bytes[2], 63); // B (0.25 * 255 = 63.75 -> 63 when cast to u32)
        assert_eq!(bytes[3], 255); // A
    }

    #[test]
    fn test_software_renderer_begin_end_frame() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        // These should not panic
        renderer.begin_frame();
        renderer.end_frame();
    }

    #[test]
    fn test_software_renderer_draw_spline() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);

        let points = vec![
            Vec2::new(10.0, 50.0),
            Vec2::new(30.0, 30.0),
            Vec2::new(70.0, 70.0),
            Vec2::new(90.0, 50.0),
        ];
        renderer.draw_spline(&points, 1.0, Color::WHITE);

        // Check that some pixels were modified along the path
        // This is a basic check - the spline should have drawn something
        let has_white = renderer.pixels().iter().any(|&p| {
            let r = (p >> 16) & 0xFF;
            r > 0
        });
        assert!(has_white, "Spline should draw something");
    }

    #[test]
    fn test_software_renderer_draw_spline_empty() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);

        // Should not panic with empty or single point
        renderer.draw_spline(&[], 1.0, Color::WHITE);
        renderer.draw_spline(&[Vec2::ZERO], 1.0, Color::WHITE);
    }

    #[test]
    fn test_plot_clipping() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);

        // These should not panic - out of bounds
        renderer.plot(-10, -10, 1.0, Color::WHITE);
        renderer.plot(1000, 1000, 1.0, Color::WHITE);
    }

    #[test]
    fn test_alpha_blending() {
        let mut renderer = SoftwareRenderer::new(10, 10);
        renderer.clear(Color::BLACK);

        // Draw a semi-transparent white pixel
        let semi_white = Color::new(1.0, 1.0, 1.0, 0.5);
        renderer.plot(5, 5, 1.0, semi_white);

        let pixel = renderer.pixels()[5 * 10 + 5];
        let r = (pixel >> 16) & 0xFF;
        let g = (pixel >> 8) & 0xFF;
        let b = pixel & 0xFF;

        // Should be grayish (blended with black)
        assert!(r > 100 && r < 150, "R should be around 128, got {r}");
        assert!(g > 100 && g < 150, "G should be around 128, got {g}");
        assert!(b > 100 && b < 150, "B should be around 128, got {b}");
    }

    #[test]
    fn test_load_default_font() {
        let mut renderer = SoftwareRenderer::new(100, 100);

        // Load the embedded default font
        let font_data = crate::default_font::ROBOTO_MONO;
        let font_id = renderer.load_font(font_data);

        assert!(font_id.is_some(), "Should successfully load default font");
    }

    #[test]
    fn test_draw_text_with_font() {
        let mut renderer = SoftwareRenderer::new(200, 100);
        renderer.clear(Color::BLACK);

        // Load font
        let font_data = crate::default_font::ROBOTO_MONO;
        let font_id = renderer.load_font(font_data).expect("Failed to load font");

        // Draw text
        renderer.draw_text("Hello", Vec2::new(10.0, 50.0), font_id, 16.0, Color::WHITE);

        // Verify some pixels were drawn (text should have affected the buffer)
        let has_white = renderer.pixels().iter().any(|&p| {
            let r = (p >> 16) & 0xFF;
            r > 100 // Some white-ish pixel
        });
        assert!(has_white, "Text rendering should draw something");
    }

    #[test]
    fn test_draw_text_empty_string() {
        let mut renderer = SoftwareRenderer::new(100, 100);
        renderer.clear(Color::BLACK);

        let font_data = crate::default_font::ROBOTO_MONO;
        let font_id = renderer.load_font(font_data).expect("Failed to load font");

        // Should not panic with empty string
        renderer.draw_text("", Vec2::new(10.0, 50.0), font_id, 16.0, Color::WHITE);
    }

    #[test]
    fn test_draw_text_various_sizes() {
        let mut renderer = SoftwareRenderer::new(200, 200);
        renderer.clear(Color::BLACK);

        let font_data = crate::default_font::ROBOTO_MONO;
        let font_id = renderer.load_font(font_data).expect("Failed to load font");

        // Test various font sizes - should not panic
        renderer.draw_text("Small", Vec2::new(10.0, 20.0), font_id, 8.0, Color::WHITE);
        renderer.draw_text("Medium", Vec2::new(10.0, 60.0), font_id, 16.0, Color::WHITE);
        renderer.draw_text("Large", Vec2::new(10.0, 120.0), font_id, 32.0, Color::WHITE);
    }
}
