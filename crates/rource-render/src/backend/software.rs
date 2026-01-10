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

/// Software renderer using CPU-based rasterization.
///
/// This renderer provides:
/// - Anti-aliased line drawing using Xiaolin Wu's algorithm
/// - Anti-aliased circle/disc drawing with sub-pixel accuracy
/// - Alpha blending for transparency
/// - Font rendering via fontdue
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
            width,
            height,
            transform: Mat4::IDENTITY,
            clips: Vec::new(),
            font_cache: FontCache::new(),
            textures: HashMap::new(),
            next_texture_id: 1,
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

    /// Plots a pixel with premultiplied alpha.
    fn plot_premultiplied(&mut self, x: i32, y: i32, r: u8, g: u8, b: u8, a: u8) {
        if self.is_clipped(x, y) {
            return;
        }

        let Some(idx) = self.pixel_index(x, y) else {
            return;
        };

        if a == 0 {
            return;
        }

        let existing = self.pixels[idx];

        if a == 255 {
            // Fully opaque - just overwrite
            self.pixels[idx] = 0xFF00_0000 | ((r as u32) << 16) | ((g as u32) << 8) | (b as u32);
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

        for y in min_y..=max_y {
            for x in min_x..=max_x {
                let dx = x as f32 - cx;
                let dy = y as f32 - cy;
                let dist = dx.hypot(dy);

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

    /// Draws a textured quad.
    fn draw_textured_quad(&mut self, bounds: Bounds, texture: &Texture, tint: Color) {
        let min_x = bounds.min.x.floor() as i32;
        let max_x = bounds.max.x.ceil() as i32;
        let min_y = bounds.min.y.floor() as i32;
        let max_y = bounds.max.y.ceil() as i32;

        let width = bounds.max.x - bounds.min.x;
        let height = bounds.max.y - bounds.min.y;

        if width <= 0.0 || height <= 0.0 {
            return;
        }

        for y in min_y..max_y {
            for x in min_x..max_x {
                // Calculate UV coordinates
                let u = (x as f32 - bounds.min.x) / width;
                let v = (y as f32 - bounds.min.y) / height;

                // Sample texture with bilinear filtering
                let (tr, tg, tb, ta) = texture.sample(u, v);

                // Apply tint
                let r = ((tr as f32 / 255.0) * tint.r * 255.0) as u8;
                let g = ((tg as f32 / 255.0) * tint.g * 255.0) as u8;
                let b = ((tb as f32 / 255.0) * tint.b * 255.0) as u8;
                let a = ((ta as f32 / 255.0) * tint.a * 255.0) as u8;

                self.plot_premultiplied(x, y, r, g, b, a);
            }
        }
    }

    /// Draws a single character glyph.
    fn draw_glyph(&mut self, x: i32, y: i32, glyph: &crate::font::CachedGlyph, color: Color) {
        let glyph_width = glyph.metrics.width;
        let glyph_height = glyph.metrics.height;

        for gy in 0..glyph_height {
            for gx in 0..glyph_width {
                let coverage = glyph.bitmap[gy * glyph_width + gx] as f32 / 255.0;
                if coverage > 0.0 {
                    let px = x + gx as i32;
                    let py = y + gy as i32;
                    self.plot(px, py, coverage, color);
                }
            }
        }
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
    }

    fn draw_circle(&mut self, center: Vec2, radius: f32, width: f32, color: Color) {
        let center = self.transform_point(center);
        self.draw_circle_aa(center.x, center.y, radius, width, color);
    }

    fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color) {
        let center = self.transform_point(center);
        self.draw_disc_aa(center.x, center.y, radius, color);
    }

    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color) {
        let start = self.transform_point(start);
        let end = self.transform_point(end);
        self.draw_thick_line_aa(start, end, width, color);
    }

    fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color) {
        if points.len() < 2 {
            return;
        }

        // Transform all points
        let transformed: Vec<Vec2> = points.iter().map(|&p| self.transform_point(p)).collect();

        // Draw line segments between points
        for window in transformed.windows(2) {
            self.draw_thick_line_aa(window[0], window[1], width, color);
        }
    }

    fn draw_quad(&mut self, bounds: Bounds, texture: Option<TextureId>, color: Color) {
        // Transform bounds corners
        let min = self.transform_point(bounds.min);
        let max = self.transform_point(bounds.max);
        let transformed = Bounds::new(min, max);

        if let Some(tex_id) = texture {
            if let Some(tex) = self.textures.get(&tex_id) {
                // Clone texture data to avoid borrow issues
                let tex_clone = tex.clone();
                self.draw_textured_quad(transformed, &tex_clone, color);
            }
        } else {
            self.draw_solid_quad(transformed, color);
        }
    }

    fn draw_text(&mut self, text: &str, position: Vec2, font: FontId, size: f32, color: Color) {
        let position = self.transform_point(position);

        let mut x = position.x as i32;
        let y = position.y as i32;

        // We need to handle the borrow checker carefully here
        // First, collect all the glyph data we need
        let mut glyph_data: Vec<(i32, i32, crate::font::CachedGlyph)> = Vec::new();

        for ch in text.chars() {
            if let Some(glyph) = self.font_cache.rasterize(font, ch, size) {
                let gx = x + glyph.metrics.xmin;
                let gy = y - glyph.metrics.ymin - glyph.metrics.height as i32 + (size * 0.8) as i32; // Baseline adjustment

                glyph_data.push((gx, gy, glyph.clone()));
                x += glyph.metrics.advance_width as i32;
            }
        }

        // Now draw all glyphs
        for (gx, gy, glyph) in &glyph_data {
            self.draw_glyph(*gx, *gy, glyph, color);
        }
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
}
