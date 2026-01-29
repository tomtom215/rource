// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Texture management for the renderer.
//!
//! Textures are stored as RGBA8 pixel data and can be used for
//! drawing textured quads and text glyphs.

/// A unique identifier for textures in the renderer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TextureId(u32);

impl TextureId {
    /// Creates a new texture ID.
    #[inline]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns the raw ID value.
    #[inline]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

/// A texture stored in CPU memory.
#[derive(Debug, Clone)]
pub struct Texture {
    /// Width in pixels.
    width: u32,

    /// Height in pixels.
    height: u32,

    /// RGBA8 pixel data (4 bytes per pixel).
    data: Vec<u8>,
}

impl Texture {
    /// Creates a new texture from RGBA8 data.
    ///
    /// # Panics
    ///
    /// Panics if the data length doesn't match `width * height * 4`.
    pub fn new(width: u32, height: u32, data: Vec<u8>) -> Self {
        assert_eq!(
            data.len(),
            (width * height * 4) as usize,
            "Texture data size mismatch: expected {}, got {}",
            width * height * 4,
            data.len()
        );

        Self {
            width,
            height,
            data,
        }
    }

    /// Creates an empty texture filled with a solid color.
    pub fn solid(width: u32, height: u32, r: u8, g: u8, b: u8, a: u8) -> Self {
        let size = (width * height * 4) as usize;
        let mut data = Vec::with_capacity(size);

        for _ in 0..(width * height) {
            data.push(r);
            data.push(g);
            data.push(b);
            data.push(a);
        }

        Self {
            width,
            height,
            data,
        }
    }

    /// Creates an empty transparent texture.
    #[inline]
    pub fn empty(width: u32, height: u32) -> Self {
        Self::solid(width, height, 0, 0, 0, 0)
    }

    /// Returns the texture width.
    #[inline]
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Returns the texture height.
    #[inline]
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Returns the raw pixel data.
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    /// Returns mutable access to the pixel data.
    #[inline]
    pub fn data_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    /// Gets a pixel at the given coordinates.
    ///
    /// Returns (r, g, b, a) tuple.
    #[inline]
    pub fn get_pixel(&self, x: u32, y: u32) -> (u8, u8, u8, u8) {
        debug_assert!(x < self.width && y < self.height);
        let idx = ((y * self.width + x) * 4) as usize;
        (
            self.data[idx],
            self.data[idx + 1],
            self.data[idx + 2],
            self.data[idx + 3],
        )
    }

    /// Sets a pixel at the given coordinates.
    #[inline]
    pub fn set_pixel(&mut self, x: u32, y: u32, r: u8, g: u8, b: u8, a: u8) {
        debug_assert!(x < self.width && y < self.height);
        let idx = ((y * self.width + x) * 4) as usize;
        self.data[idx] = r;
        self.data[idx + 1] = g;
        self.data[idx + 2] = b;
        self.data[idx + 3] = a;
    }

    /// Samples the texture at normalized UV coordinates with bilinear filtering.
    ///
    /// UV coordinates are in the range [0, 1].
    pub fn sample(&self, u: f32, v: f32) -> (u8, u8, u8, u8) {
        let u = u.clamp(0.0, 1.0);
        let v = v.clamp(0.0, 1.0);

        let x = u * (self.width - 1) as f32;
        let y = v * (self.height - 1) as f32;

        let x0 = x.floor() as u32;
        let y0 = y.floor() as u32;
        let x1 = (x0 + 1).min(self.width - 1);
        let y1 = (y0 + 1).min(self.height - 1);

        let fx = x.fract();
        let fy = y.fract();

        let p00 = self.get_pixel(x0, y0);
        let p10 = self.get_pixel(x1, y0);
        let p01 = self.get_pixel(x0, y1);
        let p11 = self.get_pixel(x1, y1);

        let lerp = |a: u8, b: u8, t: f32| -> u8 {
            let a = f32::from(a);
            let b = f32::from(b);
            (a + (b - a) * t).round() as u8
        };

        let r0 = lerp(p00.0, p10.0, fx);
        let r1 = lerp(p01.0, p11.0, fx);
        let r = lerp(r0, r1, fy);

        let g0 = lerp(p00.1, p10.1, fx);
        let g1 = lerp(p01.1, p11.1, fx);
        let g = lerp(g0, g1, fy);

        let b0 = lerp(p00.2, p10.2, fx);
        let b1 = lerp(p01.2, p11.2, fx);
        let b = lerp(b0, b1, fy);

        let a0 = lerp(p00.3, p10.3, fx);
        let a1 = lerp(p01.3, p11.3, fx);
        let a = lerp(a0, a1, fy);

        (r, g, b, a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_texture_id() {
        let id = TextureId::new(42);
        assert_eq!(id.raw(), 42);
    }

    #[test]
    fn test_texture_new() {
        let data = vec![255u8; 4 * 4 * 4]; // 4x4 white texture
        let tex = Texture::new(4, 4, data);
        assert_eq!(tex.width(), 4);
        assert_eq!(tex.height(), 4);
    }

    #[test]
    #[should_panic(expected = "Texture data size mismatch")]
    fn test_texture_new_wrong_size() {
        let data = vec![255u8; 10]; // Wrong size
        let _ = Texture::new(4, 4, data);
    }

    #[test]
    fn test_texture_solid() {
        let tex = Texture::solid(2, 2, 255, 128, 64, 255);
        let pixel = tex.get_pixel(0, 0);
        assert_eq!(pixel, (255, 128, 64, 255));
        let pixel = tex.get_pixel(1, 1);
        assert_eq!(pixel, (255, 128, 64, 255));
    }

    #[test]
    fn test_texture_empty() {
        let tex = Texture::empty(2, 2);
        let pixel = tex.get_pixel(0, 0);
        assert_eq!(pixel, (0, 0, 0, 0));
    }

    #[test]
    fn test_texture_set_get_pixel() {
        let mut tex = Texture::empty(4, 4);
        tex.set_pixel(1, 2, 100, 150, 200, 255);
        let pixel = tex.get_pixel(1, 2);
        assert_eq!(pixel, (100, 150, 200, 255));
    }

    #[test]
    fn test_texture_sample_corners() {
        let mut tex = Texture::empty(2, 2);
        tex.set_pixel(0, 0, 255, 0, 0, 255); // Top-left: red
        tex.set_pixel(1, 0, 0, 255, 0, 255); // Top-right: green
        tex.set_pixel(0, 1, 0, 0, 255, 255); // Bottom-left: blue
        tex.set_pixel(1, 1, 255, 255, 0, 255); // Bottom-right: yellow

        // Sample corners
        assert_eq!(tex.sample(0.0, 0.0), (255, 0, 0, 255));
        assert_eq!(tex.sample(1.0, 0.0), (0, 255, 0, 255));
        assert_eq!(tex.sample(0.0, 1.0), (0, 0, 255, 255));
        assert_eq!(tex.sample(1.0, 1.0), (255, 255, 0, 255));
    }

    #[test]
    fn test_texture_sample_center() {
        // Create a 2x2 texture with different colors at each corner
        let mut tex = Texture::empty(2, 2);
        tex.set_pixel(0, 0, 255, 0, 0, 255); // Red
        tex.set_pixel(1, 0, 0, 255, 0, 255); // Green
        tex.set_pixel(0, 1, 0, 0, 255, 255); // Blue
        tex.set_pixel(1, 1, 255, 255, 0, 255); // Yellow

        // Sample center - should be a blend of all four colors
        let center = tex.sample(0.5, 0.5);
        // The exact values depend on bilinear interpolation
        assert!(center.0 > 0 && center.0 < 255);
        assert!(center.1 > 0 && center.1 < 255);
    }

    #[test]
    fn test_texture_sample_clamp() {
        let tex = Texture::solid(2, 2, 128, 128, 128, 255);

        // Out of bounds should clamp
        let sample = tex.sample(-1.0, -1.0);
        assert_eq!(sample, (128, 128, 128, 255));

        let sample = tex.sample(2.0, 2.0);
        assert_eq!(sample, (128, 128, 128, 255));
    }

    // =========================================================================
    // Edge case tests
    // =========================================================================

    #[test]
    fn test_texture_id_zero() {
        let id = TextureId::new(0);
        assert_eq!(id.raw(), 0);
    }

    #[test]
    fn test_texture_id_max() {
        let id = TextureId::new(u32::MAX);
        assert_eq!(id.raw(), u32::MAX);
    }

    #[test]
    fn test_texture_id_equality() {
        let id1 = TextureId::new(42);
        let id2 = TextureId::new(42);
        let id3 = TextureId::new(43);
        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_texture_id_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(TextureId::new(1));
        set.insert(TextureId::new(2));
        set.insert(TextureId::new(1)); // Duplicate

        assert_eq!(set.len(), 2);
        assert!(set.contains(&TextureId::new(1)));
        assert!(set.contains(&TextureId::new(2)));
        assert!(!set.contains(&TextureId::new(3)));
    }

    #[test]
    fn test_texture_id_clone_copy() {
        let id1 = TextureId::new(42);
        let id2 = id1; // Copy
        let id3 = id1; // Copy (TextureId implements Copy)
        assert_eq!(id1, id2);
        assert_eq!(id1, id3);
    }

    #[test]
    fn test_texture_1x1() {
        let tex = Texture::solid(1, 1, 255, 128, 64, 255);
        assert_eq!(tex.width(), 1);
        assert_eq!(tex.height(), 1);
        assert_eq!(tex.data().len(), 4);
        assert_eq!(tex.get_pixel(0, 0), (255, 128, 64, 255));
    }

    #[test]
    fn test_texture_1x1_sample() {
        let tex = Texture::solid(1, 1, 100, 150, 200, 250);

        // All sample positions should return the same pixel
        assert_eq!(tex.sample(0.0, 0.0), (100, 150, 200, 250));
        assert_eq!(tex.sample(0.5, 0.5), (100, 150, 200, 250));
        assert_eq!(tex.sample(1.0, 1.0), (100, 150, 200, 250));
    }

    #[test]
    fn test_texture_non_square() {
        // Non-square texture (3x5)
        let tex = Texture::solid(3, 5, 255, 0, 0, 255);
        assert_eq!(tex.width(), 3);
        assert_eq!(tex.height(), 5);
        assert_eq!(tex.data().len(), 3 * 5 * 4);

        // Access corners
        assert_eq!(tex.get_pixel(0, 0), (255, 0, 0, 255));
        assert_eq!(tex.get_pixel(2, 0), (255, 0, 0, 255));
        assert_eq!(tex.get_pixel(0, 4), (255, 0, 0, 255));
        assert_eq!(tex.get_pixel(2, 4), (255, 0, 0, 255));
    }

    #[test]
    fn test_texture_data_mut() {
        let mut tex = Texture::empty(2, 2);

        // Modify pixel data directly via data_mut
        let data = tex.data_mut();
        data[0] = 255; // R
        data[1] = 128; // G
        data[2] = 64; // B
        data[3] = 255; // A

        // Verify the pixel was modified
        assert_eq!(tex.get_pixel(0, 0), (255, 128, 64, 255));
    }

    #[test]
    fn test_texture_data_len() {
        let tex = Texture::solid(4, 3, 0, 0, 0, 0);
        assert_eq!(tex.data().len(), 4 * 3 * 4);
    }

    #[test]
    fn test_texture_clone() {
        let tex1 = Texture::solid(2, 2, 100, 150, 200, 255);
        let tex2 = tex1.clone();

        assert_eq!(tex1.width(), tex2.width());
        assert_eq!(tex1.height(), tex2.height());
        assert_eq!(tex1.data(), tex2.data());
        assert_eq!(tex1.get_pixel(0, 0), tex2.get_pixel(0, 0));
    }

    #[test]
    fn test_texture_sample_horizontal_gradient() {
        // Create a horizontal gradient (left=black, right=white)
        let mut tex = Texture::empty(2, 1);
        tex.set_pixel(0, 0, 0, 0, 0, 255); // Black
        tex.set_pixel(1, 0, 255, 255, 255, 255); // White

        // Sample at midpoint should be gray
        let mid = tex.sample(0.5, 0.0);
        assert!(
            mid.0 > 100 && mid.0 < 160,
            "Expected ~127-128, got {}",
            mid.0
        );
        assert_eq!(mid.3, 255); // Alpha unchanged
    }

    #[test]
    fn test_texture_sample_vertical_gradient() {
        // Create a vertical gradient (top=black, bottom=white)
        let mut tex = Texture::empty(1, 2);
        tex.set_pixel(0, 0, 0, 0, 0, 255); // Black
        tex.set_pixel(0, 1, 255, 255, 255, 255); // White

        // Sample at midpoint should be gray
        let mid = tex.sample(0.0, 0.5);
        assert!(
            mid.0 > 100 && mid.0 < 160,
            "Expected ~127-128, got {}",
            mid.0
        );
    }

    #[test]
    fn test_texture_set_pixel_all_corners() {
        let mut tex = Texture::empty(4, 4);

        // Set all four corners with different colors
        tex.set_pixel(0, 0, 255, 0, 0, 255); // Red
        tex.set_pixel(3, 0, 0, 255, 0, 255); // Green
        tex.set_pixel(0, 3, 0, 0, 255, 255); // Blue
        tex.set_pixel(3, 3, 255, 255, 0, 255); // Yellow

        assert_eq!(tex.get_pixel(0, 0), (255, 0, 0, 255));
        assert_eq!(tex.get_pixel(3, 0), (0, 255, 0, 255));
        assert_eq!(tex.get_pixel(0, 3), (0, 0, 255, 255));
        assert_eq!(tex.get_pixel(3, 3), (255, 255, 0, 255));

        // Middle should still be empty
        assert_eq!(tex.get_pixel(1, 1), (0, 0, 0, 0));
    }

    #[test]
    fn test_texture_sample_alpha_interpolation() {
        // Test that alpha is also interpolated
        let mut tex = Texture::empty(2, 2);
        tex.set_pixel(0, 0, 255, 255, 255, 0); // Transparent
        tex.set_pixel(1, 0, 255, 255, 255, 255); // Opaque
        tex.set_pixel(0, 1, 255, 255, 255, 0); // Transparent
        tex.set_pixel(1, 1, 255, 255, 255, 255); // Opaque

        // Sample at center should have ~128 alpha
        let center = tex.sample(0.5, 0.5);
        assert!(center.3 > 100 && center.3 < 160);
    }

    #[test]
    fn test_texture_wide() {
        // Very wide texture (100x1)
        let tex = Texture::solid(100, 1, 128, 128, 128, 255);
        assert_eq!(tex.width(), 100);
        assert_eq!(tex.height(), 1);
        assert_eq!(tex.get_pixel(99, 0), (128, 128, 128, 255));
    }

    #[test]
    fn test_texture_tall() {
        // Very tall texture (1x100)
        let tex = Texture::solid(1, 100, 128, 128, 128, 255);
        assert_eq!(tex.width(), 1);
        assert_eq!(tex.height(), 100);
        assert_eq!(tex.get_pixel(0, 99), (128, 128, 128, 255));
    }

    #[test]
    #[should_panic(expected = "Texture data size mismatch")]
    fn test_texture_new_too_much_data() {
        let data = vec![255u8; 100]; // Too much data for 4x4
        let _ = Texture::new(4, 4, data);
    }

    #[test]
    #[should_panic(expected = "Texture data size mismatch")]
    fn test_texture_new_too_little_data() {
        let data = vec![255u8; 10]; // Too little data for 4x4
        let _ = Texture::new(4, 4, data);
    }
}
