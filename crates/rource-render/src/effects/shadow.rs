//! Drop shadow effect implementation.
//!
//! This module provides a CPU-efficient drop shadow effect that creates
//! depth by rendering a blurred, offset copy of visible elements behind them.
//!
//! The effect works by:
//!
//! 1. Extracting silhouettes (non-transparent pixels)
//! 2. Offsetting in the shadow direction
//! 3. Applying box blur for softness
//! 4. Blending underneath the original image

// Allow lossless casts written as `as` for brevity in numeric code
#![allow(clippy::cast_lossless)]

use rource_math::Color;

/// Configuration for the drop shadow effect.
#[derive(Debug, Clone)]
pub struct ShadowEffect {
    /// Shadow color (default: semi-transparent black).
    pub color: Color,

    /// Horizontal offset in pixels (positive = right).
    pub offset_x: i32,

    /// Vertical offset in pixels (positive = down).
    pub offset_y: i32,

    /// Blur radius in pixels.
    pub blur_radius: i32,

    /// Number of blur passes for softer shadows.
    pub blur_passes: usize,

    /// Shadow opacity multiplier (0.0 - 1.0).
    pub opacity: f32,
}

impl ShadowEffect {
    /// Creates a new shadow effect with default settings.
    ///
    /// Default settings:
    /// - color: black with 50% opacity
    /// - offset: (4, 4) pixels down-right
    /// - `blur_radius`: 3 pixels
    /// - `blur_passes`: 2
    /// - opacity: 0.5
    pub fn new() -> Self {
        Self {
            color: Color::new(0.0, 0.0, 0.0, 0.5),
            offset_x: 4,
            offset_y: 4,
            blur_radius: 3,
            blur_passes: 2,
            opacity: 0.5,
        }
    }

    /// Creates a subtle shadow (smaller offset, lighter).
    pub fn subtle() -> Self {
        Self {
            color: Color::new(0.0, 0.0, 0.0, 0.3),
            offset_x: 2,
            offset_y: 2,
            blur_radius: 2,
            blur_passes: 1,
            opacity: 0.3,
        }
    }

    /// Creates a heavy shadow (larger offset, darker).
    pub fn heavy() -> Self {
        Self {
            color: Color::new(0.0, 0.0, 0.0, 0.7),
            offset_x: 6,
            offset_y: 6,
            blur_radius: 5,
            blur_passes: 3,
            opacity: 0.7,
        }
    }

    /// Creates a soft ambient shadow (no offset, just blur).
    pub fn ambient() -> Self {
        Self {
            color: Color::new(0.0, 0.0, 0.0, 0.4),
            offset_x: 0,
            offset_y: 0,
            blur_radius: 4,
            blur_passes: 2,
            opacity: 0.4,
        }
    }

    /// Sets the shadow color.
    #[inline]
    #[must_use]
    pub fn with_color(mut self, color: Color) -> Self {
        self.color = color;
        self
    }

    /// Sets the shadow offset.
    #[inline]
    #[must_use]
    pub fn with_offset(mut self, x: i32, y: i32) -> Self {
        self.offset_x = x;
        self.offset_y = y;
        self
    }

    /// Sets the blur radius.
    #[inline]
    #[must_use]
    pub fn with_blur_radius(mut self, radius: i32) -> Self {
        self.blur_radius = radius.max(0);
        self
    }

    /// Sets the number of blur passes.
    #[inline]
    #[must_use]
    pub fn with_blur_passes(mut self, passes: usize) -> Self {
        self.blur_passes = passes.max(1);
        self
    }

    /// Sets the shadow opacity.
    #[inline]
    #[must_use]
    pub fn with_opacity(mut self, opacity: f32) -> Self {
        self.opacity = opacity.clamp(0.0, 1.0);
        self
    }

    /// Applies the shadow effect to a pixel buffer.
    ///
    /// The pixel buffer should be in ARGB8 format (0xAARRGGBB).
    /// The shadow is composited underneath the existing content.
    ///
    /// # Arguments
    /// * `pixels` - Mutable pixel buffer to apply the effect to
    /// * `width` - Buffer width in pixels
    /// * `height` - Buffer height in pixels
    pub fn apply(&self, pixels: &mut [u32], width: usize, height: usize) {
        if pixels.is_empty() || width == 0 || height == 0 {
            return;
        }

        // 1. Extract silhouette (alpha channel)
        let silhouette = self.extract_silhouette(pixels, width, height);

        // 2. Offset the silhouette
        let offset = self.offset_silhouette(&silhouette, width, height);

        // 3. Blur the shadow
        let mut shadow = offset;
        for _ in 0..self.blur_passes {
            shadow = self.box_blur(&shadow, width, height);
        }

        // 4. Colorize and blend underneath
        self.blend_shadow_underneath(pixels, &shadow, width, height);
    }

    /// Extracts the alpha channel as a silhouette.
    ///
    /// Returns a buffer where each pixel is the alpha value (0-255).
    #[allow(clippy::unused_self)]
    fn extract_silhouette(&self, pixels: &[u32], _width: usize, _height: usize) -> Vec<u8> {
        pixels
            .iter()
            .map(|&p| {
                // Extract alpha from ARGB format
                ((p >> 24) & 0xFF) as u8
            })
            .collect()
    }

    /// Offsets the silhouette by the shadow offset.
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
    fn offset_silhouette(&self, silhouette: &[u8], width: usize, height: usize) -> Vec<u8> {
        let mut result = vec![0u8; silhouette.len()];

        for y in 0..height {
            for x in 0..width {
                // Calculate source position (where to sample from)
                let src_x = x as i32 - self.offset_x;
                let src_y = y as i32 - self.offset_y;

                if src_x >= 0 && src_x < width as i32 && src_y >= 0 && src_y < height as i32 {
                    let src_idx = src_y as usize * width + src_x as usize;
                    let dst_idx = y * width + x;
                    result[dst_idx] = silhouette[src_idx];
                }
            }
        }

        result
    }

    /// Applies a separable box blur to the alpha buffer.
    #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
    fn box_blur(&self, src: &[u8], width: usize, height: usize) -> Vec<u8> {
        if src.is_empty() || width == 0 || height == 0 || self.blur_radius == 0 {
            return src.to_vec();
        }

        let radius = self.blur_radius;

        // Horizontal pass
        let mut temp = vec![0u8; src.len()];
        for y in 0..height {
            for x in 0..width {
                let mut sum = 0u32;
                let mut count = 0u32;

                for dx in -radius..=radius {
                    let nx = (x as i32 + dx).clamp(0, width as i32 - 1) as usize;
                    sum += src[y * width + nx] as u32;
                    count += 1;
                }

                temp[y * width + x] = (sum / count) as u8;
            }
        }

        // Vertical pass
        let mut result = vec![0u8; src.len()];
        for y in 0..height {
            for x in 0..width {
                let mut sum = 0u32;
                let mut count = 0u32;

                for dy in -radius..=radius {
                    let ny = (y as i32 + dy).clamp(0, height as i32 - 1) as usize;
                    sum += temp[ny * width + x] as u32;
                    count += 1;
                }

                result[y * width + x] = (sum / count) as u8;
            }
        }

        result
    }

    /// Blends the shadow underneath the original image.
    ///
    /// This uses standard alpha compositing with "shadow under" semantics.
    #[allow(clippy::cast_possible_truncation)]
    fn blend_shadow_underneath(
        &self,
        pixels: &mut [u32],
        shadow: &[u8],
        _width: usize,
        _height: usize,
    ) {
        let shadow_r = (self.color.r * 255.0) as u32;
        let shadow_g = (self.color.g * 255.0) as u32;
        let shadow_b = (self.color.b * 255.0) as u32;

        for (pixel, &shadow_alpha) in pixels.iter_mut().zip(shadow.iter()) {
            let orig_a = (*pixel >> 24) & 0xFF;
            let orig_r = (*pixel >> 16) & 0xFF;
            let orig_g = (*pixel >> 8) & 0xFF;
            let orig_b = *pixel & 0xFF;

            // Calculate effective shadow alpha
            let eff_shadow_a = (shadow_alpha as f32 * self.opacity) as u32;

            // Calculate how much shadow shows through (where original is transparent)
            let inverse_orig_a = 255 - orig_a;
            let visible_shadow_a = (eff_shadow_a * inverse_orig_a) / 255;

            if visible_shadow_a > 0 {
                // Blend shadow color with original
                let final_a = orig_a + visible_shadow_a;

                // Blend RGB components
                let final_r = (orig_r * orig_a + shadow_r * visible_shadow_a) / final_a.max(1);
                let final_g = (orig_g * orig_a + shadow_g * visible_shadow_a) / final_a.max(1);
                let final_b = (orig_b * orig_a + shadow_b * visible_shadow_a) / final_a.max(1);

                *pixel = (final_a.min(255) << 24)
                    | (final_r.min(255) << 16)
                    | (final_g.min(255) << 8)
                    | final_b.min(255);
            }
        }
    }
}

impl Default for ShadowEffect {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shadow_effect_new() {
        let shadow = ShadowEffect::new();
        assert_eq!(shadow.offset_x, 4);
        assert_eq!(shadow.offset_y, 4);
        assert_eq!(shadow.blur_radius, 3);
        assert_eq!(shadow.blur_passes, 2);
        assert!((shadow.opacity - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_shadow_effect_default() {
        let shadow = ShadowEffect::default();
        assert_eq!(shadow.offset_x, 4);
    }

    #[test]
    fn test_shadow_effect_presets() {
        let subtle = ShadowEffect::subtle();
        assert_eq!(subtle.offset_x, 2);
        assert_eq!(subtle.blur_radius, 2);
        assert!((subtle.opacity - 0.3).abs() < 0.01);

        let heavy = ShadowEffect::heavy();
        assert_eq!(heavy.offset_x, 6);
        assert_eq!(heavy.blur_radius, 5);
        assert!((heavy.opacity - 0.7).abs() < 0.01);

        let ambient = ShadowEffect::ambient();
        assert_eq!(ambient.offset_x, 0);
        assert_eq!(ambient.offset_y, 0);
    }

    #[test]
    fn test_shadow_effect_builders() {
        let shadow = ShadowEffect::new()
            .with_offset(8, 10)
            .with_blur_radius(5)
            .with_blur_passes(3)
            .with_opacity(0.8);

        assert_eq!(shadow.offset_x, 8);
        assert_eq!(shadow.offset_y, 10);
        assert_eq!(shadow.blur_radius, 5);
        assert_eq!(shadow.blur_passes, 3);
        assert!((shadow.opacity - 0.8).abs() < 0.01);
    }

    #[test]
    fn test_shadow_effect_opacity_clamp() {
        let shadow = ShadowEffect::new().with_opacity(1.5);
        assert!((shadow.opacity - 1.0).abs() < 0.01);

        let shadow = ShadowEffect::new().with_opacity(-0.5);
        assert!((shadow.opacity - 0.0).abs() < 0.01);
    }

    #[test]
    fn test_shadow_apply_empty() {
        let shadow = ShadowEffect::new();
        let mut pixels: Vec<u32> = vec![];
        shadow.apply(&mut pixels, 0, 0);
        assert!(pixels.is_empty());
    }

    #[test]
    fn test_shadow_apply_all_transparent() {
        let shadow = ShadowEffect::new();
        let mut pixels = vec![0x0000_0000_u32; 16 * 16]; // All transparent
        let original = pixels.clone();
        shadow.apply(&mut pixels, 16, 16);

        // Transparent pixels should stay transparent
        assert_eq!(pixels, original);
    }

    #[test]
    fn test_shadow_apply_opaque_pixels() {
        let shadow = ShadowEffect::new().with_offset(2, 2);
        let mut pixels = vec![0x0000_0000_u32; 8 * 8];

        // Add a single opaque white pixel at (2, 2)
        pixels[2 * 8 + 2] = 0xFFFF_FFFF;

        shadow.apply(&mut pixels, 8, 8);

        // The shadow should appear at (4, 4) offset by (2, 2)
        // Since the shadow is blurred, we check a region
        let shadow_pixel = pixels[4 * 8 + 4];
        let shadow_a = (shadow_pixel >> 24) & 0xFF;

        // There should be some shadow alpha at the offset position
        // (it might not be very strong due to blur spread)
        // Just check that *something* changed in the shadow region
        let has_shadow = (3..6).any(|y| {
            (3..6).any(|x| {
                let p = pixels[y * 8 + x];
                (p >> 24) & 0xFF > 0
            })
        });
        assert!(has_shadow || shadow_a > 0, "Shadow should appear at offset");
    }

    #[test]
    fn test_extract_silhouette() {
        let shadow = ShadowEffect::new();

        // Create pixels with varying alpha
        let pixels = vec![
            0xFF00_0000_u32, // Full alpha (opaque black)
            0x8000_0000_u32, // Half alpha
            0x00FF_FFFF_u32, // Zero alpha (transparent white)
        ];

        let silhouette = shadow.extract_silhouette(&pixels, 3, 1);

        assert_eq!(silhouette[0], 0xFF);
        assert_eq!(silhouette[1], 0x80);
        assert_eq!(silhouette[2], 0x00);
    }

    #[test]
    fn test_offset_silhouette() {
        let shadow = ShadowEffect::new().with_offset(1, 1);

        // Create a 4x4 silhouette with one opaque pixel at (0, 0)
        let mut silhouette = vec![0u8; 16];
        silhouette[0] = 255;

        let offset = shadow.offset_silhouette(&silhouette, 4, 4);

        // The opaque pixel should now be at (1, 1)
        assert_eq!(offset[0], 0, "Original position should be empty");
        assert_eq!(offset[5], 255, "Offset position (1,1) should have value");
    }

    #[test]
    fn test_box_blur() {
        let shadow = ShadowEffect::new().with_blur_radius(1);

        // Create a 5x5 buffer with center pixel bright
        let mut src = vec![0u8; 25];
        src[12] = 255; // Center pixel

        let blurred = shadow.box_blur(&src, 5, 5);

        // After blur, the center should still be brightest
        assert!(blurred[12] > 0, "Center should have some brightness");

        // But neighbors should also have brightness now
        assert!(blurred[11] > 0 || blurred[13] > 0, "Blur should spread");

        // Corners should have less brightness
        assert!(
            blurred[0] < blurred[12],
            "Corners should be dimmer than center"
        );
    }

    #[test]
    fn test_box_blur_zero_radius() {
        let shadow = ShadowEffect::new().with_blur_radius(0);

        let src = vec![128u8; 16];
        let blurred = shadow.box_blur(&src, 4, 4);

        // With zero radius, output should equal input
        assert_eq!(src, blurred);
    }

    #[test]
    fn test_shadow_with_color() {
        let shadow = ShadowEffect::new().with_color(Color::new(1.0, 0.0, 0.0, 0.5));

        assert!((shadow.color.r - 1.0).abs() < 0.01);
        assert!((shadow.color.g - 0.0).abs() < 0.01);
        assert!((shadow.color.b - 0.0).abs() < 0.01);
    }
}
