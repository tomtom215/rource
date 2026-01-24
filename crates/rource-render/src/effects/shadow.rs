// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

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
//!
//! # Performance Optimization
//!
//! This implementation uses pre-allocated buffers to eliminate per-frame allocations.
//! At 1920x1080 with default settings, this saves ~8.4 MB of allocations per frame:
//! - `silhouette_buffer`: 2.1 MB (alpha channel)
//! - `offset_buffer`: 2.1 MB (offset silhouette)
//! - `blur_temp`: 2.1 MB (blur intermediate)
//!
//! Buffers are automatically resized when dimensions change.

// Allow lossless casts written as `as` for brevity in numeric code
#![allow(clippy::cast_lossless)]

use rource_math::Color;

/// Configuration for the drop shadow effect.
///
/// Contains both effect parameters and pre-allocated buffers for zero-allocation
/// per-frame rendering. Use `apply()` which reuses internal buffers.
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

    // Pre-allocated buffers for zero-allocation rendering
    /// Buffer for silhouette extraction (alpha channel)
    silhouette_buffer: Vec<u8>,
    /// Buffer for offset silhouette
    offset_buffer: Vec<u8>,
    /// Temporary buffer for blur passes
    blur_temp: Vec<u8>,

    /// Cached dimensions to detect resize
    cached_width: usize,
    cached_height: usize,
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
    ///
    /// Buffers are allocated lazily on first `apply()` call.
    pub fn new() -> Self {
        Self {
            color: Color::new(0.0, 0.0, 0.0, 0.5),
            offset_x: 4,
            offset_y: 4,
            blur_radius: 3,
            blur_passes: 2,
            opacity: 0.5,
            // Buffers start empty, allocated on first apply()
            silhouette_buffer: Vec::new(),
            offset_buffer: Vec::new(),
            blur_temp: Vec::new(),
            cached_width: 0,
            cached_height: 0,
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
            silhouette_buffer: Vec::new(),
            offset_buffer: Vec::new(),
            blur_temp: Vec::new(),
            cached_width: 0,
            cached_height: 0,
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
            silhouette_buffer: Vec::new(),
            offset_buffer: Vec::new(),
            blur_temp: Vec::new(),
            cached_width: 0,
            cached_height: 0,
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
            silhouette_buffer: Vec::new(),
            offset_buffer: Vec::new(),
            blur_temp: Vec::new(),
            cached_width: 0,
            cached_height: 0,
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
    /// This method reuses internal buffers to avoid per-frame allocations.
    ///
    /// # Arguments
    /// * `pixels` - Mutable pixel buffer to apply the effect to
    /// * `width` - Buffer width in pixels
    /// * `height` - Buffer height in pixels
    pub fn apply(&mut self, pixels: &mut [u32], width: usize, height: usize) {
        if pixels.is_empty() || width == 0 || height == 0 {
            return;
        }

        // Ensure buffers are properly sized (only reallocates when dimensions change)
        self.ensure_buffers(width, height);

        // 1. Extract silhouette (alpha channel) into pre-allocated buffer
        self.extract_silhouette_into(pixels);

        // 2. Offset the silhouette into offset_buffer
        self.offset_silhouette_into(width, height);

        // 3. Blur the shadow (ping-pong between offset_buffer and blur_temp)
        for _ in 0..self.blur_passes {
            self.box_blur_in_place(width, height);
        }

        // 4. Colorize and blend underneath (reads from offset_buffer)
        self.blend_shadow_underneath(pixels);
    }

    /// Ensures all internal buffers are properly sized for the given dimensions.
    /// Only reallocates when dimensions change.
    fn ensure_buffers(&mut self, width: usize, height: usize) {
        let size = width * height;

        if self.cached_width != width || self.cached_height != height {
            self.cached_width = width;
            self.cached_height = height;

            // Resize all buffers
            self.silhouette_buffer.resize(size, 0);
            self.offset_buffer.resize(size, 0);
            self.blur_temp.resize(size, 0);
        }
    }

    /// Extracts the alpha channel as a silhouette into `silhouette_buffer`.
    fn extract_silhouette_into(&mut self, pixels: &[u32]) {
        for (dst, &p) in self.silhouette_buffer.iter_mut().zip(pixels.iter()) {
            // Extract alpha from ARGB format
            *dst = ((p >> 24) & 0xFF) as u8;
        }
    }

    /// Offsets the silhouette from `silhouette_buffer` into `offset_buffer`.
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
    fn offset_silhouette_into(&mut self, width: usize, height: usize) {
        // Clear offset buffer (regions outside source are 0)
        self.offset_buffer.fill(0);

        for y in 0..height {
            for x in 0..width {
                // Calculate source position (where to sample from)
                let src_x = x as i32 - self.offset_x;
                let src_y = y as i32 - self.offset_y;

                if src_x >= 0 && src_x < width as i32 && src_y >= 0 && src_y < height as i32 {
                    let src_idx = src_y as usize * width + src_x as usize;
                    let dst_idx = y * width + x;
                    self.offset_buffer[dst_idx] = self.silhouette_buffer[src_idx];
                }
            }
        }
    }

    /// Applies a separable box blur in-place using `offset_buffer` and `blur_temp`.
    /// After this call, result is in `offset_buffer`.
    ///
    /// Uses O(n) sliding window algorithm instead of O(n × radius) naive approach.
    #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
    fn box_blur_in_place(&mut self, width: usize, height: usize) {
        if width == 0 || height == 0 || self.blur_radius == 0 {
            return;
        }

        let r = self.blur_radius as usize;
        let diameter = 2 * r + 1;
        // Pre-compute reciprocal for faster division
        let inv_diameter = 1.0 / diameter as f32;

        // Horizontal pass: offset_buffer -> blur_temp (O(n) sliding window)
        for y in 0..height {
            let row = y * width;

            // Initialize window sum for x=0
            let mut sum = 0u32;

            // Add pixels in range [0, r] (or width-1 if smaller)
            for i in 0..=r.min(width - 1) {
                sum += self.offset_buffer[row + i] as u32;
            }
            // Add repeated edge pixel for clamped left positions [-r, -1]
            sum += self.offset_buffer[row] as u32 * r as u32;
            // Handle right edge clamping if width <= r
            if width <= r {
                let extra = r - width + 1;
                sum += self.offset_buffer[row + width - 1] as u32 * extra as u32;
            }

            for x in 0..width {
                // Store result using reciprocal multiplication
                self.blur_temp[row + x] = (sum as f32 * inv_diameter).min(255.0) as u8;

                // Slide window
                let leave_idx = x.saturating_sub(r);
                sum -= self.offset_buffer[row + leave_idx] as u32;

                let enter_idx = (x + r + 1).min(width - 1);
                sum += self.offset_buffer[row + enter_idx] as u32;
            }
        }

        // Vertical pass: blur_temp -> offset_buffer (O(n) sliding window)
        for x in 0..width {
            // Initialize window sum for y=0
            let mut sum = 0u32;

            // Add pixels in range [0, r] (or height-1 if smaller)
            for i in 0..=r.min(height - 1) {
                sum += self.blur_temp[i * width + x] as u32;
            }
            // Add repeated edge pixel for clamped top positions
            sum += self.blur_temp[x] as u32 * r as u32;
            // Handle bottom edge clamping if height <= r
            if height <= r {
                let extra = r - height + 1;
                sum += self.blur_temp[(height - 1) * width + x] as u32 * extra as u32;
            }

            for y in 0..height {
                // Store result
                self.offset_buffer[y * width + x] = (sum as f32 * inv_diameter).min(255.0) as u8;

                // Slide window
                let leave_idx = y.saturating_sub(r);
                sum -= self.blur_temp[leave_idx * width + x] as u32;

                let enter_idx = (y + r + 1).min(height - 1);
                sum += self.blur_temp[enter_idx * width + x] as u32;
            }
        }
    }

    /// Blends the shadow underneath the original image.
    /// Reads from `offset_buffer` (which contains the blurred shadow).
    ///
    /// This uses standard alpha compositing with "shadow under" semantics.
    #[allow(clippy::cast_possible_truncation)]
    fn blend_shadow_underneath(&self, pixels: &mut [u32]) {
        let shadow_r = (self.color.r * 255.0) as u32;
        let shadow_g = (self.color.g * 255.0) as u32;
        let shadow_b = (self.color.b * 255.0) as u32;

        for (pixel, &shadow_alpha) in pixels.iter_mut().zip(self.offset_buffer.iter()) {
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
        let mut shadow = ShadowEffect::new();
        let mut pixels: Vec<u32> = vec![];
        shadow.apply(&mut pixels, 0, 0);
        assert!(pixels.is_empty());
    }

    #[test]
    fn test_shadow_apply_all_transparent() {
        let mut shadow = ShadowEffect::new();
        let mut pixels = vec![0x0000_0000_u32; 16 * 16]; // All transparent
        let original = pixels.clone();
        shadow.apply(&mut pixels, 16, 16);

        // Transparent pixels should stay transparent
        assert_eq!(pixels, original);
    }

    #[test]
    fn test_shadow_apply_opaque_pixels() {
        let mut shadow = ShadowEffect::new().with_offset(2, 2);
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
    fn test_shadow_buffer_reuse() {
        // Test that buffers are reused across multiple apply() calls
        let mut shadow = ShadowEffect::new();
        let mut pixels = vec![0xFF00_0000_u32; 16 * 16]; // Opaque black

        // First apply - allocates buffers
        shadow.apply(&mut pixels, 16, 16);
        assert_eq!(shadow.cached_width, 16);
        assert_eq!(shadow.cached_height, 16);
        assert!(!shadow.silhouette_buffer.is_empty());

        // Second apply - reuses buffers (same dimensions)
        let mut pixels2 = vec![0xFF00_0000_u32; 16 * 16];
        shadow.apply(&mut pixels2, 16, 16);
        // Dimensions unchanged means buffers were reused
        assert_eq!(shadow.cached_width, 16);
        assert_eq!(shadow.cached_height, 16);
    }

    #[test]
    fn test_shadow_buffer_resize() {
        // Test that buffers resize when dimensions change
        let mut shadow = ShadowEffect::new();

        // First apply at 16x16
        let mut pixels1 = vec![0xFF00_0000_u32; 16 * 16];
        shadow.apply(&mut pixels1, 16, 16);
        assert_eq!(shadow.cached_width, 16);
        assert_eq!(shadow.cached_height, 16);

        // Second apply at 32x32 - buffers should resize
        let mut pixels2 = vec![0xFF00_0000_u32; 32 * 32];
        shadow.apply(&mut pixels2, 32, 32);
        assert_eq!(shadow.cached_width, 32);
        assert_eq!(shadow.cached_height, 32);
        assert_eq!(shadow.silhouette_buffer.len(), 32 * 32);
        assert_eq!(shadow.offset_buffer.len(), 32 * 32);
        assert_eq!(shadow.blur_temp.len(), 32 * 32);
    }

    #[test]
    fn test_shadow_with_color() {
        let shadow = ShadowEffect::new().with_color(Color::new(1.0, 0.0, 0.0, 0.5));

        assert!((shadow.color.r - 1.0).abs() < 0.01);
        assert!((shadow.color.g - 0.0).abs() < 0.01);
        assert!((shadow.color.b - 0.0).abs() < 0.01);
    }

    #[test]
    fn test_shadow_creates_visible_shadow() {
        // Test that the shadow effect creates visible shadow behind opaque objects
        let mut shadow = ShadowEffect::new()
            .with_offset(2, 2)
            .with_blur_radius(1)
            .with_blur_passes(1)
            .with_opacity(1.0);
        let mut pixels = vec![0x0000_0000_u32; 16 * 16]; // All transparent

        // Add a 4x4 opaque region in the center
        for dy in 0..4 {
            for dx in 0..4 {
                pixels[(6 + dy) * 16 + (6 + dx)] = 0xFFFF_FFFF;
            }
        }

        shadow.apply(&mut pixels, 16, 16);

        // Check for shadow in the offset region (below and to the right)
        // The shadow should appear at offset (8+2, 6+2) = (10, 8) to (13, 11)
        let mut has_shadow = false;
        for y in 8..14 {
            for x in 8..14 {
                // Skip the original opaque region
                if (6..10).contains(&x) && (6..10).contains(&y) {
                    continue;
                }
                let pixel = pixels[y * 16 + x];
                let alpha = (pixel >> 24) & 0xFF;
                if alpha > 0 {
                    has_shadow = true;
                    break;
                }
            }
            if has_shadow {
                break;
            }
        }
        assert!(has_shadow, "Shadow should be visible in offset region");
    }
}
