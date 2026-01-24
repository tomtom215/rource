// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Bloom (glow) effect implementation.
//!
//! This module provides a CPU-efficient bloom effect that creates a glow
//! around bright areas of the image. The effect works by:
//!
//! 1. Extracting bright pixels above a threshold
//! 2. Downscaling for faster blur
//! 3. Applying box blur (faster than Gaussian)
//! 4. Upscaling and additively blending back
//!
//! # Performance Optimization
//!
//! This implementation uses pre-allocated buffers to eliminate per-frame allocations.
//! At 1920x1080 with default settings, this saves ~19.2 MB of allocations per frame:
//! - `bright_buffer`: 8.3 MB (full resolution)
//! - `small_buffer`: 518 KB (downscaled)
//! - `blur_temp`: 518 KB (downscaled)
//! - `bloom_buffer`: 8.3 MB (full resolution)
//!
//! Buffers are automatically resized when dimensions change.

// Allow lossless casts written as `as` for brevity in numeric code
#![allow(clippy::cast_lossless)]

/// Configuration for the bloom effect.
///
/// Contains both effect parameters and pre-allocated buffers for zero-allocation
/// per-frame rendering. Use `apply()` which reuses internal buffers.
#[derive(Debug, Clone)]
pub struct BloomEffect {
    /// Brightness threshold (0.0-1.0). Pixels brighter than this will bloom.
    pub threshold: f32,

    /// Bloom intensity multiplier.
    pub intensity: f32,

    /// Number of blur passes. More passes = softer bloom.
    pub passes: usize,

    /// Downscale factor for blur buffer. Higher = faster but blockier.
    pub downscale: usize,

    /// Blur radius in pixels.
    pub radius: i32,

    // Pre-allocated buffers for zero-allocation rendering
    /// Buffer for bright pixel extraction (full resolution)
    bright_buffer: Vec<u32>,
    /// Buffer for downscaled/blurred data
    small_buffer: Vec<u32>,
    /// Temporary buffer for blur passes
    blur_temp: Vec<u32>,
    /// Buffer for upscaled bloom result
    bloom_buffer: Vec<u32>,

    /// Cached dimensions to detect resize
    cached_width: usize,
    cached_height: usize,
}

impl BloomEffect {
    /// Creates a new bloom effect with default settings.
    ///
    /// Default settings are balanced for quality and performance:
    /// - threshold: 0.7
    /// - intensity: 1.0
    /// - passes: 2
    /// - downscale: 4
    /// - radius: 2
    ///
    /// Buffers are allocated lazily on first `apply()` call.
    pub fn new() -> Self {
        Self {
            threshold: 0.7,
            intensity: 1.0,
            passes: 2,
            downscale: 4,
            radius: 2,
            // Buffers start empty, allocated on first apply()
            bright_buffer: Vec::new(),
            small_buffer: Vec::new(),
            blur_temp: Vec::new(),
            bloom_buffer: Vec::new(),
            cached_width: 0,
            cached_height: 0,
        }
    }

    /// Creates a subtle bloom effect.
    pub fn subtle() -> Self {
        Self {
            threshold: 0.8,
            intensity: 0.5,
            passes: 1,
            downscale: 4,
            radius: 2,
            bright_buffer: Vec::new(),
            small_buffer: Vec::new(),
            blur_temp: Vec::new(),
            bloom_buffer: Vec::new(),
            cached_width: 0,
            cached_height: 0,
        }
    }

    /// Creates an intense bloom effect.
    pub fn intense() -> Self {
        Self {
            threshold: 0.5,
            intensity: 2.0,
            passes: 3,
            downscale: 2,
            radius: 3,
            bright_buffer: Vec::new(),
            small_buffer: Vec::new(),
            blur_temp: Vec::new(),
            bloom_buffer: Vec::new(),
            cached_width: 0,
            cached_height: 0,
        }
    }

    /// Sets the brightness threshold.
    #[inline]
    #[must_use]
    pub fn with_threshold(mut self, threshold: f32) -> Self {
        self.threshold = threshold.clamp(0.0, 1.0);
        self
    }

    /// Sets the intensity multiplier.
    #[inline]
    #[must_use]
    pub fn with_intensity(mut self, intensity: f32) -> Self {
        self.intensity = intensity.max(0.0);
        self
    }

    /// Sets the number of blur passes.
    #[inline]
    #[must_use]
    pub fn with_passes(mut self, passes: usize) -> Self {
        self.passes = passes.max(1);
        self
    }

    /// Sets the downscale factor.
    #[inline]
    #[must_use]
    pub fn with_downscale(mut self, downscale: usize) -> Self {
        self.downscale = downscale.max(1);
        self
    }

    /// Applies the bloom effect to a pixel buffer.
    ///
    /// The pixel buffer should be in ARGB8 format (0xAARRGGBB).
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

        // Calculate dimensions
        let small_w = (width / self.downscale).max(1);
        let small_h = (height / self.downscale).max(1);

        // Ensure buffers are properly sized (only reallocates when dimensions change)
        self.ensure_buffers(width, height, small_w, small_h);

        // 1. Extract bright pixels into pre-allocated buffer
        self.extract_bright_into(pixels);

        // 2. Downscale for faster blur
        self.downscale_into(width, height, small_w, small_h);

        // 3. Apply box blur multiple times (ping-pong between small_buffer and blur_temp)
        for _ in 0..self.passes {
            self.box_blur_in_place(small_w, small_h);
        }

        // 4. Upscale into bloom_buffer
        self.upscale_into(small_w, small_h, width, height);

        // 5. Additive blend
        for (pixel, bloom_pixel) in pixels.iter_mut().zip(self.bloom_buffer.iter()) {
            *pixel = Self::additive_blend(*pixel, *bloom_pixel);
        }
    }

    /// Ensures all internal buffers are properly sized for the given dimensions.
    /// Only reallocates when dimensions change.
    fn ensure_buffers(&mut self, width: usize, height: usize, small_w: usize, small_h: usize) {
        let full_size = width * height;
        let small_size = small_w * small_h;

        // Check if dimensions changed
        if self.cached_width != width || self.cached_height != height {
            self.cached_width = width;
            self.cached_height = height;

            // Resize full-resolution buffers
            self.bright_buffer.resize(full_size, 0xFF00_0000);
            self.bloom_buffer.resize(full_size, 0xFF00_0000);

            // Resize downscaled buffers
            self.small_buffer.resize(small_size, 0xFF00_0000);
            self.blur_temp.resize(small_size, 0xFF00_0000);
        }
    }

    /// Extracts bright pixels above the threshold into `bright_buffer`.
    ///
    /// Uses integer math for brightness calculation (ITU-R BT.601 coefficients).
    /// Fixed-point: brightness = (77*R + 150*G + 29*B) / 256
    fn extract_bright_into(&mut self, pixels: &[u32]) {
        // Pre-compute threshold in 0-255 range for integer comparison
        let threshold_u8 = (self.threshold * 255.0) as u32;
        // Pre-compute intensity factor (1/255 built in for output scaling)
        let intensity_scale = self.intensity / 255.0;

        for (dst, &p) in self.bright_buffer.iter_mut().zip(pixels.iter()) {
            let r = (p >> 16) & 0xFF;
            let g = (p >> 8) & 0xFF;
            let b = p & 0xFF;

            // Calculate perceived brightness using fixed-point integer math
            // ITU-R BT.601: 0.299*R + 0.587*G + 0.114*B
            // Scaled: (77*R + 150*G + 29*B) / 256 (coefficients sum to 256)
            let brightness = (77 * r + 150 * g + 29 * b) >> 8;

            *dst = if brightness > threshold_u8 {
                // Factor scaled by intensity for output color
                let factor = (brightness - threshold_u8) as f32 * intensity_scale;
                let nr = ((r as f32 * factor) as u32).min(255);
                let ng = ((g as f32 * factor) as u32).min(255);
                let nb = ((b as f32 * factor) as u32).min(255);
                0xFF00_0000 | (nr << 16) | (ng << 8) | nb
            } else {
                0xFF00_0000 // Black with full alpha
            };
        }
    }

    /// Downscales `bright_buffer` into `small_buffer` using box filtering.
    ///
    /// Optimized with precomputed coordinate ranges for each destination pixel.
    fn downscale_into(&mut self, src_w: usize, src_h: usize, dst_w: usize, dst_h: usize) {
        if dst_w == 0 || dst_h == 0 {
            return;
        }

        // Precompute X ranges for each destination column
        // For dst pixel dx, compute (sx_start, sx_end) in source
        let x_ranges: Vec<(usize, usize)> = (0..dst_w)
            .map(|dx| {
                let sx_start = dx * src_w / dst_w;
                let sx_end = ((dx + 1) * src_w / dst_w).min(src_w);
                (sx_start, sx_end)
            })
            .collect();

        // Precompute Y ranges for each destination row
        let y_ranges: Vec<(usize, usize)> = (0..dst_h)
            .map(|dy| {
                let sy_start = dy * src_h / dst_h;
                let sy_end = ((dy + 1) * src_h / dst_h).min(src_h);
                (sy_start, sy_end)
            })
            .collect();

        // Precompute inverse count for each block size (for reciprocal multiplication)
        // The block size is typically downscale × downscale = 16 for downscale=4
        let downscale = self.downscale;
        let typical_count = (downscale * downscale) as f32;
        let inv_count = 1.0 / typical_count;

        for (dy, &(sy_start, sy_end)) in y_ranges.iter().enumerate() {
            let dst_row = dy * dst_w;

            for (dx, &(sx_start, sx_end)) in x_ranges.iter().enumerate() {
                let mut r_sum = 0u32;
                let mut g_sum = 0u32;
                let mut b_sum = 0u32;

                // Sum all pixels in the source block
                for sy in sy_start..sy_end {
                    let src_row = sy * src_w;
                    for sx in sx_start..sx_end {
                        let pixel = self.bright_buffer[src_row + sx];
                        r_sum += (pixel >> 16) & 0xFF;
                        g_sum += (pixel >> 8) & 0xFF;
                        b_sum += pixel & 0xFF;
                    }
                }

                // Compute average using reciprocal multiplication for typical case
                let count = (sy_end - sy_start) * (sx_end - sx_start);
                let (r, g, b) = if count == downscale * downscale {
                    // Common case: use precomputed reciprocal
                    let r = (r_sum as f32 * inv_count) as u32;
                    let g = (g_sum as f32 * inv_count) as u32;
                    let b = (b_sum as f32 * inv_count) as u32;
                    (r.min(255), g.min(255), b.min(255))
                } else if count > 0 {
                    // Edge case: compute reciprocal
                    let inv = 1.0 / count as f32;
                    let r = (r_sum as f32 * inv) as u32;
                    let g = (g_sum as f32 * inv) as u32;
                    let b = (b_sum as f32 * inv) as u32;
                    (r.min(255), g.min(255), b.min(255))
                } else {
                    (0, 0, 0)
                };

                self.small_buffer[dst_row + dx] = 0xFF00_0000 | (r << 16) | (g << 8) | b;
            }
        }
    }

    /// Integer lerp for bilinear interpolation: lerp(a, b, t) where t is in [0, 256].
    /// Returns (a * (256 - t) + b * t) >> 8
    #[inline]
    fn ilerp(a: u32, b: u32, t: u32) -> u32 {
        ((a * (256 - t) + b * t) >> 8).min(255)
    }

    /// Upscales `small_buffer` into `bloom_buffer` using bilinear interpolation.
    ///
    /// Optimized with precomputed coordinate tables to avoid per-pixel float math.
    /// Uses 8-bit fixed-point for interpolation weights (256 = 1.0).
    fn upscale_into(&mut self, src_w: usize, src_h: usize, dst_w: usize, dst_h: usize) {
        if dst_w <= 1 || dst_h <= 1 || src_w <= 1 || src_h <= 1 {
            // Degenerate case: just copy or fill
            for pixel in self.bloom_buffer.iter_mut().take(dst_w * dst_h) {
                *pixel = self.small_buffer.first().copied().unwrap_or(0xFF00_0000);
            }
            return;
        }

        // Precompute X coordinate table: for each dst x, store (x0, x1, fx_fixed)
        // fx_fixed is in [0, 256] where 256 = 1.0
        let scale_x = ((src_w - 1) << 16) / (dst_w - 1);
        let x_table: Vec<(usize, usize, u32)> = (0..dst_w)
            .map(|dx| {
                let sx_fixed = dx * scale_x;
                let x0 = (sx_fixed >> 16).min(src_w - 1);
                let x1 = (x0 + 1).min(src_w - 1);
                // Extract fractional part as 8-bit fixed point
                let fx = ((sx_fixed >> 8) & 0xFF) as u32;
                (x0, x1, fx)
            })
            .collect();

        // Precompute Y coordinate table
        let scale_y = ((src_h - 1) << 16) / (dst_h - 1);
        let y_table: Vec<(usize, usize, u32)> = (0..dst_h)
            .map(|dy| {
                let sy_fixed = dy * scale_y;
                let y0 = (sy_fixed >> 16).min(src_h - 1);
                let y1 = (y0 + 1).min(src_h - 1);
                let fy = ((sy_fixed >> 8) & 0xFF) as u32;
                (y0, y1, fy)
            })
            .collect();

        for (dy, &(y0, y1, fy)) in y_table.iter().enumerate() {
            let row0 = y0 * src_w;
            let row1 = y1 * src_w;
            let dst_row = dy * dst_w;

            for (dx, &(x0, x1, fx)) in x_table.iter().enumerate() {
                let p00 = self.small_buffer[row0 + x0];
                let p10 = self.small_buffer[row0 + x1];
                let p01 = self.small_buffer[row1 + x0];
                let p11 = self.small_buffer[row1 + x1];

                // Bilinear interpolation for each channel using integer math
                let r0 = Self::ilerp((p00 >> 16) & 0xFF, (p10 >> 16) & 0xFF, fx);
                let r1 = Self::ilerp((p01 >> 16) & 0xFF, (p11 >> 16) & 0xFF, fx);
                let r = Self::ilerp(r0, r1, fy);

                let g0 = Self::ilerp((p00 >> 8) & 0xFF, (p10 >> 8) & 0xFF, fx);
                let g1 = Self::ilerp((p01 >> 8) & 0xFF, (p11 >> 8) & 0xFF, fx);
                let g = Self::ilerp(g0, g1, fy);

                let b0 = Self::ilerp(p00 & 0xFF, p10 & 0xFF, fx);
                let b1 = Self::ilerp(p01 & 0xFF, p11 & 0xFF, fx);
                let b = Self::ilerp(b0, b1, fy);

                self.bloom_buffer[dst_row + dx] = 0xFF00_0000 | (r << 16) | (g << 8) | b;
            }
        }
    }

    /// Applies a separable box blur in-place using `small_buffer` and `blur_temp`.
    /// After this call, result is in `small_buffer`.
    ///
    /// Uses O(n) sliding window algorithm instead of O(n × radius) naive approach.
    /// With radius=2 and 180×320 buffer, this reduces iterations from ~1.8M to ~115K.
    #[allow(clippy::cast_possible_wrap)] // Dimensions will never overflow i32
    fn box_blur_in_place(&mut self, width: usize, height: usize) {
        if width == 0 || height == 0 {
            return;
        }

        let r = self.radius as usize;
        let diameter = 2 * r + 1;
        // Pre-compute reciprocal for faster division (multiply by reciprocal)
        let inv_diameter = 1.0 / diameter as f32;

        // Horizontal pass: small_buffer -> blur_temp (O(n) sliding window)
        for y in 0..height {
            let row = y * width;

            // Initialize window sum for x=0
            // Window covers conceptual positions [-r, r], clamped to [0, min(r, width-1)]
            let mut sum_r = 0u32;
            let mut sum_g = 0u32;
            let mut sum_b = 0u32;

            // Add pixels in range [0, r] (or width-1 if smaller)
            for i in 0..=r.min(width - 1) {
                let p = self.small_buffer[row + i];
                sum_r += (p >> 16) & 0xFF;
                sum_g += (p >> 8) & 0xFF;
                sum_b += p & 0xFF;
            }
            // Add repeated edge pixel for clamped left positions [-r, -1]
            let p0 = self.small_buffer[row];
            sum_r += ((p0 >> 16) & 0xFF) * r as u32;
            sum_g += ((p0 >> 8) & 0xFF) * r as u32;
            sum_b += (p0 & 0xFF) * r as u32;
            // Handle right edge clamping if width <= r
            if width <= r {
                let pn = self.small_buffer[row + width - 1];
                let extra = r - width + 1;
                sum_r += ((pn >> 16) & 0xFF) * extra as u32;
                sum_g += ((pn >> 8) & 0xFF) * extra as u32;
                sum_b += (pn & 0xFF) * extra as u32;
            }

            for x in 0..width {
                // Store result using reciprocal multiplication
                let avg_r = ((sum_r as f32 * inv_diameter) as u32).min(255);
                let avg_g = ((sum_g as f32 * inv_diameter) as u32).min(255);
                let avg_b = ((sum_b as f32 * inv_diameter) as u32).min(255);
                self.blur_temp[row + x] = 0xFF00_0000 | (avg_r << 16) | (avg_g << 8) | avg_b;

                // Slide window: remove leaving pixel, add entering pixel
                // Leaving pixel is at conceptual position x-r (clamped)
                let leave_idx = x.saturating_sub(r);
                let leave = self.small_buffer[row + leave_idx];
                sum_r -= (leave >> 16) & 0xFF;
                sum_g -= (leave >> 8) & 0xFF;
                sum_b -= leave & 0xFF;

                // Entering pixel is at conceptual position x+r+1 (clamped)
                let enter_idx = (x + r + 1).min(width - 1);
                let enter = self.small_buffer[row + enter_idx];
                sum_r += (enter >> 16) & 0xFF;
                sum_g += (enter >> 8) & 0xFF;
                sum_b += enter & 0xFF;
            }
        }

        // Vertical pass: blur_temp -> small_buffer (O(n) sliding window)
        for x in 0..width {
            // Initialize window sum for y=0
            let mut sum_r = 0u32;
            let mut sum_g = 0u32;
            let mut sum_b = 0u32;

            // Add pixels in range [0, r] (or height-1 if smaller)
            for i in 0..=r.min(height - 1) {
                let p = self.blur_temp[i * width + x];
                sum_r += (p >> 16) & 0xFF;
                sum_g += (p >> 8) & 0xFF;
                sum_b += p & 0xFF;
            }
            // Add repeated edge pixel for clamped top positions
            let p0 = self.blur_temp[x];
            sum_r += ((p0 >> 16) & 0xFF) * r as u32;
            sum_g += ((p0 >> 8) & 0xFF) * r as u32;
            sum_b += (p0 & 0xFF) * r as u32;
            // Handle bottom edge clamping if height <= r
            if height <= r {
                let pn = self.blur_temp[(height - 1) * width + x];
                let extra = r - height + 1;
                sum_r += ((pn >> 16) & 0xFF) * extra as u32;
                sum_g += ((pn >> 8) & 0xFF) * extra as u32;
                sum_b += (pn & 0xFF) * extra as u32;
            }

            for y in 0..height {
                // Store result
                let avg_r = ((sum_r as f32 * inv_diameter) as u32).min(255);
                let avg_g = ((sum_g as f32 * inv_diameter) as u32).min(255);
                let avg_b = ((sum_b as f32 * inv_diameter) as u32).min(255);
                self.small_buffer[y * width + x] =
                    0xFF00_0000 | (avg_r << 16) | (avg_g << 8) | avg_b;

                // Slide window
                let leave_idx = y.saturating_sub(r);
                let leave = self.blur_temp[leave_idx * width + x];
                sum_r -= (leave >> 16) & 0xFF;
                sum_g -= (leave >> 8) & 0xFF;
                sum_b -= leave & 0xFF;

                let enter_idx = (y + r + 1).min(height - 1);
                let enter = self.blur_temp[enter_idx * width + x];
                sum_r += (enter >> 16) & 0xFF;
                sum_g += (enter >> 8) & 0xFF;
                sum_b += enter & 0xFF;
            }
        }
    }

    /// Additively blends two pixels.
    #[inline]
    fn additive_blend(base: u32, bloom: u32) -> u32 {
        let r = (((base >> 16) & 0xFF) + ((bloom >> 16) & 0xFF)).min(255);
        let g = (((base >> 8) & 0xFF) + ((bloom >> 8) & 0xFF)).min(255);
        let b = ((base & 0xFF) + (bloom & 0xFF)).min(255);
        0xFF00_0000 | (r << 16) | (g << 8) | b
    }
}

impl Default for BloomEffect {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_effect_new() {
        let bloom = BloomEffect::new();
        assert!((bloom.threshold - 0.7).abs() < 0.01);
        assert!((bloom.intensity - 1.0).abs() < 0.01);
        assert_eq!(bloom.passes, 2);
        assert_eq!(bloom.downscale, 4);
    }

    #[test]
    fn test_bloom_effect_default() {
        let bloom = BloomEffect::default();
        assert!((bloom.threshold - 0.7).abs() < 0.01);
    }

    #[test]
    fn test_bloom_effect_presets() {
        let subtle = BloomEffect::subtle();
        assert!((subtle.threshold - 0.8).abs() < 0.01);
        assert!((subtle.intensity - 0.5).abs() < 0.01);

        let intense = BloomEffect::intense();
        assert!((intense.threshold - 0.5).abs() < 0.01);
        assert!((intense.intensity - 2.0).abs() < 0.01);
    }

    #[test]
    fn test_bloom_effect_builders() {
        let bloom = BloomEffect::new()
            .with_threshold(0.5)
            .with_intensity(2.0)
            .with_passes(3)
            .with_downscale(2);

        assert!((bloom.threshold - 0.5).abs() < 0.01);
        assert!((bloom.intensity - 2.0).abs() < 0.01);
        assert_eq!(bloom.passes, 3);
        assert_eq!(bloom.downscale, 2);
    }

    #[test]
    fn test_bloom_effect_threshold_clamp() {
        let bloom = BloomEffect::new().with_threshold(1.5);
        assert!((bloom.threshold - 1.0).abs() < 0.01);

        let bloom = BloomEffect::new().with_threshold(-0.5);
        assert!((bloom.threshold - 0.0).abs() < 0.01);
    }

    #[test]
    fn test_bloom_apply_empty() {
        let mut bloom = BloomEffect::new();
        let mut pixels: Vec<u32> = vec![];
        bloom.apply(&mut pixels, 0, 0);
        assert!(pixels.is_empty());
    }

    #[test]
    fn test_bloom_apply_all_black() {
        let mut bloom = BloomEffect::new();
        let mut pixels = vec![0xFF00_0000_u32; 16 * 16];
        bloom.apply(&mut pixels, 16, 16);

        // All black should stay black (below threshold)
        for &pixel in &pixels {
            assert_eq!(pixel, 0xFF00_0000);
        }
    }

    #[test]
    fn test_bloom_apply_bright_pixels() {
        let mut bloom = BloomEffect::new().with_threshold(0.5);
        let mut pixels = vec![0xFF00_0000_u32; 16 * 16];

        // Add some bright white pixels in the center
        for y in 6..10 {
            for x in 6..10 {
                pixels[y * 16 + x] = 0xFFFF_FFFF;
            }
        }

        let original = pixels.clone();
        bloom.apply(&mut pixels, 16, 16);

        // The bloom should spread the bright area
        // Check that some previously dark pixels are now brighter
        let mut has_bloom = false;
        for y in 0..16 {
            for x in 0..16 {
                if original[y * 16 + x] == 0xFF00_0000 && pixels[y * 16 + x] != 0xFF00_0000 {
                    has_bloom = true;
                    break;
                }
            }
        }
        assert!(has_bloom, "Bloom should spread to nearby pixels");
    }

    #[test]
    fn test_bloom_buffer_reuse() {
        // Test that buffers are reused across multiple apply() calls
        let mut bloom = BloomEffect::new().with_threshold(0.5);
        let mut pixels = vec![0xFFFF_FFFF_u32; 16 * 16];

        // First apply - allocates buffers
        bloom.apply(&mut pixels, 16, 16);
        assert_eq!(bloom.cached_width, 16);
        assert_eq!(bloom.cached_height, 16);
        assert!(!bloom.bright_buffer.is_empty());

        // Second apply - reuses buffers (same dimensions)
        let mut pixels2 = vec![0xFFFF_FFFF_u32; 16 * 16];
        bloom.apply(&mut pixels2, 16, 16);
        // Dimensions unchanged means buffers were reused
        assert_eq!(bloom.cached_width, 16);
        assert_eq!(bloom.cached_height, 16);
    }

    #[test]
    fn test_bloom_buffer_resize() {
        // Test that buffers resize when dimensions change
        let mut bloom = BloomEffect::new().with_threshold(0.5);

        // First apply at 16x16
        let mut pixels1 = vec![0xFFFF_FFFF_u32; 16 * 16];
        bloom.apply(&mut pixels1, 16, 16);
        assert_eq!(bloom.cached_width, 16);
        assert_eq!(bloom.cached_height, 16);

        // Second apply at 32x32 - buffers should resize
        let mut pixels2 = vec![0xFFFF_FFFF_u32; 32 * 32];
        bloom.apply(&mut pixels2, 32, 32);
        assert_eq!(bloom.cached_width, 32);
        assert_eq!(bloom.cached_height, 32);
        assert_eq!(bloom.bright_buffer.len(), 32 * 32);
        assert_eq!(bloom.bloom_buffer.len(), 32 * 32);
    }

    #[test]
    fn test_additive_blend() {
        // Blend black with white
        let result = BloomEffect::additive_blend(0xFF00_0000, 0xFFFF_FFFF);
        assert_eq!(result, 0xFFFF_FFFF);

        // Blend gray with gray (should saturate)
        let result = BloomEffect::additive_blend(0xFF80_8080, 0xFF80_8080);
        assert_eq!(result, 0xFFFF_FFFF); // Saturated to white

        // Blend dark colors
        let result = BloomEffect::additive_blend(0xFF20_2020, 0xFF10_1010);
        assert_eq!(result, 0xFF30_3030);
    }

    #[test]
    fn test_bloom_preserves_black_pixels() {
        // Test that all-black image stays black after bloom
        let mut bloom = BloomEffect::new();
        let mut pixels = vec![0xFF00_0000_u32; 32 * 32];

        bloom.apply(&mut pixels, 32, 32);

        for &pixel in &pixels {
            assert_eq!(pixel, 0xFF00_0000, "Black pixels should stay black");
        }
    }

    #[test]
    fn test_bloom_spreads_bright_pixels() {
        // Test that bright pixels spread to neighbors
        // Use downscale=1 to avoid downsampling artifacts and verify pure blur spreading
        let mut bloom = BloomEffect::new()
            .with_threshold(0.3)
            .with_intensity(2.0)
            .with_passes(2)
            .with_downscale(1); // No downscaling for predictable spreading
        let mut pixels = vec![0xFF00_0000_u32; 32 * 32];

        // Put a 4x4 bright region in the center for clear visibility
        for dy in 0..4 {
            for dx in 0..4 {
                pixels[(14 + dy) * 32 + (14 + dx)] = 0xFFFF_FFFF;
            }
        }

        let original = pixels.clone();
        bloom.apply(&mut pixels, 32, 32);

        // Check that some previously dark pixels now have bloom
        let mut count_bloomed = 0;
        for y in 0..32 {
            for x in 0..32 {
                // Was originally black but now has some color
                if original[y * 32 + x] == 0xFF00_0000 && pixels[y * 32 + x] != 0xFF00_0000 {
                    count_bloomed += 1;
                }
            }
        }

        // With downscale=1, blur radius=2, passes=2, we should see some spreading
        assert!(
            count_bloomed > 0,
            "Bloom should spread to at least some pixels outside bright region"
        );
    }
}
