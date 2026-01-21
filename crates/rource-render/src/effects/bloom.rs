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
    fn extract_bright_into(&mut self, pixels: &[u32]) {
        for (dst, &p) in self.bright_buffer.iter_mut().zip(pixels.iter()) {
            let r = ((p >> 16) & 0xFF) as f32 / 255.0;
            let g = ((p >> 8) & 0xFF) as f32 / 255.0;
            let b = (p & 0xFF) as f32 / 255.0;

            // Calculate perceived brightness (ITU-R BT.601)
            let brightness = r * 0.299 + g * 0.587 + b * 0.114;

            *dst = if brightness > self.threshold {
                let factor = (brightness - self.threshold) * self.intensity;
                let nr = ((r * factor * 255.0) as u32).min(255);
                let ng = ((g * factor * 255.0) as u32).min(255);
                let nb = ((b * factor * 255.0) as u32).min(255);
                0xFF00_0000 | (nr << 16) | (ng << 8) | nb
            } else {
                0xFF00_0000 // Black with full alpha
            };
        }
    }

    /// Downscales `bright_buffer` into `small_buffer` using box filtering.
    fn downscale_into(&mut self, src_w: usize, src_h: usize, dst_w: usize, dst_h: usize) {
        let scale_x = src_w as f32 / dst_w as f32;
        let scale_y = src_h as f32 / dst_h as f32;

        for dy in 0..dst_h {
            for dx in 0..dst_w {
                let sx_start = (dx as f32 * scale_x) as usize;
                let sy_start = (dy as f32 * scale_y) as usize;
                let sx_end = ((dx + 1) as f32 * scale_x) as usize;
                let sy_end = ((dy + 1) as f32 * scale_y) as usize;

                let mut r_sum = 0u32;
                let mut g_sum = 0u32;
                let mut b_sum = 0u32;
                let mut count = 0u32;

                for sy in sy_start..sy_end.min(src_h) {
                    for sx in sx_start..sx_end.min(src_w) {
                        let pixel = self.bright_buffer[sy * src_w + sx];
                        r_sum += (pixel >> 16) & 0xFF;
                        g_sum += (pixel >> 8) & 0xFF;
                        b_sum += pixel & 0xFF;
                        count += 1;
                    }
                }

                self.small_buffer[dy * dst_w + dx] = if count > 0 {
                    let r = r_sum / count;
                    let g = g_sum / count;
                    let b = b_sum / count;
                    0xFF00_0000 | (r << 16) | (g << 8) | b
                } else {
                    0xFF00_0000
                };
            }
        }
    }

    /// Upscales `small_buffer` into `bloom_buffer` using bilinear interpolation.
    fn upscale_into(&mut self, src_w: usize, src_h: usize, dst_w: usize, dst_h: usize) {
        let scale_x = (src_w - 1) as f32 / (dst_w - 1).max(1) as f32;
        let scale_y = (src_h - 1) as f32 / (dst_h - 1).max(1) as f32;

        for dy in 0..dst_h {
            for dx in 0..dst_w {
                let sx = dx as f32 * scale_x;
                let sy = dy as f32 * scale_y;

                let x0 = sx.floor() as usize;
                let y0 = sy.floor() as usize;
                let x1 = (x0 + 1).min(src_w - 1);
                let y1 = (y0 + 1).min(src_h - 1);

                let fx = sx.fract();
                let fy = sy.fract();

                let p00 = self.small_buffer[y0 * src_w + x0];
                let p10 = self.small_buffer[y0 * src_w + x1];
                let p01 = self.small_buffer[y1 * src_w + x0];
                let p11 = self.small_buffer[y1 * src_w + x1];

                let lerp = |a: u32, b: u32, t: f32| -> u32 {
                    ((a as f32 * (1.0 - t) + b as f32 * t) as u32).min(255)
                };

                let r0 = lerp((p00 >> 16) & 0xFF, (p10 >> 16) & 0xFF, fx);
                let r1 = lerp((p01 >> 16) & 0xFF, (p11 >> 16) & 0xFF, fx);
                let r = lerp(r0, r1, fy);

                let g0 = lerp((p00 >> 8) & 0xFF, (p10 >> 8) & 0xFF, fx);
                let g1 = lerp((p01 >> 8) & 0xFF, (p11 >> 8) & 0xFF, fx);
                let g = lerp(g0, g1, fy);

                let b0 = lerp(p00 & 0xFF, p10 & 0xFF, fx);
                let b1 = lerp(p01 & 0xFF, p11 & 0xFF, fx);
                let b = lerp(b0, b1, fy);

                self.bloom_buffer[dy * dst_w + dx] = 0xFF00_0000 | (r << 16) | (g << 8) | b;
            }
        }
    }

    /// Applies a separable box blur in-place using `small_buffer` and `blur_temp`.
    /// After this call, result is in `small_buffer`.
    #[allow(clippy::cast_possible_wrap)] // Dimensions will never overflow i32
    fn box_blur_in_place(&mut self, width: usize, height: usize) {
        if width == 0 || height == 0 {
            return;
        }

        let radius = self.radius;

        // Horizontal pass: small_buffer -> blur_temp
        for y in 0..height {
            for x in 0..width {
                let mut r = 0u32;
                let mut g = 0u32;
                let mut b = 0u32;
                let mut count = 0u32;

                for dx in -radius..=radius {
                    let nx = (x as i32 + dx).clamp(0, width as i32 - 1) as usize;
                    let pixel = self.small_buffer[y * width + nx];
                    r += (pixel >> 16) & 0xFF;
                    g += (pixel >> 8) & 0xFF;
                    b += pixel & 0xFF;
                    count += 1;
                }

                self.blur_temp[y * width + x] =
                    0xFF00_0000 | ((r / count) << 16) | ((g / count) << 8) | (b / count);
            }
        }

        // Vertical pass: blur_temp -> small_buffer
        for y in 0..height {
            for x in 0..width {
                let mut r = 0u32;
                let mut g = 0u32;
                let mut b = 0u32;
                let mut count = 0u32;

                for dy in -radius..=radius {
                    let ny = (y as i32 + dy).clamp(0, height as i32 - 1) as usize;
                    let pixel = self.blur_temp[ny * width + x];
                    r += (pixel >> 16) & 0xFF;
                    g += (pixel >> 8) & 0xFF;
                    b += pixel & 0xFF;
                    count += 1;
                }

                self.small_buffer[y * width + x] =
                    0xFF00_0000 | ((r / count) << 16) | ((g / count) << 8) | (b / count);
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
