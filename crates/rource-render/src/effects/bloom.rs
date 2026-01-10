//! Bloom (glow) effect implementation.
//!
//! This module provides a CPU-efficient bloom effect that creates a glow
//! around bright areas of the image. The effect works by:
//!
//! 1. Extracting bright pixels above a threshold
//! 2. Downscaling for faster blur
//! 3. Applying box blur (faster than Gaussian)
//! 4. Upscaling and additively blending back

// Allow lossless casts written as `as` for brevity in numeric code
#![allow(clippy::cast_lossless)]

/// Configuration for the bloom effect.
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
    pub fn new() -> Self {
        Self {
            threshold: 0.7,
            intensity: 1.0,
            passes: 2,
            downscale: 4,
            radius: 2,
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
    ///
    /// # Arguments
    /// * `pixels` - Mutable pixel buffer to apply the effect to
    /// * `width` - Buffer width in pixels
    /// * `height` - Buffer height in pixels
    pub fn apply(&self, pixels: &mut [u32], width: usize, height: usize) {
        if pixels.is_empty() || width == 0 || height == 0 {
            return;
        }

        // 1. Extract bright pixels
        let bright = self.extract_bright(pixels, width, height);

        // 2. Downscale for faster blur
        let small_w = (width / self.downscale).max(1);
        let small_h = (height / self.downscale).max(1);
        let mut small = self.downscale_buffer(&bright, width, height, small_w, small_h);

        // 3. Apply box blur multiple times
        for _ in 0..self.passes {
            small = self.box_blur(&small, small_w, small_h);
        }

        // 4. Upscale and blend back
        let bloom = self.upscale_buffer(&small, small_w, small_h, width, height);

        // 5. Additive blend
        for (pixel, bloom_pixel) in pixels.iter_mut().zip(bloom.iter()) {
            *pixel = self.additive_blend(*pixel, *bloom_pixel);
        }
    }

    /// Extracts bright pixels above the threshold.
    fn extract_bright(&self, pixels: &[u32], _width: usize, _height: usize) -> Vec<u32> {
        pixels
            .iter()
            .map(|&p| {
                let r = ((p >> 16) & 0xFF) as f32 / 255.0;
                let g = ((p >> 8) & 0xFF) as f32 / 255.0;
                let b = (p & 0xFF) as f32 / 255.0;

                // Calculate perceived brightness (ITU-R BT.601)
                let brightness = r * 0.299 + g * 0.587 + b * 0.114;

                if brightness > self.threshold {
                    let factor = (brightness - self.threshold) * self.intensity;
                    let nr = ((r * factor * 255.0) as u32).min(255);
                    let ng = ((g * factor * 255.0) as u32).min(255);
                    let nb = ((b * factor * 255.0) as u32).min(255);
                    0xFF00_0000 | (nr << 16) | (ng << 8) | nb
                } else {
                    0xFF00_0000 // Black with full alpha
                }
            })
            .collect()
    }

    /// Downscales a buffer using box filtering.
    #[allow(clippy::unused_self)]
    fn downscale_buffer(
        &self,
        src: &[u32],
        src_w: usize,
        src_h: usize,
        dst_w: usize,
        dst_h: usize,
    ) -> Vec<u32> {
        let mut dst = vec![0xFF00_0000_u32; dst_w * dst_h];

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
                        let pixel = src[sy * src_w + sx];
                        r_sum += (pixel >> 16) & 0xFF;
                        g_sum += (pixel >> 8) & 0xFF;
                        b_sum += pixel & 0xFF;
                        count += 1;
                    }
                }

                if count > 0 {
                    let r = r_sum / count;
                    let g = g_sum / count;
                    let b = b_sum / count;
                    dst[dy * dst_w + dx] = 0xFF00_0000 | (r << 16) | (g << 8) | b;
                }
            }
        }

        dst
    }

    /// Upscales a buffer using bilinear interpolation.
    #[allow(clippy::unused_self)]
    fn upscale_buffer(
        &self,
        src: &[u32],
        src_w: usize,
        src_h: usize,
        dst_w: usize,
        dst_h: usize,
    ) -> Vec<u32> {
        let mut dst = vec![0xFF00_0000_u32; dst_w * dst_h];

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

                let p00 = src[y0 * src_w + x0];
                let p10 = src[y0 * src_w + x1];
                let p01 = src[y1 * src_w + x0];
                let p11 = src[y1 * src_w + x1];

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

                dst[dy * dst_w + dx] = 0xFF00_0000 | (r << 16) | (g << 8) | b;
            }
        }

        dst
    }

    /// Applies a separable box blur.
    #[allow(clippy::cast_possible_wrap)] // Dimensions will never overflow i32
    fn box_blur(&self, src: &[u32], width: usize, height: usize) -> Vec<u32> {
        if src.is_empty() || width == 0 || height == 0 {
            return src.to_vec();
        }

        let radius = self.radius;

        // Horizontal pass
        let mut temp = vec![0xFF00_0000_u32; src.len()];
        for y in 0..height {
            for x in 0..width {
                let mut r = 0u32;
                let mut g = 0u32;
                let mut b = 0u32;
                let mut count = 0u32;

                for dx in -radius..=radius {
                    let nx = (x as i32 + dx).clamp(0, width as i32 - 1) as usize;
                    let pixel = src[y * width + nx];
                    r += (pixel >> 16) & 0xFF;
                    g += (pixel >> 8) & 0xFF;
                    b += pixel & 0xFF;
                    count += 1;
                }

                temp[y * width + x] = 0xFF00_0000 | ((r / count) << 16) | ((g / count) << 8) | (b / count);
            }
        }

        // Vertical pass
        let mut dst = vec![0xFF00_0000_u32; src.len()];
        for y in 0..height {
            for x in 0..width {
                let mut r = 0u32;
                let mut g = 0u32;
                let mut b = 0u32;
                let mut count = 0u32;

                for dy in -radius..=radius {
                    let ny = (y as i32 + dy).clamp(0, height as i32 - 1) as usize;
                    let pixel = temp[ny * width + x];
                    r += (pixel >> 16) & 0xFF;
                    g += (pixel >> 8) & 0xFF;
                    b += pixel & 0xFF;
                    count += 1;
                }

                dst[y * width + x] = 0xFF00_0000 | ((r / count) << 16) | ((g / count) << 8) | (b / count);
            }
        }

        dst
    }

    /// Additively blends two pixels.
    #[inline]
    #[allow(clippy::unused_self)]
    fn additive_blend(&self, base: u32, bloom: u32) -> u32 {
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
        let bloom = BloomEffect::new();
        let mut pixels: Vec<u32> = vec![];
        bloom.apply(&mut pixels, 0, 0);
        assert!(pixels.is_empty());
    }

    #[test]
    fn test_bloom_apply_all_black() {
        let bloom = BloomEffect::new();
        let mut pixels = vec![0xFF00_0000_u32; 16 * 16];
        bloom.apply(&mut pixels, 16, 16);

        // All black should stay black (below threshold)
        for &pixel in &pixels {
            assert_eq!(pixel, 0xFF00_0000);
        }
    }

    #[test]
    fn test_bloom_apply_bright_pixels() {
        let bloom = BloomEffect::new().with_threshold(0.5);
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
    fn test_extract_bright() {
        let bloom = BloomEffect::new().with_threshold(0.5);

        // White pixel (brightness 1.0 > 0.5)
        let pixels = vec![0xFFFF_FFFF];
        let bright = bloom.extract_bright(&pixels, 1, 1);
        assert_ne!(bright[0], 0xFF00_0000, "White pixel should be extracted");

        // Black pixel (brightness 0.0 < 0.5)
        let pixels = vec![0xFF00_0000];
        let bright = bloom.extract_bright(&pixels, 1, 1);
        assert_eq!(bright[0], 0xFF00_0000, "Black pixel should not be extracted");
    }

    #[test]
    fn test_box_blur() {
        let bloom = BloomEffect::new();

        // Create a simple gradient
        let mut pixels = vec![0xFF00_0000_u32; 4 * 4];
        pixels[5] = 0xFFFF_FFFF; // Center pixel white
        pixels[6] = 0xFFFF_FFFF;
        pixels[9] = 0xFFFF_FFFF;
        pixels[10] = 0xFFFF_FFFF;

        let blurred = bloom.box_blur(&pixels, 4, 4);

        // After blur, the bright region should spread
        // Corner pixels should have some brightness now
        let corner = blurred[0];
        let r = (corner >> 16) & 0xFF;
        assert!(r > 0, "Blur should spread brightness to corners");
    }

    #[test]
    fn test_additive_blend() {
        let bloom = BloomEffect::new();

        // Blend black with white
        let result = bloom.additive_blend(0xFF00_0000, 0xFFFF_FFFF);
        assert_eq!(result, 0xFFFF_FFFF);

        // Blend gray with gray (should saturate)
        let result = bloom.additive_blend(0xFF80_8080, 0xFF80_8080);
        assert_eq!(result, 0xFFFF_FFFF); // Saturated to white

        // Blend dark colors
        let result = bloom.additive_blend(0xFF20_2020, 0xFF10_1010);
        assert_eq!(result, 0xFF30_3030);
    }

    #[test]
    fn test_downscale_buffer() {
        let bloom = BloomEffect::new();

        // Create a 4x4 white image
        let src = vec![0xFFFF_FFFF; 4 * 4];

        // Downscale to 2x2
        let dst = bloom.downscale_buffer(&src, 4, 4, 2, 2);

        assert_eq!(dst.len(), 4);
        // All pixels should still be white
        for &pixel in &dst {
            let r = (pixel >> 16) & 0xFF;
            assert_eq!(r, 255, "Downscaled white should still be white");
        }
    }

    #[test]
    fn test_upscale_buffer() {
        let bloom = BloomEffect::new();

        // Create a 2x2 image with one white pixel
        let mut src = vec![0xFF00_0000; 2 * 2];
        src[0] = 0xFFFF_FFFF; // Top-left white

        // Upscale to 4x4
        let dst = bloom.upscale_buffer(&src, 2, 2, 4, 4);

        assert_eq!(dst.len(), 16);

        // Top-left should still be bright
        let tl = (dst[0] >> 16) & 0xFF;
        assert_eq!(tl, 255, "Top-left should be white");

        // Bottom-right should be dark
        let br = (dst[15] >> 16) & 0xFF;
        assert_eq!(br, 0, "Bottom-right should be black");
    }
}
