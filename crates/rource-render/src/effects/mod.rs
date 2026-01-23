// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Post-processing effects.
//!
//! This module provides CPU-efficient post-processing effects:
//! - [`BloomEffect`]: Glow effect for bright areas
//! - [`ShadowEffect`]: Drop shadow effect for depth
//!
//! ## Validation Helpers
//!
//! This module also exports testable validation functions for effect parameters:
//! - [`validate_bloom_threshold`] - Clamp threshold to [0.0, 1.0]
//! - [`validate_bloom_intensity`] - Clamp intensity to [0.0, ∞)
//! - [`validate_bloom_passes`] - Clamp passes to [1, ∞)
//! - [`validate_bloom_downscale`] - Clamp downscale to [1, ∞)
//! - [`validate_shadow_opacity`] - Clamp opacity to [0.0, 1.0]
//! - [`validate_shadow_blur_passes`] - Clamp passes to [1, ∞)
//! - [`validate_shadow_blur_radius`] - Clamp radius to [0, ∞)

pub mod bloom;
pub mod shadow;

pub use bloom::BloomEffect;
pub use shadow::ShadowEffect;

// ============================================================================
// Validation Helper Functions (testable without effect instance)
// ============================================================================

/// Helper functions for validating effect parameters.
///
/// These functions encapsulate pure validation logic that can be unit tested
/// independently and reused across different backends (wgpu, WebGL2, software).
#[allow(dead_code)]
#[allow(clippy::cast_lossless)]
mod helpers {
    // ========================================================================
    // Bloom Validation
    // ========================================================================

    /// Valid range for bloom threshold.
    pub const BLOOM_THRESHOLD_MIN: f32 = 0.0;
    /// Valid range for bloom threshold.
    pub const BLOOM_THRESHOLD_MAX: f32 = 1.0;
    /// Default bloom threshold.
    pub const BLOOM_THRESHOLD_DEFAULT: f32 = 0.7;

    /// Valid minimum for bloom intensity.
    pub const BLOOM_INTENSITY_MIN: f32 = 0.0;
    /// Default bloom intensity.
    pub const BLOOM_INTENSITY_DEFAULT: f32 = 1.0;

    /// Valid minimum for bloom passes.
    pub const BLOOM_PASSES_MIN: usize = 1;
    /// Default bloom passes.
    pub const BLOOM_PASSES_DEFAULT: usize = 2;

    /// Valid minimum for bloom downscale.
    pub const BLOOM_DOWNSCALE_MIN: usize = 1;
    /// Default bloom downscale.
    pub const BLOOM_DOWNSCALE_DEFAULT: usize = 4;

    /// Valid minimum for bloom radius.
    pub const BLOOM_RADIUS_MIN: i32 = 1;
    /// Default bloom radius.
    pub const BLOOM_RADIUS_DEFAULT: i32 = 2;

    /// Validates and clamps a bloom threshold value.
    ///
    /// # Arguments
    /// * `threshold` - The threshold value to validate
    ///
    /// # Returns
    /// A valid threshold clamped to [0.0, 1.0].
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_bloom_threshold;
    /// assert!((validate_bloom_threshold(0.5) - 0.5).abs() < 0.001);
    /// assert!((validate_bloom_threshold(-0.5) - 0.0).abs() < 0.001);
    /// assert!((validate_bloom_threshold(1.5) - 1.0).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_bloom_threshold(threshold: f32) -> f32 {
        if threshold.is_nan() {
            return BLOOM_THRESHOLD_DEFAULT;
        }
        threshold.clamp(BLOOM_THRESHOLD_MIN, BLOOM_THRESHOLD_MAX)
    }

    /// Validates and clamps a bloom intensity value.
    ///
    /// # Arguments
    /// * `intensity` - The intensity value to validate
    ///
    /// # Returns
    /// A valid intensity clamped to [0.0, ∞).
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_bloom_intensity;
    /// assert!((validate_bloom_intensity(1.5) - 1.5).abs() < 0.001);
    /// assert!((validate_bloom_intensity(-0.5) - 0.0).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_bloom_intensity(intensity: f32) -> f32 {
        if intensity.is_nan() || intensity.is_infinite() {
            return BLOOM_INTENSITY_DEFAULT;
        }
        intensity.max(BLOOM_INTENSITY_MIN)
    }

    /// Validates and clamps a bloom passes value.
    ///
    /// # Arguments
    /// * `passes` - The passes value to validate
    ///
    /// # Returns
    /// A valid passes count of at least 1.
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_bloom_passes;
    /// assert_eq!(validate_bloom_passes(3), 3);
    /// assert_eq!(validate_bloom_passes(0), 1);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_bloom_passes(passes: usize) -> usize {
        passes.max(BLOOM_PASSES_MIN)
    }

    /// Validates and clamps a bloom downscale value.
    ///
    /// # Arguments
    /// * `downscale` - The downscale factor to validate
    ///
    /// # Returns
    /// A valid downscale factor of at least 1.
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_bloom_downscale;
    /// assert_eq!(validate_bloom_downscale(4), 4);
    /// assert_eq!(validate_bloom_downscale(0), 1);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_bloom_downscale(downscale: usize) -> usize {
        downscale.max(BLOOM_DOWNSCALE_MIN)
    }

    /// Validates and clamps a bloom radius value.
    ///
    /// # Arguments
    /// * `radius` - The blur radius to validate
    ///
    /// # Returns
    /// A valid radius of at least 1.
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_bloom_radius;
    /// assert_eq!(validate_bloom_radius(3), 3);
    /// assert_eq!(validate_bloom_radius(0), 1);
    /// assert_eq!(validate_bloom_radius(-5), 1);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_bloom_radius(radius: i32) -> i32 {
        radius.max(BLOOM_RADIUS_MIN)
    }

    // ========================================================================
    // Shadow Validation
    // ========================================================================

    /// Valid range for shadow opacity.
    pub const SHADOW_OPACITY_MIN: f32 = 0.0;
    /// Valid range for shadow opacity.
    pub const SHADOW_OPACITY_MAX: f32 = 1.0;
    /// Default shadow opacity.
    pub const SHADOW_OPACITY_DEFAULT: f32 = 0.5;

    /// Valid minimum for shadow blur passes.
    pub const SHADOW_BLUR_PASSES_MIN: usize = 1;
    /// Default shadow blur passes.
    pub const SHADOW_BLUR_PASSES_DEFAULT: usize = 2;

    /// Valid minimum for shadow blur radius.
    pub const SHADOW_BLUR_RADIUS_MIN: i32 = 0;
    /// Default shadow blur radius.
    pub const SHADOW_BLUR_RADIUS_DEFAULT: i32 = 3;

    /// Validates and clamps a shadow opacity value.
    ///
    /// # Arguments
    /// * `opacity` - The opacity value to validate
    ///
    /// # Returns
    /// A valid opacity clamped to [0.0, 1.0].
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_shadow_opacity;
    /// assert!((validate_shadow_opacity(0.5) - 0.5).abs() < 0.001);
    /// assert!((validate_shadow_opacity(-0.5) - 0.0).abs() < 0.001);
    /// assert!((validate_shadow_opacity(1.5) - 1.0).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_shadow_opacity(opacity: f32) -> f32 {
        if opacity.is_nan() {
            return SHADOW_OPACITY_DEFAULT;
        }
        opacity.clamp(SHADOW_OPACITY_MIN, SHADOW_OPACITY_MAX)
    }

    /// Validates and clamps a shadow blur passes value.
    ///
    /// # Arguments
    /// * `passes` - The passes value to validate
    ///
    /// # Returns
    /// A valid passes count of at least 1.
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_shadow_blur_passes;
    /// assert_eq!(validate_shadow_blur_passes(3), 3);
    /// assert_eq!(validate_shadow_blur_passes(0), 1);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_shadow_blur_passes(passes: usize) -> usize {
        passes.max(SHADOW_BLUR_PASSES_MIN)
    }

    /// Validates and clamps a shadow blur radius value.
    ///
    /// # Arguments
    /// * `radius` - The blur radius to validate
    ///
    /// # Returns
    /// A valid radius of at least 0.
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::validate_shadow_blur_radius;
    /// assert_eq!(validate_shadow_blur_radius(3), 3);
    /// assert_eq!(validate_shadow_blur_radius(-5), 0);
    /// ```
    #[inline]
    #[must_use]
    pub fn validate_shadow_blur_radius(radius: i32) -> i32 {
        radius.max(SHADOW_BLUR_RADIUS_MIN)
    }

    // ========================================================================
    // Computed Values
    // ========================================================================

    /// Computes the downscaled buffer dimensions for bloom/shadow effects.
    ///
    /// # Arguments
    /// * `width` - Original width
    /// * `height` - Original height
    /// * `downscale` - Downscale factor (1 = no downscaling)
    ///
    /// # Returns
    /// A tuple of (`downscaled_width`, `downscaled_height`), with minimum of 1.
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::compute_downscaled_dimensions;
    /// assert_eq!(compute_downscaled_dimensions(1920, 1080, 4), (480, 270));
    /// assert_eq!(compute_downscaled_dimensions(100, 100, 1), (100, 100));
    /// assert_eq!(compute_downscaled_dimensions(3, 3, 4), (1, 1));
    /// ```
    #[inline]
    #[must_use]
    pub fn compute_downscaled_dimensions(
        width: usize,
        height: usize,
        downscale: usize,
    ) -> (usize, usize) {
        let downscale = downscale.max(1);
        let small_w = (width / downscale).max(1);
        let small_h = (height / downscale).max(1);
        (small_w, small_h)
    }

    /// Computes the buffer size needed for effect processing.
    ///
    /// # Arguments
    /// * `width` - Buffer width
    /// * `height` - Buffer height
    ///
    /// # Returns
    /// Total number of pixels (width * height).
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::compute_buffer_size;
    /// assert_eq!(compute_buffer_size(1920, 1080), 2_073_600);
    /// assert_eq!(compute_buffer_size(100, 100), 10_000);
    /// ```
    #[inline]
    #[must_use]
    pub fn compute_buffer_size(width: usize, height: usize) -> usize {
        width * height
    }

    /// Computes pixel brightness using ITU-R BT.601 luminance coefficients.
    ///
    /// # Arguments
    /// * `r` - Red component (0-255)
    /// * `g` - Green component (0-255)
    /// * `b` - Blue component (0-255)
    ///
    /// # Returns
    /// Luminance value (0.0-1.0).
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::compute_luminance;
    /// // Pure white
    /// assert!((compute_luminance(255, 255, 255) - 1.0).abs() < 0.01);
    /// // Pure black
    /// assert!((compute_luminance(0, 0, 0) - 0.0).abs() < 0.01);
    /// // Green has highest coefficient
    /// let g_lum = compute_luminance(0, 255, 0);
    /// let r_lum = compute_luminance(255, 0, 0);
    /// let b_lum = compute_luminance(0, 0, 255);
    /// assert!(g_lum > r_lum);
    /// assert!(r_lum > b_lum);
    /// ```
    #[inline]
    #[must_use]
    pub fn compute_luminance(r: u8, g: u8, b: u8) -> f32 {
        // ITU-R BT.601 luminance coefficients
        (0.299 * r as f32 + 0.587 * g as f32 + 0.114 * b as f32) / 255.0
    }

    /// Checks if a pixel is bright enough for bloom extraction.
    ///
    /// # Arguments
    /// * `r` - Red component (0-255)
    /// * `g` - Green component (0-255)
    /// * `b` - Blue component (0-255)
    /// * `threshold` - Brightness threshold (0.0-1.0)
    ///
    /// # Returns
    /// `true` if the pixel luminance exceeds the threshold.
    ///
    /// # Examples
    /// ```
    /// use rource_render::effects::is_pixel_bright;
    /// // White pixel at 0.5 threshold should be bright
    /// assert!(is_pixel_bright(255, 255, 255, 0.5));
    /// // Black pixel should never be bright
    /// assert!(!is_pixel_bright(0, 0, 0, 0.5));
    /// ```
    #[inline]
    #[must_use]
    pub fn is_pixel_bright(r: u8, g: u8, b: u8, threshold: f32) -> bool {
        compute_luminance(r, g, b) > threshold
    }
}

#[allow(unused_imports)]
pub use helpers::*;

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Bloom Threshold Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_bloom_threshold_normal() {
        assert!((validate_bloom_threshold(0.5) - 0.5).abs() < 0.001);
        assert!((validate_bloom_threshold(0.7) - 0.7).abs() < 0.001);
        assert!((validate_bloom_threshold(0.0) - 0.0).abs() < 0.001);
        assert!((validate_bloom_threshold(1.0) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_bloom_threshold_clamp_min() {
        assert!((validate_bloom_threshold(-0.5) - 0.0).abs() < 0.001);
        assert!((validate_bloom_threshold(-100.0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_bloom_threshold_clamp_max() {
        assert!((validate_bloom_threshold(1.5) - 1.0).abs() < 0.001);
        assert!((validate_bloom_threshold(100.0) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_bloom_threshold_nan() {
        let result = validate_bloom_threshold(f32::NAN);
        assert!((result - BLOOM_THRESHOLD_DEFAULT).abs() < 0.001);
    }

    // ========================================================================
    // Bloom Intensity Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_bloom_intensity_normal() {
        assert!((validate_bloom_intensity(1.0) - 1.0).abs() < 0.001);
        assert!((validate_bloom_intensity(2.0) - 2.0).abs() < 0.001);
        assert!((validate_bloom_intensity(0.5) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_validate_bloom_intensity_clamp_min() {
        assert!((validate_bloom_intensity(-0.5) - 0.0).abs() < 0.001);
        assert!((validate_bloom_intensity(-100.0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_bloom_intensity_large_values() {
        // Large positive values are allowed
        assert!((validate_bloom_intensity(100.0) - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_bloom_intensity_nan() {
        let result = validate_bloom_intensity(f32::NAN);
        assert!((result - BLOOM_INTENSITY_DEFAULT).abs() < 0.001);
    }

    #[test]
    fn test_validate_bloom_intensity_infinity() {
        let result = validate_bloom_intensity(f32::INFINITY);
        assert!((result - BLOOM_INTENSITY_DEFAULT).abs() < 0.001);
    }

    // ========================================================================
    // Bloom Passes Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_bloom_passes_normal() {
        assert_eq!(validate_bloom_passes(1), 1);
        assert_eq!(validate_bloom_passes(2), 2);
        assert_eq!(validate_bloom_passes(10), 10);
    }

    #[test]
    fn test_validate_bloom_passes_zero() {
        assert_eq!(validate_bloom_passes(0), 1);
    }

    // ========================================================================
    // Bloom Downscale Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_bloom_downscale_normal() {
        assert_eq!(validate_bloom_downscale(1), 1);
        assert_eq!(validate_bloom_downscale(4), 4);
        assert_eq!(validate_bloom_downscale(8), 8);
    }

    #[test]
    fn test_validate_bloom_downscale_zero() {
        assert_eq!(validate_bloom_downscale(0), 1);
    }

    // ========================================================================
    // Bloom Radius Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_bloom_radius_normal() {
        assert_eq!(validate_bloom_radius(2), 2);
        assert_eq!(validate_bloom_radius(5), 5);
    }

    #[test]
    fn test_validate_bloom_radius_zero() {
        assert_eq!(validate_bloom_radius(0), 1);
    }

    #[test]
    fn test_validate_bloom_radius_negative() {
        assert_eq!(validate_bloom_radius(-5), 1);
    }

    // ========================================================================
    // Shadow Opacity Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_shadow_opacity_normal() {
        assert!((validate_shadow_opacity(0.5) - 0.5).abs() < 0.001);
        assert!((validate_shadow_opacity(0.0) - 0.0).abs() < 0.001);
        assert!((validate_shadow_opacity(1.0) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_shadow_opacity_clamp_min() {
        assert!((validate_shadow_opacity(-0.5) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_shadow_opacity_clamp_max() {
        assert!((validate_shadow_opacity(1.5) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_validate_shadow_opacity_nan() {
        let result = validate_shadow_opacity(f32::NAN);
        assert!((result - SHADOW_OPACITY_DEFAULT).abs() < 0.001);
    }

    // ========================================================================
    // Shadow Blur Passes Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_shadow_blur_passes_normal() {
        assert_eq!(validate_shadow_blur_passes(1), 1);
        assert_eq!(validate_shadow_blur_passes(3), 3);
    }

    #[test]
    fn test_validate_shadow_blur_passes_zero() {
        assert_eq!(validate_shadow_blur_passes(0), 1);
    }

    // ========================================================================
    // Shadow Blur Radius Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_shadow_blur_radius_normal() {
        assert_eq!(validate_shadow_blur_radius(3), 3);
        assert_eq!(validate_shadow_blur_radius(0), 0);
    }

    #[test]
    fn test_validate_shadow_blur_radius_negative() {
        assert_eq!(validate_shadow_blur_radius(-5), 0);
    }

    // ========================================================================
    // Computed Dimension Tests
    // ========================================================================

    #[test]
    fn test_compute_downscaled_dimensions_normal() {
        assert_eq!(compute_downscaled_dimensions(1920, 1080, 4), (480, 270));
        assert_eq!(compute_downscaled_dimensions(1000, 1000, 2), (500, 500));
    }

    #[test]
    fn test_compute_downscaled_dimensions_no_downscale() {
        assert_eq!(compute_downscaled_dimensions(100, 100, 1), (100, 100));
    }

    #[test]
    fn test_compute_downscaled_dimensions_large_downscale() {
        // Minimum dimension is 1
        assert_eq!(compute_downscaled_dimensions(10, 10, 100), (1, 1));
    }

    #[test]
    fn test_compute_downscaled_dimensions_zero_downscale() {
        // Zero downscale treated as 1
        assert_eq!(compute_downscaled_dimensions(100, 100, 0), (100, 100));
    }

    // ========================================================================
    // Buffer Size Tests
    // ========================================================================

    #[test]
    fn test_compute_buffer_size_normal() {
        assert_eq!(compute_buffer_size(1920, 1080), 2_073_600);
        assert_eq!(compute_buffer_size(100, 100), 10_000);
    }

    #[test]
    fn test_compute_buffer_size_small() {
        assert_eq!(compute_buffer_size(1, 1), 1);
    }

    // ========================================================================
    // Luminance Tests
    // ========================================================================

    #[test]
    fn test_compute_luminance_white() {
        assert!((compute_luminance(255, 255, 255) - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_compute_luminance_black() {
        assert!((compute_luminance(0, 0, 0) - 0.0).abs() < 0.01);
    }

    #[test]
    fn test_compute_luminance_coefficients() {
        // Green has highest coefficient (0.587)
        let g_lum = compute_luminance(0, 255, 0);
        // Red has middle coefficient (0.299)
        let r_lum = compute_luminance(255, 0, 0);
        // Blue has lowest coefficient (0.114)
        let b_lum = compute_luminance(0, 0, 255);

        assert!(g_lum > r_lum);
        assert!(r_lum > b_lum);
    }

    #[test]
    fn test_compute_luminance_mid_gray() {
        // 128 is approximately half brightness
        let lum = compute_luminance(128, 128, 128);
        assert!(lum > 0.45 && lum < 0.55);
    }

    // ========================================================================
    // Pixel Brightness Tests
    // ========================================================================

    #[test]
    fn test_is_pixel_bright_white() {
        assert!(is_pixel_bright(255, 255, 255, 0.5));
        assert!(is_pixel_bright(255, 255, 255, 0.9));
    }

    #[test]
    fn test_is_pixel_bright_black() {
        assert!(!is_pixel_bright(0, 0, 0, 0.1));
        assert!(!is_pixel_bright(0, 0, 0, 0.0)); // 0.0 threshold, but luminance is 0
    }

    #[test]
    fn test_is_pixel_bright_threshold_boundary() {
        // Pure white has luminance 1.0
        assert!(is_pixel_bright(255, 255, 255, 0.99));
        assert!(!is_pixel_bright(255, 255, 255, 1.0)); // Exactly at threshold, not greater
    }

    // ========================================================================
    // Constant Tests
    // ========================================================================

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_bloom_constants() {
        assert!(BLOOM_THRESHOLD_MIN < BLOOM_THRESHOLD_MAX);
        assert!(BLOOM_INTENSITY_MIN >= 0.0);
        assert!(BLOOM_PASSES_MIN >= 1);
        assert!(BLOOM_DOWNSCALE_MIN >= 1);
        assert!(BLOOM_RADIUS_MIN >= 1);
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_shadow_constants() {
        assert!(SHADOW_OPACITY_MIN < SHADOW_OPACITY_MAX);
        assert!(SHADOW_BLUR_PASSES_MIN >= 1);
        assert!(SHADOW_BLUR_RADIUS_MIN >= 0);
    }
}
