// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Post-processing effect configuration methods for the WebGL2 renderer.
//!
//! This module contains methods for configuring bloom, shadow, and adaptive quality effects.

use super::{
    adaptive::{QualityAdjustment, QualityLevel},
    bloom::BloomConfig,
    shadow::ShadowConfig,
    WebGl2Renderer,
};

impl WebGl2Renderer {
    // =========================================================================
    // Bloom Effect API
    // =========================================================================

    /// Returns whether the bloom effect is enabled and initialized.
    #[inline]
    pub fn is_bloom_enabled(&self) -> bool {
        self.bloom_pipeline.is_active()
    }

    /// Enables or disables the bloom effect.
    ///
    /// When enabled, bright areas of the scene will glow.
    /// Bloom is processed entirely on the GPU for maximum performance.
    #[inline]
    pub fn set_bloom_enabled(&mut self, enabled: bool) {
        self.bloom_pipeline.config.enabled = enabled;
    }

    /// Returns the current bloom threshold.
    #[inline]
    pub fn bloom_threshold(&self) -> f32 {
        self.bloom_pipeline.config.threshold
    }

    /// Sets the brightness threshold for bloom.
    ///
    /// Pixels with brightness above this threshold will contribute to the bloom effect.
    /// Lower values create more bloom, higher values restrict bloom to very bright areas.
    ///
    /// Default: 0.7
    #[inline]
    pub fn set_bloom_threshold(&mut self, threshold: f32) {
        self.bloom_pipeline.config.threshold = threshold.clamp(0.0, 1.0);
    }

    /// Returns the current bloom intensity.
    #[inline]
    pub fn bloom_intensity(&self) -> f32 {
        self.bloom_pipeline.config.intensity
    }

    /// Sets the bloom intensity multiplier.
    ///
    /// Higher values create a stronger glow effect.
    ///
    /// Default: 1.0
    #[inline]
    pub fn set_bloom_intensity(&mut self, intensity: f32) {
        self.bloom_pipeline.config.intensity = intensity.max(0.0);
    }

    /// Returns the current bloom downscale factor.
    #[inline]
    pub fn bloom_downscale(&self) -> u32 {
        self.bloom_pipeline.config.downscale
    }

    /// Sets the bloom downscale factor.
    ///
    /// Higher values use a smaller bloom buffer (faster but blockier).
    /// Common values: 2, 4, 8.
    ///
    /// Default: 4
    #[inline]
    pub fn set_bloom_downscale(&mut self, downscale: u32) {
        self.bloom_pipeline.config.downscale = downscale.max(1);
    }

    /// Returns the number of bloom blur passes.
    #[inline]
    pub fn bloom_passes(&self) -> u32 {
        self.bloom_pipeline.config.passes
    }

    /// Sets the number of bloom blur passes.
    ///
    /// More passes create a softer, more spread-out bloom.
    ///
    /// Default: 2
    #[inline]
    pub fn set_bloom_passes(&mut self, passes: u32) {
        self.bloom_pipeline.config.passes = passes.max(1);
    }

    /// Returns the full bloom configuration.
    #[inline]
    pub fn bloom_config(&self) -> BloomConfig {
        self.bloom_pipeline.config
    }

    /// Sets the full bloom configuration.
    #[inline]
    pub fn set_bloom_config(&mut self, config: BloomConfig) {
        self.bloom_pipeline.config = config;
    }

    // =========================================================================
    // Shadow Effect API
    // =========================================================================

    /// Returns whether the shadow effect is enabled and initialized.
    #[inline]
    pub fn is_shadow_enabled(&self) -> bool {
        self.shadow_pipeline.is_active()
    }

    /// Enables or disables the shadow effect.
    ///
    /// When enabled, entities will cast soft drop shadows.
    /// Shadow is processed entirely on the GPU for maximum performance.
    #[inline]
    pub fn set_shadow_enabled(&mut self, enabled: bool) {
        self.shadow_pipeline.config.enabled = enabled;
    }

    /// Returns the current shadow offset (X, Y) in pixels.
    #[inline]
    pub fn shadow_offset(&self) -> (f32, f32) {
        (
            self.shadow_pipeline.config.offset_x,
            self.shadow_pipeline.config.offset_y,
        )
    }

    /// Sets the shadow offset in pixels.
    ///
    /// Positive values move the shadow right and down.
    ///
    /// Default: (4.0, 4.0)
    #[inline]
    pub fn set_shadow_offset(&mut self, offset_x: f32, offset_y: f32) {
        self.shadow_pipeline.config.offset_x = offset_x;
        self.shadow_pipeline.config.offset_y = offset_y;
    }

    /// Returns the current shadow opacity.
    #[inline]
    pub fn shadow_opacity(&self) -> f32 {
        self.shadow_pipeline.config.opacity
    }

    /// Sets the shadow opacity (0.0 - 1.0).
    ///
    /// Default: 0.5
    #[inline]
    pub fn set_shadow_opacity(&mut self, opacity: f32) {
        self.shadow_pipeline.config.opacity = opacity.clamp(0.0, 1.0);
    }

    /// Returns the current shadow blur passes.
    #[inline]
    pub fn shadow_blur_passes(&self) -> u32 {
        self.shadow_pipeline.config.blur_passes
    }

    /// Sets the number of shadow blur passes.
    ///
    /// More passes create softer shadow edges.
    ///
    /// Default: 2
    #[inline]
    pub fn set_shadow_blur_passes(&mut self, passes: u32) {
        self.shadow_pipeline.config.blur_passes = passes.max(1);
    }

    /// Returns the current shadow color (RGBA).
    #[inline]
    pub fn shadow_color(&self) -> [f32; 4] {
        self.shadow_pipeline.config.color
    }

    /// Sets the shadow color (RGBA).
    ///
    /// Default: [0.0, 0.0, 0.0, 1.0] (black)
    #[inline]
    pub fn set_shadow_color(&mut self, color: [f32; 4]) {
        self.shadow_pipeline.config.color = color;
    }

    /// Returns the full shadow configuration.
    #[inline]
    pub fn shadow_config(&self) -> ShadowConfig {
        self.shadow_pipeline.config
    }

    /// Sets the full shadow configuration.
    #[inline]
    pub fn set_shadow_config(&mut self, config: ShadowConfig) {
        self.shadow_pipeline.config = config;
    }

    // =========================================================================
    // Adaptive Quality API
    // =========================================================================

    /// Returns whether adaptive quality is enabled.
    #[inline]
    pub fn is_adaptive_quality_enabled(&self) -> bool {
        self.adaptive_quality.is_enabled()
    }

    /// Enables or disables adaptive quality adjustment.
    ///
    /// When enabled, the renderer will automatically adjust bloom and shadow
    /// quality based on frame timing to maintain target FPS.
    #[inline]
    pub fn set_adaptive_quality_enabled(&mut self, enabled: bool) {
        self.adaptive_quality.set_enabled(enabled);
    }

    /// Returns the current adaptive quality level.
    #[inline]
    pub fn adaptive_quality_level(&self) -> QualityLevel {
        self.adaptive_quality.level()
    }

    /// Sets the adaptive quality level directly.
    ///
    /// This overrides automatic adjustment temporarily.
    #[inline]
    pub fn set_adaptive_quality_level(&mut self, level: QualityLevel) {
        self.adaptive_quality.set_level(level);
        self.apply_quality_adjustment(level.adjustment());
    }

    /// Returns the target FPS for adaptive quality.
    #[inline]
    pub fn adaptive_quality_target_fps(&self) -> f32 {
        self.adaptive_quality.target_fps()
    }

    /// Sets the target FPS for adaptive quality adjustment.
    ///
    /// The adaptive system will try to maintain this frame rate by
    /// adjusting effect quality.
    ///
    /// Default: 60.0
    #[inline]
    pub fn set_adaptive_quality_target_fps(&mut self, fps: f32) {
        self.adaptive_quality.set_target_fps(fps);
    }

    /// Updates adaptive quality based on the latest frame time.
    ///
    /// Call this once per frame with the frame duration. If quality
    /// adjustments are needed, they will be applied automatically.
    ///
    /// # Arguments
    ///
    /// * `frame_time_ms` - Duration of the last frame in milliseconds.
    ///
    /// # Returns
    ///
    /// `true` if quality was adjusted, `false` otherwise.
    pub fn update_adaptive_quality(&mut self, frame_time_ms: f32) -> bool {
        self.adaptive_quality
            .update(frame_time_ms)
            .is_some_and(|adjustment| {
                self.apply_quality_adjustment(adjustment);
                true
            })
    }

    /// Applies a quality adjustment to bloom and shadow pipelines.
    pub(super) fn apply_quality_adjustment(&mut self, adjustment: QualityAdjustment) {
        self.bloom_pipeline.config.downscale = adjustment.bloom_downscale;
        self.bloom_pipeline.config.passes = adjustment.bloom_passes;
        self.shadow_pipeline.config.downscale = adjustment.shadow_downscale;
        self.shadow_pipeline.config.blur_passes = adjustment.shadow_blur_passes;
    }

    /// Resets adaptive quality to initial state.
    pub fn reset_adaptive_quality(&mut self) {
        self.adaptive_quality.reset();
        self.apply_quality_adjustment(QualityAdjustment::default());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_config() {
        let config = BloomConfig::default();
        assert!(config.threshold > 0.0);
        assert!(config.intensity > 0.0);

        let subtle = BloomConfig::subtle();
        let intense = BloomConfig::intense();
        assert!(intense.intensity > subtle.intensity);
    }

    #[test]
    fn test_shadow_config() {
        let config = ShadowConfig::default();
        assert!(config.opacity > 0.0);
        assert!(config.offset_x != 0.0 || config.offset_y != 0.0);

        let subtle = ShadowConfig::subtle();
        let pronounced = ShadowConfig::pronounced();
        assert!(pronounced.opacity > subtle.opacity);
    }

    #[test]
    fn test_quality_adjustment() {
        let adjustment = QualityAdjustment::default();
        assert!(adjustment.bloom_downscale > 0);
        assert!(adjustment.bloom_passes > 0);
        assert!(adjustment.shadow_downscale > 0);
        assert!(adjustment.shadow_blur_passes > 0);
    }

    #[test]
    fn test_quality_level() {
        let high = QualityLevel::High;
        let low = QualityLevel::Low;

        let high_adj = high.adjustment();
        let low_adj = low.adjustment();

        // Higher quality = lower downscale (larger buffers)
        assert!(high_adj.bloom_downscale <= low_adj.bloom_downscale);
        // Higher quality = more blur passes
        assert!(high_adj.bloom_passes >= low_adj.bloom_passes);
    }
}
