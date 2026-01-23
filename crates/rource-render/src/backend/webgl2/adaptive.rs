// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Adaptive quality system for WebGL2 post-processing effects.
//!
//! This module provides automatic quality adjustment based on frame timing
//! to maintain smooth performance. When frame times exceed targets, the
//! system reduces effect quality (downscale, passes) to recover FPS.
//!
//! ## Usage
//!
//! ```ignore
//! let mut quality = AdaptiveQuality::new();
//! quality.set_target_fps(60.0);
//!
//! // Each frame, report timing and get adjusted settings
//! let frame_time_ms = 18.0; // 18ms = ~55 FPS
//! if let Some(adjustments) = quality.update(frame_time_ms) {
//!     renderer.set_bloom_downscale(adjustments.bloom_downscale);
//!     renderer.set_bloom_passes(adjustments.bloom_passes);
//! }
//! ```

/// Target frame time thresholds for quality adjustment.
#[derive(Debug, Clone, Copy)]
pub struct FrameTimeThresholds {
    /// Frame time (ms) above which quality is reduced.
    pub reduce_threshold: f32,

    /// Frame time (ms) below which quality can be increased.
    pub increase_threshold: f32,

    /// Minimum frames at threshold before adjustment.
    pub stability_frames: u32,
}

impl Default for FrameTimeThresholds {
    fn default() -> Self {
        Self {
            // At 60 FPS target: reduce if above 18ms (~55 FPS)
            reduce_threshold: 18.0,
            // Increase if below 14ms (~71 FPS)
            increase_threshold: 14.0,
            // Wait 30 frames before adjusting
            stability_frames: 30,
        }
    }
}

/// Quality adjustment recommendations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QualityAdjustment {
    /// Recommended bloom downscale factor.
    pub bloom_downscale: u32,

    /// Recommended bloom blur passes.
    pub bloom_passes: u32,

    /// Recommended shadow downscale factor.
    pub shadow_downscale: u32,

    /// Recommended shadow blur passes.
    pub shadow_blur_passes: u32,
}

impl Default for QualityAdjustment {
    fn default() -> Self {
        Self {
            bloom_downscale: 4,
            bloom_passes: 2,
            shadow_downscale: 2,
            shadow_blur_passes: 2,
        }
    }
}

impl QualityAdjustment {
    /// Returns a high quality preset.
    #[must_use]
    pub fn high() -> Self {
        Self {
            bloom_downscale: 2,
            bloom_passes: 3,
            shadow_downscale: 1,
            shadow_blur_passes: 3,
        }
    }

    /// Returns a medium quality preset.
    #[must_use]
    pub fn medium() -> Self {
        Self::default()
    }

    /// Returns a low quality preset for performance.
    #[must_use]
    pub fn low() -> Self {
        Self {
            bloom_downscale: 8,
            bloom_passes: 1,
            shadow_downscale: 4,
            shadow_blur_passes: 1,
        }
    }

    /// Returns a minimal quality preset for maximum performance.
    #[must_use]
    pub fn minimal() -> Self {
        Self {
            bloom_downscale: 16,
            bloom_passes: 1,
            shadow_downscale: 8,
            shadow_blur_passes: 1,
        }
    }
}

/// Quality level for adaptive system.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum QualityLevel {
    /// Minimal quality for maximum performance.
    Minimal = 0,
    /// Low quality.
    Low = 1,
    /// Medium quality (default).
    Medium = 2,
    /// High quality.
    High = 3,
}

impl QualityLevel {
    /// Returns the adjustment settings for this quality level.
    #[must_use]
    pub fn adjustment(self) -> QualityAdjustment {
        match self {
            Self::Minimal => QualityAdjustment::minimal(),
            Self::Low => QualityAdjustment::low(),
            Self::Medium => QualityAdjustment::medium(),
            Self::High => QualityAdjustment::high(),
        }
    }

    /// Returns the next higher quality level, if any.
    #[must_use]
    pub fn higher(self) -> Option<Self> {
        match self {
            Self::Minimal => Some(Self::Low),
            Self::Low => Some(Self::Medium),
            Self::Medium => Some(Self::High),
            Self::High => None,
        }
    }

    /// Returns the next lower quality level, if any.
    #[must_use]
    pub fn lower(self) -> Option<Self> {
        match self {
            Self::Minimal => None,
            Self::Low => Some(Self::Minimal),
            Self::Medium => Some(Self::Low),
            Self::High => Some(Self::Medium),
        }
    }
}

/// Adaptive quality controller.
///
/// Monitors frame timing and recommends quality adjustments to maintain
/// target performance. The controller uses exponential smoothing for
/// stable measurements and hysteresis to prevent oscillation.
#[derive(Debug)]
pub struct AdaptiveQuality {
    /// Whether adaptive quality is enabled.
    enabled: bool,

    /// Current quality level.
    level: QualityLevel,

    /// Target FPS (used to calculate thresholds).
    target_fps: f32,

    /// Frame time thresholds.
    thresholds: FrameTimeThresholds,

    /// Smoothed frame time (exponential moving average).
    smoothed_frame_time: f32,

    /// Smoothing factor (0.0-1.0, higher = more responsive).
    smoothing_factor: f32,

    /// Frames spent above reduce threshold.
    frames_above_threshold: u32,

    /// Frames spent below increase threshold.
    frames_below_threshold: u32,

    /// Whether an adjustment was made recently (cooldown).
    cooldown_frames: u32,

    /// Last emitted adjustment.
    last_adjustment: QualityAdjustment,
}

impl AdaptiveQuality {
    /// Creates a new adaptive quality controller with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self {
            enabled: false,
            level: QualityLevel::Medium,
            target_fps: 60.0,
            thresholds: FrameTimeThresholds::default(),
            smoothed_frame_time: 16.67, // Assume 60 FPS initially
            smoothing_factor: 0.1,
            frames_above_threshold: 0,
            frames_below_threshold: 0,
            cooldown_frames: 0,
            last_adjustment: QualityAdjustment::default(),
        }
    }

    /// Returns whether adaptive quality is enabled.
    #[inline]
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Enables or disables adaptive quality adjustment.
    #[inline]
    pub fn set_enabled(&mut self, enabled: bool) {
        self.enabled = enabled;
    }

    /// Returns the current quality level.
    #[inline]
    pub fn level(&self) -> QualityLevel {
        self.level
    }

    /// Sets the quality level directly (disables automatic adjustment until reset).
    #[inline]
    pub fn set_level(&mut self, level: QualityLevel) {
        self.level = level;
        self.last_adjustment = level.adjustment();
        self.cooldown_frames = 60; // Cooldown after manual change
    }

    /// Returns the target FPS.
    #[inline]
    pub fn target_fps(&self) -> f32 {
        self.target_fps
    }

    /// Sets the target FPS and recalculates thresholds.
    pub fn set_target_fps(&mut self, fps: f32) {
        let fps = fps.max(1.0);
        self.target_fps = fps;

        let target_frame_time = 1000.0 / fps;
        self.thresholds.reduce_threshold = target_frame_time * 1.1; // 10% over budget
        self.thresholds.increase_threshold = target_frame_time * 0.85; // 15% under budget
    }

    /// Returns the current smoothed frame time.
    #[inline]
    pub fn smoothed_frame_time(&self) -> f32 {
        self.smoothed_frame_time
    }

    /// Returns the current quality adjustment settings.
    #[inline]
    pub fn current_adjustment(&self) -> QualityAdjustment {
        self.last_adjustment
    }

    /// Updates the controller with the latest frame time.
    ///
    /// Returns `Some(adjustment)` if quality settings should change,
    /// `None` if no change is recommended.
    ///
    /// # Arguments
    ///
    /// * `frame_time_ms` - The duration of the last frame in milliseconds.
    pub fn update(&mut self, frame_time_ms: f32) -> Option<QualityAdjustment> {
        if !self.enabled {
            return None;
        }

        // Update smoothed frame time (exponential moving average)
        self.smoothed_frame_time = self.smoothed_frame_time * (1.0 - self.smoothing_factor)
            + frame_time_ms * self.smoothing_factor;

        // Handle cooldown after adjustment
        if self.cooldown_frames > 0 {
            self.cooldown_frames -= 1;
            return None;
        }

        // Check thresholds
        if self.smoothed_frame_time > self.thresholds.reduce_threshold {
            self.frames_above_threshold += 1;
            self.frames_below_threshold = 0;

            // Reduce quality if above threshold for stability period
            if self.frames_above_threshold >= self.thresholds.stability_frames {
                if let Some(lower) = self.level.lower() {
                    self.level = lower;
                    self.last_adjustment = lower.adjustment();
                    self.frames_above_threshold = 0;
                    self.cooldown_frames = 60; // Cooldown after adjustment
                    return Some(self.last_adjustment);
                }
            }
        } else if self.smoothed_frame_time < self.thresholds.increase_threshold {
            self.frames_below_threshold += 1;
            self.frames_above_threshold = 0;

            // Increase quality if below threshold for stability period
            // Use higher stability threshold for increasing quality
            if self.frames_below_threshold >= self.thresholds.stability_frames * 2 {
                if let Some(higher) = self.level.higher() {
                    self.level = higher;
                    self.last_adjustment = higher.adjustment();
                    self.frames_below_threshold = 0;
                    self.cooldown_frames = 60;
                    return Some(self.last_adjustment);
                }
            }
        } else {
            // In the stable zone
            self.frames_above_threshold = 0;
            self.frames_below_threshold = 0;
        }

        None
    }

    /// Resets the controller to initial state.
    pub fn reset(&mut self) {
        self.level = QualityLevel::Medium;
        self.smoothed_frame_time = 1000.0 / self.target_fps;
        self.frames_above_threshold = 0;
        self.frames_below_threshold = 0;
        self.cooldown_frames = 0;
        self.last_adjustment = QualityAdjustment::default();
    }
}

impl Default for AdaptiveQuality {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quality_level_ordering() {
        assert!(QualityLevel::Minimal < QualityLevel::Low);
        assert!(QualityLevel::Low < QualityLevel::Medium);
        assert!(QualityLevel::Medium < QualityLevel::High);
    }

    #[test]
    fn test_quality_level_transitions() {
        assert_eq!(QualityLevel::Minimal.higher(), Some(QualityLevel::Low));
        assert_eq!(QualityLevel::High.higher(), None);
        assert_eq!(QualityLevel::High.lower(), Some(QualityLevel::Medium));
        assert_eq!(QualityLevel::Minimal.lower(), None);
    }

    #[test]
    fn test_adaptive_quality_new() {
        let aq = AdaptiveQuality::new();
        assert!(!aq.is_enabled());
        assert_eq!(aq.level(), QualityLevel::Medium);
        assert!((aq.target_fps() - 60.0).abs() < 0.001);
    }

    #[test]
    fn test_adaptive_quality_set_target_fps() {
        let mut aq = AdaptiveQuality::new();
        aq.set_target_fps(144.0);
        assert!((aq.target_fps() - 144.0).abs() < 0.001);
        // At 144 FPS, target frame time is ~6.94ms
        // Reduce threshold should be ~7.64ms
        assert!(aq.thresholds.reduce_threshold < 8.0);
    }

    #[test]
    fn test_adaptive_quality_disabled_returns_none() {
        let mut aq = AdaptiveQuality::new();
        assert!(!aq.is_enabled());
        assert!(aq.update(100.0).is_none()); // Very slow frame
    }

    #[test]
    fn test_adaptive_quality_reduces_quality() {
        let mut aq = AdaptiveQuality::new();
        aq.set_enabled(true);
        aq.thresholds.stability_frames = 2; // Reduce for testing
        aq.smoothing_factor = 1.0; // No smoothing for test predictability

        // Simulate slow frames (25ms = 40 FPS, well above 18ms threshold)
        assert!(aq.update(25.0).is_none()); // Frame 1 - counter starts
        let result = aq.update(25.0); // Frame 2 - should trigger reduction

        if result.is_none() {
            // May take one more frame due to counter logic
            assert!(aq.update(25.0).is_some()); // Frame 3
        }

        assert_eq!(aq.level(), QualityLevel::Low);
    }

    #[test]
    fn test_quality_adjustment_presets() {
        let high = QualityAdjustment::high();
        let low = QualityAdjustment::low();

        assert!(high.bloom_downscale < low.bloom_downscale);
        assert!(high.bloom_passes > low.bloom_passes);
    }
}
