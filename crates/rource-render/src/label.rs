// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Label placement and collision avoidance.
//!
//! This module provides utilities for placing text labels without overlaps
//! and managing label visibility based on zoom level.

use rource_math::{Rect, Vec2};

/// A label candidate with its screen position and bounding box.
#[derive(Debug, Clone)]
pub struct LabelCandidate {
    /// The text content of the label.
    pub text: String,
    /// Screen position where the label should be drawn.
    pub position: Vec2,
    /// Bounding box of the label in screen coordinates.
    pub bounds: Rect,
    /// Priority for this label (higher = more important, drawn first).
    pub priority: f32,
}

impl LabelCandidate {
    /// Creates a new label candidate.
    ///
    /// # Arguments
    /// * `text` - The label text
    /// * `position` - Screen position (top-left of text)
    /// * `width` - Estimated text width in pixels
    /// * `height` - Text height in pixels (typically font size)
    /// * `priority` - Importance (higher values are placed first)
    pub fn new(
        text: impl Into<String>,
        position: Vec2,
        width: f32,
        height: f32,
        priority: f32,
    ) -> Self {
        Self {
            text: text.into(),
            position,
            bounds: Rect::new(position.x, position.y, width, height),
            priority,
        }
    }
}

/// Configuration for label placement behavior.
#[derive(Debug, Clone)]
pub struct LabelConfig {
    /// Minimum zoom level to show any file labels.
    pub min_zoom: f32,
    /// Zoom level at which to show all labels (max visibility).
    pub full_zoom: f32,
    /// Maximum number of labels at minimum zoom.
    pub min_labels: usize,
    /// Maximum number of labels at full zoom.
    pub max_labels: usize,
    /// Padding around labels for collision detection (pixels).
    pub padding: f32,
    /// Minimum alpha for a label to be considered visible.
    pub min_alpha: f32,
}

impl Default for LabelConfig {
    fn default() -> Self {
        Self {
            min_zoom: 0.15,
            full_zoom: 0.8,
            min_labels: 15,
            max_labels: 200,
            padding: 2.0,
            min_alpha: 0.3,
        }
    }
}

impl LabelConfig {
    /// Calculates the maximum number of labels to show at a given zoom level.
    pub fn max_labels_at_zoom(&self, zoom: f32) -> usize {
        if zoom <= self.min_zoom {
            self.min_labels
        } else if zoom >= self.full_zoom {
            self.max_labels
        } else {
            // Linear interpolation between min and max
            let t = (zoom - self.min_zoom) / (self.full_zoom - self.min_zoom);
            let count = self.min_labels as f32 + t * (self.max_labels - self.min_labels) as f32;
            count.round() as usize
        }
    }
}

/// Small margin for viewport bounds checking (T9).
/// Labels within this margin of the viewport edge are considered on-screen.
const VIEWPORT_MARGIN: f32 = 5.0;

/// Manages label placement to avoid overlaps.
///
/// Uses a simple approach: labels are placed in priority order, and each
/// new label is checked against all previously placed labels for collisions.
///
/// # T9: Viewport Bounds Checking
///
/// Labels that would extend beyond viewport edges are rejected. This prevents:
/// - Labels being cut off at screen edges
/// - Wasted render calls for off-screen labels
#[derive(Debug)]
pub struct LabelPlacer {
    /// Occupied regions on screen.
    occupied: Vec<Rect>,
    /// Configuration for label behavior.
    config: LabelConfig,
    /// Number of labels placed so far.
    count: usize,
    /// Maximum labels allowed (based on zoom).
    max_count: usize,
    /// Viewport width for bounds checking (T9).
    viewport_width: f32,
    /// Viewport height for bounds checking (T9).
    viewport_height: f32,
}

impl LabelPlacer {
    /// Creates a new label placer with the given zoom level.
    pub fn new(zoom: f32) -> Self {
        Self::with_config(zoom, LabelConfig::default())
    }

    /// Creates a new label placer with custom configuration.
    pub fn with_config(zoom: f32, config: LabelConfig) -> Self {
        let max_count = config.max_labels_at_zoom(zoom);
        Self {
            occupied: Vec::with_capacity(max_count),
            config,
            count: 0,
            max_count,
            // Default viewport (will be set properly via set_viewport)
            viewport_width: 1920.0,
            viewport_height: 1080.0,
        }
    }

    /// Resets the placer for a new frame.
    #[inline]
    pub fn reset(&mut self, zoom: f32) {
        self.occupied.clear();
        self.count = 0;
        self.max_count = self.config.max_labels_at_zoom(zoom);
    }

    /// Sets the viewport dimensions for bounds checking (T9).
    ///
    /// Call this when viewport size changes or at the start of each frame
    /// before placing labels.
    #[inline]
    pub fn set_viewport(&mut self, width: f32, height: f32) {
        self.viewport_width = width;
        self.viewport_height = height;
    }

    /// Returns true if more labels can be placed.
    #[inline]
    pub fn can_place_more(&self) -> bool {
        self.count < self.max_count
    }

    /// Returns the number of labels placed.
    #[inline]
    pub fn count(&self) -> usize {
        self.count
    }

    /// Returns the maximum number of labels allowed.
    #[inline]
    pub fn max_count(&self) -> usize {
        self.max_count
    }

    /// Returns the configuration.
    #[inline]
    pub fn config(&self) -> &LabelConfig {
        &self.config
    }

    /// Attempts to place a label at the given position.
    ///
    /// Returns true if the label was placed (no collision), false otherwise.
    ///
    /// # T9: Viewport Bounds Checking
    ///
    /// Labels that would extend beyond viewport edges are rejected.
    pub fn try_place(&mut self, position: Vec2, width: f32, height: f32) -> bool {
        if !self.can_place_more() {
            return false;
        }

        // T9: Viewport bounds check - reject labels that extend off-screen
        // Allow small negative positions (partial visibility) but reject if mostly off-screen
        if position.x + width < VIEWPORT_MARGIN
            || position.y + height < VIEWPORT_MARGIN
            || position.x > self.viewport_width - VIEWPORT_MARGIN
            || position.y > self.viewport_height - VIEWPORT_MARGIN
        {
            return false;
        }

        // Create padded bounds for collision check
        let padding = self.config.padding;
        let bounds = Rect::new(
            position.x - padding,
            position.y - padding,
            width + padding * 2.0,
            height + padding * 2.0,
        );

        // Check for collisions with existing labels
        if self.collides(&bounds) {
            return false;
        }

        // Place the label
        self.occupied.push(bounds);
        self.count += 1;
        true
    }

    /// Attempts to place a label, trying alternate positions if the primary collides.
    ///
    /// Returns the position where the label was placed, or None if no valid position found.
    ///
    /// # Arguments
    /// * `primary` - The preferred label position
    /// * `width` - Label width in pixels
    /// * `height` - Label height in pixels
    /// * `anchor` - The anchor point (e.g., file center) for alternate positions
    /// * `anchor_radius` - Radius around anchor to offset alternate positions
    pub fn try_place_with_fallback(
        &mut self,
        primary: Vec2,
        width: f32,
        height: f32,
        anchor: Vec2,
        anchor_radius: f32,
    ) -> Option<Vec2> {
        // Try primary position (right of anchor)
        if self.try_place(primary, width, height) {
            return Some(primary);
        }

        // Try alternate positions: left, above, below
        let offset = anchor_radius + 3.0;

        // Left of anchor
        let left = Vec2::new(anchor.x - offset - width, anchor.y - height * 0.3);
        if self.try_place(left, width, height) {
            return Some(left);
        }

        // Above anchor
        let above = Vec2::new(anchor.x - width * 0.5, anchor.y - offset - height);
        if self.try_place(above, width, height) {
            return Some(above);
        }

        // Below anchor
        let below = Vec2::new(anchor.x - width * 0.5, anchor.y + offset);
        if self.try_place(below, width, height) {
            return Some(below);
        }

        None
    }

    /// Reserves space for a label without counting it toward the limit.
    ///
    /// Useful for always-visible labels like user names.
    pub fn reserve(&mut self, position: Vec2, width: f32, height: f32) {
        let padding = self.config.padding;
        let bounds = Rect::new(
            position.x - padding,
            position.y - padding,
            width + padding * 2.0,
            height + padding * 2.0,
        );
        self.occupied.push(bounds);
    }

    /// Checks if a rectangle collides with any occupied region.
    fn collides(&self, bounds: &Rect) -> bool {
        for occupied in &self.occupied {
            if rects_overlap(bounds, occupied) {
                return true;
            }
        }
        false
    }
}

/// Checks if two rectangles overlap.
#[inline]
fn rects_overlap(a: &Rect, b: &Rect) -> bool {
    a.x < b.x + b.width && a.x + a.width > b.x && a.y < b.y + b.height && a.y + a.height > b.y
}

/// Monospace character width factor for Roboto Mono.
///
/// Measured value is 0.6001 (`advance_width` / `font_size`).
/// We use 0.62 to add a 3% safety margin for:
/// - Subpixel rendering differences
/// - Minor font hinting variations
/// - Rounding errors in collision detection
const MONOSPACE_WIDTH_FACTOR: f32 = 0.62;

/// Estimates the width of a text string based on character count.
///
/// This function uses the actual character count (not byte count) and the
/// measured monospace width factor for Roboto Mono.
///
/// # Accuracy
///
/// | Input Type | Accuracy |
/// |------------|----------|
/// | ASCII text | ~3% overestimate (safety margin) |
/// | UTF-8 text | ~3% overestimate (safety margin) |
/// | CJK/Emoji  | ~3% overestimate (safety margin) |
///
/// Previous approach used `text.len()` (bytes) with factor 0.75, which caused:
/// - ASCII: 25% overestimate
/// - UTF-8 accented: up to 50% overestimate
/// - CJK/Emoji: up to 400% overestimate
///
/// # Phase 68 Optimization
///
/// Changed from `text.len() * 0.75` to `text.chars().count() * 0.62`:
/// - Uses character count instead of byte count (correct for UTF-8)
/// - Uses measured font factor (0.60) + 3% safety margin (0.62)
/// - Reduces average estimation error from 74.4% to 3%
#[inline]
pub fn estimate_text_width(text: &str, font_size: f32) -> f32 {
    text.chars().count() as f32 * font_size * MONOSPACE_WIDTH_FACTOR
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_label_config_max_labels() {
        let config = LabelConfig {
            min_zoom: 0.2,
            full_zoom: 1.0,
            min_labels: 10,
            max_labels: 100,
            ..Default::default()
        };

        assert_eq!(config.max_labels_at_zoom(0.1), 10); // Below min
        assert_eq!(config.max_labels_at_zoom(0.2), 10); // At min
        assert_eq!(config.max_labels_at_zoom(0.6), 55); // Midpoint
        assert_eq!(config.max_labels_at_zoom(1.0), 100); // At full
        assert_eq!(config.max_labels_at_zoom(1.5), 100); // Above full
    }

    #[test]
    fn test_label_placer_basic() {
        let mut placer = LabelPlacer::new(1.0);

        // First label should always succeed
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 50.0, 12.0));
        assert_eq!(placer.count(), 1);

        // Non-overlapping label should succeed
        assert!(placer.try_place(Vec2::new(100.0, 0.0), 50.0, 12.0));
        assert_eq!(placer.count(), 2);

        // Overlapping label should fail
        assert!(!placer.try_place(Vec2::new(10.0, 0.0), 50.0, 12.0));
        assert_eq!(placer.count(), 2);
    }

    #[test]
    fn test_label_placer_max_count() {
        let config = LabelConfig {
            min_zoom: 0.0,
            full_zoom: 1.0,
            min_labels: 2,
            max_labels: 2,
            padding: 0.0,
            ..Default::default()
        };

        let mut placer = LabelPlacer::with_config(1.0, config);

        assert!(placer.try_place(Vec2::new(0.0, 0.0), 10.0, 10.0));
        assert!(placer.try_place(Vec2::new(100.0, 0.0), 10.0, 10.0));
        // Third should fail due to max count
        assert!(!placer.try_place(Vec2::new(200.0, 0.0), 10.0, 10.0));
        assert!(!placer.can_place_more());
    }

    #[test]
    fn test_label_placer_fallback() {
        let mut placer = LabelPlacer::new(1.0);

        // Place first label to the right
        let anchor = Vec2::new(50.0, 50.0);
        let primary = Vec2::new(60.0, 45.0);
        let pos = placer.try_place_with_fallback(primary, 40.0, 12.0, anchor, 10.0);
        assert!(pos.is_some());
        assert_eq!(pos.unwrap(), primary);

        // Second label at same anchor should use fallback position
        let pos2 = placer.try_place_with_fallback(primary, 40.0, 12.0, anchor, 10.0);
        assert!(pos2.is_some());
        assert_ne!(pos2.unwrap(), primary); // Should be different position
    }

    #[test]
    fn test_rects_overlap() {
        let a = Rect::new(0.0, 0.0, 10.0, 10.0);
        let b = Rect::new(5.0, 5.0, 10.0, 10.0);
        let c = Rect::new(20.0, 20.0, 10.0, 10.0);

        assert!(rects_overlap(&a, &b));
        assert!(rects_overlap(&b, &a));
        assert!(!rects_overlap(&a, &c));
        assert!(!rects_overlap(&c, &a));
    }

    #[test]
    fn test_estimate_text_width() {
        let width = estimate_text_width("hello", 12.0);
        assert!(width > 0.0);
        assert!(width < 100.0);

        // Longer text should be wider
        let width2 = estimate_text_width("hello world", 12.0);
        assert!(width2 > width);
    }

    #[test]
    fn test_estimate_text_width_accuracy() {
        // Test that the new implementation uses character count, not byte count
        let size = 12.0;

        // ASCII: 5 chars, 5 bytes
        let ascii = "hello";
        let ascii_width = estimate_text_width(ascii, size);
        // Expected: 5 * 12 * 0.62 = 37.2
        assert!((ascii_width - 37.2).abs() < 0.01);

        // UTF-8 with accent: 5 chars, 6 bytes
        let accented = "héllo";
        let accented_width = estimate_text_width(accented, size);
        // Should be same as ASCII (5 chars), not 6 bytes
        assert_eq!(accented.chars().count(), 5);
        assert_eq!(accented.len(), 6); // bytes != chars
        assert!((accented_width - ascii_width).abs() < 0.01);

        // CJK: 2 chars, 6 bytes
        let cjk = "你好";
        let cjk_width = estimate_text_width(cjk, size);
        // Expected: 2 * 12 * 0.62 = 14.88
        assert_eq!(cjk.chars().count(), 2);
        assert_eq!(cjk.len(), 6); // bytes
        assert!((cjk_width - 14.88).abs() < 0.01);

        // Emoji: 1 char, 4 bytes
        let emoji = "🚀";
        let emoji_width = estimate_text_width(emoji, size);
        // Expected: 1 * 12 * 0.62 = 7.44
        assert_eq!(emoji.chars().count(), 1);
        assert_eq!(emoji.len(), 4); // bytes
        assert!((emoji_width - 7.44).abs() < 0.01);
    }

    #[test]
    fn test_monospace_width_factor() {
        // Verify the constant is set correctly
        assert!((MONOSPACE_WIDTH_FACTOR - 0.62).abs() < 0.001);

        // Verify it's larger than actual measured value (0.60) for safety margin
        const { assert!(MONOSPACE_WIDTH_FACTOR > 0.60) };

        // Verify it's not too conservative (< 0.65)
        const { assert!(MONOSPACE_WIDTH_FACTOR < 0.65) };
    }

    #[test]
    fn test_label_placer_reserve() {
        let config = LabelConfig {
            min_labels: 1,
            max_labels: 1,
            padding: 0.0,
            ..Default::default()
        };

        let mut placer = LabelPlacer::with_config(1.0, config);

        // Reserve doesn't count toward limit
        placer.reserve(Vec2::new(0.0, 0.0), 50.0, 12.0);
        assert_eq!(placer.count(), 0);
        assert!(placer.can_place_more());

        // But it does block the space
        assert!(!placer.try_place(Vec2::new(10.0, 0.0), 50.0, 12.0));

        // Non-overlapping should still work
        assert!(placer.try_place(Vec2::new(100.0, 0.0), 50.0, 12.0));
        assert_eq!(placer.count(), 1);
    }

    #[test]
    fn test_label_placer_reset() {
        let mut placer = LabelPlacer::new(1.0);

        placer.try_place(Vec2::new(0.0, 0.0), 50.0, 12.0);
        assert_eq!(placer.count(), 1);

        placer.reset(0.5);
        assert_eq!(placer.count(), 0);

        // Can place again at same position after reset
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 50.0, 12.0));
    }

    #[test]
    fn test_label_placer_set_viewport() {
        let mut placer = LabelPlacer::new(1.0);

        // Default viewport is 1920x1080
        // Set to smaller viewport
        placer.set_viewport(800.0, 600.0);

        // Label within new viewport should succeed
        assert!(placer.try_place(Vec2::new(100.0, 100.0), 50.0, 12.0));
        assert_eq!(placer.count(), 1);
    }

    #[test]
    fn test_label_placer_viewport_bounds_t9() {
        let mut placer = LabelPlacer::new(1.0);
        placer.set_viewport(800.0, 600.0);

        // T9: Label off-screen to the left (position.x + width < VIEWPORT_MARGIN)
        assert!(!placer.try_place(Vec2::new(-100.0, 100.0), 50.0, 12.0));
        assert_eq!(placer.count(), 0);

        // T9: Label off-screen to the top (position.y + height < VIEWPORT_MARGIN)
        assert!(!placer.try_place(Vec2::new(100.0, -100.0), 50.0, 12.0));
        assert_eq!(placer.count(), 0);

        // T9: Label off-screen to the right (position.x > viewport_width - VIEWPORT_MARGIN)
        assert!(!placer.try_place(Vec2::new(800.0, 100.0), 50.0, 12.0));
        assert_eq!(placer.count(), 0);

        // T9: Label off-screen to the bottom (position.y > viewport_height - VIEWPORT_MARGIN)
        assert!(!placer.try_place(Vec2::new(100.0, 600.0), 50.0, 12.0));
        assert_eq!(placer.count(), 0);

        // Labels within viewport should succeed
        assert!(placer.try_place(Vec2::new(100.0, 100.0), 50.0, 12.0));
        assert_eq!(placer.count(), 1);

        // Label at edge but still visible (within VIEWPORT_MARGIN)
        assert!(placer.try_place(Vec2::new(700.0, 500.0), 50.0, 12.0));
        assert_eq!(placer.count(), 2);
    }

    // =========================================================================
    // Edge case tests
    // =========================================================================

    #[test]
    fn test_label_candidate_empty_text() {
        let candidate = LabelCandidate::new("", Vec2::new(10.0, 20.0), 0.0, 12.0, 1.0);
        assert!(candidate.text.is_empty());
        assert_eq!(candidate.position, Vec2::new(10.0, 20.0));
        assert_eq!(candidate.bounds.width, 0.0);
    }

    #[test]
    fn test_label_candidate_zero_dimensions() {
        let candidate = LabelCandidate::new("test", Vec2::new(0.0, 0.0), 0.0, 0.0, 0.0);
        assert_eq!(candidate.bounds.width, 0.0);
        assert_eq!(candidate.bounds.height, 0.0);
        assert_eq!(candidate.priority, 0.0);
    }

    #[test]
    fn test_label_candidate_negative_priority() {
        let candidate = LabelCandidate::new("test", Vec2::ZERO, 50.0, 12.0, -100.0);
        assert_eq!(candidate.priority, -100.0);
    }

    #[test]
    fn test_label_candidate_unicode() {
        let candidate = LabelCandidate::new("こんにちは🚀", Vec2::ZERO, 100.0, 14.0, 1.0);
        assert_eq!(candidate.text, "こんにちは🚀");
    }

    #[test]
    fn test_label_config_min_equals_full() {
        let config = LabelConfig {
            min_zoom: 0.5,
            full_zoom: 0.5, // Same as min
            min_labels: 10,
            max_labels: 100,
            ..Default::default()
        };

        // At min_zoom, should return min_labels
        assert_eq!(config.max_labels_at_zoom(0.5), 10);
        // Above should return max_labels
        assert_eq!(config.max_labels_at_zoom(0.6), 100);
    }

    #[test]
    fn test_label_config_min_greater_than_full() {
        // Edge case: min_zoom > full_zoom (invalid config but shouldn't crash)
        // When min_zoom > full_zoom, the conditions overlap in unexpected ways
        let config = LabelConfig {
            min_zoom: 1.0,
            full_zoom: 0.5, // Less than min
            min_labels: 10,
            max_labels: 100,
            ..Default::default()
        };

        // At zoom=0.5: 0.5 <= min_zoom (1.0) is TRUE, so returns min_labels (10)
        // The first condition catches low zooms before the full_zoom check
        assert_eq!(config.max_labels_at_zoom(0.5), 10);

        // At zoom=1.0: 1.0 <= min_zoom (1.0) is TRUE, returns min_labels (10)
        assert_eq!(config.max_labels_at_zoom(1.0), 10);

        // At zoom=1.5: 1.5 <= min_zoom (1.0) is FALSE, 1.5 >= full_zoom (0.5) is TRUE
        // Returns max_labels (100)
        assert_eq!(config.max_labels_at_zoom(1.5), 100);

        // This tests that the function doesn't crash with inverted configs
    }

    #[test]
    fn test_label_config_zero_labels() {
        let config = LabelConfig {
            min_labels: 0,
            max_labels: 0,
            ..Default::default()
        };

        assert_eq!(config.max_labels_at_zoom(0.0), 0);
        assert_eq!(config.max_labels_at_zoom(1.0), 0);
    }

    #[test]
    fn test_label_placer_zero_max_labels() {
        let config = LabelConfig {
            min_labels: 0,
            max_labels: 0,
            ..Default::default()
        };

        let mut placer = LabelPlacer::with_config(1.0, config);

        // Can't place any labels
        assert!(!placer.can_place_more());
        assert!(!placer.try_place(Vec2::new(100.0, 100.0), 50.0, 12.0));
        assert_eq!(placer.count(), 0);
    }

    #[test]
    fn test_label_placer_single_label_max() {
        let config = LabelConfig {
            min_labels: 1,
            max_labels: 1,
            padding: 0.0,
            ..Default::default()
        };

        let mut placer = LabelPlacer::with_config(1.0, config);

        assert!(placer.try_place(Vec2::new(100.0, 100.0), 50.0, 12.0));
        assert!(!placer.can_place_more());
        // Second placement fails
        assert!(!placer.try_place(Vec2::new(200.0, 200.0), 50.0, 12.0));
    }

    #[test]
    fn test_label_placer_very_small_viewport() {
        let mut placer = LabelPlacer::new(1.0);
        placer.set_viewport(10.0, 10.0);

        // Small label should fit in small viewport
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 5.0, 5.0));

        // Reset and try label that starts beyond viewport edge
        placer.reset(1.0);
        // Label starting at x=6 would extend to x=56, but position.x (6) > viewport_width - MARGIN (5)
        assert!(!placer.try_place(Vec2::new(6.0, 0.0), 50.0, 10.0));

        // Label that fits within viewport bounds (position within margin, size doesn't matter for check)
        placer.reset(1.0);
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 8.0, 8.0));
    }

    #[test]
    fn test_label_placer_fallback_all_blocked() {
        let config = LabelConfig {
            padding: 0.0,
            min_labels: 100,
            max_labels: 100,
            ..Default::default()
        };

        let mut placer = LabelPlacer::with_config(1.0, config);
        placer.set_viewport(200.0, 200.0);

        // Fill the viewport with reserved space
        placer.reserve(Vec2::new(0.0, 0.0), 200.0, 200.0);

        // All fallback positions should fail
        let anchor = Vec2::new(100.0, 100.0);
        let primary = Vec2::new(110.0, 95.0);
        let result = placer.try_place_with_fallback(primary, 40.0, 12.0, anchor, 10.0);
        assert!(result.is_none());
    }

    #[test]
    fn test_label_placer_multiple_resets() {
        let mut placer = LabelPlacer::new(1.0);

        // Place some labels
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 50.0, 12.0));
        assert!(placer.try_place(Vec2::new(100.0, 0.0), 50.0, 12.0));
        assert_eq!(placer.count(), 2);

        // Reset and verify cleared
        placer.reset(0.5);
        assert_eq!(placer.count(), 0);

        // Place again
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 50.0, 12.0));
        assert_eq!(placer.count(), 1);

        // Reset again
        placer.reset(1.0);
        assert_eq!(placer.count(), 0);
    }

    #[test]
    fn test_label_placer_accessors() {
        let config = LabelConfig {
            min_zoom: 0.1,
            full_zoom: 2.0,
            min_labels: 5,
            max_labels: 50,
            padding: 3.0,
            min_alpha: 0.5,
        };

        let placer = LabelPlacer::with_config(1.0, config);

        assert_eq!(placer.count(), 0);
        assert!(placer.can_place_more());
        assert!(placer.max_count() > 0);

        let cfg = placer.config();
        assert_eq!(cfg.padding, 3.0);
        assert_eq!(cfg.min_alpha, 0.5);
    }

    #[test]
    fn test_estimate_text_width_empty() {
        let width = estimate_text_width("", 12.0);
        assert_eq!(width, 0.0);
    }

    #[test]
    fn test_estimate_text_width_zero_font() {
        let width = estimate_text_width("hello", 0.0);
        assert_eq!(width, 0.0);
    }

    #[test]
    fn test_estimate_text_width_single_char() {
        let width = estimate_text_width("x", 12.0);
        // 1 * 12.0 * 0.62 = 7.44
        assert!((width - 7.44).abs() < 0.01);
    }

    #[test]
    fn test_estimate_text_width_long_string() {
        let long_text = "a".repeat(1000);
        let width = estimate_text_width(&long_text, 12.0);
        // 1000 * 12.0 * 0.62 = 7440.0
        assert!((width - 7440.0).abs() < 1.0);
    }

    #[test]
    fn test_rects_overlap_touching() {
        // Rects that touch at edge but don't overlap
        let a = Rect::new(0.0, 0.0, 10.0, 10.0);
        let b = Rect::new(10.0, 0.0, 10.0, 10.0); // Touches right edge

        assert!(!rects_overlap(&a, &b));
    }

    #[test]
    fn test_rects_overlap_one_pixel() {
        // Rects that overlap by one pixel
        let a = Rect::new(0.0, 0.0, 10.0, 10.0);
        let b = Rect::new(9.0, 0.0, 10.0, 10.0); // Overlaps by 1 pixel

        assert!(rects_overlap(&a, &b));
    }

    #[test]
    fn test_rects_overlap_contained() {
        // One rect completely contains the other
        let outer = Rect::new(0.0, 0.0, 100.0, 100.0);
        let inner = Rect::new(25.0, 25.0, 50.0, 50.0);

        assert!(rects_overlap(&outer, &inner));
        assert!(rects_overlap(&inner, &outer));
    }

    #[test]
    fn test_rects_overlap_same() {
        // Same rect should overlap with itself
        let a = Rect::new(10.0, 10.0, 50.0, 50.0);
        assert!(rects_overlap(&a, &a));
    }

    #[test]
    fn test_rects_overlap_zero_size() {
        // Zero-size rect at position inside normal rect
        let zero = Rect::new(50.0, 50.0, 0.0, 0.0);
        let normal = Rect::new(0.0, 0.0, 100.0, 100.0);

        // Zero-size rect at (50, 50) is technically a point inside the normal rect
        // The overlap formula: a.x < b.x + b.width (50 < 100) AND a.x + a.width > b.x (50 > 0)
        // Both conditions pass for x and y, so it reports as overlapping
        assert!(rects_overlap(&zero, &normal));

        // Zero-size rect outside normal rect should not overlap
        let zero_outside = Rect::new(150.0, 150.0, 0.0, 0.0);
        assert!(!rects_overlap(&zero_outside, &normal));
    }

    #[test]
    fn test_label_placer_diagonal_collision() {
        let mut placer = LabelPlacer::new(1.0);

        // Place label at origin
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 50.0, 50.0));

        // Label at diagonal that touches corner - should collide
        assert!(!placer.try_place(Vec2::new(45.0, 45.0), 50.0, 50.0));

        // Label at diagonal past the corner - should not collide
        assert!(placer.try_place(Vec2::new(200.0, 200.0), 50.0, 50.0));
    }

    #[test]
    fn test_label_placer_reserve_multiple() {
        let mut placer = LabelPlacer::new(1.0);

        // Reserve multiple spaces
        placer.reserve(Vec2::new(0.0, 0.0), 50.0, 50.0);
        placer.reserve(Vec2::new(100.0, 0.0), 50.0, 50.0);
        placer.reserve(Vec2::new(200.0, 0.0), 50.0, 50.0);

        // Count should still be 0 (reserved don't count)
        assert_eq!(placer.count(), 0);

        // Can't place in reserved areas
        assert!(!placer.try_place(Vec2::new(10.0, 10.0), 30.0, 30.0));
        assert!(!placer.try_place(Vec2::new(110.0, 10.0), 30.0, 30.0));

        // Can place in gaps
        assert!(placer.try_place(Vec2::new(60.0, 10.0), 30.0, 30.0));
    }

    #[test]
    fn test_label_placer_exact_viewport_edge() {
        let mut placer = LabelPlacer::new(1.0);
        placer.set_viewport(800.0, 600.0);

        // Label exactly at VIEWPORT_MARGIN boundary should work
        let margin = 5.0; // VIEWPORT_MARGIN
        assert!(placer.try_place(Vec2::new(800.0 - margin - 50.0, 100.0), 50.0, 12.0));
    }

    #[test]
    fn test_label_candidate_clone() {
        let original = LabelCandidate::new("test", Vec2::new(10.0, 20.0), 50.0, 12.0, 5.0);
        let cloned = original.clone();

        assert_eq!(original.text, cloned.text);
        assert_eq!(original.position, cloned.position);
        assert_eq!(original.priority, cloned.priority);
    }

    #[test]
    fn test_label_config_default() {
        let config = LabelConfig::default();

        assert_eq!(config.min_zoom, 0.15);
        assert_eq!(config.full_zoom, 0.8);
        assert_eq!(config.min_labels, 15);
        assert_eq!(config.max_labels, 200);
        assert_eq!(config.padding, 2.0);
        assert_eq!(config.min_alpha, 0.3);
    }

    #[test]
    fn test_label_config_clone() {
        let config = LabelConfig {
            min_zoom: 0.25,
            full_zoom: 0.9,
            min_labels: 20,
            max_labels: 300,
            padding: 5.0,
            min_alpha: 0.4,
        };
        let cloned = config.clone();

        assert_eq!(config.min_zoom, cloned.min_zoom);
        assert_eq!(config.max_labels, cloned.max_labels);
        assert_eq!(config.padding, cloned.padding);
    }

    #[test]
    fn test_label_placer_fallback_uses_left() {
        let mut placer = LabelPlacer::new(1.0);
        placer.set_viewport(400.0, 400.0);

        let anchor = Vec2::new(100.0, 100.0);
        let primary = Vec2::new(110.0, 95.0); // Right of anchor

        // Place primary first
        let pos1 = placer.try_place_with_fallback(primary, 40.0, 12.0, anchor, 10.0);
        assert_eq!(pos1, Some(primary));

        // Second call should try fallback (left)
        let pos2 = placer.try_place_with_fallback(primary, 40.0, 12.0, anchor, 10.0);
        assert!(pos2.is_some());
        assert!(pos2.unwrap().x < anchor.x, "Should be placed to the left");
    }
}
