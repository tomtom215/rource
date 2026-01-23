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

/// Manages label placement to avoid overlaps.
///
/// Uses a simple approach: labels are placed in priority order, and each
/// new label is checked against all previously placed labels for collisions.
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
        }
    }

    /// Resets the placer for a new frame.
    pub fn reset(&mut self, zoom: f32) {
        self.occupied.clear();
        self.count = 0;
        self.max_count = self.config.max_labels_at_zoom(zoom);
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
    pub fn try_place(&mut self, position: Vec2, width: f32, height: f32) -> bool {
        if !self.can_place_more() {
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

/// Estimates the width of a text string based on character count.
///
/// This is a simple heuristic when font metrics aren't available.
/// Assumes a monospace-like font where each character is roughly 0.6 * `font_size` wide.
#[inline]
pub fn estimate_text_width(text: &str, font_size: f32) -> f32 {
    text.len() as f32 * font_size * 0.55
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
}
