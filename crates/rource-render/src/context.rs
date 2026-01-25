// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Rendering context and configuration.
//!
//! This module provides shared rendering configuration that can be used by
//! both CLI and WASM renderers to ensure visual parity and reduce parameter
//! passing in rendering functions.
//!
//! ## Design
//!
//! The [`RenderConfig`] struct holds rendering parameters that don't depend on
//! specific entity types. This allows it to be defined in `rource-render` without
//! creating circular dependencies with `rource-core`.
//!
//! Platform-specific contexts (CLI/WASM) extend this with entity visibility lists
//! that reference `rource-core` types.
//!
//! ## Usage
//!
//! ```
//! use rource_render::context::RenderConfig;
//!
//! let config = RenderConfig::default()
//!     .with_zoom(0.5)
//!     .with_labels(true)
//!     .with_font_size(12.0);
//!
//! assert_eq!(config.camera_zoom, 0.5);
//! assert!(config.show_labels);
//! ```

use rource_math::Bounds;

use crate::FontId;

/// Rendering configuration shared between CLI and WASM.
///
/// This struct holds rendering parameters that affect how entities are drawn
/// but doesn't include entity-specific data (which varies by platform).
///
/// Use the builder methods (`with_*`) to construct configurations fluently.
///
/// Note: The multiple boolean fields represent independent visibility/feature flags
/// that map directly to user configuration options (CLI args, config file settings).
/// Using enums for each would add complexity without benefit.
#[derive(Debug, Clone)]
#[allow(clippy::struct_excessive_bools)]
pub struct RenderConfig {
    /// Visible bounds in world space for culling.
    pub visible_bounds: Bounds,

    /// Current camera zoom level.
    ///
    /// Used for LOD calculations: `screen_radius = world_radius * camera_zoom`
    pub camera_zoom: f32,

    /// Whether to use curved (spline) branches.
    ///
    /// When `true`, branches are drawn as Catmull-Rom splines.
    /// When `false`, branches are drawn as straight lines.
    pub use_curves: bool,

    /// Whether to show entity labels.
    pub show_labels: bool,

    /// Font ID for text rendering.
    ///
    /// `None` if fonts are not loaded or text rendering is disabled.
    pub font_id: Option<FontId>,

    /// Font size in pixels for labels.
    pub font_size: f32,

    /// Opacity falloff rate for branch lines based on depth.
    ///
    /// Higher values make deep branches fade faster.
    /// Typical range: 0.0-1.0
    pub branch_depth_fade: f32,

    /// Maximum opacity for directory-to-parent branch lines.
    ///
    /// Typical range: 0.0-1.0, default 0.35
    pub branch_opacity_max: f32,

    /// Whether to hide the tree structure (branches).
    pub hide_tree: bool,

    /// Whether to hide filenames.
    pub hide_filenames: bool,

    /// Whether to hide usernames.
    pub hide_usernames: bool,

    /// Whether to hide directory names.
    pub hide_dirnames: bool,

    /// Maximum directory depth to show labels for.
    pub dir_name_depth: u32,

    /// Screen width in pixels.
    pub screen_width: f32,

    /// Screen height in pixels.
    pub screen_height: f32,
}

impl Default for RenderConfig {
    fn default() -> Self {
        Self {
            visible_bounds: Bounds::ZERO,
            camera_zoom: 1.0,
            use_curves: true,
            show_labels: true,
            font_id: None,
            font_size: 12.0,
            branch_depth_fade: 0.8,
            branch_opacity_max: 0.35,
            hide_tree: false,
            hide_filenames: false,
            hide_usernames: false,
            hide_dirnames: false,
            dir_name_depth: 2,
            screen_width: 800.0,
            screen_height: 600.0,
        }
    }
}

impl RenderConfig {
    /// Creates a new render configuration with default values.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the visible bounds for culling.
    #[inline]
    #[must_use]
    pub fn with_visible_bounds(mut self, bounds: Bounds) -> Self {
        self.visible_bounds = bounds;
        self
    }

    /// Sets the camera zoom level.
    #[inline]
    #[must_use]
    pub fn with_zoom(mut self, zoom: f32) -> Self {
        self.camera_zoom = zoom;
        self
    }

    /// Sets whether to use curved branches.
    #[inline]
    #[must_use]
    pub fn with_curves(mut self, use_curves: bool) -> Self {
        self.use_curves = use_curves;
        self
    }

    /// Sets whether to show labels.
    #[inline]
    #[must_use]
    pub fn with_labels(mut self, show_labels: bool) -> Self {
        self.show_labels = show_labels;
        self
    }

    /// Sets the font ID for text rendering.
    #[inline]
    #[must_use]
    pub fn with_font(mut self, font_id: FontId) -> Self {
        self.font_id = Some(font_id);
        self
    }

    /// Sets the font size.
    #[inline]
    #[must_use]
    pub fn with_font_size(mut self, size: f32) -> Self {
        self.font_size = size;
        self
    }

    /// Sets the branch depth fade rate.
    #[inline]
    #[must_use]
    pub fn with_branch_depth_fade(mut self, fade: f32) -> Self {
        self.branch_depth_fade = fade;
        self
    }

    /// Sets the maximum branch opacity.
    #[inline]
    #[must_use]
    pub fn with_branch_opacity_max(mut self, opacity: f32) -> Self {
        self.branch_opacity_max = opacity;
        self
    }

    /// Sets whether to hide the tree structure.
    #[inline]
    #[must_use]
    pub fn with_hide_tree(mut self, hide: bool) -> Self {
        self.hide_tree = hide;
        self
    }

    /// Sets whether to hide filenames.
    #[inline]
    #[must_use]
    pub fn with_hide_filenames(mut self, hide: bool) -> Self {
        self.hide_filenames = hide;
        self
    }

    /// Sets whether to hide usernames.
    #[inline]
    #[must_use]
    pub fn with_hide_usernames(mut self, hide: bool) -> Self {
        self.hide_usernames = hide;
        self
    }

    /// Sets whether to hide directory names.
    #[inline]
    #[must_use]
    pub fn with_hide_dirnames(mut self, hide: bool) -> Self {
        self.hide_dirnames = hide;
        self
    }

    /// Sets the maximum directory depth for labels.
    #[inline]
    #[must_use]
    pub fn with_dir_name_depth(mut self, depth: u32) -> Self {
        self.dir_name_depth = depth;
        self
    }

    /// Sets the screen dimensions.
    #[inline]
    #[must_use]
    pub fn with_screen_size(mut self, width: f32, height: f32) -> Self {
        self.screen_width = width;
        self.screen_height = height;
        self
    }

    /// Returns whether file branches should be rendered at the current zoom.
    #[inline]
    #[must_use]
    pub fn should_render_file_branches(&self) -> bool {
        crate::lod::should_render_file_branches(self.camera_zoom, self.hide_tree)
    }

    /// Returns whether directory branches should be rendered at the current zoom.
    #[inline]
    #[must_use]
    pub fn should_render_dir_branches(&self) -> bool {
        crate::lod::should_render_dir_branches(self.camera_zoom, self.hide_tree)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_render_config_default() {
        let config = RenderConfig::default();
        assert!((config.camera_zoom - 1.0).abs() < f32::EPSILON);
        assert!(config.use_curves);
        assert!(config.show_labels);
        assert!(config.font_id.is_none());
        assert!((config.font_size - 12.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_render_config_builder() {
        let config = RenderConfig::new()
            .with_zoom(0.5)
            .with_labels(false)
            .with_font_size(16.0)
            .with_curves(false);

        assert!((config.camera_zoom - 0.5).abs() < f32::EPSILON);
        assert!(!config.show_labels);
        assert!((config.font_size - 16.0).abs() < f32::EPSILON);
        assert!(!config.use_curves);
    }

    #[test]
    fn test_render_config_with_font() {
        let font_id = FontId::new(42);
        let config = RenderConfig::new().with_font(font_id);

        assert_eq!(config.font_id, Some(font_id));
    }

    #[test]
    fn test_render_config_screen_size() {
        let config = RenderConfig::new().with_screen_size(1920.0, 1080.0);

        assert!((config.screen_width - 1920.0).abs() < f32::EPSILON);
        assert!((config.screen_height - 1080.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_render_config_branch_visibility() {
        // High zoom - branches visible
        let config = RenderConfig::new().with_zoom(0.1).with_hide_tree(false);
        assert!(config.should_render_file_branches());
        assert!(config.should_render_dir_branches());

        // Low zoom - file branches hidden
        let config = RenderConfig::new().with_zoom(0.01).with_hide_tree(false);
        assert!(!config.should_render_file_branches());
        assert!(config.should_render_dir_branches());

        // Very low zoom - all branches hidden
        let config = RenderConfig::new().with_zoom(0.005).with_hide_tree(false);
        assert!(!config.should_render_file_branches());
        assert!(!config.should_render_dir_branches());

        // Tree explicitly hidden
        let config = RenderConfig::new().with_zoom(1.0).with_hide_tree(true);
        assert!(!config.should_render_file_branches());
        assert!(!config.should_render_dir_branches());
    }

    #[test]
    fn test_render_config_visibility_flags() {
        let config = RenderConfig::new()
            .with_hide_filenames(true)
            .with_hide_usernames(true)
            .with_hide_dirnames(true)
            .with_dir_name_depth(3);

        assert!(config.hide_filenames);
        assert!(config.hide_usernames);
        assert!(config.hide_dirnames);
        assert_eq!(config.dir_name_depth, 3);
    }

    #[test]
    fn test_render_config_branch_styling() {
        let config = RenderConfig::new()
            .with_branch_depth_fade(0.9)
            .with_branch_opacity_max(0.5);

        assert!((config.branch_depth_fade - 0.9).abs() < f32::EPSILON);
        assert!((config.branch_opacity_max - 0.5).abs() < f32::EPSILON);
    }
}
