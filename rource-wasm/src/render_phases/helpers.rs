// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Pure computation functions for rendering phases.
//!
//! These functions encapsulate all rendering logic as pure computations.
//! They take input data and return computed values without side effects,
//! making them 100% testable without requiring a renderer.
//!
//! Note: Some functions in this module are only used for testing purposes
//! or reserved for future rendering phases. They are kept public for test
//! accessibility and to maintain the pure function extraction pattern.
#![allow(dead_code)]

use rource_core::config::WatermarkPosition;
use rource_math::Color;

// Import shared LOD constants from rource-render for visual parity with CLI
use rource_render::lod::{
    MIN_DIR_LABEL_RADIUS as LOD_MIN_DIR_LABEL_RADIUS, MIN_DIR_RADIUS as LOD_MIN_DIR_RADIUS,
    MIN_FILE_LABEL_RADIUS as LOD_MIN_FILE_LABEL_RADIUS, MIN_FILE_RADIUS as LOD_MIN_FILE_RADIUS,
    MIN_USER_LABEL_RADIUS as LOD_MIN_USER_LABEL_RADIUS, MIN_USER_RADIUS as LOD_MIN_USER_RADIUS,
    MIN_ZOOM_FOR_DIR_BRANCHES as LOD_MIN_ZOOM_FOR_DIR_BRANCHES,
    MIN_ZOOM_FOR_FILE_BRANCHES as LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
};

/// Precomputed reciprocal for depth factor calculation (1.0 / 6.0).
const INV_DEPTH_MAX: f32 = 1.0 / 6.0;

/// Computes the depth factor used for depth-based styling.
///
/// The depth factor is normalized to [0.0, 1.0] where 0 is root and 1.0 is
/// a directory at depth 6 or greater.
///
/// # Arguments
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
/// Normalized depth factor in range [0.0, 1.0].
#[inline]
#[must_use]
pub fn compute_depth_factor(depth: u32) -> f32 {
    (depth as f32 * INV_DEPTH_MAX).min(1.0)
}

/// Computes directory color based on depth.
///
/// Deeper directories are rendered with lower brightness to create
/// visual hierarchy and reduce clutter.
///
/// # Arguments
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
/// Color for the directory node.
#[inline]
#[must_use]
pub fn compute_directory_color(depth: u32) -> Color {
    let depth_factor = compute_depth_factor(depth);
    let base_brightness = 0.25 + 0.1 * (1.0 - depth_factor);
    Color::new(
        base_brightness * 0.9,
        base_brightness,
        base_brightness * 1.1 + 0.05,
        0.55,
    )
}

/// Computes branch line width based on directory depth.
///
/// Deeper directories have thinner branches to reduce visual noise.
///
/// # Arguments
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
/// Branch width in pixels.
#[inline]
#[must_use]
pub fn compute_branch_width(depth: u32) -> f32 {
    let depth_factor = compute_depth_factor(depth);
    (1.5 - depth_factor * 0.5).max(0.8)
}

/// Computes branch opacity with depth-based fade.
///
/// Deeper branches fade to reduce visual clutter while maintaining
/// structure visibility.
///
/// # Arguments
/// * `depth` - Directory depth (0 = root)
/// * `max_opacity` - Maximum opacity for branches (0.0-1.0)
/// * `fade_rate` - How quickly opacity fades with depth (0.0-1.0)
///
/// # Returns
/// Branch opacity in range \[0.05, `max_opacity`\].
#[inline]
#[must_use]
pub fn compute_branch_opacity(depth: u32, max_opacity: f32, fade_rate: f32) -> f32 {
    let depth_factor = compute_depth_factor(depth);
    max_opacity * (1.0 - depth_factor * fade_rate).max(0.05)
}

/// Computes branch color from directory color with opacity adjustment.
///
/// # Arguments
/// * `dir_color` - Base directory color
/// * `opacity` - Computed branch opacity
///
/// # Returns
/// Branch color with slight brightness boost and specified opacity.
#[inline]
#[must_use]
pub fn compute_branch_color(dir_color: Color, opacity: f32) -> Color {
    Color::new(
        dir_color.r * 1.1,
        dir_color.g * 1.1,
        dir_color.b * 1.2,
        opacity,
    )
}

/// Determines if a directory should be rendered based on LOD.
///
/// Root directory (depth 0) is always rendered as it's the anchor point.
/// Other directories are culled when their screen radius is below threshold.
///
/// # Arguments
/// * `screen_radius` - Radius in screen pixels
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
/// `true` if the directory should be rendered.
#[inline]
#[must_use]
pub fn should_render_directory(screen_radius: f32, depth: u32) -> bool {
    depth == 0 || screen_radius >= LOD_MIN_DIR_RADIUS
}

/// Determines if a file should be rendered based on LOD.
///
/// # Arguments
/// * `screen_radius` - Radius in screen pixels
/// * `alpha` - File alpha (0.0-1.0)
///
/// # Returns
/// `true` if the file should be rendered.
#[inline]
#[must_use]
pub fn should_render_file(screen_radius: f32, alpha: f32) -> bool {
    alpha >= 0.01 && screen_radius >= LOD_MIN_FILE_RADIUS
}

/// Determines if a user should be rendered based on LOD.
///
/// # Arguments
/// * `screen_radius` - Radius in screen pixels
/// * `alpha` - User alpha (0.0-1.0)
///
/// # Returns
/// `true` if the user should be rendered.
#[inline]
#[must_use]
pub fn should_render_user(screen_radius: f32, alpha: f32) -> bool {
    alpha >= 0.01 && screen_radius >= LOD_MIN_USER_RADIUS
}

/// Determines if a directory label should be rendered based on LOD.
///
/// # Arguments
/// * `screen_radius` - Radius in screen pixels
/// * `depth` - Directory depth
///
/// # Returns
/// `true` if the label should be rendered.
#[inline]
#[must_use]
pub fn should_render_directory_label(screen_radius: f32, depth: u32) -> bool {
    depth <= 2 && screen_radius >= LOD_MIN_DIR_LABEL_RADIUS
}

/// Determines if a file label should be rendered based on LOD.
///
/// # Arguments
/// * `screen_radius` - Radius in screen pixels
/// * `alpha` - File alpha
/// * `camera_zoom` - Current camera zoom level
///
/// # Returns
/// `true` if the label should be rendered.
#[inline]
#[must_use]
pub fn should_render_file_label(screen_radius: f32, alpha: f32, camera_zoom: f32) -> bool {
    alpha >= 0.3 && camera_zoom > 0.15 && screen_radius >= LOD_MIN_FILE_LABEL_RADIUS
}

/// Determines if a user label should be rendered based on LOD.
///
/// # Arguments
/// * `screen_radius` - Radius in screen pixels
/// * `alpha` - User alpha
///
/// # Returns
/// `true` if the label should be rendered.
#[inline]
#[must_use]
pub fn should_render_user_label(screen_radius: f32, alpha: f32) -> bool {
    alpha >= 0.01 && screen_radius >= LOD_MIN_USER_LABEL_RADIUS
}

/// Determines if directory-to-parent branches should be rendered.
///
/// # Arguments
/// * `camera_zoom` - Current camera zoom level
///
/// # Returns
/// `true` if branches should be rendered.
#[inline]
#[must_use]
pub fn should_render_directory_branches(camera_zoom: f32) -> bool {
    camera_zoom >= LOD_MIN_ZOOM_FOR_DIR_BRANCHES
}

/// Determines if file-to-directory branches should be rendered.
///
/// # Arguments
/// * `camera_zoom` - Current camera zoom level
///
/// # Returns
/// `true` if branches should be rendered.
#[inline]
#[must_use]
pub fn should_render_file_branches(camera_zoom: f32) -> bool {
    camera_zoom >= LOD_MIN_ZOOM_FOR_FILE_BRANCHES
}

/// Computes the effective render radius for a file.
///
/// Files have a minimum render size to remain visible.
///
/// # Arguments
/// * `screen_radius` - Raw screen radius
///
/// # Returns
/// Effective radius (at least 2.0 pixels).
#[inline]
#[must_use]
pub fn compute_file_effective_radius(screen_radius: f32) -> f32 {
    screen_radius.max(2.0)
}

/// Computes the effective render radius for a user.
///
/// Users have a minimum render size to remain visible.
///
/// # Arguments
/// * `screen_radius` - Raw screen radius
///
/// # Returns
/// Effective radius (at least 5.0 pixels).
#[inline]
#[must_use]
pub fn compute_user_effective_radius(screen_radius: f32) -> f32 {
    screen_radius.max(5.0)
}

/// Computes file glow intensity based on touch state.
///
/// Recently touched files have a brighter glow.
///
/// # Arguments
/// * `is_touched` - Whether the file was recently modified
///
/// # Returns
/// Glow intensity multiplier.
#[inline]
#[must_use]
pub fn compute_file_glow_intensity(is_touched: bool) -> f32 {
    if is_touched {
        0.25
    } else {
        0.08
    }
}

/// Computes file border color from main color.
///
/// Border is a darker version of the main color.
///
/// # Arguments
/// * `color` - Main file color
///
/// # Returns
/// Border color (60% brightness of main).
#[inline]
#[must_use]
pub fn compute_file_border_color(color: Color) -> Color {
    Color::new(color.r * 0.6, color.g * 0.6, color.b * 0.6, color.a)
}

/// Computes file branch color with depth-based opacity.
///
/// # Arguments
/// * `color` - File color
/// * `alpha` - File alpha
/// * `depth` - Parent directory depth
/// * `branch_depth_fade` - Fade rate for depth
///
/// # Returns
/// Branch color with computed opacity.
#[inline]
#[must_use]
pub fn compute_file_branch_color(
    color: Color,
    alpha: f32,
    depth: u32,
    branch_depth_fade: f32,
) -> Color {
    let depth_factor = compute_depth_factor(depth);
    let depth_opacity = (1.0 - depth_factor * branch_depth_fade).max(0.05);
    Color::new(
        color.r * 0.7,
        color.g * 0.7,
        color.b * 0.7,
        0.25 * alpha * depth_opacity,
    )
}

/// Computes file label priority for sorting.
///
/// Higher priority labels are rendered first in collision avoidance.
///
/// # Arguments
/// * `radius` - File world radius
/// * `alpha` - File alpha
/// * `is_touched` - Whether file was recently modified
///
/// # Returns
/// Priority score (higher = more important).
#[inline]
#[must_use]
pub fn compute_file_label_priority(radius: f32, alpha: f32, is_touched: bool) -> f32 {
    let activity_bonus = if is_touched { 100.0 } else { 0.0 };
    radius * alpha * 10.0 + activity_bonus
}

/// Computes adaptive max labels based on zoom level.
///
/// At higher zoom, more labels can be displayed without clutter.
///
/// # Arguments
/// * `camera_zoom` - Current camera zoom level
///
/// # Returns
/// Maximum number of labels to render.
#[inline]
#[must_use]
pub fn compute_max_labels(camera_zoom: f32) -> usize {
    if camera_zoom > 1.0 {
        200
    } else if camera_zoom > 0.5 {
        100
    } else {
        50
    }
}

/// Computes watermark base position based on corner placement.
///
/// # Arguments
/// * `position` - Watermark corner position
/// * `margin` - Margin from screen edge
/// * `text_width` - Maximum text width
/// * `total_height` - Total height of watermark text
/// * `screen_width` - Screen width
/// * `screen_height` - Screen height
///
/// # Returns
/// (x, y) base position for the watermark.
#[inline]
#[must_use]
pub fn compute_watermark_position(
    position: WatermarkPosition,
    margin: f32,
    text_width: f32,
    total_height: f32,
    screen_width: f32,
    screen_height: f32,
) -> (f32, f32) {
    match position {
        WatermarkPosition::TopLeft => (margin, margin),
        WatermarkPosition::TopRight => (screen_width - text_width - margin, margin),
        WatermarkPosition::BottomLeft => (margin, screen_height - total_height - margin),
        WatermarkPosition::BottomRight => (
            screen_width - text_width - margin,
            screen_height - total_height - margin,
        ),
    }
}

/// Computes watermark total height based on whether subtext is present.
///
/// # Arguments
/// * `font_size` - Primary text font size
/// * `has_subtext` - Whether there is subtext
///
/// # Returns
/// Total height of watermark.
#[inline]
#[must_use]
pub fn compute_watermark_height(font_size: f32, has_subtext: bool) -> f32 {
    if has_subtext {
        font_size * 1.2 + font_size * 0.85
    } else {
        font_size
    }
}
