// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Shared rendering helper functions.
//!
//! This module contains pure computation functions used by both CLI and WASM
//! renderers to ensure visual parity. All functions are pure (no side effects)
//! and can be unit tested independently.
//!
//! ## Contents
//!
//! - **Directory styling**: Depth-based colors, branch widths, opacity
//! - **File styling**: Effective radii, glow intensities, colors
//! - **User styling**: Avatar radii, glow effects, border colors
//! - **Watermark positioning**: Layout calculations for watermark text
//!
//! ## Design Principles
//!
//! 1. **Pure functions**: All functions take inputs and return outputs without
//!    modifying external state. This enables easy testing and parallel execution.
//!
//! 2. **Performance**: Functions are `#[inline]` for zero-cost abstraction.
//!    Precomputed constants are used where beneficial.
//!
//! 3. **Visual parity**: Identical logic in CLI and WASM ensures consistent
//!    appearance across platforms.

use rource_math::Color;

// =============================================================================
// Constants
// =============================================================================

/// Precomputed reciprocal for depth factor calculation (1.0 / 6.0).
///
/// Using multiplication by reciprocal is faster than division.
const INV_DEPTH_MAX: f32 = 1.0 / 6.0;

/// Maximum directory depth for depth factor normalization.
///
/// Depths beyond this are clamped to 1.0.
pub const MAX_DEPTH_FOR_FACTOR: u32 = 6;

/// Default branch opacity when not using depth-based fading.
pub const DEFAULT_BRANCH_OPACITY: f32 = 0.35;

/// Minimum file render size in screen pixels.
///
/// Files smaller than their screen radius are rendered at this minimum size
/// to ensure visibility at low zoom levels.
pub const MIN_FILE_RENDER_SIZE: f32 = 2.0;

/// Minimum user render size in screen pixels.
///
/// Users smaller than their screen radius are rendered at this minimum size
/// to ensure visibility at low zoom levels.
pub const MIN_USER_RENDER_SIZE: f32 = 5.0;

// =============================================================================
// Directory Styling
// =============================================================================

/// Computes the depth factor used for depth-based styling.
///
/// The depth factor is normalized to \[0.0, 1.0\] where 0 is root and 1.0 is
/// a directory at depth 6 or greater.
///
/// # Arguments
///
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
///
/// Normalized depth factor in range \[0.0, 1.0\].
///
/// # Example
///
/// ```
/// use rource_render::helpers::compute_depth_factor;
///
/// assert!((compute_depth_factor(0) - 0.0).abs() < 0.001);
/// assert!((compute_depth_factor(3) - 0.5).abs() < 0.001);
/// assert!((compute_depth_factor(6) - 1.0).abs() < 0.001);
/// assert!((compute_depth_factor(10) - 1.0).abs() < 0.001); // Clamped
/// ```
#[inline]
#[must_use]
pub fn compute_depth_factor(depth: u32) -> f32 {
    (depth as f32 * INV_DEPTH_MAX).min(1.0)
}

/// Computes the base brightness for directory coloring.
///
/// Shallower directories are brighter, providing visual hierarchy.
///
/// # Arguments
///
/// * `depth_factor` - Normalized depth (0.0-1.0)
///
/// # Returns
///
/// Base brightness value in range \[0.25, 0.35\].
///
/// # Example
///
/// ```
/// use rource_render::helpers::compute_base_brightness;
///
/// // Root (depth_factor=0) is brightest
/// assert!((compute_base_brightness(0.0) - 0.35).abs() < 0.001);
///
/// // Deepest (depth_factor=1) is dimmest
/// assert!((compute_base_brightness(1.0) - 0.25).abs() < 0.001);
/// ```
#[inline]
#[must_use]
pub fn compute_base_brightness(depth_factor: f32) -> f32 {
    0.25 + 0.1 * (1.0 - depth_factor)
}

/// Computes directory color based on depth.
///
/// Deeper directories are rendered with lower brightness to create
/// visual hierarchy and reduce clutter. Colors have a slight blue tint.
///
/// # Arguments
///
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
///
/// Color for the directory node with alpha of 0.55.
///
/// # Example
///
/// ```
/// use rource_render::helpers::compute_directory_color;
///
/// let color = compute_directory_color(0);
/// assert!(color.a > 0.5); // Semi-transparent
/// assert!(color.b > color.r); // Blue tint
/// ```
#[inline]
#[must_use]
pub fn compute_directory_color(depth: u32) -> Color {
    let depth_factor = compute_depth_factor(depth);
    let base_brightness = compute_base_brightness(depth_factor);
    Color::new(
        base_brightness * 0.9,
        base_brightness,
        base_brightness * 1.1 + 0.05,
        0.55,
    )
}

/// Computes the glow color for directory background effect.
///
/// # Arguments
///
/// * `dir_color` - Base directory color
///
/// # Returns
///
/// Same color with reduced alpha for glow effect.
#[inline]
#[must_use]
pub fn compute_directory_glow_color(dir_color: Color) -> Color {
    dir_color.with_alpha(0.1)
}

/// Computes the center dot color for directory nodes.
///
/// # Arguments
///
/// * `dir_color` - Base directory color
///
/// # Returns
///
/// Same color with adjusted alpha for center dot.
#[inline]
#[must_use]
pub fn compute_directory_center_color(dir_color: Color) -> Color {
    dir_color.with_alpha(0.4)
}

/// Computes branch line width based on directory depth.
///
/// Deeper directories have thinner branches to reduce visual noise.
///
/// # Arguments
///
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
///
/// Branch width in pixels, range \[0.8, 1.5\].
///
/// # Example
///
/// ```
/// use rource_render::helpers::compute_branch_width;
///
/// // Root branches are thickest
/// assert!((compute_branch_width(0) - 1.5).abs() < 0.001);
///
/// // Deep branches are thinner (but not below minimum)
/// assert!(compute_branch_width(10) >= 0.8);
/// ```
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
///
/// * `depth` - Directory depth (0 = root)
/// * `max_opacity` - Maximum opacity for branches (0.0-1.0)
/// * `fade_rate` - How quickly opacity fades with depth (0.0-1.0)
///
/// # Returns
///
/// Branch opacity in range \[0.05 * `max_opacity`, `max_opacity`\].
///
/// # Example
///
/// ```
/// use rource_render::helpers::compute_branch_opacity;
///
/// // Root has maximum opacity
/// let root_opacity = compute_branch_opacity(0, 0.5, 0.8);
/// assert!((root_opacity - 0.5).abs() < 0.001);
///
/// // Deep branches fade
/// let deep_opacity = compute_branch_opacity(6, 0.5, 0.8);
/// assert!(deep_opacity < 0.2);
/// ```
#[inline]
#[must_use]
pub fn compute_branch_opacity(depth: u32, max_opacity: f32, fade_rate: f32) -> f32 {
    let depth_factor = compute_depth_factor(depth);
    max_opacity * (1.0 - depth_factor * fade_rate).max(0.05)
}

/// Computes branch color from directory color.
///
/// Branch color is slightly brighter than the directory with specified opacity.
///
/// # Arguments
///
/// * `dir_color` - Base directory color
/// * `opacity` - Branch opacity (0.0-1.0)
///
/// # Returns
///
/// Branch color with brightness boost and specified opacity.
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

/// Computes branch color with default opacity.
///
/// Convenience function using [`DEFAULT_BRANCH_OPACITY`].
///
/// # Arguments
///
/// * `dir_color` - Base directory color
///
/// # Returns
///
/// Branch color with default opacity (0.35).
#[inline]
#[must_use]
pub fn compute_branch_color_default(dir_color: Color) -> Color {
    compute_branch_color(dir_color, DEFAULT_BRANCH_OPACITY)
}

// =============================================================================
// File Styling
// =============================================================================

/// Computes the effective file radius with minimum size enforcement.
///
/// Files are never rendered smaller than [`MIN_FILE_RENDER_SIZE`] to ensure
/// visibility at low zoom levels.
///
/// # Arguments
///
/// * `screen_radius` - Computed screen radius
///
/// # Returns
///
/// Effective radius (at least 2.0 pixels).
///
/// # Example
///
/// ```
/// use rource_render::helpers::compute_effective_file_radius;
///
/// assert!((compute_effective_file_radius(10.0) - 10.0).abs() < 0.001);
/// assert!((compute_effective_file_radius(1.0) - 2.0).abs() < 0.001);
/// assert!((compute_effective_file_radius(0.5) - 2.0).abs() < 0.001);
/// ```
#[inline]
#[must_use]
pub fn compute_effective_file_radius(screen_radius: f32) -> f32 {
    screen_radius.max(MIN_FILE_RENDER_SIZE)
}

/// Computes file glow intensity based on activity state.
///
/// Touched files have a glow effect that draws attention to recent changes.
///
/// # Arguments
///
/// * `is_touched` - Whether the file was recently modified
/// * `base_intensity` - Base glow intensity (typically 0.3-0.5)
///
/// # Returns
///
/// Glow intensity (0.0 if not touched, `base_intensity` if touched).
#[inline]
#[must_use]
pub fn compute_file_glow_intensity(is_touched: bool, base_intensity: f32) -> f32 {
    if is_touched {
        base_intensity
    } else {
        0.0
    }
}

/// Computes file glow color from base color.
///
/// # Arguments
///
/// * `file_color` - Base file color
/// * `intensity` - Glow intensity (0.0-1.0)
///
/// # Returns
///
/// Glow color with adjusted alpha.
#[inline]
#[must_use]
pub fn compute_file_glow_color(file_color: Color, intensity: f32) -> Color {
    file_color.with_alpha(intensity)
}

/// Computes file border color (darker version of base color).
///
/// # Arguments
///
/// * `file_color` - Base file color
///
/// # Returns
///
/// Darker border color for definition.
#[inline]
#[must_use]
pub fn compute_file_border_color(file_color: Color) -> Color {
    Color::new(
        file_color.r * 0.6,
        file_color.g * 0.6,
        file_color.b * 0.6,
        file_color.a,
    )
}

// =============================================================================
// User Styling
// =============================================================================

/// Computes the effective user radius with minimum size enforcement.
///
/// Users are never rendered smaller than [`MIN_USER_RENDER_SIZE`] to ensure
/// visibility at low zoom levels.
///
/// # Arguments
///
/// * `screen_radius` - Computed screen radius
///
/// # Returns
///
/// Effective radius (at least 5.0 pixels).
///
/// # Example
///
/// ```
/// use rource_render::helpers::compute_effective_user_radius;
///
/// assert!((compute_effective_user_radius(20.0) - 20.0).abs() < 0.001);
/// assert!((compute_effective_user_radius(3.0) - 5.0).abs() < 0.001);
/// assert!((compute_effective_user_radius(1.0) - 5.0).abs() < 0.001);
/// ```
#[inline]
#[must_use]
pub fn compute_effective_user_radius(screen_radius: f32) -> f32 {
    screen_radius.max(MIN_USER_RENDER_SIZE)
}

/// Computes user border color (darker version of base color).
///
/// # Arguments
///
/// * `user_color` - Base user color
/// * `alpha` - User alpha for transparency
///
/// # Returns
///
/// Darker border color with specified alpha.
#[inline]
#[must_use]
pub fn compute_user_border_color(user_color: Color, alpha: f32) -> Color {
    Color::new(
        user_color.r * 0.5,
        user_color.g * 0.5,
        user_color.b * 0.5,
        alpha,
    )
}

/// Computes user glow radius for active users.
///
/// # Arguments
///
/// * `base_radius` - Base avatar radius
/// * `layer` - Glow layer index (0, 1, 2...)
///
/// # Returns
///
/// Glow radius for the specified layer.
#[inline]
#[must_use]
pub fn compute_user_glow_radius(base_radius: f32, layer: u32) -> f32 {
    base_radius * (1.3 + layer as f32 * 0.15)
}

/// Computes user glow alpha for active users.
///
/// # Arguments
///
/// * `base_alpha` - User base alpha
/// * `layer` - Glow layer index (0, 1, 2...)
///
/// # Returns
///
/// Glow alpha for the specified layer.
#[inline]
#[must_use]
pub fn compute_user_glow_alpha(base_alpha: f32, layer: u32) -> f32 {
    base_alpha * 0.15 * (1.0 - layer as f32 * 0.25)
}

// =============================================================================
// Watermark Positioning
// =============================================================================

/// Watermark position enum for positioning calculations.
///
/// This is a local copy to avoid circular dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum WatermarkPosition {
    /// Top-left corner
    #[default]
    TopLeft,
    /// Top-right corner
    TopRight,
    /// Bottom-left corner
    BottomLeft,
    /// Bottom-right corner
    BottomRight,
    /// Top-center
    TopCenter,
    /// Bottom-center
    BottomCenter,
}

/// Computes watermark position based on alignment and screen dimensions.
///
/// # Arguments
///
/// * `position` - Watermark alignment
/// * `margin` - Margin from screen edge in pixels
/// * `text_width` - Width of the watermark text
/// * `total_height` - Total height of all watermark lines
/// * `screen_width` - Screen width in pixels
/// * `screen_height` - Screen height in pixels
///
/// # Returns
///
/// (x, y) position for the watermark top-left corner.
///
/// # Example
///
/// ```
/// use rource_render::helpers::{compute_watermark_position, WatermarkPosition};
///
/// let (x, y) = compute_watermark_position(
///     WatermarkPosition::TopLeft,
///     10.0,  // margin
///     100.0, // text width
///     20.0,  // total height
///     800.0, // screen width
///     600.0, // screen height
/// );
/// assert!((x - 10.0).abs() < 0.001);
/// assert!((y - 10.0).abs() < 0.001);
/// ```
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
        WatermarkPosition::TopCenter => ((screen_width - text_width) * 0.5, margin),
        WatermarkPosition::BottomCenter => (
            (screen_width - text_width) * 0.5,
            screen_height - total_height - margin,
        ),
    }
}

/// Computes total watermark height from lines and font size.
///
/// # Arguments
///
/// * `line_count` - Number of watermark lines
/// * `font_size` - Font size in pixels
/// * `line_spacing` - Additional spacing between lines (typically 0.2-0.5)
///
/// # Returns
///
/// Total height in pixels.
#[inline]
#[must_use]
pub fn compute_watermark_height(line_count: usize, font_size: f32, line_spacing: f32) -> f32 {
    if line_count == 0 {
        0.0
    } else {
        line_count as f32 * font_size * (1.0 + line_spacing)
    }
}

// =============================================================================
// Label Positioning
// =============================================================================

/// Computes label position offset from entity center.
///
/// Labels are positioned to the right of the entity with vertical centering.
///
/// # Arguments
///
/// * `screen_x` - Entity screen X position
/// * `screen_y` - Entity screen Y position
/// * `entity_radius` - Entity radius in screen pixels
/// * `font_size` - Label font size
/// * `horizontal_offset` - Additional horizontal offset (typically 4-5)
///
/// # Returns
///
/// (x, y) position for the label.
#[inline]
#[must_use]
pub fn compute_label_position(
    screen_x: f32,
    screen_y: f32,
    entity_radius: f32,
    font_size: f32,
    horizontal_offset: f32,
) -> (f32, f32) {
    (
        screen_x + entity_radius + horizontal_offset,
        screen_y - font_size * 0.3,
    )
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Depth Factor Tests ----

    #[test]
    fn test_compute_depth_factor_root() {
        assert!((compute_depth_factor(0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_depth_factor_mid() {
        assert!((compute_depth_factor(3) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_depth_factor_max() {
        assert!((compute_depth_factor(6) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_depth_factor_clamped() {
        assert!((compute_depth_factor(10) - 1.0).abs() < 0.001);
        assert!((compute_depth_factor(100) - 1.0).abs() < 0.001);
    }

    // ---- Base Brightness Tests ----

    #[test]
    fn test_compute_base_brightness_range() {
        let bright = compute_base_brightness(0.0);
        let dim = compute_base_brightness(1.0);

        assert!((bright - 0.35).abs() < 0.001);
        assert!((dim - 0.25).abs() < 0.001);
        assert!(bright > dim);
    }

    // ---- Directory Color Tests ----

    #[test]
    fn test_compute_directory_color_has_blue_tint() {
        let color = compute_directory_color(0);
        assert!(color.b > color.r);
        assert!(color.b > color.g);
    }

    #[test]
    fn test_compute_directory_color_alpha() {
        let color = compute_directory_color(3);
        assert!((color.a - 0.55).abs() < 0.001);
    }

    #[test]
    fn test_compute_directory_color_depth_affects_brightness() {
        let shallow = compute_directory_color(0);
        let deep = compute_directory_color(6);

        assert!(shallow.r > deep.r);
        assert!(shallow.g > deep.g);
        assert!(shallow.b > deep.b);
    }

    // ---- Branch Width Tests ----

    #[test]
    fn test_compute_branch_width_root() {
        assert!((compute_branch_width(0) - 1.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_branch_width_minimum() {
        // Should not go below 0.8
        assert!(compute_branch_width(10) >= 0.8);
        assert!(compute_branch_width(100) >= 0.8);
    }

    #[test]
    fn test_compute_branch_width_decreases_with_depth() {
        let root = compute_branch_width(0);
        let mid = compute_branch_width(3);
        let deep = compute_branch_width(6);

        assert!(root > mid);
        assert!(mid > deep);
    }

    // ---- Branch Opacity Tests ----

    #[test]
    fn test_compute_branch_opacity_root() {
        let opacity = compute_branch_opacity(0, 0.5, 0.8);
        assert!((opacity - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_branch_opacity_fades() {
        let root = compute_branch_opacity(0, 0.5, 0.8);
        let deep = compute_branch_opacity(6, 0.5, 0.8);

        assert!(root > deep);
        assert!(deep > 0.0); // Should have minimum
    }

    // ---- File Radius Tests ----

    #[test]
    fn test_compute_effective_file_radius_large() {
        assert!((compute_effective_file_radius(10.0) - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_effective_file_radius_minimum() {
        assert!((compute_effective_file_radius(1.0) - 2.0).abs() < 0.001);
        assert!((compute_effective_file_radius(0.5) - 2.0).abs() < 0.001);
    }

    // ---- User Radius Tests ----

    #[test]
    fn test_compute_effective_user_radius_large() {
        assert!((compute_effective_user_radius(20.0) - 20.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_effective_user_radius_minimum() {
        assert!((compute_effective_user_radius(3.0) - 5.0).abs() < 0.001);
        assert!((compute_effective_user_radius(1.0) - 5.0).abs() < 0.001);
    }

    // ---- Watermark Position Tests ----

    #[test]
    fn test_compute_watermark_position_top_left() {
        let (x, y) =
            compute_watermark_position(WatermarkPosition::TopLeft, 10.0, 100.0, 20.0, 800.0, 600.0);
        assert!((x - 10.0).abs() < 0.001);
        assert!((y - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_position_bottom_right() {
        let (x, y) = compute_watermark_position(
            WatermarkPosition::BottomRight,
            10.0,
            100.0,
            20.0,
            800.0,
            600.0,
        );
        assert!((x - 690.0).abs() < 0.001); // 800 - 100 - 10
        assert!((y - 570.0).abs() < 0.001); // 600 - 20 - 10
    }

    #[test]
    fn test_compute_watermark_position_center() {
        let (x, _) = compute_watermark_position(
            WatermarkPosition::TopCenter,
            10.0,
            100.0,
            20.0,
            800.0,
            600.0,
        );
        assert!((x - 350.0).abs() < 0.001); // (800 - 100) / 2
    }

    // ---- Watermark Height Tests ----

    #[test]
    fn test_compute_watermark_height_empty() {
        assert!((compute_watermark_height(0, 12.0, 0.2) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_height_single_line() {
        let height = compute_watermark_height(1, 12.0, 0.2);
        assert!((height - 14.4).abs() < 0.001); // 12 * 1.2
    }

    #[test]
    fn test_compute_watermark_height_multi_line() {
        let height = compute_watermark_height(3, 12.0, 0.2);
        assert!((height - 43.2).abs() < 0.001); // 3 * 12 * 1.2
    }

    // ---- Label Position Tests ----

    #[test]
    fn test_compute_label_position() {
        let (x, y) = compute_label_position(100.0, 200.0, 10.0, 12.0, 4.0);
        assert!((x - 114.0).abs() < 0.001); // 100 + 10 + 4
        assert!((y - 196.4).abs() < 0.001); // 200 - 12 * 0.3
    }

    // ---- File Glow Tests ----

    #[test]
    fn test_compute_file_glow_intensity_touched() {
        assert!((compute_file_glow_intensity(true, 0.4) - 0.4).abs() < 0.001);
    }

    #[test]
    fn test_compute_file_glow_intensity_not_touched() {
        assert!((compute_file_glow_intensity(false, 0.4) - 0.0).abs() < 0.001);
    }

    // ---- Border Color Tests ----

    #[test]
    fn test_compute_file_border_color() {
        let base = Color::new(1.0, 0.8, 0.6, 1.0);
        let border = compute_file_border_color(base);

        assert!((border.r - 0.6).abs() < 0.001);
        assert!((border.g - 0.48).abs() < 0.001);
        assert!((border.b - 0.36).abs() < 0.001);
        assert!((border.a - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_user_border_color() {
        let base = Color::new(1.0, 0.8, 0.6, 1.0);
        let border = compute_user_border_color(base, 0.5);

        assert!((border.r - 0.5).abs() < 0.001);
        assert!((border.g - 0.4).abs() < 0.001);
        assert!((border.b - 0.3).abs() < 0.001);
        assert!((border.a - 0.5).abs() < 0.001);
    }

    // ---- User Glow Tests ----

    #[test]
    fn test_compute_user_glow_radius() {
        let base = 10.0;
        assert!((compute_user_glow_radius(base, 0) - 13.0).abs() < 0.001);
        assert!((compute_user_glow_radius(base, 1) - 14.5).abs() < 0.001);
        assert!((compute_user_glow_radius(base, 2) - 16.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_user_glow_alpha() {
        let base = 1.0;
        assert!((compute_user_glow_alpha(base, 0) - 0.15).abs() < 0.001);
        assert!((compute_user_glow_alpha(base, 1) - 0.1125).abs() < 0.001);
        assert!((compute_user_glow_alpha(base, 2) - 0.075).abs() < 0.001);
    }
}
