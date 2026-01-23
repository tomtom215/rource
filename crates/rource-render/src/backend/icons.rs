// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Procedural file icon generator (shared across backends).
//!
//! This module generates simple, visually distinct icons for different file
//! extensions. Icons are 32x32 RGBA images that can be used with texture
//! arrays for batched rendering.
//!
//! # Icon Design
//!
//! Each icon is a stylized document shape with:
//! - A folded corner (top-right)
//! - Extension-based fill color
//! - Subtle gradient and border
//!
//! # Usage
//!
//! ```ignore
//! use rource_render::backend::icons::{generate_icon, ICON_SIZE};
//! use rource_math::Color;
//!
//! let icon_data = generate_icon(Color::from_rgb8(222, 165, 132)); // Rust orange
//! assert_eq!(icon_data.len(), ICON_SIZE * ICON_SIZE * 4);
//! ```

use rource_math::Color;

/// Default icon size in pixels (32x32).
pub const ICON_SIZE: usize = 32;

/// Document fold size (corner fold effect).
const FOLD_SIZE: usize = 8;

/// Border width in pixels.
const BORDER_WIDTH: f32 = 1.5;

/// Generates an RGBA icon for a file extension color.
///
/// The icon is a stylized document shape with a folded corner.
///
/// # Arguments
///
/// * `color` - The fill color for the icon (RGBA as Color)
///
/// # Returns
///
/// A `Vec<u8>` containing `ICON_SIZE * ICON_SIZE * 4` bytes of RGBA data.
#[must_use]
pub fn generate_icon(color: Color) -> Vec<u8> {
    let mut data = vec![0u8; ICON_SIZE * ICON_SIZE * 4];

    // Convert color to u8 components
    let r = (color.r * 255.0) as u8;
    let g = (color.g * 255.0) as u8;
    let b = (color.b * 255.0) as u8;

    // Lighter version for gradient
    let lighter_r = ((color.r * 255.0 * 1.2).min(255.0)) as u8;
    let lighter_g = ((color.g * 255.0 * 1.2).min(255.0)) as u8;
    let lighter_b = ((color.b * 255.0 * 1.2).min(255.0)) as u8;

    // Darker version for border and fold
    let darker_r = (color.r * 255.0 * 0.7) as u8;
    let darker_g = (color.g * 255.0 * 0.7) as u8;
    let darker_b = (color.b * 255.0 * 0.7) as u8;

    // Document boundaries (with margin)
    let margin = 2;
    let left = margin;
    let right = ICON_SIZE - margin - 1;
    let top = margin;
    let bottom = ICON_SIZE - margin - 1;

    for y in 0..ICON_SIZE {
        for x in 0..ICON_SIZE {
            let idx = (y * ICON_SIZE + x) * 4;
            let fx = x as f32;
            let fy = y as f32;

            // Check if inside document shape (excluding fold corner)
            let in_fold_region = x > right - FOLD_SIZE && y < top + FOLD_SIZE;
            let in_document = x >= left && x <= right && y >= top && y <= bottom && !in_fold_region;

            // Check if in the fold triangle
            let fold_x = (right - FOLD_SIZE) as f32;
            let fold_y = (top + FOLD_SIZE) as f32;
            let in_fold_triangle = x > right - FOLD_SIZE
                && y < top + FOLD_SIZE
                && (fx - fold_x) + (fold_y - fy) >= 0.0;

            if in_document {
                // Calculate distance to edges for anti-aliasing
                let dist_left = (fx - left as f32).max(0.0);
                let dist_right = (right as f32 - fx).max(0.0);
                let dist_top = (fy - top as f32).max(0.0);
                let dist_bottom = (bottom as f32 - fy).max(0.0);

                // Check for border region
                let in_border = dist_left < BORDER_WIDTH
                    || dist_right < BORDER_WIDTH
                    || dist_top < BORDER_WIDTH
                    || dist_bottom < BORDER_WIDTH;

                // Simple gradient from top to bottom
                let gradient_t = (y - top) as f32 / (bottom - top) as f32;

                if in_border {
                    // Border color (darker)
                    data[idx] = darker_r;
                    data[idx + 1] = darker_g;
                    data[idx + 2] = darker_b;
                } else {
                    // Interior with gradient
                    data[idx] = lerp_u8(lighter_r, r, gradient_t);
                    data[idx + 1] = lerp_u8(lighter_g, g, gradient_t);
                    data[idx + 2] = lerp_u8(lighter_b, b, gradient_t);
                }
                data[idx + 3] = 255;
            } else if in_fold_triangle {
                // Fold effect (slightly darker)
                data[idx] = darker_r;
                data[idx + 1] = darker_g;
                data[idx + 2] = darker_b;
                data[idx + 3] = 255;
            }
            // else: transparent (default)
        }
    }

    data
}

/// Generates a circular icon (for directory nodes).
///
/// # Arguments
///
/// * `color` - The fill color for the icon
///
/// # Returns
///
/// A `Vec<u8>` containing `ICON_SIZE * ICON_SIZE * 4` bytes of RGBA data.
#[must_use]
pub fn generate_circle_icon(color: Color) -> Vec<u8> {
    let mut data = vec![0u8; ICON_SIZE * ICON_SIZE * 4];

    let center = ICON_SIZE as f32 / 2.0;
    let radius = center - 2.0;
    let inner_radius = radius - BORDER_WIDTH;

    // Convert color to u8 components
    let r = (color.r * 255.0) as u8;
    let g = (color.g * 255.0) as u8;
    let b = (color.b * 255.0) as u8;

    // Darker version for border
    let darker_r = (color.r * 255.0 * 0.7) as u8;
    let darker_g = (color.g * 255.0 * 0.7) as u8;
    let darker_b = (color.b * 255.0 * 0.7) as u8;

    for y in 0..ICON_SIZE {
        for x in 0..ICON_SIZE {
            let idx = (y * ICON_SIZE + x) * 4;
            let fx = x as f32 + 0.5;
            let fy = y as f32 + 0.5;

            let dx = fx - center;
            let dy = fy - center;
            let dist = dx.hypot(dy);

            if dist <= inner_radius {
                // Interior
                data[idx] = r;
                data[idx + 1] = g;
                data[idx + 2] = b;
                data[idx + 3] = 255;
            } else if dist <= radius {
                // Border with anti-aliasing
                let alpha = ((radius - dist) * 255.0).clamp(0.0, 255.0) as u8;
                data[idx] = darker_r;
                data[idx + 1] = darker_g;
                data[idx + 2] = darker_b;
                data[idx + 3] = alpha;
            } else if dist <= radius + 1.0 {
                // Anti-aliased edge
                let alpha = ((radius + 1.0 - dist) * 255.0).clamp(0.0, 255.0) as u8;
                data[idx] = darker_r;
                data[idx + 1] = darker_g;
                data[idx + 2] = darker_b;
                data[idx + 3] = alpha;
            }
        }
    }

    data
}

/// Generates a default/unknown file type icon.
///
/// This is a gray document icon used when the extension is not recognized.
#[must_use]
pub fn generate_default_icon() -> Vec<u8> {
    generate_icon(Color::from_rgb8(141, 160, 203)) // Default blueish-gray
}

/// Linear interpolation for u8 values.
#[inline]
fn lerp_u8(a: u8, b: u8, t: f32) -> u8 {
    let a_f = f32::from(a);
    let b_f = f32::from(b);
    (a_f + (b_f - a_f) * t) as u8
}

/// Common file extension colors (matching file.rs).
///
/// Returns a vector of (extension, Color) pairs for pre-registration.
#[must_use]
pub fn common_extensions() -> Vec<(&'static str, Color)> {
    vec![
        // Rust
        ("rs", Color::from_rgb8(222, 165, 132)),
        // JavaScript/TypeScript
        ("js", Color::from_rgb8(247, 223, 30)),
        ("ts", Color::from_rgb8(49, 120, 198)),
        ("jsx", Color::from_rgb8(97, 218, 251)),
        ("tsx", Color::from_rgb8(97, 218, 251)),
        // Python
        ("py", Color::from_rgb8(53, 114, 165)),
        // Go
        ("go", Color::from_rgb8(0, 173, 216)),
        // Java/Kotlin
        ("java", Color::from_rgb8(176, 114, 25)),
        ("kt", Color::from_rgb8(167, 139, 250)),
        // C/C++
        ("c", Color::from_rgb8(85, 85, 255)),
        ("h", Color::from_rgb8(85, 85, 255)),
        ("cpp", Color::from_rgb8(0, 89, 156)),
        ("hpp", Color::from_rgb8(0, 89, 156)),
        // C#
        ("cs", Color::from_rgb8(155, 79, 150)),
        // Web
        ("html", Color::from_rgb8(227, 76, 38)),
        ("css", Color::from_rgb8(86, 61, 124)),
        ("scss", Color::from_rgb8(205, 103, 153)),
        ("vue", Color::from_rgb8(65, 184, 131)),
        // Data/Config
        ("json", Color::from_rgb8(128, 128, 128)),
        ("yaml", Color::from_rgb8(203, 23, 30)),
        ("yml", Color::from_rgb8(203, 23, 30)),
        ("toml", Color::from_rgb8(156, 66, 33)),
        ("xml", Color::from_rgb8(0, 96, 172)),
        // Documentation
        ("md", Color::from_rgb8(200, 200, 200)),
        ("txt", Color::from_rgb8(180, 180, 180)),
        // Shell
        ("sh", Color::from_rgb8(0, 128, 0)),
        ("bash", Color::from_rgb8(0, 128, 0)),
        // Database
        ("sql", Color::from_rgb8(255, 128, 0)),
        // Ruby
        ("rb", Color::from_rgb8(204, 52, 45)),
        // PHP
        ("php", Color::from_rgb8(119, 123, 179)),
        // Swift
        ("swift", Color::from_rgb8(240, 81, 56)),
    ]
}

/// Generates icons for all common file extensions.
///
/// Returns a vector of (extension, `icon_data`) pairs.
#[must_use]
pub fn generate_common_icons() -> Vec<(&'static str, Vec<u8>)> {
    common_extensions()
        .iter()
        .map(|(ext, color)| (*ext, generate_icon(*color)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_icon_size() {
        let icon = generate_icon(Color::RED);
        assert_eq!(icon.len(), ICON_SIZE * ICON_SIZE * 4);
    }

    #[test]
    fn test_generate_icon_has_content() {
        let icon = generate_icon(Color::from_rgb8(222, 165, 132));

        // Check that some pixels are non-transparent
        let non_transparent = icon.chunks(4).filter(|px| px[3] > 0).count();
        assert!(non_transparent > 0, "Icon should have visible pixels");

        // Most of the center should be filled
        let center_y = ICON_SIZE / 2;
        let center_x = ICON_SIZE / 2;
        let center_idx = (center_y * ICON_SIZE + center_x) * 4;
        assert_eq!(icon[center_idx + 3], 255, "Center should be opaque");
    }

    #[test]
    fn test_generate_circle_icon_size() {
        let icon = generate_circle_icon(Color::BLUE);
        assert_eq!(icon.len(), ICON_SIZE * ICON_SIZE * 4);
    }

    #[test]
    fn test_generate_circle_icon_center() {
        let icon = generate_circle_icon(Color::GREEN);

        // Center should be filled
        let center = ICON_SIZE / 2;
        let idx = (center * ICON_SIZE + center) * 4;
        assert_eq!(icon[idx + 3], 255, "Center should be opaque");
    }

    #[test]
    fn test_generate_default_icon() {
        let icon = generate_default_icon();
        assert_eq!(icon.len(), ICON_SIZE * ICON_SIZE * 4);
    }

    #[test]
    fn test_common_extensions() {
        let extensions = common_extensions();
        assert!(extensions.len() >= 20, "Should have many common extensions");

        // Check for Rust
        assert!(
            extensions.iter().any(|(ext, _)| ext == &"rs"),
            "Should include Rust"
        );

        // Check for JavaScript
        assert!(
            extensions.iter().any(|(ext, _)| ext == &"js"),
            "Should include JavaScript"
        );
    }

    #[test]
    fn test_generate_common_icons() {
        let icons = generate_common_icons();
        assert!(!icons.is_empty());

        for (ext, data) in icons {
            assert_eq!(
                data.len(),
                ICON_SIZE * ICON_SIZE * 4,
                "Icon for {ext} should be correct size"
            );
        }
    }

    #[test]
    fn test_lerp_u8() {
        assert_eq!(lerp_u8(0, 100, 0.0), 0);
        assert_eq!(lerp_u8(0, 100, 1.0), 100);
        assert_eq!(lerp_u8(0, 100, 0.5), 50);
        assert_eq!(lerp_u8(100, 200, 0.5), 150);
    }
}
