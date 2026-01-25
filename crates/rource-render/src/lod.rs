// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Level-of-Detail (LOD) constants for rendering optimization.
//!
//! This module provides shared LOD thresholds used by both CLI and WASM
//! renderers to ensure visual parity and consistent performance behavior.
//!
//! ## How LOD Works
//!
//! The screen radius of an entity is calculated as:
//!
//! ```text
//! screen_radius = world_radius * camera_zoom
//! ```
//!
//! When this falls below the threshold, the entity is either:
//! - Skipped entirely (for very small entities)
//! - Rendered without labels (for medium-small entities)
//!
//! This provides significant performance gains for large repositories:
//! - At zoom=0.01 with 50,000 files, most files are sub-pixel and skipped
//! - Labels are the most expensive to render; skipping them has high impact
//!
//! ## Usage
//!
//! ```
//! use rource_render::lod;
//!
//! // Example entity properties
//! let world_radius = 5.0_f32;
//! let camera_zoom = 0.5_f32;
//!
//! // Check if a file should be rendered
//! let screen_radius = world_radius * camera_zoom;
//! if screen_radius >= lod::MIN_FILE_RADIUS {
//!     // Render the file
//! }
//!
//! // Check if a file label should be rendered
//! if screen_radius >= lod::MIN_FILE_LABEL_RADIUS {
//!     // Render the label
//! }
//! ```

// =============================================================================
// Entity Rendering Thresholds
// =============================================================================

/// Minimum screen radius for a file to be rendered at all.
///
/// Files smaller than this are completely invisible and skipped.
/// Set low (0.1px) because we enforce a minimum render size of 2px anyway.
/// This allows files to remain visible at low zoom levels.
pub const MIN_FILE_RADIUS: f32 = 0.1;

/// Minimum screen radius for a directory node to be rendered.
///
/// Directories are important landmarks, so we use a very low threshold.
/// Root directory (depth 0) is always rendered regardless of this threshold.
pub const MIN_DIR_RADIUS: f32 = 0.05;

/// Minimum screen radius for user avatars to be rendered.
///
/// Set low (0.3px) because we enforce a minimum render size of 5px anyway.
/// This allows users to remain visible at low zoom levels.
pub const MIN_USER_RADIUS: f32 = 0.3;

// =============================================================================
// Label Rendering Thresholds
// =============================================================================

/// Minimum screen radius for file labels to be rendered.
///
/// Labels are expensive (text rendering + shadow) so we skip them earlier.
/// At 3.0 pixels radius, the entity is visible but labels would be unreadable.
pub const MIN_FILE_LABEL_RADIUS: f32 = 3.0;

/// Minimum screen radius for directory labels to be rendered.
///
/// Directory labels are slightly larger threshold than files since directory
/// names are typically longer and more important for navigation.
pub const MIN_DIR_LABEL_RADIUS: f32 = 4.0;

/// Minimum screen radius for user labels to be rendered.
///
/// User labels require more space to be readable.
pub const MIN_USER_LABEL_RADIUS: f32 = 5.0;

// =============================================================================
// Zoom Level Thresholds
// =============================================================================

/// Minimum zoom level for rendering file-to-directory connections.
///
/// Set low to keep branch structure visible during zoom out.
/// Below this zoom, file branches are skipped for performance.
pub const MIN_ZOOM_FOR_FILE_BRANCHES: f32 = 0.02;

/// Minimum zoom level for rendering directory-to-parent connections.
///
/// Directory branches are more important for structure, so the threshold
/// is lower than for file branches.
pub const MIN_ZOOM_FOR_DIR_BRANCHES: f32 = 0.01;

/// Minimum zoom level for auto-fit to prevent LOD culling all entities.
///
/// This is calculated based on keeping entities above their LOD thresholds:
/// - Files: `world_radius`=5.0, LOD=0.1 → `min_zoom` = 0.1/5.0 = 0.02
/// - Users: `world_radius`=15.0, LOD=0.3 → `min_zoom` = 0.3/15.0 = 0.02
///
/// We use 0.05 to provide a comfortable margin above the thresholds,
/// ensuring entities remain visible even at extreme zoom-out.
/// At 0.05: file `screen_radius` = 5.0 * 0.05 = 0.25 > 0.1 threshold (150% margin)
pub const AUTO_FIT_MIN_ZOOM: f32 = 0.05;

// =============================================================================
// Helper Functions
// =============================================================================

/// Determines if a directory should be rendered based on LOD.
///
/// Root directory (depth 0) is always rendered as it's the anchor point.
/// Other directories are culled when their screen radius is below threshold.
///
/// # Arguments
///
/// * `screen_radius` - Radius in screen pixels
/// * `depth` - Directory depth (0 = root)
///
/// # Returns
///
/// `true` if the directory should be rendered.
///
/// # Example
///
/// ```
/// use rource_render::lod;
///
/// // Root is always rendered
/// assert!(lod::should_render_directory(0.01, 0));
///
/// // Non-root with sufficient size
/// assert!(lod::should_render_directory(0.1, 2));
///
/// // Non-root too small
/// assert!(!lod::should_render_directory(0.01, 2));
/// ```
#[inline]
#[must_use]
pub const fn should_render_directory(screen_radius: f32, depth: u32) -> bool {
    depth == 0 || screen_radius >= MIN_DIR_RADIUS
}

/// Determines if a file should be rendered based on LOD.
///
/// # Arguments
///
/// * `screen_radius` - Radius in screen pixels
/// * `alpha` - File alpha (0.0-1.0)
///
/// # Returns
///
/// `true` if the file should be rendered.
///
/// # Example
///
/// ```
/// use rource_render::lod;
///
/// // Visible file with sufficient size
/// assert!(lod::should_render_file(0.5, 1.0));
///
/// // File too small
/// assert!(!lod::should_render_file(0.05, 1.0));
///
/// // File fully transparent
/// assert!(!lod::should_render_file(1.0, 0.001));
/// ```
#[inline]
#[must_use]
pub const fn should_render_file(screen_radius: f32, alpha: f32) -> bool {
    alpha >= 0.01 && screen_radius >= MIN_FILE_RADIUS
}

/// Determines if a user should be rendered based on LOD.
///
/// # Arguments
///
/// * `screen_radius` - Radius in screen pixels
/// * `alpha` - User alpha (0.0-1.0)
///
/// # Returns
///
/// `true` if the user should be rendered.
///
/// # Example
///
/// ```
/// use rource_render::lod;
///
/// // Visible user with sufficient size
/// assert!(lod::should_render_user(1.0, 1.0));
///
/// // User too small
/// assert!(!lod::should_render_user(0.1, 1.0));
///
/// // User fully transparent
/// assert!(!lod::should_render_user(1.0, 0.001));
/// ```
#[inline]
#[must_use]
pub const fn should_render_user(screen_radius: f32, alpha: f32) -> bool {
    alpha >= 0.01 && screen_radius >= MIN_USER_RADIUS
}

/// Determines if a file label should be rendered based on LOD.
///
/// # Arguments
///
/// * `screen_radius` - Radius in screen pixels
///
/// # Returns
///
/// `true` if the label should be rendered.
#[inline]
#[must_use]
pub const fn should_render_file_label(screen_radius: f32) -> bool {
    screen_radius >= MIN_FILE_LABEL_RADIUS
}

/// Determines if a directory label should be rendered based on LOD.
///
/// # Arguments
///
/// * `screen_radius` - Radius in screen pixels
/// * `depth` - Directory depth (0 = root)
/// * `max_depth` - Maximum depth to show labels for
///
/// # Returns
///
/// `true` if the label should be rendered.
#[inline]
#[must_use]
pub const fn should_render_dir_label(screen_radius: f32, depth: u32, max_depth: u32) -> bool {
    depth <= max_depth && screen_radius >= MIN_DIR_LABEL_RADIUS
}

/// Determines if a user label should be rendered based on LOD.
///
/// # Arguments
///
/// * `screen_radius` - Radius in screen pixels
///
/// # Returns
///
/// `true` if the label should be rendered.
#[inline]
#[must_use]
pub const fn should_render_user_label(screen_radius: f32) -> bool {
    screen_radius >= MIN_USER_LABEL_RADIUS
}

/// Determines if file branches should be rendered at this zoom level.
///
/// # Arguments
///
/// * `zoom` - Current camera zoom level
/// * `hide_tree` - Whether tree is explicitly hidden
///
/// # Returns
///
/// `true` if file branches should be rendered.
#[inline]
#[must_use]
pub const fn should_render_file_branches(zoom: f32, hide_tree: bool) -> bool {
    !hide_tree && zoom >= MIN_ZOOM_FOR_FILE_BRANCHES
}

/// Determines if directory branches should be rendered at this zoom level.
///
/// # Arguments
///
/// * `zoom` - Current camera zoom level
/// * `hide_tree` - Whether tree is explicitly hidden
///
/// # Returns
///
/// `true` if directory branches should be rendered.
#[inline]
#[must_use]
pub const fn should_render_dir_branches(zoom: f32, hide_tree: bool) -> bool {
    !hide_tree && zoom >= MIN_ZOOM_FOR_DIR_BRANCHES
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_min_file_radius_value() {
        assert!((MIN_FILE_RADIUS - 0.1).abs() < f32::EPSILON);
    }

    #[test]
    fn test_min_dir_radius_value() {
        assert!((MIN_DIR_RADIUS - 0.05).abs() < f32::EPSILON);
    }

    #[test]
    fn test_min_user_radius_value() {
        assert!((MIN_USER_RADIUS - 0.3).abs() < f32::EPSILON);
    }

    #[test]
    fn test_should_render_directory_root_always_visible() {
        // Root directory should always be rendered regardless of size
        assert!(should_render_directory(0.0, 0));
        assert!(should_render_directory(0.001, 0));
        assert!(should_render_directory(100.0, 0));
    }

    #[test]
    fn test_should_render_directory_non_root() {
        // Non-root directories need minimum size
        assert!(should_render_directory(0.05, 1));
        assert!(should_render_directory(1.0, 2));
        assert!(!should_render_directory(0.04, 1));
        assert!(!should_render_directory(0.01, 5));
    }

    #[test]
    fn test_should_render_file() {
        // Visible file with sufficient size
        assert!(should_render_file(0.1, 1.0));
        assert!(should_render_file(1.0, 0.5));

        // File too small
        assert!(!should_render_file(0.05, 1.0));
        assert!(!should_render_file(0.09, 1.0));

        // File too transparent
        assert!(!should_render_file(1.0, 0.009));
        assert!(!should_render_file(1.0, 0.0));
    }

    #[test]
    fn test_should_render_user() {
        // Visible user with sufficient size
        assert!(should_render_user(0.3, 1.0));
        assert!(should_render_user(1.0, 0.5));

        // User too small
        assert!(!should_render_user(0.2, 1.0));
        assert!(!should_render_user(0.29, 1.0));

        // User too transparent
        assert!(!should_render_user(1.0, 0.009));
    }

    #[test]
    fn test_should_render_file_label() {
        assert!(should_render_file_label(3.0));
        assert!(should_render_file_label(10.0));
        assert!(!should_render_file_label(2.9));
        assert!(!should_render_file_label(1.0));
    }

    #[test]
    fn test_should_render_dir_label() {
        // Within depth limit and size
        assert!(should_render_dir_label(4.0, 0, 2));
        assert!(should_render_dir_label(5.0, 2, 2));

        // Exceeds depth limit
        assert!(!should_render_dir_label(10.0, 3, 2));

        // Too small
        assert!(!should_render_dir_label(3.0, 0, 2));
    }

    #[test]
    fn test_should_render_user_label() {
        assert!(should_render_user_label(5.0));
        assert!(should_render_user_label(10.0));
        assert!(!should_render_user_label(4.9));
        assert!(!should_render_user_label(1.0));
    }

    #[test]
    fn test_should_render_file_branches() {
        assert!(should_render_file_branches(0.02, false));
        assert!(should_render_file_branches(0.1, false));
        assert!(!should_render_file_branches(0.019, false));
        assert!(!should_render_file_branches(1.0, true)); // hidden
    }

    #[test]
    fn test_should_render_dir_branches() {
        assert!(should_render_dir_branches(0.01, false));
        assert!(should_render_dir_branches(0.1, false));
        assert!(!should_render_dir_branches(0.009, false));
        assert!(!should_render_dir_branches(1.0, true)); // hidden
    }

    #[test]
    fn test_auto_fit_min_zoom_margin() {
        // At AUTO_FIT_MIN_ZOOM, files and users should be visible
        let file_world_radius = 5.0;
        let file_screen_radius = file_world_radius * AUTO_FIT_MIN_ZOOM;
        assert!(file_screen_radius > MIN_FILE_RADIUS);

        let user_world_radius = 15.0;
        let user_screen_radius = user_world_radius * AUTO_FIT_MIN_ZOOM;
        assert!(user_screen_radius > MIN_USER_RADIUS);
    }
}
