// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Tests for LabelPlacer spatial hash collision detection.

use rource_math::{Rect, Vec2};

use crate::render_phases::label_placer::{rects_intersect, LabelPlacer};

// Import LOD constants for tests
use rource_render::lod::{
    MIN_DIR_LABEL_RADIUS as LOD_MIN_DIR_LABEL_RADIUS, MIN_DIR_RADIUS as LOD_MIN_DIR_RADIUS,
    MIN_FILE_LABEL_RADIUS as LOD_MIN_FILE_LABEL_RADIUS, MIN_FILE_RADIUS as LOD_MIN_FILE_RADIUS,
    MIN_USER_LABEL_RADIUS as LOD_MIN_USER_LABEL_RADIUS, MIN_USER_RADIUS as LOD_MIN_USER_RADIUS,
    MIN_ZOOM_FOR_DIR_BRANCHES as LOD_MIN_ZOOM_FOR_DIR_BRANCHES,
    MIN_ZOOM_FOR_FILE_BRANCHES as LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
};

// -------------------------------------------------------------------------
// LabelPlacer Basic Tests
// -------------------------------------------------------------------------

#[test]
fn test_label_placer_basic() {
    let mut placer = LabelPlacer::new(1.0);
    assert!(placer.can_place_more());

    // First label should always succeed
    assert!(placer.try_place(Vec2::new(0.0, 0.0), 50.0, 20.0));

    // Overlapping label should fail
    assert!(!placer.try_place(Vec2::new(10.0, 5.0), 50.0, 20.0));

    // Non-overlapping label should succeed
    assert!(placer.try_place(Vec2::new(100.0, 0.0), 50.0, 20.0));
}

#[test]
fn test_label_placer_fallback() {
    let mut placer = LabelPlacer::new(1.0);
    // T9: Set viewport for test to allow fallback positions
    placer.set_viewport(800.0, 600.0);

    // Place at primary position (center of viewport to allow fallbacks in all directions)
    placer.try_place(Vec2::new(300.0, 300.0), 50.0, 20.0);

    // Try to place overlapping - should use fallback
    let result = placer.try_place_with_fallback(
        Vec2::new(300.0, 300.0),
        50.0,
        20.0,
        Vec2::new(300.0, 310.0),
        5.0,
    );
    // Should find a fallback position
    assert!(result.is_some());
}

#[test]
fn test_rects_intersect() {
    let a = Rect::new(0.0, 0.0, 10.0, 10.0);
    let b = Rect::new(5.0, 5.0, 10.0, 10.0);
    let c = Rect::new(20.0, 20.0, 10.0, 10.0);

    assert!(rects_intersect(&a, &b));
    assert!(!rects_intersect(&a, &c));
}

// =============================================================================
// Level-of-Detail (LOD) Tests
// =============================================================================

#[test]
#[allow(clippy::assertions_on_constants)]
fn test_lod_constants_are_reasonable() {
    // Verify LOD constants are in sensible ranges for pixel-based thresholds

    // File radius threshold should be sub-pixel (< 1.0)
    assert!(
        LOD_MIN_FILE_RADIUS > 0.0,
        "File radius threshold must be positive"
    );
    assert!(
        LOD_MIN_FILE_RADIUS < 1.0,
        "File radius threshold should be sub-pixel"
    );

    // Directory radius threshold should be very small
    assert!(
        LOD_MIN_DIR_RADIUS > 0.0,
        "Dir radius threshold must be positive"
    );
    assert!(
        LOD_MIN_DIR_RADIUS < 1.0,
        "Dir radius threshold should be sub-pixel"
    );

    // Label thresholds should be larger than entity thresholds
    assert!(
        LOD_MIN_FILE_LABEL_RADIUS > LOD_MIN_FILE_RADIUS,
        "File label threshold should be larger than file threshold"
    );
    assert!(
        LOD_MIN_DIR_LABEL_RADIUS > LOD_MIN_DIR_RADIUS,
        "Dir label threshold should be larger than dir threshold"
    );
    assert!(
        LOD_MIN_USER_LABEL_RADIUS > LOD_MIN_USER_RADIUS,
        "User label threshold should be larger than user threshold"
    );

    // Label thresholds should be readable sizes (at least a few pixels)
    assert!(
        LOD_MIN_FILE_LABEL_RADIUS >= 2.0,
        "File labels should be at least 2px"
    );
    assert!(
        LOD_MIN_DIR_LABEL_RADIUS >= 2.0,
        "Dir labels should be at least 2px"
    );
    assert!(
        LOD_MIN_USER_LABEL_RADIUS >= 2.0,
        "User labels should be at least 2px"
    );

    // Zoom thresholds should be positive and less than 1.0
    assert!(
        LOD_MIN_ZOOM_FOR_FILE_BRANCHES > 0.0,
        "Branch zoom threshold must be positive"
    );
    assert!(
        LOD_MIN_ZOOM_FOR_FILE_BRANCHES < 1.0,
        "Branch zoom threshold should be less than 1.0"
    );
    assert!(
        LOD_MIN_ZOOM_FOR_DIR_BRANCHES > 0.0,
        "Dir branch zoom threshold must be positive"
    );
    assert!(
        LOD_MIN_ZOOM_FOR_DIR_BRANCHES < 1.0,
        "Dir branch zoom threshold should be less than 1.0"
    );
}

#[test]
fn test_lod_file_visibility_at_various_zoom_levels() {
    // Simulate LOD behavior at different zoom levels
    let file_world_radius = 5.0; // Typical file radius in world units

    // At zoom = 1.0, file should be visible (5px > 0.5px threshold)
    let zoom_normal = 1.0;
    let screen_radius_normal = file_world_radius * zoom_normal;
    assert!(
        screen_radius_normal >= LOD_MIN_FILE_RADIUS,
        "File visible at normal zoom"
    );

    // At zoom = 0.01, file should be invisible (0.05px < 0.5px threshold)
    let zoom_far = 0.01;
    let screen_radius_far = file_world_radius * zoom_far;
    assert!(
        screen_radius_far < LOD_MIN_FILE_RADIUS,
        "File culled at far zoom"
    );

    // At zoom = 0.1, file should be visible (0.5px = threshold)
    let zoom_threshold = LOD_MIN_FILE_RADIUS / file_world_radius;
    let screen_radius_threshold = file_world_radius * zoom_threshold;
    assert!(
        (screen_radius_threshold - LOD_MIN_FILE_RADIUS).abs() < 0.001,
        "File at exact threshold"
    );
}

#[test]
fn test_lod_label_visibility_separate_from_entity() {
    // Labels should disappear before entities
    let file_world_radius = 5.0;

    // Find zoom where file is visible but label is not
    let zoom_file_visible_label_hidden = LOD_MIN_FILE_LABEL_RADIUS / file_world_radius - 0.1;
    let screen_radius = file_world_radius * zoom_file_visible_label_hidden.max(0.0);

    // At this zoom, the file entity would be visible but label would be skipped
    // (assuming zoom is not too low)
    if zoom_file_visible_label_hidden > LOD_MIN_FILE_RADIUS / file_world_radius {
        assert!(
            screen_radius < LOD_MIN_FILE_LABEL_RADIUS,
            "Label should be hidden"
        );
        assert!(
            screen_radius >= LOD_MIN_FILE_RADIUS,
            "File should still be visible"
        );
    }
}

#[test]
#[allow(clippy::assertions_on_constants)]
fn test_lod_branch_rendering_zoom_thresholds() {
    // Verify branch rendering is controlled by zoom thresholds

    // File branches should render at normal zoom
    assert!(
        1.0 >= LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
        "File branches at normal zoom"
    );

    // File branches should not render at very low zoom
    assert!(
        0.01 < LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
        "File branches culled at very low zoom"
    );

    // Directory branches have lower threshold (more important structure)
    assert!(
        LOD_MIN_ZOOM_FOR_DIR_BRANCHES <= LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
        "Dir branches have lower (or equal) threshold than file branches"
    );
}
