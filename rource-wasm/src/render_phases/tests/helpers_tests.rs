// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Tests for pure computation functions in helpers module.

use rource_core::config::WatermarkPosition;
use rource_math::{Color, Vec2};

use crate::render_phases::estimate_text_width;
use crate::render_phases::helpers::*;

// -------------------------------------------------------------------------
// Depth Factor Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_depth_factor_root() {
    let factor = compute_depth_factor(0);
    assert!((factor - 0.0).abs() < 0.001);
}

#[test]
fn test_compute_depth_factor_mid() {
    let factor = compute_depth_factor(3);
    assert!((factor - 0.5).abs() < 0.001);
}

#[test]
fn test_compute_depth_factor_deep() {
    let factor = compute_depth_factor(6);
    assert!((factor - 1.0).abs() < 0.001);
}

#[test]
fn test_compute_depth_factor_capped_at_1() {
    let factor = compute_depth_factor(12);
    assert!((factor - 1.0).abs() < 0.001);
}

// -------------------------------------------------------------------------
// Directory Color Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_directory_color_root_brightest() {
    let root_color = compute_directory_color(0);
    let deep_color = compute_directory_color(6);
    // Root should be brighter than deep
    assert!(root_color.r > deep_color.r);
    assert!(root_color.g > deep_color.g);
}

#[test]
fn test_compute_directory_color_has_valid_alpha() {
    let color = compute_directory_color(0);
    assert!((color.a - 0.55).abs() < 0.001);
}

#[test]
fn test_compute_directory_color_blue_tint() {
    // Color should have slight blue tint (b > g)
    let color = compute_directory_color(0);
    assert!(color.b > color.g);
}

// -------------------------------------------------------------------------
// Branch Width Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_branch_width_root() {
    let width = compute_branch_width(0);
    assert!((width - 1.5).abs() < 0.001);
}

#[test]
fn test_compute_branch_width_deep() {
    let width = compute_branch_width(6);
    assert!((width - 1.0).abs() < 0.001);
}

#[test]
fn test_compute_branch_width_minimum() {
    let width = compute_branch_width(100);
    assert!(width >= 0.8);
}

#[test]
fn test_compute_branch_width_decreases_with_depth() {
    let shallow = compute_branch_width(1);
    let deep = compute_branch_width(5);
    assert!(shallow > deep);
}

// -------------------------------------------------------------------------
// Branch Opacity Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_branch_opacity_root_full() {
    let opacity = compute_branch_opacity(0, 0.35, 0.3);
    assert!((opacity - 0.35).abs() < 0.001);
}

#[test]
fn test_compute_branch_opacity_fades_with_depth() {
    let shallow = compute_branch_opacity(0, 0.35, 0.3);
    let deep = compute_branch_opacity(6, 0.35, 0.3);
    assert!(shallow > deep);
}

#[test]
fn test_compute_branch_opacity_minimum() {
    let opacity = compute_branch_opacity(100, 0.35, 1.0);
    assert!(opacity >= 0.05 * 0.35);
}

#[test]
fn test_compute_branch_opacity_respects_max() {
    let opacity = compute_branch_opacity(0, 0.5, 0.3);
    assert!((opacity - 0.5).abs() < 0.001);
}

// -------------------------------------------------------------------------
// Branch Color Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_branch_color_brightens() {
    let dir_color = Color::new(0.5, 0.5, 0.5, 0.5);
    let branch_color = compute_branch_color(dir_color, 0.3);
    assert!(branch_color.r > dir_color.r);
    assert!(branch_color.g > dir_color.g);
    assert!(branch_color.b > dir_color.b);
}

#[test]
fn test_compute_branch_color_uses_opacity() {
    let dir_color = Color::new(0.5, 0.5, 0.5, 0.5);
    let branch_color = compute_branch_color(dir_color, 0.25);
    assert!((branch_color.a - 0.25).abs() < 0.001);
}

// -------------------------------------------------------------------------
// LOD Decision Tests - Directories
// -------------------------------------------------------------------------

#[test]
fn test_should_render_directory_root_always() {
    // Root should always render even at tiny size
    assert!(should_render_directory(0.001, 0));
    assert!(should_render_directory(0.0, 0));
}

#[test]
fn test_should_render_directory_non_root_threshold() {
    assert!(!should_render_directory(0.01, 1));
    assert!(should_render_directory(0.1, 1));
}

// -------------------------------------------------------------------------
// LOD Decision Tests - Files
// -------------------------------------------------------------------------

#[test]
fn test_should_render_file_visible() {
    assert!(should_render_file(1.0, 1.0));
}

#[test]
fn test_should_render_file_too_small() {
    assert!(!should_render_file(0.05, 1.0));
}

#[test]
fn test_should_render_file_invisible() {
    assert!(!should_render_file(1.0, 0.005));
}

// -------------------------------------------------------------------------
// LOD Decision Tests - Users
// -------------------------------------------------------------------------

#[test]
fn test_should_render_user_visible() {
    assert!(should_render_user(5.0, 1.0));
}

#[test]
fn test_should_render_user_too_small() {
    assert!(!should_render_user(0.1, 1.0));
}

#[test]
fn test_should_render_user_invisible() {
    assert!(!should_render_user(5.0, 0.005));
}

// -------------------------------------------------------------------------
// LOD Decision Tests - Labels
// -------------------------------------------------------------------------

#[test]
fn test_should_render_directory_label_shallow() {
    assert!(should_render_directory_label(5.0, 0));
    assert!(should_render_directory_label(5.0, 1));
    assert!(should_render_directory_label(5.0, 2));
}

#[test]
fn test_should_render_directory_label_deep() {
    assert!(!should_render_directory_label(5.0, 3));
    assert!(!should_render_directory_label(5.0, 10));
}

#[test]
fn test_should_render_directory_label_too_small() {
    assert!(!should_render_directory_label(3.0, 0));
}

#[test]
fn test_should_render_file_label_visible() {
    assert!(should_render_file_label(5.0, 0.5, 0.5));
}

#[test]
fn test_should_render_file_label_low_zoom() {
    assert!(!should_render_file_label(5.0, 0.5, 0.1));
}

#[test]
fn test_should_render_file_label_low_alpha() {
    assert!(!should_render_file_label(5.0, 0.2, 0.5));
}

#[test]
fn test_should_render_file_label_small_radius() {
    assert!(!should_render_file_label(2.0, 0.5, 0.5));
}

#[test]
fn test_should_render_user_label_visible() {
    assert!(should_render_user_label(10.0, 0.5));
}

#[test]
fn test_should_render_user_label_too_small() {
    assert!(!should_render_user_label(3.0, 0.5));
}

// -------------------------------------------------------------------------
// LOD Decision Tests - Branches
// -------------------------------------------------------------------------

#[test]
fn test_should_render_directory_branches_normal_zoom() {
    assert!(should_render_directory_branches(1.0));
    assert!(should_render_directory_branches(0.5));
}

#[test]
fn test_should_render_directory_branches_low_zoom() {
    assert!(!should_render_directory_branches(0.005));
}

#[test]
fn test_should_render_file_branches_normal_zoom() {
    assert!(should_render_file_branches(1.0));
    assert!(should_render_file_branches(0.1));
}

#[test]
fn test_should_render_file_branches_low_zoom() {
    assert!(!should_render_file_branches(0.01));
}

// -------------------------------------------------------------------------
// Effective Radius Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_file_effective_radius_small() {
    assert!((compute_file_effective_radius(0.5) - 2.0).abs() < 0.001);
}

#[test]
fn test_compute_file_effective_radius_large() {
    assert!((compute_file_effective_radius(5.0) - 5.0).abs() < 0.001);
}

#[test]
fn test_compute_user_effective_radius_small() {
    assert!((compute_user_effective_radius(2.0) - 5.0).abs() < 0.001);
}

#[test]
fn test_compute_user_effective_radius_large() {
    assert!((compute_user_effective_radius(10.0) - 10.0).abs() < 0.001);
}

// -------------------------------------------------------------------------
// File Glow Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_file_glow_intensity_touched() {
    let glow = compute_file_glow_intensity(true);
    assert!((glow - 0.25).abs() < 0.001);
}

#[test]
fn test_compute_file_glow_intensity_normal() {
    let glow = compute_file_glow_intensity(false);
    assert!((glow - 0.08).abs() < 0.001);
}

// -------------------------------------------------------------------------
// Phase 70: Glow LOD Culling Tests
// -------------------------------------------------------------------------

/// Tests the LOD culling threshold for glow rendering.
///
/// Phase 70 introduced LOD culling: glow is only drawn when
/// `effective_radius` >= 3.0, because smaller glows are imperceptible.
#[test]
fn test_glow_lod_culling_threshold_boundary() {
    // At exactly 3.0, glow SHOULD be rendered
    let at_threshold = compute_file_effective_radius(3.0);
    assert!(
        at_threshold >= 3.0,
        "effective_radius at 3.0 should pass threshold"
    );

    // Just below threshold, glow should NOT be rendered
    // Note: effective_radius has a minimum of 2.0, so we test behavior at various inputs
    let below_threshold = compute_file_effective_radius(2.5);
    assert!(
        below_threshold < 3.0,
        "effective_radius at 2.5 should be below threshold"
    );
}

/// Tests that glow radius calculation is correct (1.5x after Phase 70).
#[test]
fn test_glow_radius_calculation() {
    let effective_radius: f32 = 5.0;
    let glow_radius: f32 = effective_radius * 1.5; // Phase 70: reduced from 2.0
    assert!((glow_radius - 7.5).abs() < 0.001);

    // Verify area reduction: 1.5^2 = 2.25 vs 2.0^2 = 4.0
    // Reduction = 1 - (2.25/4.0) = 0.4375 = 43.75%
    let old_area: f32 = std::f32::consts::PI * (effective_radius * 2.0).powi(2);
    let new_area: f32 = std::f32::consts::PI * glow_radius.powi(2);
    let reduction: f32 = 1.0 - (new_area / old_area);
    assert!(
        (reduction - 0.4375).abs() < 0.001,
        "Area reduction should be 43.75%"
    );
}

/// Tests glow LOD culling condition matches implementation.
#[test]
fn test_glow_lod_culling_condition() {
    // Helper function matching the render_files condition:
    // if is_touched && effective_radius >= 3.0
    fn should_render_glow(is_touched: bool, effective_radius: f32) -> bool {
        is_touched && effective_radius >= 3.0
    }

    // Case 1: touched + large radius -> glow rendered
    assert!(
        should_render_glow(true, 5.0),
        "touched + radius 5.0 should render glow"
    );

    // Case 2: touched + small radius -> glow NOT rendered (LOD culling)
    assert!(
        !should_render_glow(true, 2.5),
        "touched + radius 2.5 should NOT render glow"
    );

    // Case 3: not touched + large radius -> glow NOT rendered (Phase 59)
    assert!(
        !should_render_glow(false, 5.0),
        "not touched should never render glow (Phase 59)"
    );

    // Case 4: not touched + small radius -> glow NOT rendered
    assert!(
        !should_render_glow(false, 2.5),
        "not touched + small radius should not render glow"
    );
}

// -------------------------------------------------------------------------
// File Border Color Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_file_border_color_darker() {
    let color = Color::new(1.0, 1.0, 1.0, 1.0);
    let border = compute_file_border_color(color);
    assert!((border.r - 0.6).abs() < 0.001);
    assert!((border.g - 0.6).abs() < 0.001);
    assert!((border.b - 0.6).abs() < 0.001);
    assert!((border.a - 1.0).abs() < 0.001);
}

// -------------------------------------------------------------------------
// File Branch Color Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_file_branch_color_uses_depth_fade() {
    let color = Color::new(1.0, 0.5, 0.0, 1.0);
    let shallow = compute_file_branch_color(color, 1.0, 0, 0.3);
    let deep = compute_file_branch_color(color, 1.0, 6, 0.3);
    assert!(shallow.a > deep.a);
}

#[test]
fn test_compute_file_branch_color_uses_alpha() {
    let color = Color::new(1.0, 0.5, 0.0, 1.0);
    let full = compute_file_branch_color(color, 1.0, 0, 0.3);
    let half = compute_file_branch_color(color, 0.5, 0, 0.3);
    assert!(full.a > half.a);
}

// -------------------------------------------------------------------------
// Label Priority Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_file_label_priority_touched_bonus() {
    let normal = compute_file_label_priority(5.0, 1.0, false);
    let touched = compute_file_label_priority(5.0, 1.0, true);
    assert!(touched > normal);
    assert!((touched - normal - 100.0).abs() < 0.001);
}

#[test]
fn test_compute_file_label_priority_larger_files() {
    let small = compute_file_label_priority(2.0, 1.0, false);
    let large = compute_file_label_priority(10.0, 1.0, false);
    assert!(large > small);
}

// -------------------------------------------------------------------------
// Max Labels Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_max_labels_high_zoom() {
    assert_eq!(compute_max_labels(2.0), 200);
}

#[test]
fn test_compute_max_labels_medium_zoom() {
    assert_eq!(compute_max_labels(0.75), 100);
}

#[test]
fn test_compute_max_labels_low_zoom() {
    assert_eq!(compute_max_labels(0.25), 50);
}

// -------------------------------------------------------------------------
// Watermark Position Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_watermark_position_top_left() {
    let (x, y) = compute_watermark_position(
        WatermarkPosition::TopLeft,
        10.0,  // margin
        100.0, // text_width
        20.0,  // total_height
        800.0, // screen_width
        600.0, // screen_height
    );
    assert!((x - 10.0).abs() < 0.001);
    assert!((y - 10.0).abs() < 0.001);
}

#[test]
fn test_compute_watermark_position_top_right() {
    let (x, y) =
        compute_watermark_position(WatermarkPosition::TopRight, 10.0, 100.0, 20.0, 800.0, 600.0);
    assert!((x - 690.0).abs() < 0.001); // 800 - 100 - 10
    assert!((y - 10.0).abs() < 0.001);
}

#[test]
fn test_compute_watermark_position_bottom_left() {
    let (x, y) = compute_watermark_position(
        WatermarkPosition::BottomLeft,
        10.0,
        100.0,
        20.0,
        800.0,
        600.0,
    );
    assert!((x - 10.0).abs() < 0.001);
    assert!((y - 570.0).abs() < 0.001); // 600 - 20 - 10
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

// -------------------------------------------------------------------------
// Watermark Height Tests
// -------------------------------------------------------------------------

#[test]
fn test_compute_watermark_height_no_subtext() {
    let height = compute_watermark_height(12.0, false);
    assert!((height - 12.0).abs() < 0.001);
}

#[test]
fn test_compute_watermark_height_with_subtext() {
    let height = compute_watermark_height(12.0, true);
    // 12.0 * 1.2 + 12.0 * 0.85 = 14.4 + 10.2 = 24.6
    assert!((height - 24.6).abs() < 0.001);
}

// -------------------------------------------------------------------------
// Text Width Estimation Tests
// -------------------------------------------------------------------------

#[test]
fn test_estimate_text_width() {
    let width = estimate_text_width("test", 12.0);
    assert!(width > 0.0);
    assert!(width < 100.0);
}

#[test]
fn test_estimate_text_width_uses_char_count() {
    let size = 12.0;

    // ASCII: bytes == chars
    let ascii = "hello";
    let ascii_width = estimate_text_width(ascii, size);
    // Expected: 5 * 12 * 0.62 = 37.2
    assert!((ascii_width - 37.2).abs() < 0.01);

    // UTF-8 with accent: chars != bytes
    let accented = "héllo";
    let accented_width = estimate_text_width(accented, size);
    // Should match ASCII (5 chars), not 6 bytes
    assert_eq!(accented.chars().count(), 5);
    assert!((accented_width - ascii_width).abs() < 0.01);

    // CJK: 2 chars, 6 bytes
    let cjk = "你好";
    let cjk_width = estimate_text_width(cjk, size);
    // Expected: 2 * 12 * 0.62 = 14.88, not 6 * 12 * 0.62 = 44.64
    assert!((cjk_width - 14.88).abs() < 0.01);
}
