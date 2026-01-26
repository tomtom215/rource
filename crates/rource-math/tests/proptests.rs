// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Property-based tests for rource-math.
//!
//! These tests verify mathematical invariants using proptest to generate
//! random inputs and ensure properties hold for all valid values.

use proptest::prelude::*;
use rource_math::{Color, Vec2, Vec3, EPSILON};

// =============================================================================
// Vec2 Property Tests
// =============================================================================

proptest! {
    /// Normalized vectors should have unit length (or be zero).
    #[test]
    fn vec2_normalize_preserves_direction(x in -1e3f32..1e3f32, y in -1e3f32..1e3f32) {
        let v = Vec2::new(x, y);
        let len = v.length();
        let n = v.normalized();

        if len > EPSILON * 10.0 {
            // Length should be approximately 1
            let normalized_len = n.length();
            prop_assert!(
                (normalized_len - 1.0).abs() < 1e-4,
                "Normalized length {} should be 1.0 for vector {:?}",
                normalized_len, v
            );

            // Direction should be preserved (dot product with original should equal original length)
            let dot = v.dot(n);
            // Use relative tolerance
            let tolerance = 1e-4 * len.max(1.0);
            prop_assert!(
                (dot - len).abs() < tolerance,
                "Dot product {} should equal length {} for {:?}",
                dot, len, v
            );
        } else {
            // Near-zero vector normalizes to zero or unit
            prop_assert!(n.length() <= 1.0 + EPSILON, "Normalized near-zero should be unit or zero");
        }
    }

    /// Perpendicular vectors should be orthogonal.
    #[test]
    fn vec2_perp_is_orthogonal(x in -1e6f32..1e6f32, y in -1e6f32..1e6f32) {
        let v = Vec2::new(x, y);
        let perp = v.perp();

        // Dot product of perpendicular vectors should be zero
        let dot = v.dot(perp);
        let tolerance = EPSILON * v.length() * perp.length();
        prop_assert!(
            dot.abs() < tolerance.max(EPSILON),
            "Perpendicular dot product {} should be ~0 for {:?}",
            dot, v
        );
    }

    /// Perpendicular preserves length.
    #[test]
    fn vec2_perp_preserves_length(x in -1e6f32..1e6f32, y in -1e6f32..1e6f32) {
        let v = Vec2::new(x, y);
        let perp = v.perp();

        prop_assert!(
            (v.length() - perp.length()).abs() < EPSILON,
            "Perp should preserve length: {} vs {}",
            v.length(), perp.length()
        );
    }

    /// Addition is commutative: a + b = b + a
    #[test]
    fn vec2_add_commutative(
        x1 in -1e6f32..1e6f32, y1 in -1e6f32..1e6f32,
        x2 in -1e6f32..1e6f32, y2 in -1e6f32..1e6f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let sum1 = a + b;
        let sum2 = b + a;

        prop_assert!(sum1.approx_eq(sum2), "{:?} + {:?} should be commutative", a, b);
    }

    /// Dot product is commutative: a.dot(b) = b.dot(a)
    #[test]
    fn vec2_dot_commutative(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let dot1 = a.dot(b);
        let dot2 = b.dot(a);

        prop_assert!(
            (dot1 - dot2).abs() < EPSILON,
            "Dot product should be commutative: {} vs {}",
            dot1, dot2
        );
    }

    /// Cross product is anti-commutative: a.cross(b) = -b.cross(a)
    #[test]
    fn vec2_cross_anticommutative(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let cross1 = a.cross(b);
        let cross2 = b.cross(a);

        prop_assert!(
            (cross1 + cross2).abs() < EPSILON,
            "Cross should be anti-commutative: {} vs {}",
            cross1, cross2
        );
    }

    /// Distance is symmetric: a.distance(b) = b.distance(a)
    #[test]
    fn vec2_distance_symmetric(
        x1 in -1e6f32..1e6f32, y1 in -1e6f32..1e6f32,
        x2 in -1e6f32..1e6f32, y2 in -1e6f32..1e6f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let d1 = a.distance(b);
        let d2 = b.distance(a);

        prop_assert!(
            (d1 - d2).abs() < EPSILON,
            "Distance should be symmetric: {} vs {}",
            d1, d2
        );
    }

    /// Distance is non-negative.
    #[test]
    fn vec2_distance_non_negative(
        x1 in -1e6f32..1e6f32, y1 in -1e6f32..1e6f32,
        x2 in -1e6f32..1e6f32, y2 in -1e6f32..1e6f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        prop_assert!(a.distance(b) >= 0.0, "Distance should be non-negative");
    }

    /// Lerp at t=0 returns start, at t=1 returns end.
    #[test]
    fn vec2_lerp_endpoints(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        // Lerp(0) should return start
        let lerp0 = a.lerp(b, 0.0);
        prop_assert!(
            (lerp0.x - a.x).abs() < EPSILON && (lerp0.y - a.y).abs() < EPSILON,
            "lerp(0) should return start: {:?} vs {:?}", lerp0, a
        );

        // Lerp(1) should return end (with tolerance for large values)
        let lerp1 = a.lerp(b, 1.0);
        let tolerance = 1e-4 * (b.x.abs().max(b.y.abs()).max(1.0));
        prop_assert!(
            (lerp1.x - b.x).abs() < tolerance && (lerp1.y - b.y).abs() < tolerance,
            "lerp(1) should return end: {:?} vs {:?}", lerp1, b
        );
    }

    /// Lerp at t=0.5 is the midpoint.
    #[test]
    fn vec2_lerp_midpoint(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let mid = a.lerp(b, 0.5);
        let expected = Vec2::new((x1 + x2) / 2.0, (y1 + y2) / 2.0);

        // Use relative tolerance for larger values
        let tolerance = 1e-4 * (expected.x.abs().max(expected.y.abs()).max(1.0));
        prop_assert!(
            (mid.x - expected.x).abs() < tolerance && (mid.y - expected.y).abs() < tolerance,
            "lerp(0.5) should be midpoint: {:?} vs {:?}",
            mid, expected
        );
    }

    /// Rotation by 2π returns to original.
    #[test]
    fn vec2_rotate_full_circle(x in -1e2f32..1e2f32, y in -1e2f32..1e2f32) {
        let v = Vec2::new(x, y);
        let rotated = v.rotate(std::f32::consts::TAU);

        // Use relative tolerance for larger values
        let tolerance = 1e-4 * (v.x.abs().max(v.y.abs()).max(1.0));
        prop_assert!(
            (v.x - rotated.x).abs() < tolerance && (v.y - rotated.y).abs() < tolerance,
            "Rotation by 2π should return to original: {:?} vs {:?}",
            v, rotated
        );
    }

    /// Rotation preserves length.
    #[test]
    fn vec2_rotate_preserves_length(
        x in -1e3f32..1e3f32,
        y in -1e3f32..1e3f32,
        angle in -10.0f32..10.0f32
    ) {
        let v = Vec2::new(x, y);
        let rotated = v.rotate(angle);

        // Relative tolerance for floating point
        let tolerance = 1e-4 * v.length().max(1.0);
        prop_assert!(
            (v.length() - rotated.length()).abs() < tolerance,
            "Rotation should preserve length: {} vs {}",
            v.length(), rotated.length()
        );
    }

    /// Negation is self-inverse: -(-v) = v
    #[test]
    fn vec2_neg_self_inverse(x in -1e6f32..1e6f32, y in -1e6f32..1e6f32) {
        let v = Vec2::new(x, y);
        prop_assert_eq!(-(-v), v, "Double negation should return original");
    }

    /// Reflect off horizontal surface preserves x, negates y.
    #[test]
    fn vec2_reflect_horizontal(x in -1e3f32..1e3f32, y in -1e3f32..1e3f32) {
        let v = Vec2::new(x, y);
        let normal = Vec2::Y;
        let reflected = v.reflect(normal);

        prop_assert!(
            (reflected.x - x).abs() < EPSILON,
            "Horizontal reflect should preserve x"
        );
        prop_assert!(
            (reflected.y + y).abs() < EPSILON,
            "Horizontal reflect should negate y"
        );
    }
}

// =============================================================================
// Vec3 Property Tests
// =============================================================================

proptest! {
    /// Normalized Vec3 vectors should have unit length (or be zero).
    #[test]
    fn vec3_normalize_unit_length(
        x in -1e6f32..1e6f32,
        y in -1e6f32..1e6f32,
        z in -1e6f32..1e6f32
    ) {
        let v = Vec3::new(x, y, z);
        let len = v.length();

        if len > EPSILON {
            let n = v.normalized();
            let normalized_len = n.length();

            prop_assert!(
                (normalized_len - 1.0).abs() < 1e-5,
                "Normalized length {} should be 1.0",
                normalized_len
            );
        } else {
            prop_assert_eq!(v.normalized(), Vec3::ZERO);
        }
    }

    /// Vec3 dot product is commutative.
    #[test]
    fn vec3_dot_commutative(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32, z1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32, z2 in -1e3f32..1e3f32
    ) {
        let a = Vec3::new(x1, y1, z1);
        let b = Vec3::new(x2, y2, z2);

        let dot1 = a.dot(b);
        let dot2 = b.dot(a);

        prop_assert!(
            (dot1 - dot2).abs() < EPSILON,
            "Dot product should be commutative"
        );
    }

    /// Vec3 cross product is anti-commutative.
    #[test]
    fn vec3_cross_anticommutative(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32, z1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32, z2 in -1e3f32..1e3f32
    ) {
        let a = Vec3::new(x1, y1, z1);
        let b = Vec3::new(x2, y2, z2);

        let cross1 = a.cross(b);
        let cross2 = b.cross(a);

        prop_assert!(
            cross1.approx_eq(-cross2),
            "Cross should be anti-commutative: {:?} vs {:?}",
            cross1, -cross2
        );
    }

    /// Cross product is perpendicular to both input vectors.
    #[test]
    fn vec3_cross_perpendicular(
        x1 in -1e2f32..1e2f32, y1 in -1e2f32..1e2f32, z1 in -1e2f32..1e2f32,
        x2 in -1e2f32..1e2f32, y2 in -1e2f32..1e2f32, z2 in -1e2f32..1e2f32
    ) {
        let a = Vec3::new(x1, y1, z1);
        let b = Vec3::new(x2, y2, z2);
        let cross = a.cross(b);

        // Cross product should be perpendicular to both a and b
        // Use relative tolerance based on input magnitudes
        let tolerance = 1e-3 * a.length() * b.length().max(1.0);

        prop_assert!(
            cross.dot(a).abs() < tolerance.max(1e-4),
            "Cross should be perpendicular to a: {}",
            cross.dot(a)
        );
        prop_assert!(
            cross.dot(b).abs() < tolerance.max(1e-4),
            "Cross should be perpendicular to b: {}",
            cross.dot(b)
        );
    }
}

// =============================================================================
// Color Property Tests
// =============================================================================

proptest! {
    /// Color::new preserves exact input values (no clamping).
    /// This is intentional for HDR support and intermediate calculations.
    #[test]
    fn color_new_preserves_values(
        r in -10.0f32..10.0f32,
        g in -10.0f32..10.0f32,
        b in -10.0f32..10.0f32,
        a in -10.0f32..10.0f32
    ) {
        let color = Color::new(r, g, b, a);

        prop_assert_eq!(color.r, r, "R should be preserved exactly");
        prop_assert_eq!(color.g, g, "G should be preserved exactly");
        prop_assert_eq!(color.b, b, "B should be preserved exactly");
        prop_assert_eq!(color.a, a, "A should be preserved exactly");
    }

    /// Color round-trip: RGBA8 -> Color -> RGBA8 should be exact.
    #[test]
    fn color_rgba8_roundtrip(r in 0u8..=255, g in 0u8..=255, b in 0u8..=255, a in 0u8..=255) {
        let color = Color::from_rgba8(r, g, b, a);
        let packed = color.to_rgba8();

        // Unpack and verify
        let recovered_r = ((packed >> 24) & 0xFF) as u8;
        let recovered_g = ((packed >> 16) & 0xFF) as u8;
        let recovered_b = ((packed >> 8) & 0xFF) as u8;
        let recovered_a = (packed & 0xFF) as u8;

        prop_assert_eq!(r, recovered_r, "Red channel round-trip failed");
        prop_assert_eq!(g, recovered_g, "Green channel round-trip failed");
        prop_assert_eq!(b, recovered_b, "Blue channel round-trip failed");
        prop_assert_eq!(a, recovered_a, "Alpha channel round-trip failed");
    }

    /// Color from RGB8 has alpha = 1.0.
    #[test]
    fn color_rgb8_has_full_alpha(r in 0u8..=255, g in 0u8..=255, b in 0u8..=255) {
        let color = Color::from_rgb8(r, g, b);
        prop_assert_eq!(color.a, 1.0, "RGB8 color should have alpha = 1.0");
    }

    /// Lerp between same color returns that color.
    #[test]
    fn color_lerp_same(
        r in 0.0f32..1.0f32,
        g in 0.0f32..1.0f32,
        b in 0.0f32..1.0f32,
        a in 0.0f32..1.0f32,
        t in 0.0f32..1.0f32
    ) {
        let color = Color::new(r, g, b, a);
        let lerped = color.lerp(color, t);

        prop_assert!(
            (lerped.r - color.r).abs() < EPSILON &&
            (lerped.g - color.g).abs() < EPSILON &&
            (lerped.b - color.b).abs() < EPSILON &&
            (lerped.a - color.a).abs() < EPSILON,
            "Lerp with same color should return that color"
        );
    }

    /// Color with_alpha preserves RGB.
    #[test]
    fn color_with_alpha_preserves_rgb(
        r in 0.0f32..1.0f32,
        g in 0.0f32..1.0f32,
        b in 0.0f32..1.0f32,
        a1 in 0.0f32..1.0f32,
        a2 in 0.0f32..1.0f32
    ) {
        let color = Color::new(r, g, b, a1);
        let modified = color.with_alpha(a2);

        prop_assert_eq!(color.r, modified.r, "with_alpha should preserve R");
        prop_assert_eq!(color.g, modified.g, "with_alpha should preserve G");
        prop_assert_eq!(color.b, modified.b, "with_alpha should preserve B");
        prop_assert_eq!(modified.a, a2.clamp(0.0, 1.0), "with_alpha should set A");
    }
}

// =============================================================================
// Mathematical Identity Tests
// =============================================================================

proptest! {
    /// Triangle inequality: |a + b| <= |a| + |b|
    #[test]
    fn vec2_triangle_inequality(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let sum_length = (a + b).length();
        let length_sum = a.length() + b.length();

        // Allow small epsilon for floating point
        prop_assert!(
            sum_length <= length_sum + EPSILON,
            "Triangle inequality violated: {} > {}",
            sum_length, length_sum
        );
    }

    /// Cauchy-Schwarz: |a.dot(b)| <= |a| * |b|
    #[test]
    fn vec2_cauchy_schwarz(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let dot_abs = a.dot(b).abs();
        let length_product = a.length() * b.length();

        prop_assert!(
            dot_abs <= length_product + EPSILON,
            "Cauchy-Schwarz violated: {} > {}",
            dot_abs, length_product
        );
    }

    /// Parallelogram law: |a + b|² + |a - b|² = 2(|a|² + |b|²)
    #[test]
    fn vec2_parallelogram_law(
        x1 in -1e2f32..1e2f32, y1 in -1e2f32..1e2f32,
        x2 in -1e2f32..1e2f32, y2 in -1e2f32..1e2f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let lhs = (a + b).length_squared() + (a - b).length_squared();
        let rhs = 2.0 * (a.length_squared() + b.length_squared());

        // Use relative tolerance
        let tolerance = 1e-4 * rhs.max(1.0);
        prop_assert!(
            (lhs - rhs).abs() < tolerance,
            "Parallelogram law violated: {} vs {}",
            lhs, rhs
        );
    }
}

// =============================================================================
// Determinism Tests
// =============================================================================

proptest! {
    /// Same inputs should produce identical outputs.
    #[test]
    fn vec2_deterministic(x in -1e6f32..1e6f32, y in -1e6f32..1e6f32) {
        let v1 = Vec2::new(x, y);
        let v2 = Vec2::new(x, y);

        prop_assert_eq!(v1.length(), v2.length(), "length() should be deterministic");
        prop_assert_eq!(v1.normalized(), v2.normalized(), "normalized() should be deterministic");
        prop_assert_eq!(v1.perp(), v2.perp(), "perp() should be deterministic");
    }

    /// Color operations should be deterministic.
    #[test]
    fn color_deterministic(r in 0u8..=255, g in 0u8..=255, b in 0u8..=255, a in 0u8..=255) {
        let c1 = Color::from_rgba8(r, g, b, a);
        let c2 = Color::from_rgba8(r, g, b, a);

        prop_assert_eq!(c1.to_argb8(), c2.to_argb8(), "Color conversion should be deterministic");
        prop_assert_eq!(c1.to_rgba8(), c2.to_rgba8(), "Color conversion should be deterministic");
    }
}
