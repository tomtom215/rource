// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Property-based tests for rource-math.
//!
//! These tests verify mathematical invariants using proptest to generate
//! random inputs and ensure properties hold for all valid values.

use proptest::prelude::*;
use rource_math::{Color, Mat3, Mat4, Vec2, Vec3, Vec4, EPSILON};

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
    ///
    /// Uses relative epsilon to account for floating-point precision limits.
    /// For f32, machine epsilon ≈ 1.19e-7, so values with magnitude M have
    /// precision limit of approximately M * 1.19e-7. We use 1e-5 relative
    /// tolerance to account for accumulated errors from sqrt operations.
    #[test]
    fn vec2_triangle_inequality(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let sum_length = (a + b).length();
        let length_sum = a.length() + b.length();

        // Use relative epsilon that scales with magnitude, plus small absolute epsilon
        // for near-zero cases. The 1e-5 factor accounts for accumulated rounding in
        // multiple sqrt() calls and additions.
        let tolerance = length_sum * 1e-5 + EPSILON;
        prop_assert!(
            sum_length <= length_sum + tolerance,
            "Triangle inequality violated: {} > {} (tolerance: {})",
            sum_length, length_sum, tolerance
        );
    }

    /// Cauchy-Schwarz: |a.dot(b)| <= |a| * |b|
    ///
    /// Uses relative epsilon since length_product can reach ~1e6 for vectors
    /// with magnitude ~1e3, where absolute epsilon 1e-6 is insufficient.
    #[test]
    fn vec2_cauchy_schwarz(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32
    ) {
        let a = Vec2::new(x1, y1);
        let b = Vec2::new(x2, y2);

        let dot_abs = a.dot(b).abs();
        let length_product = a.length() * b.length();

        // Use relative epsilon that scales with magnitude
        let tolerance = length_product * 1e-5 + EPSILON;
        prop_assert!(
            dot_abs <= length_product + tolerance,
            "Cauchy-Schwarz violated: {} > {} (tolerance: {})",
            dot_abs, length_product, tolerance
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

// =============================================================================
// Vec4 Property Tests (TST-2)
// =============================================================================

proptest! {
    /// Vec4 normalized vectors should have unit length (or be zero).
    #[test]
    fn vec4_normalize_unit_length(
        x in -1e3f32..1e3f32,
        y in -1e3f32..1e3f32,
        z in -1e3f32..1e3f32,
        w in -1e3f32..1e3f32
    ) {
        let v = Vec4::new(x, y, z, w);
        let len = v.length();

        if len > EPSILON * 10.0 {
            let n = v.normalized();
            let normalized_len = n.length();

            prop_assert!(
                (normalized_len - 1.0).abs() < 1e-4,
                "Normalized length {} should be 1.0 for {:?}",
                normalized_len, v
            );
        }
    }

    /// Vec4 dot product is commutative: a.dot(b) = b.dot(a)
    #[test]
    fn vec4_dot_commutative(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32, z1 in -1e3f32..1e3f32, w1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32, z2 in -1e3f32..1e3f32, w2 in -1e3f32..1e3f32
    ) {
        let a = Vec4::new(x1, y1, z1, w1);
        let b = Vec4::new(x2, y2, z2, w2);

        let dot1 = a.dot(b);
        let dot2 = b.dot(a);

        prop_assert!(
            (dot1 - dot2).abs() < EPSILON * 10.0,
            "Dot product should be commutative: {} vs {}",
            dot1, dot2
        );
    }

    /// Vec4 addition is commutative: a + b = b + a
    #[test]
    fn vec4_add_commutative(
        x1 in -1e6f32..1e6f32, y1 in -1e6f32..1e6f32, z1 in -1e6f32..1e6f32, w1 in -1e6f32..1e6f32,
        x2 in -1e6f32..1e6f32, y2 in -1e6f32..1e6f32, z2 in -1e6f32..1e6f32, w2 in -1e6f32..1e6f32
    ) {
        let a = Vec4::new(x1, y1, z1, w1);
        let b = Vec4::new(x2, y2, z2, w2);

        let sum1 = a + b;
        let sum2 = b + a;

        prop_assert!(sum1.approx_eq(sum2), "{:?} + {:?} should be commutative", a, b);
    }

    /// Vec4 negation is self-inverse: -(-v) = v
    #[test]
    fn vec4_neg_self_inverse(
        x in -1e6f32..1e6f32,
        y in -1e6f32..1e6f32,
        z in -1e6f32..1e6f32,
        w in -1e6f32..1e6f32
    ) {
        let v = Vec4::new(x, y, z, w);
        prop_assert_eq!(-(-v), v, "Double negation should return original");
    }

    /// Vec4 lerp at t=0 returns start, at t=1 returns end.
    #[test]
    fn vec4_lerp_endpoints(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32, z1 in -1e3f32..1e3f32, w1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32, z2 in -1e3f32..1e3f32, w2 in -1e3f32..1e3f32
    ) {
        let a = Vec4::new(x1, y1, z1, w1);
        let b = Vec4::new(x2, y2, z2, w2);

        // Helper to check approximate equality with relative tolerance
        let approx_eq_rel = |v1: Vec4, v2: Vec4| -> bool {
            let tolerance = 1e-5 * (v1.length().max(v2.length()).max(1.0));
            (v1.x - v2.x).abs() < tolerance &&
            (v1.y - v2.y).abs() < tolerance &&
            (v1.z - v2.z).abs() < tolerance &&
            (v1.w - v2.w).abs() < tolerance
        };

        // Lerp(0) should return start
        let lerp0 = a.lerp(b, 0.0);
        prop_assert!(
            approx_eq_rel(lerp0, a),
            "lerp(0) should return start: {:?} vs {:?}",
            lerp0, a
        );

        // Lerp(1) should return end
        let lerp1 = a.lerp(b, 1.0);
        prop_assert!(
            approx_eq_rel(lerp1, b),
            "lerp(1) should return end: {:?} vs {:?}",
            lerp1, b
        );
    }

    /// Vec4 distance is symmetric: distance(a, b) = distance(b, a)
    /// Computes distance as (a - b).length()
    #[test]
    fn vec4_distance_symmetric(
        x1 in -1e3f32..1e3f32, y1 in -1e3f32..1e3f32, z1 in -1e3f32..1e3f32, w1 in -1e3f32..1e3f32,
        x2 in -1e3f32..1e3f32, y2 in -1e3f32..1e3f32, z2 in -1e3f32..1e3f32, w2 in -1e3f32..1e3f32
    ) {
        let a = Vec4::new(x1, y1, z1, w1);
        let b = Vec4::new(x2, y2, z2, w2);

        // Compute distance manually: distance = |a - b|
        let d1 = (a - b).length();
        let d2 = (b - a).length();

        prop_assert!(
            (d1 - d2).abs() < EPSILON,
            "Distance should be symmetric: {} vs {}",
            d1, d2
        );
    }

    /// Vec4 triangle inequality: |a + b| <= |a| + |b|
    #[test]
    fn vec4_triangle_inequality(
        x1 in -1e2f32..1e2f32, y1 in -1e2f32..1e2f32, z1 in -1e2f32..1e2f32, w1 in -1e2f32..1e2f32,
        x2 in -1e2f32..1e2f32, y2 in -1e2f32..1e2f32, z2 in -1e2f32..1e2f32, w2 in -1e2f32..1e2f32
    ) {
        let a = Vec4::new(x1, y1, z1, w1);
        let b = Vec4::new(x2, y2, z2, w2);

        let sum_length = (a + b).length();
        let length_sum = a.length() + b.length();

        let tolerance = length_sum * 1e-5 + EPSILON;
        prop_assert!(
            sum_length <= length_sum + tolerance,
            "Triangle inequality violated: {} > {} (tolerance: {})",
            sum_length, length_sum, tolerance
        );
    }

    /// Vec4 Cauchy-Schwarz: |a.dot(b)| <= |a| * |b|
    #[test]
    fn vec4_cauchy_schwarz(
        x1 in -1e2f32..1e2f32, y1 in -1e2f32..1e2f32, z1 in -1e2f32..1e2f32, w1 in -1e2f32..1e2f32,
        x2 in -1e2f32..1e2f32, y2 in -1e2f32..1e2f32, z2 in -1e2f32..1e2f32, w2 in -1e2f32..1e2f32
    ) {
        let a = Vec4::new(x1, y1, z1, w1);
        let b = Vec4::new(x2, y2, z2, w2);

        let dot_abs = a.dot(b).abs();
        let length_product = a.length() * b.length();

        let tolerance = length_product * 1e-5 + EPSILON;
        prop_assert!(
            dot_abs <= length_product + tolerance,
            "Cauchy-Schwarz violated: {} > {} (tolerance: {})",
            dot_abs, length_product, tolerance
        );
    }
}

// =============================================================================
// Mat3 Property Tests (TST-2)
// =============================================================================

proptest! {
    /// Mat3 identity property: A * I = A and I * A = A
    #[test]
    fn mat3_identity_property(
        c0r0 in -1e2f32..1e2f32, c0r1 in -1e2f32..1e2f32, c0r2 in -1e2f32..1e2f32,
        c1r0 in -1e2f32..1e2f32, c1r1 in -1e2f32..1e2f32, c1r2 in -1e2f32..1e2f32,
        c2r0 in -1e2f32..1e2f32, c2r1 in -1e2f32..1e2f32, c2r2 in -1e2f32..1e2f32
    ) {
        let a = Mat3::new(c0r0, c0r1, c0r2, c1r0, c1r1, c1r2, c2r0, c2r1, c2r2);
        let identity = Mat3::IDENTITY;

        let ai = a * identity;
        let ia = identity * a;

        prop_assert!(ai.approx_eq(a), "A * I should equal A");
        prop_assert!(ia.approx_eq(a), "I * A should equal A");
    }

    /// Mat3 inverse property: A * A^-1 = I (for invertible matrices)
    #[test]
    fn mat3_inverse_property(
        tx in -1e2f32..1e2f32,
        ty in -1e2f32..1e2f32,
        angle in -10.0f32..10.0f32,
        sx in 0.1f32..10.0f32,
        sy in 0.1f32..10.0f32
    ) {
        // Build a guaranteed invertible matrix from TRS
        let t = Mat3::translation(tx, ty);
        let r = Mat3::rotation(angle);
        let s = Mat3::scaling(sx, sy);
        let a = t * r * s;

        if let Some(a_inv) = a.inverse() {
            let product = a * a_inv;
            // Use looser tolerance due to accumulated floating-point errors in TRS composition
            let is_identity = product.m.iter().enumerate().all(|(i, &v)| {
                let expected = if i % 4 == 0 { 1.0 } else { 0.0 }; // diagonal is 1, rest is 0
                (v - expected).abs() < 1e-4
            });
            prop_assert!(
                is_identity,
                "A * A^-1 should equal identity for invertible matrix: {:?}",
                product.m
            );
        }
    }

    /// Mat3 transpose of transpose equals original: (A^T)^T = A
    #[test]
    fn mat3_transpose_self_inverse(
        c0r0 in -1e3f32..1e3f32, c0r1 in -1e3f32..1e3f32, c0r2 in -1e3f32..1e3f32,
        c1r0 in -1e3f32..1e3f32, c1r1 in -1e3f32..1e3f32, c1r2 in -1e3f32..1e3f32,
        c2r0 in -1e3f32..1e3f32, c2r1 in -1e3f32..1e3f32, c2r2 in -1e3f32..1e3f32
    ) {
        let a = Mat3::new(c0r0, c0r1, c0r2, c1r0, c1r1, c1r2, c2r0, c2r1, c2r2);
        let double_transpose = a.transpose().transpose();

        prop_assert!(double_transpose.approx_eq(a), "(A^T)^T should equal A");
    }

    /// Mat3 rotation preserves length (orthogonal matrix)
    #[test]
    fn mat3_rotation_preserves_length(
        angle in -10.0f32..10.0f32,
        x in -1e3f32..1e3f32,
        y in -1e3f32..1e3f32
    ) {
        let r = Mat3::rotation(angle);
        let v = Vec2::new(x, y);
        let rotated = r.transform_vector(v);

        let tolerance = 1e-4 * v.length().max(1.0);
        prop_assert!(
            (v.length() - rotated.length()).abs() < tolerance,
            "Rotation should preserve length: {} vs {}",
            v.length(), rotated.length()
        );
    }

    /// Mat3 determinant of identity is 1
    #[test]
    fn mat3_identity_determinant(_ignored in 0..1u8) {
        prop_assert_eq!(Mat3::IDENTITY.determinant(), 1.0, "det(I) should be 1");
    }

    /// Mat3 determinant of rotation is 1 (orthogonal matrix)
    #[test]
    fn mat3_rotation_determinant(angle in -10.0f32..10.0f32) {
        let r = Mat3::rotation(angle);
        prop_assert!(
            (r.determinant() - 1.0).abs() < EPSILON,
            "det(rotation) should be 1, got {}",
            r.determinant()
        );
    }

    /// Mat3 transform_point then inverse returns original
    #[test]
    fn mat3_transform_point_inverse_roundtrip(
        tx in -1e2f32..1e2f32,
        ty in -1e2f32..1e2f32,
        px in -1e2f32..1e2f32,
        py in -1e2f32..1e2f32
    ) {
        let t = Mat3::translation(tx, ty);
        let p = Vec2::new(px, py);

        let transformed = t.transform_point(p);
        if let Some(t_inv) = t.inverse() {
            let recovered = t_inv.transform_point(transformed);
            let tolerance = 1e-4 * p.length().max(1.0);
            prop_assert!(
                (p.x - recovered.x).abs() < tolerance && (p.y - recovered.y).abs() < tolerance,
                "Transform then inverse should recover original: {:?} vs {:?}",
                p, recovered
            );
        }
    }
}

// =============================================================================
// Mat4 Property Tests (TST-2)
// =============================================================================

proptest! {
    /// Mat4 identity property: A * I = A and I * A = A
    #[test]
    fn mat4_identity_property(
        tx in -1e2f32..1e2f32,
        ty in -1e2f32..1e2f32,
        tz in -1e2f32..1e2f32
    ) {
        let a = Mat4::translation(tx, ty, tz);
        let identity = Mat4::IDENTITY;

        let ai = a * identity;
        let ia = identity * a;

        prop_assert!(ai.approx_eq(a), "A * I should equal A");
        prop_assert!(ia.approx_eq(a), "I * A should equal A");
    }

    /// Mat4 multiplication associativity: (A * B) * C = A * (B * C)
    ///
    /// Note: Uses tolerance due to floating-point accumulation across multiple operations.
    #[test]
    fn mat4_mul_associative(
        tx1 in -10.0f32..10.0f32, ty1 in -10.0f32..10.0f32, tz1 in -10.0f32..10.0f32,
        tx2 in -10.0f32..10.0f32, ty2 in -10.0f32..10.0f32, tz2 in -10.0f32..10.0f32,
        sx in 0.5f32..2.0f32, sy in 0.5f32..2.0f32, sz in 0.5f32..2.0f32
    ) {
        let a = Mat4::translation(tx1, ty1, tz1);
        let b = Mat4::scaling(sx, sy, sz);
        let c = Mat4::translation(tx2, ty2, tz2);

        let ab_c = (a * b) * c;
        let a_bc = a * (b * c);

        // Allow for accumulated floating-point errors
        let matrices_close = ab_c.m.iter().zip(a_bc.m.iter()).all(|(x, y)| {
            let diff = (x - y).abs();
            diff < 1e-4 * x.abs().max(y.abs()).max(1.0)
        });

        prop_assert!(
            matrices_close,
            "Matrix multiplication should be associative:\n(A*B)*C: {:?}\nA*(B*C): {:?}",
            ab_c.m, a_bc.m
        );
    }

    /// Mat4 inverse property: A * A^-1 = I (for invertible matrices)
    #[test]
    fn mat4_inverse_property(
        tx in -1e2f32..1e2f32,
        ty in -1e2f32..1e2f32,
        tz in -1e2f32..1e2f32,
        sx in 0.1f32..10.0f32,
        sy in 0.1f32..10.0f32,
        sz in 0.1f32..10.0f32
    ) {
        // Build a guaranteed invertible matrix
        let t = Mat4::translation(tx, ty, tz);
        let s = Mat4::scaling(sx, sy, sz);
        let a = t * s;

        if let Some(a_inv) = a.inverse() {
            let product = a * a_inv;
            // Use looser tolerance due to accumulated floating-point errors
            let is_identity = product.m.iter().enumerate().all(|(i, &v)| {
                let expected = if i % 5 == 0 { 1.0 } else { 0.0 }; // diagonal at 0, 5, 10, 15
                (v - expected).abs() < 1e-4
            });
            prop_assert!(
                is_identity,
                "A * A^-1 should equal identity: {:?}",
                product.m
            );
        }
    }

    /// Mat4 transpose of transpose equals original: (A^T)^T = A
    #[test]
    fn mat4_transpose_self_inverse(
        tx in -1e2f32..1e2f32,
        ty in -1e2f32..1e2f32,
        tz in -1e2f32..1e2f32
    ) {
        let a = Mat4::translation(tx, ty, tz);
        let double_transpose = a.transpose().transpose();

        prop_assert!(double_transpose.approx_eq(a), "(A^T)^T should equal A");
    }

    /// Mat4 determinant of identity is 1
    #[test]
    fn mat4_identity_determinant(_ignored in 0..1u8) {
        prop_assert_eq!(Mat4::IDENTITY.determinant(), 1.0, "det(I) should be 1");
    }

    /// Mat4 determinant of scaling equals product of scale factors
    #[test]
    fn mat4_scaling_determinant(
        sx in 0.1f32..10.0f32,
        sy in 0.1f32..10.0f32,
        sz in 0.1f32..10.0f32
    ) {
        let s = Mat4::scaling(sx, sy, sz);
        let expected_det = sx * sy * sz;
        let tolerance = 1e-4 * expected_det.abs().max(1.0);

        prop_assert!(
            (s.determinant() - expected_det).abs() < tolerance,
            "det(scaling) should be sx*sy*sz: {} vs {}",
            s.determinant(), expected_det
        );
    }

    /// Mat4 rotation preserves length (orthogonal matrix)
    #[test]
    fn mat4_rotation_preserves_length(
        angle in -10.0f32..10.0f32,
        x in -1e2f32..1e2f32,
        y in -1e2f32..1e2f32,
        z in -1e2f32..1e2f32
    ) {
        let r = Mat4::rotation_z(angle);
        let v = Vec3::new(x, y, z);
        let rotated = r.transform_vector(v);

        let tolerance = 1e-4 * v.length().max(1.0);
        prop_assert!(
            (v.length() - rotated.length()).abs() < tolerance,
            "Rotation should preserve length: {} vs {}",
            v.length(), rotated.length()
        );
    }

    /// Mat4 transform_point then inverse returns original
    #[test]
    fn mat4_transform_point_inverse_roundtrip(
        tx in -1e2f32..1e2f32,
        ty in -1e2f32..1e2f32,
        tz in -1e2f32..1e2f32,
        px in -1e2f32..1e2f32,
        py in -1e2f32..1e2f32,
        pz in -1e2f32..1e2f32
    ) {
        let t = Mat4::translation(tx, ty, tz);
        let p = Vec3::new(px, py, pz);

        let transformed = t.transform_point(p);
        if let Some(t_inv) = t.inverse() {
            let recovered = t_inv.transform_point(transformed);
            // Use relative tolerance based on point magnitude
            let tolerance = 1e-4 * (p.length() + transformed.length()).max(1.0);
            prop_assert!(
                (p.x - recovered.x).abs() < tolerance &&
                (p.y - recovered.y).abs() < tolerance &&
                (p.z - recovered.z).abs() < tolerance,
                "Transform then inverse should recover original: {:?} vs {:?} (tolerance: {})",
                p, recovered, tolerance
            );
        }
    }

    /// Mat4 rotation determinant is 1
    #[test]
    fn mat4_rotation_determinant(angle in -10.0f32..10.0f32) {
        let rx = Mat4::rotation_x(angle);
        let ry = Mat4::rotation_y(angle);
        let rz = Mat4::rotation_z(angle);

        prop_assert!(
            (rx.determinant() - 1.0).abs() < EPSILON,
            "det(rotation_x) should be 1, got {}",
            rx.determinant()
        );
        prop_assert!(
            (ry.determinant() - 1.0).abs() < EPSILON,
            "det(rotation_y) should be 1, got {}",
            ry.determinant()
        );
        prop_assert!(
            (rz.determinant() - 1.0).abs() < EPSILON,
            "det(rotation_z) should be 1, got {}",
            rz.determinant()
        );
    }
}

// =============================================================================
// Additional Color Property Tests (TST-2)
// =============================================================================

proptest! {
    /// Color ARGB8 round-trip: to_argb8 -> unpack should preserve values.
    /// ARGB8 format is 0xAARRGGBB.
    #[test]
    fn color_argb8_roundtrip(r in 0u8..=255, g in 0u8..=255, b in 0u8..=255, a in 0u8..=255) {
        let color = Color::from_rgba8(r, g, b, a);
        let packed = color.to_argb8();

        // Manually unpack ARGB8 (0xAARRGGBB)
        let unpacked_a = ((packed >> 24) & 0xFF) as u8;
        let unpacked_r = ((packed >> 16) & 0xFF) as u8;
        let unpacked_g = ((packed >> 8) & 0xFF) as u8;
        let unpacked_b = (packed & 0xFF) as u8;
        let unpacked = Color::from_rgba8(unpacked_r, unpacked_g, unpacked_b, unpacked_a);

        // Check each channel
        let orig_rgba = color.to_rgba8();
        let recovered_rgba = unpacked.to_rgba8();

        prop_assert_eq!(orig_rgba, recovered_rgba, "ARGB8 round-trip should preserve color");
    }

    /// Color lerp at t=0 returns first color, t=1 returns second color.
    #[test]
    fn color_lerp_endpoints(
        r1 in 0.0f32..1.0f32, g1 in 0.0f32..1.0f32, b1 in 0.0f32..1.0f32, a1 in 0.0f32..1.0f32,
        r2 in 0.0f32..1.0f32, g2 in 0.0f32..1.0f32, b2 in 0.0f32..1.0f32, a2 in 0.0f32..1.0f32
    ) {
        let c1 = Color::new(r1, g1, b1, a1);
        let c2 = Color::new(r2, g2, b2, a2);

        // Lerp(0) should return c1
        let lerp0 = c1.lerp(c2, 0.0);
        prop_assert!(
            (lerp0.r - c1.r).abs() < EPSILON &&
            (lerp0.g - c1.g).abs() < EPSILON &&
            (lerp0.b - c1.b).abs() < EPSILON &&
            (lerp0.a - c1.a).abs() < EPSILON,
            "lerp(0) should return first color"
        );

        // Lerp(1) should return c2
        let lerp1 = c1.lerp(c2, 1.0);
        prop_assert!(
            (lerp1.r - c2.r).abs() < EPSILON &&
            (lerp1.g - c2.g).abs() < EPSILON &&
            (lerp1.b - c2.b).abs() < EPSILON &&
            (lerp1.a - c2.a).abs() < EPSILON,
            "lerp(1) should return second color"
        );
    }

    /// Color lerp at t=0.5 is the midpoint.
    #[test]
    fn color_lerp_midpoint(
        r1 in 0.0f32..1.0f32, g1 in 0.0f32..1.0f32, b1 in 0.0f32..1.0f32, a1 in 0.0f32..1.0f32,
        r2 in 0.0f32..1.0f32, g2 in 0.0f32..1.0f32, b2 in 0.0f32..1.0f32, a2 in 0.0f32..1.0f32
    ) {
        let c1 = Color::new(r1, g1, b1, a1);
        let c2 = Color::new(r2, g2, b2, a2);
        let mid = c1.lerp(c2, 0.5);

        let expected_r = (r1 + r2) / 2.0;
        let expected_g = (g1 + g2) / 2.0;
        let expected_b = (b1 + b2) / 2.0;
        let expected_a = (a1 + a2) / 2.0;

        prop_assert!(
            (mid.r - expected_r).abs() < EPSILON &&
            (mid.g - expected_g).abs() < EPSILON &&
            (mid.b - expected_b).abs() < EPSILON &&
            (mid.a - expected_a).abs() < EPSILON,
            "lerp(0.5) should be midpoint"
        );
    }

    /// Color clamp() values are in [0, 1].
    #[test]
    fn color_clamp_in_range(
        r in -10.0f32..10.0f32,
        g in -10.0f32..10.0f32,
        b in -10.0f32..10.0f32,
        a in -10.0f32..10.0f32
    ) {
        let color = Color::new(r, g, b, a);
        let clamped = color.clamp();

        prop_assert!(clamped.r >= 0.0 && clamped.r <= 1.0, "Clamped R should be in [0,1]");
        prop_assert!(clamped.g >= 0.0 && clamped.g <= 1.0, "Clamped G should be in [0,1]");
        prop_assert!(clamped.b >= 0.0 && clamped.b <= 1.0, "Clamped B should be in [0,1]");
        prop_assert!(clamped.a >= 0.0 && clamped.a <= 1.0, "Clamped A should be in [0,1]");
    }

    /// HSL to_color -> to_hsl roundtrip preserves hue/sat for colored values.
    #[test]
    fn color_hsl_roundtrip(
        r in 0.1f32..0.9f32,
        g in 0.1f32..0.9f32,
        b in 0.1f32..0.9f32
    ) {
        // Avoid near-gray colors where hue is undefined
        let color = Color::rgb(r, g, b);
        let hsl = color.to_hsl();
        let back = hsl.to_color();

        // Allow tolerance for floating-point conversion
        let tolerance = 1e-3;
        prop_assert!(
            (color.r - back.r).abs() < tolerance &&
            (color.g - back.g).abs() < tolerance &&
            (color.b - back.b).abs() < tolerance,
            "HSL roundtrip should preserve color: {:?} -> {:?} -> {:?}",
            color, hsl, back
        );
    }

    /// HSL with_lightness changes the lightness.
    #[test]
    fn hsl_with_lightness_changes_l(
        r in 0.0f32..1.0f32,
        g in 0.0f32..1.0f32,
        b in 0.0f32..1.0f32,
        new_l in 0.0f32..1.0f32
    ) {
        let color = Color::rgb(r, g, b);
        let hsl = color.to_hsl();
        let adjusted = hsl.with_lightness(new_l);

        prop_assert!(
            (adjusted.l - new_l).abs() < EPSILON,
            "with_lightness should set lightness to {}, got {}",
            new_l, adjusted.l
        );
        // Hue and saturation should be preserved
        prop_assert_eq!(adjusted.h, hsl.h, "Hue should be preserved");
        prop_assert_eq!(adjusted.s, hsl.s, "Saturation should be preserved");
    }
}
