// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Mat3 f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for Mat3 operations: determinant,
//! inverse (division-by-zero guard), and transform_point.

use crate::{Mat3, Vec2};

/// Bound for 3×3 determinant: involves products of 3 elements.
/// Worst case: `6·v³ < MAX` → `v < (MAX/6)^(1/3) ≈ 3.8e12`. Using 1e12.
const DET_BOUND: f32 = 1e12;

/// Bound for transform_point: `3 multiplications + addition per component`.
/// Worst case: `3·v² < MAX` → `v < sqrt(MAX/3)`. Using 1e18.
const TRANSFORM_BOUND: f32 = 1e18;

// ============================================================================
// determinant
// ============================================================================

/// **Finiteness**: `determinant()` with bounded elements is finite.
#[kani::proof]
fn verify_mat3_determinant_finite() {
    let m: [f32; 9] = [
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
    ];
    for i in 0..9 {
        kani::assume(m[i].is_finite() && m[i].abs() < DET_BOUND);
    }
    let mat = Mat3 { m };
    let det = mat.determinant();
    assert!(det.is_finite(), "determinant() non-finite for bounded Mat3");
}

// ============================================================================
// inverse
// ============================================================================

/// **Guard verification**: `inverse()` returns None for singular matrices.
#[kani::proof]
fn verify_mat3_inverse_zero_is_none() {
    let inv = Mat3::ZERO.inverse();
    assert!(inv.is_none(), "inverse of zero matrix should be None");
}

/// **Postcondition**: `inverse()` returns Some for the identity matrix.
#[kani::proof]
fn verify_mat3_inverse_identity_is_some() {
    let inv = Mat3::IDENTITY.inverse();
    assert!(inv.is_some(), "inverse of identity should be Some");
}

// ============================================================================
// transform_point
// ============================================================================

/// **Finiteness**: `transform_point()` with bounded inputs is finite.
#[kani::proof]
fn verify_mat3_transform_point_finite() {
    let m: [f32; 9] = [
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
    ];
    for i in 0..9 {
        kani::assume(m[i].is_finite() && m[i].abs() < TRANSFORM_BOUND);
    }
    let mat = Mat3 { m };
    let px: f32 = kani::any();
    let py: f32 = kani::any();
    kani::assume(px.is_finite() && px.abs() < TRANSFORM_BOUND);
    kani::assume(py.is_finite() && py.abs() < TRANSFORM_BOUND);
    let result = mat.transform_point(Vec2::new(px, py));
    assert!(result.x.is_finite(), "transform_point().x non-finite");
    assert!(result.y.is_finite(), "transform_point().y non-finite");
}

// ============================================================================
// rotation
// ============================================================================

/// **NaN-freedom**: `rotation()` with finite angle has no NaN elements.
#[kani::proof]
fn verify_mat3_rotation_no_nan() {
    let radians: f32 = kani::any();
    kani::assume(radians.is_finite());
    let mat = Mat3::rotation(radians);
    for i in 0..9 {
        assert!(!mat.m[i].is_nan(), "rotation() element is NaN");
    }
}

/// **Identity preservation**: Identity transform preserves any bounded point.
#[kani::proof]
fn verify_mat3_identity_preserves_point() {
    let px: f32 = kani::any();
    let py: f32 = kani::any();
    kani::assume(px.is_finite());
    kani::assume(py.is_finite());
    let p = Vec2::new(px, py);
    let result = Mat3::IDENTITY.transform_point(p);
    assert!(result.x == px, "identity should preserve x");
    assert!(result.y == py, "identity should preserve y");
}
