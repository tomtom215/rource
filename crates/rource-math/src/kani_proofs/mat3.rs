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

// ============================================================================
// transpose involutive
// ============================================================================

/// **Involution**: `transpose(transpose(M)) == M` for all bounded matrices.
#[kani::proof]
fn verify_mat3_transpose_involutive() {
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
        kani::assume(m[i].is_finite());
    }
    let mat = Mat3 { m };
    let tt = mat.transpose().transpose();
    for i in 0..9 {
        assert!(tt.m[i] == mat.m[i], "transpose should be involutive");
    }
}

// ============================================================================
// translation
// ============================================================================

/// **Finiteness**: `translation()` with bounded inputs produces finite matrix.
#[kani::proof]
fn verify_mat3_translation_finite() {
    let tx: f32 = kani::any();
    let ty: f32 = kani::any();
    kani::assume(tx.is_finite());
    kani::assume(ty.is_finite());
    let mat = Mat3::translation(tx, ty);
    for i in 0..9 {
        assert!(mat.m[i].is_finite(), "translation() element non-finite");
    }
}

// ============================================================================
// scaling
// ============================================================================

/// **Finiteness**: `scaling()` with bounded inputs produces finite matrix.
#[kani::proof]
fn verify_mat3_scaling_finite() {
    let sx: f32 = kani::any();
    let sy: f32 = kani::any();
    kani::assume(sx.is_finite());
    kani::assume(sy.is_finite());
    let mat = Mat3::scaling(sx, sy);
    for i in 0..9 {
        assert!(mat.m[i].is_finite(), "scaling() element non-finite");
    }
}

// ============================================================================
// shearing
// ============================================================================

/// **Finiteness**: `shearing()` with bounded inputs produces finite matrix.
#[kani::proof]
fn verify_mat3_shearing_finite() {
    let shx: f32 = kani::any();
    let shy: f32 = kani::any();
    kani::assume(shx.is_finite());
    kani::assume(shy.is_finite());
    let mat = Mat3::shearing(shx, shy);
    for i in 0..9 {
        assert!(mat.m[i].is_finite(), "shearing() element non-finite");
    }
}

// ============================================================================
// transform_vector
// ============================================================================

/// **Finiteness**: `transform_vector()` with bounded inputs is finite.
#[kani::proof]
fn verify_mat3_transform_vector_finite() {
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
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    kani::assume(vx.is_finite() && vx.abs() < TRANSFORM_BOUND);
    kani::assume(vy.is_finite() && vy.abs() < TRANSFORM_BOUND);
    let result = mat.transform_vector(Vec2::new(vx, vy));
    assert!(result.x.is_finite(), "transform_vector().x non-finite");
    assert!(result.y.is_finite(), "transform_vector().y non-finite");
}

// ============================================================================
// get_translation / get_scale
// ============================================================================

/// **Postcondition**: `get_translation()` of a translation matrix matches input.
#[kani::proof]
fn verify_mat3_get_translation_roundtrip() {
    let tx: f32 = kani::any();
    let ty: f32 = kani::any();
    kani::assume(tx.is_finite());
    kani::assume(ty.is_finite());
    let mat = Mat3::translation(tx, ty);
    let t = mat.get_translation();
    assert!(t.x == tx, "get_translation().x should match");
    assert!(t.y == ty, "get_translation().y should match");
}

/// **Finiteness**: `get_scale()` with bounded inputs produces finite output.
///
/// Note: Exact value matching (get_scale(scaling(s)) == s) is too expensive
/// for CBMC due to symbolic sqrt(). We verify finiteness instead, which
/// catches NaN/overflow edge cases. The exact roundtrip property is verified
/// algebraically in Verus/Coq.
#[kani::proof]
fn verify_mat3_get_scale_finite() {
    let sx: f32 = kani::any();
    let sy: f32 = kani::any();
    kani::assume(sx.is_finite() && sx.abs() < TRANSFORM_BOUND);
    kani::assume(sy.is_finite() && sy.abs() < TRANSFORM_BOUND);
    let mat = Mat3::scaling(sx, sy);
    let s = mat.get_scale();
    assert!(s.x.is_finite(), "get_scale().x non-finite");
    assert!(s.y.is_finite(), "get_scale().y non-finite");
}

// ============================================================================
// approx_eq
// ============================================================================

/// **Reflexivity**: `approx_eq(M, M)` is true for all finite matrices.
#[kani::proof]
fn verify_mat3_approx_eq_reflexive() {
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
        kani::assume(m[i].is_finite());
    }
    let mat = Mat3 { m };
    assert!(mat.approx_eq(mat), "approx_eq not reflexive");
}

// ============================================================================
// mul (matrix multiplication)
// ============================================================================

/// **Right identity**: `M * IDENTITY == M` for all finite matrices.
#[kani::proof]
fn verify_mat3_mul_identity_right() {
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
        kani::assume(m[i].is_finite());
    }
    let mat = Mat3 { m };
    let result = mat * Mat3::IDENTITY;
    for i in 0..9 {
        assert!(result.m[i] == mat.m[i], "M * I should equal M");
    }
}

/// **Left identity**: `IDENTITY * M == M` for all finite matrices.
#[kani::proof]
fn verify_mat3_mul_identity_left() {
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
        kani::assume(m[i].is_finite());
    }
    let mat = Mat3 { m };
    let result = Mat3::IDENTITY * mat;
    for i in 0..9 {
        assert!(result.m[i] == mat.m[i], "I * M should equal M");
    }
}

// ============================================================================
// uniform_scaling
// ============================================================================

/// **Finiteness**: `uniform_scaling()` with bounded input produces finite matrix.
#[kani::proof]
fn verify_mat3_uniform_scaling_finite() {
    let s: f32 = kani::any();
    kani::assume(s.is_finite());
    let mat = Mat3::uniform_scaling(s);
    for i in 0..9 {
        assert!(mat.m[i].is_finite(), "uniform_scaling() element non-finite");
    }
}

/// **Diagonal structure**: `uniform_scaling(s)` has `s` on diagonal, `0` off-diagonal.
#[kani::proof]
fn verify_mat3_uniform_scaling_structure() {
    let s: f32 = kani::any();
    kani::assume(s.is_finite());
    let mat = Mat3::uniform_scaling(s);
    // Diagonal elements should be s
    assert!(mat.m[0] == s, "uniform_scaling diagonal[0] should be s");
    assert!(mat.m[4] == s, "uniform_scaling diagonal[1] should be s");
    // m[8] is the homogeneous coordinate, should be 1.0
    assert!(mat.m[8] == 1.0, "uniform_scaling m[8] should be 1.0");
    // Off-diagonal should be 0
    assert!(mat.m[1] == 0.0, "off-diagonal should be 0");
    assert!(mat.m[2] == 0.0, "off-diagonal should be 0");
    assert!(mat.m[3] == 0.0, "off-diagonal should be 0");
    assert!(mat.m[5] == 0.0, "off-diagonal should be 0");
}

// ============================================================================
// from_translation
// ============================================================================

/// **Finiteness**: `from_translation()` with finite Vec2 produces finite matrix.
#[kani::proof]
fn verify_mat3_from_translation_finite() {
    let tx: f32 = kani::any();
    let ty: f32 = kani::any();
    kani::assume(tx.is_finite());
    kani::assume(ty.is_finite());
    let mat = Mat3::from_translation(Vec2::new(tx, ty));
    for i in 0..9 {
        assert!(
            mat.m[i].is_finite(),
            "from_translation() element non-finite"
        );
    }
}

// ============================================================================
// Default
// ============================================================================

/// **Default is identity**: `Default::default()` returns IDENTITY.
#[kani::proof]
fn verify_mat3_default_is_identity() {
    let def = Mat3::default();
    let id = Mat3::IDENTITY;
    for i in 0..9 {
        assert!(def.m[i] == id.m[i], "default should be identity");
    }
}

// ============================================================================
// identity determinant
// ============================================================================

/// **Exact value**: Identity determinant is exactly 1.0.
#[kani::proof]
fn verify_mat3_identity_determinant() {
    let det = Mat3::IDENTITY.determinant();
    assert!(det == 1.0, "identity determinant should be 1.0");
}

// ============================================================================
// zero determinant
// ============================================================================

/// **Exact value**: Zero matrix determinant is exactly 0.0.
#[kani::proof]
fn verify_mat3_zero_determinant() {
    let det = Mat3::ZERO.determinant();
    assert!(det == 0.0, "zero matrix determinant should be 0.0");
}

// ============================================================================
// translation determinant
// ============================================================================

/// **Postcondition**: `translation().determinant()` is exactly 1.0.
///
/// Translation matrices have the form [[1,0,tx],[0,1,ty],[0,0,1]] (column-major),
/// so det = 1*1*1 + 0*0*0 + 0*0*0 - 0*1*0 - 1*0*0 - 0*0*1 = 1.
#[kani::proof]
fn verify_mat3_translation_det_is_one() {
    let tx: f32 = kani::any();
    let ty: f32 = kani::any();
    kani::assume(tx.is_finite() && tx.abs() < 1e6);
    kani::assume(ty.is_finite() && ty.abs() < 1e6);
    let mat = Mat3::translation(tx, ty);
    let det = mat.determinant();
    assert!(det == 1.0, "translation det should be 1.0");
}
