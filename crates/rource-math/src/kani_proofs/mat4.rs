// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Mat4 f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for Mat4 operations: determinant,
//! inverse, orthographic, and perspective.

use crate::Mat4;

/// Bound for 4×4 determinant: involves products of 4 elements.
/// Worst case: `~24·v⁴ < MAX` → `v < (MAX/24)^(1/4) ≈ 1.2e9`. Using 1e9.
const DET_BOUND: f32 = 1e9;

// ============================================================================
// determinant
// ============================================================================

/// **Finiteness**: `determinant()` with bounded elements is finite.
#[kani::proof]
fn verify_mat4_determinant_finite() {
    let m: [f32; 16] = [
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
        kani::any(),
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
    for i in 0..16 {
        kani::assume(m[i].is_finite() && m[i].abs() < DET_BOUND);
    }
    let mat = Mat4 { m };
    let det = mat.determinant();
    assert!(det.is_finite(), "determinant() non-finite for bounded Mat4");
}

// ============================================================================
// inverse
// ============================================================================

/// **Guard verification**: `inverse()` returns None for the zero matrix.
#[kani::proof]
fn verify_mat4_inverse_zero_is_none() {
    let inv = Mat4::ZERO.inverse();
    assert!(inv.is_none(), "inverse of zero matrix should be None");
}

/// **Postcondition**: `inverse()` returns Some for the identity matrix.
#[kani::proof]
fn verify_mat4_inverse_identity_is_some() {
    let inv = Mat4::IDENTITY.inverse();
    assert!(inv.is_some(), "inverse of identity should be Some");
}

// ============================================================================
// orthographic
// ============================================================================

/// **Finiteness**: `orthographic()` with distinct bounded parameters is finite.
///
/// Precondition: All parameters bounded, bounds are distinct (non-zero diffs).
/// This verifies the division operations produce finite results.
#[kani::proof]
fn verify_mat4_orthographic_finite() {
    let left: f32 = kani::any();
    let right: f32 = kani::any();
    let bottom: f32 = kani::any();
    let top: f32 = kani::any();
    let near: f32 = kani::any();
    let far: f32 = kani::any();
    kani::assume(left.is_finite() && left.abs() < DET_BOUND);
    kani::assume(right.is_finite() && right.abs() < DET_BOUND);
    kani::assume(bottom.is_finite() && bottom.abs() < DET_BOUND);
    kani::assume(top.is_finite() && top.abs() < DET_BOUND);
    kani::assume(near.is_finite() && near.abs() < DET_BOUND);
    kani::assume(far.is_finite() && far.abs() < DET_BOUND);
    // Distinct bounds prevent division by zero
    kani::assume((right - left).abs() > 1e-6);
    kani::assume((top - bottom).abs() > 1e-6);
    kani::assume((far - near).abs() > 1e-6);
    let m = Mat4::orthographic(left, right, bottom, top, near, far);
    for i in 0..16 {
        assert!(m.m[i].is_finite(), "orthographic element non-finite");
    }
}

// ============================================================================
// perspective
// ============================================================================

// NOTE: `perspective()` cannot be verified by Kani because it calls `f32::tan()`,
// which delegates to the C foreign function `tanf`. Kani does not support
// transcendental C math functions (tracked: https://github.com/model-checking/kani/issues/2423).
// The perspective function is verified algebraically by Verus and Coq instead.

// ============================================================================
// identity properties
// ============================================================================

/// **Exact value**: Identity determinant is exactly 1.0.
#[kani::proof]
fn verify_mat4_identity_determinant() {
    let det = Mat4::IDENTITY.determinant();
    assert!(det == 1.0, "identity determinant should be 1.0");
}

/// **Exact value**: Zero matrix determinant is exactly 0.0.
#[kani::proof]
fn verify_mat4_zero_determinant() {
    let det = Mat4::ZERO.determinant();
    assert!(det == 0.0, "zero matrix determinant should be 0.0");
}
