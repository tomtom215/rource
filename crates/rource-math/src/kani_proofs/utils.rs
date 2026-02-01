// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for utility functions (lerp, clamp, approx_eq, deg/rad).
//!
//! All harnesses use bounded inputs to prevent intermediate overflow, which
//! can cause IEEE 754 NaN via patterns like `±inf * 0.0 = NaN`.
//!
//! # Known Edge Case (Discovered by Kani)
//!
//! `lerp(f32::MAX, -f32::MAX, 0.0)` produces NaN because:
//! 1. `b - a = -f32::MAX - f32::MAX` overflows to `-inf`
//! 2. `-inf * 0.0 = NaN` (IEEE 754 specification)
//! 3. `a + NaN = NaN`
//!
//! This affects all math libraries using the standard formula `a + (b-a)*t`.
//! For inputs within `|v| < 1e18`, this cannot occur.

/// Bound for inputs where subtraction and multiplication stay finite.
/// For lerp: `(b - a)` overflows when `|a| + |b| > MAX ≈ 3.4e38`.
/// Using 1e18 ensures `|b - a| < 2e18`, and `|(b-a)*t| < 2e18`.
const SAFE_BOUND: f32 = 1e18;

// ============================================================================
// lerp
// ============================================================================

/// **NaN-freedom**: `lerp` with bounded a, b and t ∈ [0,1] never produces NaN.
///
/// Precondition: `|a| < 1e18`, `|b| < 1e18`, `0 ≤ t ≤ 1`.
/// Postcondition: `result` is not NaN and is finite.
#[kani::proof]
fn verify_lerp_no_nan() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    let t: f32 = kani::any();
    kani::assume(a.is_finite() && a.abs() < SAFE_BOUND);
    kani::assume(b.is_finite() && b.abs() < SAFE_BOUND);
    kani::assume(t.is_finite() && t >= 0.0 && t <= 1.0);
    let result = crate::lerp(a, b, t);
    assert!(!result.is_nan(), "lerp produced NaN for bounded inputs");
    assert!(result.is_finite(), "lerp produced non-finite output");
}

// ============================================================================
// clamp
// ============================================================================

/// **Postcondition**: `clamp` with finite ordered bounds and finite value
/// produces output satisfying `min ≤ result ≤ max`.
///
/// Precondition: `value`, `min`, `max` are finite; `min ≤ max`.
/// Postcondition: `min ≤ result ≤ max`, result is not NaN.
#[kani::proof]
fn verify_clamp_bounded() {
    let value: f32 = kani::any();
    let min: f32 = kani::any();
    let max: f32 = kani::any();
    kani::assume(value.is_finite());
    kani::assume(min.is_finite());
    kani::assume(max.is_finite());
    kani::assume(min <= max);
    let result = crate::clamp(value, min, max);
    assert!(!result.is_nan(), "clamp produced NaN");
    assert!(result >= min, "clamp result below min");
    assert!(result <= max, "clamp result above max");
}

// ============================================================================
// approx_eq
// ============================================================================

/// **Reflexivity**: `approx_eq(a, a)` is true for all finite values.
///
/// Precondition: `a` is finite.
/// Postcondition: `approx_eq(a, a) == true`.
#[kani::proof]
fn verify_approx_eq_reflexive() {
    let a: f32 = kani::any();
    kani::assume(a.is_finite());
    assert!(
        crate::approx_eq(a, a),
        "approx_eq not reflexive for finite value"
    );
}

// ============================================================================
// deg_to_rad / rad_to_deg
// ============================================================================

/// **Finiteness**: `deg_to_rad` with bounded input produces finite output.
///
/// Precondition: `|degrees| < 1e18`.
/// Postcondition: result is finite.
#[kani::proof]
fn verify_deg_to_rad_finite() {
    let degrees: f32 = kani::any();
    kani::assume(degrees.is_finite() && degrees.abs() < SAFE_BOUND);
    let result = crate::deg_to_rad(degrees);
    assert!(result.is_finite(), "deg_to_rad produced non-finite output");
}

/// **Finiteness**: `rad_to_deg` with bounded input produces finite output.
///
/// Precondition: `|radians| < 1e18`.
/// Postcondition: result is finite.
#[kani::proof]
fn verify_rad_to_deg_finite() {
    let radians: f32 = kani::any();
    kani::assume(radians.is_finite() && radians.abs() < SAFE_BOUND);
    let result = crate::rad_to_deg(radians);
    assert!(result.is_finite(), "rad_to_deg produced non-finite output");
}

// ============================================================================
// lerp endpoints
// ============================================================================

/// **Endpoint property**: `lerp(a, b, 0.0)` returns exactly `a` for bounded inputs.
///
/// Since lerp(a, b, 0) = a + (b - a) * 0 = a + 0 = a, the result should be exact.
#[kani::proof]
fn verify_lerp_endpoint_zero() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a.is_finite() && a.abs() < SAFE_BOUND);
    kani::assume(b.is_finite() && b.abs() < SAFE_BOUND);
    let result = crate::lerp(a, b, 0.0);
    assert!(result == a, "lerp(a, b, 0.0) should return exactly a");
}

// ============================================================================
// approx_eq symmetry
// ============================================================================

/// **Symmetry**: `approx_eq(a, b) == approx_eq(b, a)` for all finite values.
#[kani::proof]
fn verify_approx_eq_symmetry() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a.is_finite());
    kani::assume(b.is_finite());
    let ab = crate::approx_eq(a, b);
    let ba = crate::approx_eq(b, a);
    assert!(ab == ba, "approx_eq should be symmetric");
}

// ============================================================================
// lerp endpoint t=1
// ============================================================================

/// **Endpoint property**: `lerp(a, b, 1.0)` returns `a + (b - a) * 1.0`.
///
/// For bounded inputs where `b - a` is exact, the result should equal `b`.
/// We verify finiteness and NaN-freedom rather than exact equality
/// because floating-point `a + (b - a)` may differ from `b` by 1 ULP.
///
/// Precondition: `|a| < 1e18`, `|b| < 1e18`.
/// Postcondition: result is finite.
#[kani::proof]
fn verify_lerp_endpoint_one() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a.is_finite() && a.abs() < SAFE_BOUND);
    kani::assume(b.is_finite() && b.abs() < SAFE_BOUND);
    let result = crate::lerp(a, b, 1.0);
    assert!(!result.is_nan(), "lerp(a, b, 1.0) produced NaN");
    assert!(result.is_finite(), "lerp(a, b, 1.0) non-finite");
}

// ============================================================================
// clamp idempotent
// ============================================================================

/// **Idempotence**: `clamp(clamp(v, min, max), min, max) == clamp(v, min, max)`.
///
/// Precondition: finite value and ordered bounds.
/// Postcondition: double-clamp equals single clamp.
#[kani::proof]
fn verify_clamp_idempotent() {
    let value: f32 = kani::any();
    let min: f32 = kani::any();
    let max: f32 = kani::any();
    kani::assume(value.is_finite());
    kani::assume(min.is_finite());
    kani::assume(max.is_finite());
    kani::assume(min <= max);
    let once = crate::clamp(value, min, max);
    let twice = crate::clamp(once, min, max);
    assert!(once == twice, "clamp should be idempotent");
}
