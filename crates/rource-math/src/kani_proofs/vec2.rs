// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Vec2 f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for all Vec2 operations that involve
//! f32 arithmetic: length, normalized, dot, cross, project, reflect, rotate,
//! distance, and lerp.
//!
//! All harnesses use bounded inputs (`|v| < SAFE_BOUND`) to prevent
//! intermediate overflow that causes IEEE 754 NaN via `±inf * 0 = NaN`.

use crate::Vec2;

/// Bound for 2-component operations (dot, cross, length_squared).
/// For `x*x + y*y < MAX`: `|v| < sqrt(MAX/2) ≈ 1.3e19`. Using 1e18.
const SAFE_BOUND: f32 = 1e18;

// ============================================================================
// length / length_squared
// ============================================================================

/// **NaN-freedom + non-negativity**: `length()` with bounded inputs
/// never produces NaN and is always ≥ 0.
///
/// Mathematical basis: `sqrt(x² + y²) ≥ 0` for all real x, y.
/// IEEE 754: `sqrt` of non-negative finite value is always defined.
#[kani::proof]
fn verify_vec2_length_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    let v = Vec2::new(x, y);
    let len = v.length();
    assert!(!len.is_nan(), "length() produced NaN");
    assert!(len >= 0.0, "length() returned negative value");
    assert!(len.is_finite(), "length() produced non-finite output");
}

/// **NaN-freedom + non-negativity**: `length_squared()` with bounded inputs.
#[kani::proof]
fn verify_vec2_length_squared_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    let v = Vec2::new(x, y);
    let len_sq = v.length_squared();
    assert!(!len_sq.is_nan(), "length_squared() produced NaN");
    assert!(len_sq >= 0.0, "length_squared() returned negative value");
}

// ============================================================================
// normalized
// ============================================================================

/// **NaN-freedom**: `normalized()` with bounded inputs never produces NaN.
/// The zero-vector guard ensures division by zero returns ZERO.
#[kani::proof]
fn verify_vec2_normalized_no_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    let v = Vec2::new(x, y);
    let n = v.normalized();
    assert!(!n.x.is_nan(), "normalized().x is NaN");
    assert!(!n.y.is_nan(), "normalized().y is NaN");
}

// ============================================================================
// dot
// ============================================================================

/// **Finiteness**: `dot()` with bounded inputs produces finite output.
///
/// Bound justification: `|x1*x2 + y1*y2| ≤ 2 * SAFE_BOUND² < MAX`.
#[kani::proof]
fn verify_vec2_dot_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    let a = Vec2::new(ax, ay);
    let b = Vec2::new(bx, by);
    let d = a.dot(b);
    assert!(
        d.is_finite(),
        "dot() produced non-finite output for bounded inputs"
    );
}

// ============================================================================
// cross
// ============================================================================

/// **Finiteness**: `cross()` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec2_cross_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    let a = Vec2::new(ax, ay);
    let b = Vec2::new(bx, by);
    let c = a.cross(b);
    assert!(c.is_finite(), "cross() produced non-finite output");
}

// ============================================================================
// project
// ============================================================================

/// **Zero-guard verification**: `project()` onto zero vector returns ZERO.
/// This verifies the division-by-zero guard in project().
#[kani::proof]
fn verify_vec2_project_zero_guard() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    kani::assume(vx.is_finite() && vx.abs() < SAFE_BOUND);
    kani::assume(vy.is_finite() && vy.abs() < SAFE_BOUND);
    let v = Vec2::new(vx, vy);
    let result = v.project(Vec2::ZERO);
    assert!(result.x == 0.0, "project onto zero should return zero x");
    assert!(result.y == 0.0, "project onto zero should return zero y");
}

/// **NaN-freedom**: `project()` with bounded non-degenerate onto vector.
///
/// The onto vector must have length_squared above a minimum threshold to
/// prevent overflow in `dot / length_squared` when the denominator is
/// a denormalized float (e.g., 1e-40²). This is a genuine IEEE 754 edge
/// case: `onto_len_sq > 0.0` passes but `large_dot / tiny_len_sq = ±inf`,
/// and subsequent `inf * 0.0 = NaN`.
#[kani::proof]
fn verify_vec2_project_no_nan() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let ox: f32 = kani::any();
    let oy: f32 = kani::any();
    kani::assume(vx.is_finite() && vx.abs() < SAFE_BOUND);
    kani::assume(vy.is_finite() && vy.abs() < SAFE_BOUND);
    kani::assume(ox.is_finite() && ox.abs() < SAFE_BOUND);
    kani::assume(oy.is_finite() && oy.abs() < SAFE_BOUND);
    // Require non-degenerate onto: length_squared must be above f32 min_positive
    // to prevent division overflow
    kani::assume(ox * ox + oy * oy > f32::MIN_POSITIVE);
    let v = Vec2::new(vx, vy);
    let onto = Vec2::new(ox, oy);
    let result = v.project(onto);
    assert!(!result.x.is_nan(), "project().x is NaN");
    assert!(!result.y.is_nan(), "project().y is NaN");
}

// ============================================================================
// distance
// ============================================================================

/// **Non-negativity**: `distance()` with bounded inputs is ≥ 0.
#[kani::proof]
fn verify_vec2_distance_non_negative() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    let a = Vec2::new(ax, ay);
    let b = Vec2::new(bx, by);
    let d = a.distance(b);
    assert!(d >= 0.0, "distance() returned negative value");
    assert!(!d.is_nan(), "distance() produced NaN");
}

// ============================================================================
// rotate
// ============================================================================

/// **NaN-freedom**: `rotate()` with bounded vector and finite angle
/// produces non-NaN output.
#[kani::proof]
fn verify_vec2_rotate_no_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let angle: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(angle.is_finite());
    let v = Vec2::new(x, y);
    let r = v.rotate(angle);
    assert!(!r.x.is_nan(), "rotate().x is NaN");
    assert!(!r.y.is_nan(), "rotate().y is NaN");
}

// ============================================================================
// from_angle
// ============================================================================

/// **NaN-freedom**: `from_angle()` with finite angle produces non-NaN.
/// cos/sin are always defined for finite inputs.
#[kani::proof]
fn verify_vec2_from_angle_no_nan() {
    let angle: f32 = kani::any();
    kani::assume(angle.is_finite());
    let v = Vec2::from_angle(angle);
    assert!(!v.x.is_nan(), "from_angle().x is NaN");
    assert!(!v.y.is_nan(), "from_angle().y is NaN");
}

// ============================================================================
// lerp
// ============================================================================

/// **NaN-freedom + finiteness**: `lerp()` with bounded inputs and t ∈ [0,1].
#[kani::proof]
fn verify_vec2_lerp_no_nan() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let t: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(t.is_finite() && t >= 0.0 && t <= 1.0);
    let a = Vec2::new(ax, ay);
    let b = Vec2::new(bx, by);
    let r = a.lerp(b, t);
    assert!(!r.x.is_nan(), "lerp().x is NaN");
    assert!(!r.y.is_nan(), "lerp().y is NaN");
}

// ============================================================================
// distance_squared
// ============================================================================

/// **Non-negativity + finiteness**: `distance_squared()` with bounded inputs
/// is ≥ 0 and finite.
///
/// Mathematical basis: `(ax-bx)² + (ay-by)² ≥ 0` for all real values.
#[kani::proof]
fn verify_vec2_distance_squared_non_negative() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    let a = Vec2::new(ax, ay);
    let b = Vec2::new(bx, by);
    let d = a.distance_squared(b);
    assert!(d >= 0.0, "distance_squared() returned negative value");
    assert!(!d.is_nan(), "distance_squared() produced NaN");
    assert!(
        d.is_finite(),
        "distance_squared() produced non-finite output"
    );
}

// ============================================================================
// abs
// ============================================================================

/// **Non-negativity**: `abs()` with finite inputs produces non-negative components.
#[kani::proof]
fn verify_vec2_abs_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    let v = Vec2::new(x, y);
    let a = v.abs();
    assert!(a.x >= 0.0, "abs().x should be non-negative");
    assert!(a.y >= 0.0, "abs().y should be non-negative");
    assert!(!a.x.is_nan(), "abs().x is NaN");
    assert!(!a.y.is_nan(), "abs().y is NaN");
}

// ============================================================================
// floor / ceil / round
// ============================================================================

/// **Finiteness**: `floor()` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec2_floor_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    let v = Vec2::new(x, y);
    let f = v.floor();
    assert!(f.x.is_finite(), "floor().x non-finite");
    assert!(f.y.is_finite(), "floor().y non-finite");
}

/// **Finiteness**: `ceil()` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec2_ceil_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    let v = Vec2::new(x, y);
    let c = v.ceil();
    assert!(c.x.is_finite(), "ceil().x non-finite");
    assert!(c.y.is_finite(), "ceil().y non-finite");
}

/// **Finiteness**: `round()` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec2_round_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    let v = Vec2::new(x, y);
    let r = v.round();
    assert!(r.x.is_finite(), "round().x non-finite");
    assert!(r.y.is_finite(), "round().y non-finite");
}

// ============================================================================
// min / max
// ============================================================================

/// **Postcondition**: `min(a, b)` components are ≤ both `a` and `b` components.
#[kani::proof]
fn verify_vec2_min_componentwise() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite());
    kani::assume(ay.is_finite());
    kani::assume(bx.is_finite());
    kani::assume(by.is_finite());
    let a = Vec2::new(ax, ay);
    let b = Vec2::new(bx, by);
    let m = a.min(b);
    assert!(m.x <= ax && m.x <= bx, "min().x not minimum");
    assert!(m.y <= ay && m.y <= by, "min().y not minimum");
}

/// **Postcondition**: `max(a, b)` components are ≥ both `a` and `b` components.
#[kani::proof]
fn verify_vec2_max_componentwise() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite());
    kani::assume(ay.is_finite());
    kani::assume(bx.is_finite());
    kani::assume(by.is_finite());
    let a = Vec2::new(ax, ay);
    let b = Vec2::new(bx, by);
    let m = a.max(b);
    assert!(m.x >= ax && m.x >= bx, "max().x not maximum");
    assert!(m.y >= ay && m.y >= by, "max().y not maximum");
}

// ============================================================================
// clamp
// ============================================================================

/// **Postcondition**: `clamp(v, min, max)` result is within [min, max] bounds.
#[kani::proof]
fn verify_vec2_clamp_bounded() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let minx: f32 = kani::any();
    let miny: f32 = kani::any();
    let maxx: f32 = kani::any();
    let maxy: f32 = kani::any();
    kani::assume(vx.is_finite());
    kani::assume(vy.is_finite());
    kani::assume(minx.is_finite());
    kani::assume(miny.is_finite());
    kani::assume(maxx.is_finite());
    kani::assume(maxy.is_finite());
    kani::assume(minx <= maxx);
    kani::assume(miny <= maxy);
    let v = Vec2::new(vx, vy);
    let lo = Vec2::new(minx, miny);
    let hi = Vec2::new(maxx, maxy);
    let c = v.clamp(lo, hi);
    assert!(c.x >= minx && c.x <= maxx, "clamp().x out of bounds");
    assert!(c.y >= miny && c.y <= maxy, "clamp().y out of bounds");
}

// ============================================================================
// perp
// ============================================================================

/// **Finiteness**: `perp()` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec2_perp_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    let v = Vec2::new(x, y);
    let p = v.perp();
    assert!(p.x.is_finite(), "perp().x non-finite");
    assert!(p.y.is_finite(), "perp().y non-finite");
}

// ============================================================================
// approx_eq
// ============================================================================

/// **Reflexivity**: `approx_eq(v, v)` is true for all finite vectors.
#[kani::proof]
fn verify_vec2_approx_eq_reflexive() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    let v = Vec2::new(x, y);
    assert!(v.approx_eq(v), "approx_eq not reflexive");
}
