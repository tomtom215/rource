// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Vec4 f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for Vec4 operations: length,
//! normalized, and dot.

use crate::Vec4;

/// Bound for 4-component dot: `x² + y² + z² + w² < MAX`.
const SAFE_BOUND: f32 = 1e18;

// ============================================================================
// length / length_squared
// ============================================================================

/// **NaN-freedom + non-negativity**: `length()` with bounded inputs.
#[kani::proof]
fn verify_vec4_length_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w.abs() < SAFE_BOUND);
    let v = Vec4::new(x, y, z, w);
    let len = v.length();
    assert!(!len.is_nan(), "length() produced NaN");
    assert!(len >= 0.0, "length() returned negative value");
}

// ============================================================================
// normalized
// ============================================================================

/// **NaN-freedom**: `normalized()` with bounded inputs never produces NaN.
#[kani::proof]
fn verify_vec4_normalized_no_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w.abs() < SAFE_BOUND);
    let v = Vec4::new(x, y, z, w);
    let n = v.normalized();
    assert!(!n.x.is_nan(), "normalized().x is NaN");
    assert!(!n.y.is_nan(), "normalized().y is NaN");
    assert!(!n.z.is_nan(), "normalized().z is NaN");
    assert!(!n.w.is_nan(), "normalized().w is NaN");
}

// ============================================================================
// dot
// ============================================================================

/// **Finiteness**: `dot()` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec4_dot_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let aw: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    let bw: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(aw.is_finite() && aw.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    kani::assume(bw.is_finite() && bw.abs() < SAFE_BOUND);
    let a = Vec4::new(ax, ay, az, aw);
    let b = Vec4::new(bx, by, bz, bw);
    let d = a.dot(b);
    assert!(d.is_finite(), "dot() produced non-finite output");
}

// ============================================================================
// lerp
// ============================================================================

/// **NaN-freedom + finiteness**: `lerp()` with bounded inputs and t ∈ [0,1].
#[kani::proof]
fn verify_vec4_lerp_no_nan() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let aw: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    let bw: f32 = kani::any();
    let t: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(aw.is_finite() && aw.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    kani::assume(bw.is_finite() && bw.abs() < SAFE_BOUND);
    kani::assume(t.is_finite() && t >= 0.0 && t <= 1.0);
    let a = Vec4::new(ax, ay, az, aw);
    let b = Vec4::new(bx, by, bz, bw);
    let r = a.lerp(b, t);
    assert!(!r.x.is_nan(), "lerp().x is NaN");
    assert!(!r.y.is_nan(), "lerp().y is NaN");
    assert!(!r.z.is_nan(), "lerp().z is NaN");
    assert!(!r.w.is_nan(), "lerp().w is NaN");
}

// ============================================================================
// abs
// ============================================================================

/// **Non-negativity**: `abs()` with finite inputs produces non-negative components.
#[kani::proof]
fn verify_vec4_abs_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    kani::assume(w.is_finite());
    let v = Vec4::new(x, y, z, w);
    let a = v.abs();
    assert!(a.x >= 0.0, "abs().x should be non-negative");
    assert!(a.y >= 0.0, "abs().y should be non-negative");
    assert!(a.z >= 0.0, "abs().z should be non-negative");
    assert!(a.w >= 0.0, "abs().w should be non-negative");
}

// ============================================================================
// min / max
// ============================================================================

/// **Postcondition**: `min(a, b)` components are ≤ both `a` and `b` components.
#[kani::proof]
fn verify_vec4_min_componentwise() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let aw: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    let bw: f32 = kani::any();
    kani::assume(ax.is_finite());
    kani::assume(ay.is_finite());
    kani::assume(az.is_finite());
    kani::assume(aw.is_finite());
    kani::assume(bx.is_finite());
    kani::assume(by.is_finite());
    kani::assume(bz.is_finite());
    kani::assume(bw.is_finite());
    let a = Vec4::new(ax, ay, az, aw);
    let b = Vec4::new(bx, by, bz, bw);
    let m = a.min(b);
    assert!(m.x <= ax && m.x <= bx, "min().x not minimum");
    assert!(m.y <= ay && m.y <= by, "min().y not minimum");
    assert!(m.z <= az && m.z <= bz, "min().z not minimum");
    assert!(m.w <= aw && m.w <= bw, "min().w not minimum");
}

/// **Postcondition**: `max(a, b)` components are ≥ both `a` and `b` components.
#[kani::proof]
fn verify_vec4_max_componentwise() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let aw: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    let bw: f32 = kani::any();
    kani::assume(ax.is_finite());
    kani::assume(ay.is_finite());
    kani::assume(az.is_finite());
    kani::assume(aw.is_finite());
    kani::assume(bx.is_finite());
    kani::assume(by.is_finite());
    kani::assume(bz.is_finite());
    kani::assume(bw.is_finite());
    let a = Vec4::new(ax, ay, az, aw);
    let b = Vec4::new(bx, by, bz, bw);
    let m = a.max(b);
    assert!(m.x >= ax && m.x >= bx, "max().x not maximum");
    assert!(m.y >= ay && m.y >= by, "max().y not maximum");
    assert!(m.z >= az && m.z >= bz, "max().z not maximum");
    assert!(m.w >= aw && m.w >= bw, "max().w not maximum");
}

// ============================================================================
// clamp
// ============================================================================

/// **Postcondition**: `clamp(v, min, max)` result is within [min, max] bounds.
#[kani::proof]
fn verify_vec4_clamp_bounded() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let vz: f32 = kani::any();
    let vw: f32 = kani::any();
    let minx: f32 = kani::any();
    let miny: f32 = kani::any();
    let minz: f32 = kani::any();
    let minw: f32 = kani::any();
    let maxx: f32 = kani::any();
    let maxy: f32 = kani::any();
    let maxz: f32 = kani::any();
    let maxw: f32 = kani::any();
    kani::assume(vx.is_finite());
    kani::assume(vy.is_finite());
    kani::assume(vz.is_finite());
    kani::assume(vw.is_finite());
    kani::assume(minx.is_finite() && maxx.is_finite() && minx <= maxx);
    kani::assume(miny.is_finite() && maxy.is_finite() && miny <= maxy);
    kani::assume(minz.is_finite() && maxz.is_finite() && minz <= maxz);
    kani::assume(minw.is_finite() && maxw.is_finite() && minw <= maxw);
    let v = Vec4::new(vx, vy, vz, vw);
    let lo = Vec4::new(minx, miny, minz, minw);
    let hi = Vec4::new(maxx, maxy, maxz, maxw);
    let c = v.clamp(lo, hi);
    assert!(c.x >= minx && c.x <= maxx, "clamp().x out of bounds");
    assert!(c.y >= miny && c.y <= maxy, "clamp().y out of bounds");
    assert!(c.z >= minz && c.z <= maxz, "clamp().z out of bounds");
    assert!(c.w >= minw && c.w <= maxw, "clamp().w out of bounds");
}

// ============================================================================
// approx_eq
// ============================================================================

/// **Reflexivity**: `approx_eq(v, v)` is true for all finite vectors.
#[kani::proof]
fn verify_vec4_approx_eq_reflexive() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    kani::assume(w.is_finite());
    let v = Vec4::new(x, y, z, w);
    assert!(v.approx_eq(v), "approx_eq not reflexive");
}
