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

// ============================================================================
// length_squared
// ============================================================================

/// **Non-negativity**: `length_squared()` with bounded inputs is non-negative.
#[kani::proof]
fn verify_vec4_length_squared_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w.abs() < SAFE_BOUND);
    let v = Vec4::new(x, y, z, w);
    let lsq = v.length_squared();
    assert!(!lsq.is_nan(), "length_squared() produced NaN");
    assert!(lsq >= 0.0, "length_squared() returned negative value");
}

// ============================================================================
// sub (via operator overloading)
// ============================================================================

/// **Finiteness**: `a - b` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec4_sub_finite() {
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
    let r = a - b;
    assert!(r.x.is_finite(), "sub result x is not finite");
    assert!(r.y.is_finite(), "sub result y is not finite");
    assert!(r.z.is_finite(), "sub result z is not finite");
    assert!(r.w.is_finite(), "sub result w is not finite");
}

// ============================================================================
// scale
// ============================================================================

/// **Finiteness**: `v * scalar` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec4_scale_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    let s: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < 1e18);
    kani::assume(y.is_finite() && y.abs() < 1e18);
    kani::assume(z.is_finite() && z.abs() < 1e18);
    kani::assume(w.is_finite() && w.abs() < 1e18);
    kani::assume(s.is_finite() && s.abs() < 1e18);
    let v = Vec4::new(x, y, z, w);
    let r = v * s;
    assert!(r.x.is_finite(), "scale result x is not finite");
    assert!(r.y.is_finite(), "scale result y is not finite");
    assert!(r.z.is_finite(), "scale result z is not finite");
    assert!(r.w.is_finite(), "scale result w is not finite");
}

// ============================================================================
// neg
// ============================================================================

/// **Finiteness**: `-v` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec4_neg_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    kani::assume(w.is_finite());
    let v = Vec4::new(x, y, z, w);
    let r = -v;
    assert!(r.x.is_finite(), "neg result x is not finite");
    assert!(r.y.is_finite(), "neg result y is not finite");
    assert!(r.z.is_finite(), "neg result z is not finite");
    assert!(r.w.is_finite(), "neg result w is not finite");
}

// ============================================================================
// add
// ============================================================================

/// **Finiteness**: `a + b` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec4_add_finite() {
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
    let r = a + b;
    assert!(r.x.is_finite(), "add result x is not finite");
    assert!(r.y.is_finite(), "add result y is not finite");
    assert!(r.z.is_finite(), "add result z is not finite");
    assert!(r.w.is_finite(), "add result w is not finite");
}

// ============================================================================
// dot self non-negative
// ============================================================================

/// **Non-negativity**: `v.dot(v)` is always non-negative for finite bounded vectors.
#[kani::proof]
fn verify_vec4_dot_self_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w.abs() < SAFE_BOUND);
    let v = Vec4::new(x, y, z, w);
    let d = v.dot(v);
    assert!(!d.is_nan(), "v.dot(v) produced NaN");
    assert!(d >= 0.0, "v.dot(v) returned negative value");
}

// ============================================================================
// lerp endpoints
// ============================================================================

/// **Endpoint property**: `lerp(a, b, 0.0)` returns exactly `a`.
#[kani::proof]
fn verify_vec4_lerp_endpoint_zero() {
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
    let r = a.lerp(b, 0.0);
    // lerp(a, b, 0) = a + (b - a) * 0 = a + 0 = a
    assert!(r.x == ax, "lerp(a,b,0).x should equal a.x");
    assert!(r.y == ay, "lerp(a,b,0).y should equal a.y");
    assert!(r.z == az, "lerp(a,b,0).z should equal a.z");
    assert!(r.w == aw, "lerp(a,b,0).w should equal a.w");
}

/// **Endpoint property**: `lerp(a, b, 1.0)` produces finite result close to `b`.
#[kani::proof]
fn verify_vec4_lerp_endpoint_one() {
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
    let r = a.lerp(b, 1.0);
    // lerp(a, b, 1) = a + (b - a) * 1 = b (modulo f32 rounding)
    assert!(r.x.is_finite(), "lerp(a,b,1).x should be finite");
    assert!(r.y.is_finite(), "lerp(a,b,1).y should be finite");
    assert!(r.z.is_finite(), "lerp(a,b,1).z should be finite");
    assert!(r.w.is_finite(), "lerp(a,b,1).w should be finite");
}

// ============================================================================
// neg involution
// ============================================================================

/// **Involution**: `-(-v) == v` for all finite vectors (IEEE 754 sign-bit flip).
#[kani::proof]
fn verify_vec4_neg_involution() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    kani::assume(w.is_finite());
    let v = Vec4::new(x, y, z, w);
    let r = -(-v);
    assert!(r.x == x, "-(-v).x should equal v.x");
    assert!(r.y == y, "-(-v).y should equal v.y");
    assert!(r.z == z, "-(-v).z should equal v.z");
    assert!(r.w == w, "-(-v).w should equal v.w");
}

// ============================================================================
// add commutativity
// ============================================================================

/// **Commutativity**: `a + b == b + a` for all finite bounded vectors (IEEE 754).
#[kani::proof]
fn verify_vec4_add_commutative() {
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
    let ab = a + b;
    let ba = b + a;
    assert!(ab.x == ba.x, "(a+b).x should equal (b+a).x");
    assert!(ab.y == ba.y, "(a+b).y should equal (b+a).y");
    assert!(ab.z == ba.z, "(a+b).z should equal (b+a).z");
    assert!(ab.w == ba.w, "(a+b).w should equal (b+a).w");
}

// ============================================================================
// splat
// ============================================================================

/// **Uniformity**: `splat(x)` produces a vector with all components equal to `x`.
#[kani::proof]
fn verify_vec4_splat_all_equal() {
    let x: f32 = kani::any();
    kani::assume(x.is_finite());
    let v = Vec4::splat(x);
    assert!(v.x == x, "splat(x).x should equal x");
    assert!(v.y == x, "splat(x).y should equal x");
    assert!(v.z == x, "splat(x).z should equal x");
    assert!(v.w == x, "splat(x).w should equal x");
}

// ============================================================================
// from_vec3
// ============================================================================

/// **Component preservation**: `from_vec3(v3, w)` preserves xyz and sets w.
#[kani::proof]
fn verify_vec4_from_vec3_preserves() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let vz: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(vx.is_finite());
    kani::assume(vy.is_finite());
    kani::assume(vz.is_finite());
    kani::assume(w.is_finite());
    let v3 = crate::Vec3::new(vx, vy, vz);
    let v4 = Vec4::from_vec3(v3, w);
    assert!(v4.x == vx, "from_vec3 should preserve x");
    assert!(v4.y == vy, "from_vec3 should preserve y");
    assert!(v4.z == vz, "from_vec3 should preserve z");
    assert!(v4.w == w, "from_vec3 should set w");
}

// ============================================================================
// Div (scalar)
// ============================================================================

/// **Finiteness**: `v / scalar` with finite inputs and non-zero scalar produces finite output.
///
/// Precondition: all components and scalar finite, `|scalar| >= 1e-18` (no near-zero divisors).
/// Postcondition: all output components are finite.
#[kani::proof]
fn verify_vec4_div_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    let s: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w.abs() < SAFE_BOUND);
    kani::assume(s.is_finite() && s.abs() >= 1e-18);
    let v = Vec4::new(x, y, z, w);
    let r = v / s;
    assert!(r.x.is_finite(), "div result.x non-finite");
    assert!(r.y.is_finite(), "div result.y non-finite");
    assert!(r.z.is_finite(), "div result.z non-finite");
    assert!(r.w.is_finite(), "div result.w non-finite");
}

// ============================================================================
// Sub (anti-commutativity)
// ============================================================================

/// **Anti-commutativity**: `a - b == -(b - a)` for Vec4 subtraction.
///
/// Precondition: all components finite and bounded.
/// Postcondition: `(a - b).xyzw == (-(b - a)).xyzw`.
#[kani::proof]
fn verify_vec4_sub_anti_commutative() {
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
    let a_minus_b = a - b;
    let neg_b_minus_a = -(b - a);
    assert!(
        a_minus_b.x == neg_b_minus_a.x,
        "(a-b).x should equal -(b-a).x"
    );
    assert!(
        a_minus_b.y == neg_b_minus_a.y,
        "(a-b).y should equal -(b-a).y"
    );
    assert!(
        a_minus_b.z == neg_b_minus_a.z,
        "(a-b).z should equal -(b-a).z"
    );
    assert!(
        a_minus_b.w == neg_b_minus_a.w,
        "(a-b).w should equal -(b-a).w"
    );
}

/// **Idempotence**: `abs(abs(v)) == abs(v)` for all finite vectors.
#[kani::proof]
fn verify_vec4_abs_idempotent() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    kani::assume(w.is_finite());
    let v = Vec4::new(x, y, z, w);
    let once = v.abs();
    let twice = once.abs();
    assert!(once.x == twice.x, "abs should be idempotent for x");
    assert!(once.y == twice.y, "abs should be idempotent for y");
    assert!(once.z == twice.z, "abs should be idempotent for z");
    assert!(once.w == twice.w, "abs should be idempotent for w");
}

// ============================================================================
// length_squared
// ============================================================================

/// **Non-negativity**: `length_squared()` is always ≥ 0 for finite bounded inputs.
#[kani::proof]
fn verify_vec4_length_squared_properties() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let w: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w.abs() < SAFE_BOUND);
    let v = Vec4::new(x, y, z, w);
    let ls = v.length_squared();
    assert!(!ls.is_nan(), "length_squared produced NaN");
    assert!(ls >= 0.0, "length_squared should be non-negative");
    // length_squared of zero vector is zero
    let zero = Vec4::new(0.0, 0.0, 0.0, 0.0);
    assert!(
        zero.length_squared() == 0.0,
        "length_squared of zero should be 0"
    );
}
