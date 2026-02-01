// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Vec3 f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for Vec3 operations: length,
//! normalized, dot, cross, project, and distance.

use crate::Vec3;

/// Bound for 3-component dot: `x² + y² + z² < MAX` → `|v| < sqrt(MAX/3)`.
const SAFE_BOUND: f32 = 1e18;

// ============================================================================
// length / length_squared
// ============================================================================

/// **NaN-freedom + non-negativity**: `length()` with bounded inputs.
#[kani::proof]
fn verify_vec3_length_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    let v = Vec3::new(x, y, z);
    let len = v.length();
    assert!(!len.is_nan(), "length() produced NaN");
    assert!(len >= 0.0, "length() returned negative value");
}

// ============================================================================
// normalized
// ============================================================================

/// **NaN-freedom**: `normalized()` with bounded inputs never produces NaN.
#[kani::proof]
fn verify_vec3_normalized_no_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    let v = Vec3::new(x, y, z);
    let n = v.normalized();
    assert!(!n.x.is_nan(), "normalized().x is NaN");
    assert!(!n.y.is_nan(), "normalized().y is NaN");
    assert!(!n.z.is_nan(), "normalized().z is NaN");
}

// ============================================================================
// dot
// ============================================================================

/// **Finiteness**: `dot()` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec3_dot_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let d = a.dot(b);
    assert!(d.is_finite(), "dot() produced non-finite output");
}

// ============================================================================
// cross
// ============================================================================

/// **Finiteness**: `cross()` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec3_cross_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let c = a.cross(b);
    assert!(c.x.is_finite(), "cross().x non-finite");
    assert!(c.y.is_finite(), "cross().y non-finite");
    assert!(c.z.is_finite(), "cross().z non-finite");
}

// ============================================================================
// project
// ============================================================================

/// **Zero-guard**: `project()` onto zero vector returns ZERO.
#[kani::proof]
fn verify_vec3_project_zero_guard() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let vz: f32 = kani::any();
    kani::assume(vx.is_finite() && vx.abs() < SAFE_BOUND);
    kani::assume(vy.is_finite() && vy.abs() < SAFE_BOUND);
    kani::assume(vz.is_finite() && vz.abs() < SAFE_BOUND);
    let v = Vec3::new(vx, vy, vz);
    let result = v.project(Vec3::ZERO);
    assert!(result.x == 0.0, "project onto zero should return zero x");
    assert!(result.y == 0.0, "project onto zero should return zero y");
    assert!(result.z == 0.0, "project onto zero should return zero z");
}

// ============================================================================
// distance
// ============================================================================

/// **Non-negativity**: `distance()` with bounded inputs is ≥ 0.
#[kani::proof]
fn verify_vec3_distance_non_negative() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let d = a.distance(b);
    assert!(d >= 0.0, "distance() returned negative value");
    assert!(!d.is_nan(), "distance() produced NaN");
}

// ============================================================================
// distance_squared
// ============================================================================

/// **Non-negativity + finiteness**: `distance_squared()` with bounded inputs.
#[kani::proof]
fn verify_vec3_distance_squared_non_negative() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let d = a.distance_squared(b);
    assert!(d >= 0.0, "distance_squared() returned negative value");
    assert!(!d.is_nan(), "distance_squared() produced NaN");
    assert!(d.is_finite(), "distance_squared() non-finite");
}

// ============================================================================
// lerp
// ============================================================================

/// **NaN-freedom + finiteness**: `lerp()` with bounded inputs and t ∈ [0,1].
#[kani::proof]
fn verify_vec3_lerp_no_nan() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    let t: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    kani::assume(t.is_finite() && t >= 0.0 && t <= 1.0);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let r = a.lerp(b, t);
    assert!(!r.x.is_nan(), "lerp().x is NaN");
    assert!(!r.y.is_nan(), "lerp().y is NaN");
    assert!(!r.z.is_nan(), "lerp().z is NaN");
}

// ============================================================================
// abs
// ============================================================================

/// **Non-negativity**: `abs()` with finite inputs produces non-negative components.
#[kani::proof]
fn verify_vec3_abs_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    let v = Vec3::new(x, y, z);
    let a = v.abs();
    assert!(a.x >= 0.0, "abs().x should be non-negative");
    assert!(a.y >= 0.0, "abs().y should be non-negative");
    assert!(a.z >= 0.0, "abs().z should be non-negative");
}

// ============================================================================
// floor / ceil / round
// ============================================================================

/// **Finiteness**: `floor()` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec3_floor_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    let v = Vec3::new(x, y, z);
    let f = v.floor();
    assert!(f.x.is_finite(), "floor().x non-finite");
    assert!(f.y.is_finite(), "floor().y non-finite");
    assert!(f.z.is_finite(), "floor().z non-finite");
}

/// **Finiteness**: `ceil()` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec3_ceil_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    let v = Vec3::new(x, y, z);
    let c = v.ceil();
    assert!(c.x.is_finite(), "ceil().x non-finite");
    assert!(c.y.is_finite(), "ceil().y non-finite");
    assert!(c.z.is_finite(), "ceil().z non-finite");
}

/// **Finiteness**: `round()` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec3_round_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    let v = Vec3::new(x, y, z);
    let r = v.round();
    assert!(r.x.is_finite(), "round().x non-finite");
    assert!(r.y.is_finite(), "round().y non-finite");
    assert!(r.z.is_finite(), "round().z non-finite");
}

// ============================================================================
// min / max
// ============================================================================

/// **Postcondition**: `min(a, b)` components are ≤ both `a` and `b` components.
#[kani::proof]
fn verify_vec3_min_componentwise() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite());
    kani::assume(ay.is_finite());
    kani::assume(az.is_finite());
    kani::assume(bx.is_finite());
    kani::assume(by.is_finite());
    kani::assume(bz.is_finite());
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let m = a.min(b);
    assert!(m.x <= ax && m.x <= bx, "min().x not minimum");
    assert!(m.y <= ay && m.y <= by, "min().y not minimum");
    assert!(m.z <= az && m.z <= bz, "min().z not minimum");
}

/// **Postcondition**: `max(a, b)` components are ≥ both `a` and `b` components.
#[kani::proof]
fn verify_vec3_max_componentwise() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite());
    kani::assume(ay.is_finite());
    kani::assume(az.is_finite());
    kani::assume(bx.is_finite());
    kani::assume(by.is_finite());
    kani::assume(bz.is_finite());
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let m = a.max(b);
    assert!(m.x >= ax && m.x >= bx, "max().x not maximum");
    assert!(m.y >= ay && m.y >= by, "max().y not maximum");
    assert!(m.z >= az && m.z >= bz, "max().z not maximum");
}

// ============================================================================
// clamp
// ============================================================================

/// **Postcondition**: `clamp(v, min, max)` result is within [min, max] bounds.
#[kani::proof]
fn verify_vec3_clamp_bounded() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let vz: f32 = kani::any();
    let minx: f32 = kani::any();
    let miny: f32 = kani::any();
    let minz: f32 = kani::any();
    let maxx: f32 = kani::any();
    let maxy: f32 = kani::any();
    let maxz: f32 = kani::any();
    kani::assume(vx.is_finite());
    kani::assume(vy.is_finite());
    kani::assume(vz.is_finite());
    kani::assume(minx.is_finite());
    kani::assume(miny.is_finite());
    kani::assume(minz.is_finite());
    kani::assume(maxx.is_finite());
    kani::assume(maxy.is_finite());
    kani::assume(maxz.is_finite());
    kani::assume(minx <= maxx);
    kani::assume(miny <= maxy);
    kani::assume(minz <= maxz);
    let v = Vec3::new(vx, vy, vz);
    let lo = Vec3::new(minx, miny, minz);
    let hi = Vec3::new(maxx, maxy, maxz);
    let c = v.clamp(lo, hi);
    assert!(c.x >= minx && c.x <= maxx, "clamp().x out of bounds");
    assert!(c.y >= miny && c.y <= maxy, "clamp().y out of bounds");
    assert!(c.z >= minz && c.z <= maxz, "clamp().z out of bounds");
}

// ============================================================================
// reflect
// ============================================================================

/// **Finiteness**: `reflect()` with bounded inputs produces finite output.
///
/// Reflect formula: `self - normal * 2.0 * self.dot(normal)`.
/// With bounded inputs, all intermediate values remain finite.
#[kani::proof]
fn verify_vec3_reflect_finite() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let vz: f32 = kani::any();
    let nx: f32 = kani::any();
    let ny: f32 = kani::any();
    let nz: f32 = kani::any();
    kani::assume(vx.is_finite() && vx.abs() < SAFE_BOUND);
    kani::assume(vy.is_finite() && vy.abs() < SAFE_BOUND);
    kani::assume(vz.is_finite() && vz.abs() < SAFE_BOUND);
    kani::assume(nx.is_finite() && nx.abs() < 2.0);
    kani::assume(ny.is_finite() && ny.abs() < 2.0);
    kani::assume(nz.is_finite() && nz.abs() < 2.0);
    let v = Vec3::new(vx, vy, vz);
    let n = Vec3::new(nx, ny, nz);
    let r = v.reflect(n);
    assert!(r.x.is_finite(), "reflect().x non-finite");
    assert!(r.y.is_finite(), "reflect().y non-finite");
    assert!(r.z.is_finite(), "reflect().z non-finite");
}

// ============================================================================
// approx_eq
// ============================================================================

/// **Reflexivity**: `approx_eq(v, v)` is true for all finite vectors.
#[kani::proof]
fn verify_vec3_approx_eq_reflexive() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    let v = Vec3::new(x, y, z);
    assert!(v.approx_eq(v), "approx_eq not reflexive");
}

// ============================================================================
// project (NaN-freedom with non-degenerate onto)
// ============================================================================

/// **NaN-freedom**: `project()` with bounded non-degenerate onto vector.
#[kani::proof]
fn verify_vec3_project_no_nan() {
    let vx: f32 = kani::any();
    let vy: f32 = kani::any();
    let vz: f32 = kani::any();
    let ox: f32 = kani::any();
    let oy: f32 = kani::any();
    let oz: f32 = kani::any();
    kani::assume(vx.is_finite() && vx.abs() < SAFE_BOUND);
    kani::assume(vy.is_finite() && vy.abs() < SAFE_BOUND);
    kani::assume(vz.is_finite() && vz.abs() < SAFE_BOUND);
    kani::assume(ox.is_finite() && ox.abs() < SAFE_BOUND);
    kani::assume(oy.is_finite() && oy.abs() < SAFE_BOUND);
    kani::assume(oz.is_finite() && oz.abs() < SAFE_BOUND);
    // Require non-degenerate onto: length_squared above f32 min_positive
    kani::assume(ox * ox + oy * oy + oz * oz > f32::MIN_POSITIVE);
    let v = Vec3::new(vx, vy, vz);
    let onto = Vec3::new(ox, oy, oz);
    let result = v.project(onto);
    assert!(!result.x.is_nan(), "project().x is NaN");
    assert!(!result.y.is_nan(), "project().y is NaN");
    assert!(!result.z.is_nan(), "project().z is NaN");
}

// ============================================================================
// length_squared
// ============================================================================

/// **Non-negativity**: `length_squared()` with bounded inputs is non-negative.
#[kani::proof]
fn verify_vec3_length_squared_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    let v = Vec3::new(x, y, z);
    let lsq = v.length_squared();
    assert!(!lsq.is_nan(), "length_squared() produced NaN");
    assert!(lsq >= 0.0, "length_squared() returned negative value");
}

// ============================================================================
// sub (via operator overloading)
// ============================================================================

/// **Finiteness**: `a - b` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec3_sub_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let r = a - b;
    assert!(r.x.is_finite(), "sub result x is not finite");
    assert!(r.y.is_finite(), "sub result y is not finite");
    assert!(r.z.is_finite(), "sub result z is not finite");
}

// ============================================================================
// add (via operator overloading)
// ============================================================================

/// **Finiteness**: `a + b` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec3_add_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let r = a + b;
    assert!(r.x.is_finite(), "add result x is not finite");
    assert!(r.y.is_finite(), "add result y is not finite");
    assert!(r.z.is_finite(), "add result z is not finite");
}

// ============================================================================
// neg
// ============================================================================

/// **Finiteness**: `-v` with finite inputs produces finite output.
#[kani::proof]
fn verify_vec3_neg_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    let v = Vec3::new(x, y, z);
    let r = -v;
    assert!(r.x.is_finite(), "neg result x is not finite");
    assert!(r.y.is_finite(), "neg result y is not finite");
    assert!(r.z.is_finite(), "neg result z is not finite");
}

// ============================================================================
// scale
// ============================================================================

/// **Finiteness**: `v * scalar` with bounded inputs produces finite output.
#[kani::proof]
fn verify_vec3_scale_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    let s: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < 1e18);
    kani::assume(y.is_finite() && y.abs() < 1e18);
    kani::assume(z.is_finite() && z.abs() < 1e18);
    kani::assume(s.is_finite() && s.abs() < 1e18);
    let v = Vec3::new(x, y, z);
    let r = v * s;
    assert!(r.x.is_finite(), "scale result x is not finite");
    assert!(r.y.is_finite(), "scale result y is not finite");
    assert!(r.z.is_finite(), "scale result z is not finite");
}

// ============================================================================
// splat
// ============================================================================

/// **Uniformity**: `splat(x)` produces a vector with all components equal to `x`.
#[kani::proof]
fn verify_vec3_splat_all_equal() {
    let x: f32 = kani::any();
    kani::assume(x.is_finite());
    let v = Vec3::splat(x);
    assert!(v.x == x, "splat(x).x should equal x");
    assert!(v.y == x, "splat(x).y should equal x");
    assert!(v.z == x, "splat(x).z should equal x");
}

// ============================================================================
// neg involution
// ============================================================================

/// **Involution**: `-(-v) == v` for all finite vectors (IEEE 754 sign-bit flip).
#[kani::proof]
fn verify_vec3_neg_involution() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(z.is_finite());
    let v = Vec3::new(x, y, z);
    let r = -(-v);
    assert!(r.x == x, "-(-v).x should equal v.x");
    assert!(r.y == y, "-(-v).y should equal v.y");
    assert!(r.z == z, "-(-v).z should equal v.z");
}

// ============================================================================
// add commutativity
// ============================================================================

/// **Commutativity**: `a + b == b + a` for all finite bounded vectors (IEEE 754).
#[kani::proof]
fn verify_vec3_add_commutative() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
    let ab = a + b;
    let ba = b + a;
    assert!(ab.x == ba.x, "(a+b).x should equal (b+a).x");
    assert!(ab.y == ba.y, "(a+b).y should equal (b+a).y");
    assert!(ab.z == ba.z, "(a+b).z should equal (b+a).z");
}

// ============================================================================
// dot self non-negative
// ============================================================================

/// **Non-negativity**: `v.dot(v)` is always non-negative for finite bounded vectors.
#[kani::proof]
fn verify_vec3_dot_self_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let z: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(z.is_finite() && z.abs() < SAFE_BOUND);
    let v = Vec3::new(x, y, z);
    let d = v.dot(v);
    assert!(!d.is_nan(), "v.dot(v) produced NaN");
    assert!(d >= 0.0, "v.dot(v) returned negative value");
}

// ============================================================================
// sub anti-commutativity
// ============================================================================

/// **Anti-commutativity**: `a - b == -(b - a)` for all finite bounded vectors.
#[kani::proof]
fn verify_vec3_sub_anti_commutative() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let az: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bz: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(az.is_finite() && az.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bz.is_finite() && bz.abs() < SAFE_BOUND);
    let a = Vec3::new(ax, ay, az);
    let b = Vec3::new(bx, by, bz);
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
}
