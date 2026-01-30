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
