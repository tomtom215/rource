// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Vec2 Operations
//!
//! This module contains machine-checked proofs of correctness for Vec2 operations
//! using the Verus formal verification tool.
//!
//! ## Verification Status
//!
//! All proofs in this file have been verified by Verus with zero admits.
//!
//! ## Properties Verified
//!
//! 1. **Algebraic Properties**
//!    - Addition commutativity: a + b = b + a
//!    - Addition associativity: (a + b) + c = a + (b + c)
//!    - Additive identity: a + 0 = a
//!    - Additive inverse: a + (-a) = 0
//!    - Scalar multiplication associativity: (s * t) * v = s * (t * v)
//!    - Scalar distribution over vector addition: s * (a + b) = s * a + s * b
//!    - Vector distribution over scalar addition: (s + t) * v = s * v + t * v
//!
//! 2. **Geometric Properties**
//!    - Dot product commutativity: a · b = b · a
//!    - Dot product positive-definiteness: a · a ≥ 0
//!    - Cross product anti-symmetry: a × b = -(b × a)
//!    - Perpendicular dot product: perp(a) · a = 0
//!
//! 3. **Length Properties**
//!    - Non-negativity: length_squared(a) ≥ 0
//!
//! ## Proof Methodology
//!
//! We model Vec2 operations over mathematical integers. This proves the algorithms
//! are mathematically correct for exact arithmetic. The translation to IEEE 754
//! floating point introduces precision considerations documented separately.
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/vec2_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Vec2 Specification Type
// =============================================================================

/// Mathematical specification of a 2D vector over integers.
#[derive(PartialEq, Eq)]
pub struct SpecVec2 {
    pub x: int,
    pub y: int,
}

// =============================================================================
// Vector Operations (Spec Functions)
// =============================================================================

/// Creates a new vector.
pub open spec fn vec2_new(x: int, y: int) -> SpecVec2 {
    SpecVec2 { x, y }
}

/// The zero vector.
pub open spec fn vec2_zero() -> SpecVec2 {
    SpecVec2 { x: 0, y: 0 }
}

/// Vector addition: a + b
pub open spec fn vec2_add(a: SpecVec2, b: SpecVec2) -> SpecVec2 {
    SpecVec2 { x: a.x + b.x, y: a.y + b.y }
}

/// Vector subtraction: a - b
pub open spec fn vec2_sub(a: SpecVec2, b: SpecVec2) -> SpecVec2 {
    SpecVec2 { x: a.x - b.x, y: a.y - b.y }
}

/// Scalar multiplication: s * v
pub open spec fn vec2_scale(s: int, v: SpecVec2) -> SpecVec2 {
    SpecVec2 { x: s * v.x, y: s * v.y }
}

/// Vector negation: -v
pub open spec fn vec2_neg(v: SpecVec2) -> SpecVec2 {
    SpecVec2 { x: -v.x, y: -v.y }
}

/// Dot product: a · b
pub open spec fn vec2_dot(a: SpecVec2, b: SpecVec2) -> int {
    a.x * b.x + a.y * b.y
}

/// Cross product (2D pseudo-cross, returns scalar): a × b
pub open spec fn vec2_cross(a: SpecVec2, b: SpecVec2) -> int {
    a.x * b.y - a.y * b.x
}

/// Perpendicular vector (90° counter-clockwise rotation)
pub open spec fn vec2_perp(v: SpecVec2) -> SpecVec2 {
    SpecVec2 { x: -v.y, y: v.x }
}

/// Length squared: |v|²
pub open spec fn vec2_length_squared(v: SpecVec2) -> int {
    vec2_dot(v, v)
}

/// Component-wise multiplication: a * b
pub open spec fn vec2_mul(a: SpecVec2, b: SpecVec2) -> SpecVec2 {
    SpecVec2 { x: a.x * b.x, y: a.y * b.y }
}

// =============================================================================
// ALGEBRAIC PROOFS
// =============================================================================

/// **Theorem 1**: Vector addition is commutative.
///
/// For all vectors a, b: a + b = b + a
proof fn vec2_add_commutative(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_add(a, b) == vec2_add(b, a),
{
    // Follows from commutativity of integer addition
    assert(a.x + b.x == b.x + a.x);
    assert(a.y + b.y == b.y + a.y);
}

/// **Theorem 2**: Vector addition is associative.
///
/// For all vectors a, b, c: (a + b) + c = a + (b + c)
proof fn vec2_add_associative(a: SpecVec2, b: SpecVec2, c: SpecVec2)
    ensures
        vec2_add(vec2_add(a, b), c) == vec2_add(a, vec2_add(b, c)),
{
    // Follows from associativity of integer addition
    assert((a.x + b.x) + c.x == a.x + (b.x + c.x));
    assert((a.y + b.y) + c.y == a.y + (b.y + c.y));
}

/// **Theorem 3**: The zero vector is an additive identity.
///
/// For all vectors a: a + 0 = a
proof fn vec2_add_identity(a: SpecVec2)
    ensures
        vec2_add(a, vec2_zero()) == a,
{
    assert(a.x + 0 == a.x);
    assert(a.y + 0 == a.y);
}

/// **Theorem 4**: Every vector has an additive inverse.
///
/// For all vectors a: a + (-a) = 0
proof fn vec2_add_inverse(a: SpecVec2)
    ensures
        vec2_add(a, vec2_neg(a)) == vec2_zero(),
{
    assert(a.x + (-a.x) == 0);
    assert(a.y + (-a.y) == 0);
}

/// **Theorem 5**: Scalar multiplication is associative.
///
/// For all scalars s, t and vector v: (s * t) * v = s * (t * v)
proof fn vec2_scale_associative(s: int, t: int, v: SpecVec2)
    ensures
        vec2_scale(s * t, v) == vec2_scale(s, vec2_scale(t, v)),
{
    // Need to show: (s * t) * v.x == s * (t * v.x)
    // This follows from associativity of integer multiplication
    assert((s * t) * v.x == s * (t * v.x)) by(nonlinear_arith);
    assert((s * t) * v.y == s * (t * v.y)) by(nonlinear_arith);
}

/// **Theorem 6**: Scalar multiplication distributes over vector addition.
///
/// For all scalars s and vectors a, b: s * (a + b) = s * a + s * b
proof fn vec2_scale_distributes_over_add(s: int, a: SpecVec2, b: SpecVec2)
    ensures
        vec2_scale(s, vec2_add(a, b)) == vec2_add(vec2_scale(s, a), vec2_scale(s, b)),
{
    // s * (a.x + b.x) == s * a.x + s * b.x by distributivity
    assert(s * (a.x + b.x) == s * a.x + s * b.x) by(nonlinear_arith);
    assert(s * (a.y + b.y) == s * a.y + s * b.y) by(nonlinear_arith);
}

/// **Theorem 7**: Vector addition distributes over scalar addition.
///
/// For all scalars s, t and vector v: (s + t) * v = s * v + t * v
proof fn vec2_add_scalars_distributes(s: int, t: int, v: SpecVec2)
    ensures
        vec2_scale(s + t, v) == vec2_add(vec2_scale(s, v), vec2_scale(t, v)),
{
    // (s + t) * v.x == s * v.x + t * v.x by distributivity
    assert((s + t) * v.x == s * v.x + t * v.x) by(nonlinear_arith);
    assert((s + t) * v.y == s * v.y + t * v.y) by(nonlinear_arith);
}

/// **Theorem 8**: Scaling by 1 is the identity operation.
///
/// For all vectors v: 1 * v = v
proof fn vec2_scale_identity(v: SpecVec2)
    ensures
        vec2_scale(1, v) == v,
{
    assert(1 * v.x == v.x);
    assert(1 * v.y == v.y);
}

/// **Theorem 9**: Scaling by 0 produces the zero vector.
///
/// For all vectors v: 0 * v = 0
proof fn vec2_scale_zero(v: SpecVec2)
    ensures
        vec2_scale(0, v) == vec2_zero(),
{
    assert(0 * v.x == 0);
    assert(0 * v.y == 0);
}

// =============================================================================
// GEOMETRIC PROOFS
// =============================================================================

/// **Theorem 10**: Dot product is commutative.
///
/// For all vectors a, b: a · b = b · a
proof fn vec2_dot_commutative(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_dot(a, b) == vec2_dot(b, a),
{
    // a.x * b.x + a.y * b.y == b.x * a.x + b.y * a.y
    assert(a.x * b.x == b.x * a.x) by(nonlinear_arith);
    assert(a.y * b.y == b.y * a.y) by(nonlinear_arith);
}

/// **Theorem 11**: Dot product is bilinear (linear in first argument).
///
/// For all scalars s and vectors a, b: (s * a) · b = s * (a · b)
proof fn vec2_dot_linear_first(s: int, a: SpecVec2, b: SpecVec2)
    ensures
        vec2_dot(vec2_scale(s, a), b) == s * vec2_dot(a, b),
{
    // (s * a.x) * b.x + (s * a.y) * b.y == s * (a.x * b.x + a.y * b.y)
    assert((s * a.x) * b.x == s * (a.x * b.x)) by(nonlinear_arith);
    assert((s * a.y) * b.y == s * (a.y * b.y)) by(nonlinear_arith);
    assert((s * a.x) * b.x + (s * a.y) * b.y == s * (a.x * b.x) + s * (a.y * b.y));
    assert(s * (a.x * b.x) + s * (a.y * b.y) == s * (a.x * b.x + a.y * b.y)) by(nonlinear_arith);
}

/// **Theorem 12**: Dot product is bilinear (distributes over addition).
///
/// For all vectors a, b, c: (a + b) · c = a · c + b · c
proof fn vec2_dot_distributes(a: SpecVec2, b: SpecVec2, c: SpecVec2)
    ensures
        vec2_dot(vec2_add(a, b), c) == vec2_dot(a, c) + vec2_dot(b, c),
{
    // (a.x + b.x) * c.x + (a.y + b.y) * c.y
    // == a.x * c.x + b.x * c.x + a.y * c.y + b.y * c.y
    // == (a.x * c.x + a.y * c.y) + (b.x * c.x + b.y * c.y)
    assert((a.x + b.x) * c.x == a.x * c.x + b.x * c.x) by(nonlinear_arith);
    assert((a.y + b.y) * c.y == a.y * c.y + b.y * c.y) by(nonlinear_arith);
}

/// **Theorem 13**: Cross product is anti-commutative.
///
/// For all vectors a, b: a × b = -(b × a)
proof fn vec2_cross_anticommutative(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_cross(a, b) == -vec2_cross(b, a),
{
    // a.x * b.y - a.y * b.x == -(b.x * a.y - b.y * a.x)
    assert(a.x * b.y == b.y * a.x) by(nonlinear_arith);
    assert(a.y * b.x == b.x * a.y) by(nonlinear_arith);
}

/// **Theorem 14**: Cross product of a vector with itself is zero.
///
/// For all vectors a: a × a = 0
proof fn vec2_cross_self_zero(a: SpecVec2)
    ensures
        vec2_cross(a, a) == 0,
{
    // a.x * a.y - a.y * a.x = 0
    assert(a.x * a.y == a.y * a.x) by(nonlinear_arith);
}

/// **Theorem 15**: The perpendicular vector is orthogonal to the original.
///
/// For all vectors a: perp(a) · a = 0
proof fn vec2_perp_orthogonal(a: SpecVec2)
    ensures
        vec2_dot(vec2_perp(a), a) == 0,
{
    // perp(a) = (-a.y, a.x)
    // perp(a) · a = (-a.y) * a.x + a.x * a.y
    //            = -a.y * a.x + a.x * a.y
    //            = 0
    assert((-a.y) * a.x == -(a.y * a.x)) by(nonlinear_arith);
    assert(a.x * a.y == a.y * a.x) by(nonlinear_arith);
    assert(-(a.y * a.x) + a.x * a.y == 0);
}

/// **Theorem 16**: Double perpendicular equals negation.
///
/// For all vectors a: perp(perp(a)) = -a
proof fn vec2_perp_double_is_neg(a: SpecVec2)
    ensures
        vec2_perp(vec2_perp(a)) == vec2_neg(a),
{
    // perp(a) = (-a.y, a.x)
    // perp(perp(a)) = (-a.x, -a.y) = -a
    let p1 = vec2_perp(a);
    assert(p1.x == -a.y);
    assert(p1.y == a.x);
    let p2 = vec2_perp(p1);
    assert(p2.x == -p1.y);
    assert(p2.y == p1.x);
    assert(p2.x == -a.x);
    assert(p2.y == -a.y);
}

// =============================================================================
// LENGTH PROOFS
// =============================================================================

/// **Theorem 17**: Length squared is always non-negative.
///
/// For all vectors a: |a|² ≥ 0
///
/// Proof: |a|² = a.x² + a.y², which is a sum of squares.
proof fn vec2_length_squared_nonnegative(a: SpecVec2)
    ensures
        vec2_length_squared(a) >= 0,
{
    // |a|² = a.x * a.x + a.y * a.y
    // Both terms are non-negative (squares of integers)
    assert(a.x * a.x >= 0) by(nonlinear_arith);
    assert(a.y * a.y >= 0) by(nonlinear_arith);
}

/// **Theorem 18**: Length squared is zero iff vector is zero.
///
/// For all vectors a: |a|² = 0 ⟺ a = 0
proof fn vec2_length_squared_zero_iff_zero(a: SpecVec2)
    ensures
        vec2_length_squared(a) == 0 <==> a == vec2_zero(),
{
    // Forward: if a = 0, then |a|² = 0
    // Backward: if |a|² = 0, since x² ≥ 0 and y² ≥ 0, both must be 0
    assert(a.x * a.x >= 0) by(nonlinear_arith);
    assert(a.y * a.y >= 0) by(nonlinear_arith);
    assert(a.x * a.x == 0 ==> a.x == 0) by(nonlinear_arith);
    assert(a.y * a.y == 0 ==> a.y == 0) by(nonlinear_arith);
    // If a.x² + a.y² = 0 and both are non-negative, both must be 0
    if a.x * a.x + a.y * a.y == 0 {
        assert(a.x * a.x == 0);
        assert(a.y * a.y == 0);
    }
}

// =============================================================================
// ADDITIONAL GEOMETRIC PROOFS
// =============================================================================

/// **Theorem 19**: Subtraction is equivalent to adding the negative.
///
/// For all vectors a, b: a - b = a + (-b)
proof fn vec2_sub_is_add_neg(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_sub(a, b) == vec2_add(a, vec2_neg(b)),
{
    assert(a.x - b.x == a.x + (-b.x));
    assert(a.y - b.y == a.y + (-b.y));
}

/// **Theorem 20**: Component-wise multiplication is commutative.
///
/// For all vectors a, b: a * b = b * a
proof fn vec2_mul_commutative(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_mul(a, b) == vec2_mul(b, a),
{
    assert(a.x * b.x == b.x * a.x) by(nonlinear_arith);
    assert(a.y * b.y == b.y * a.y) by(nonlinear_arith);
}

/// **Theorem 21**: Cross product equals perpendicular dot product.
///
/// For all vectors a, b: a × b = perp(a) · b
proof fn vec2_cross_equals_perp_dot(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_cross(a, b) == vec2_dot(vec2_perp(a), b),
{
    // cross(a, b) = a.x * b.y - a.y * b.x
    // perp(a) = (-a.y, a.x)
    // dot(perp(a), b) = (-a.y) * b.x + a.x * b.y = a.x * b.y - a.y * b.x
    assert((-a.y) * b.x == -(a.y * b.x)) by(nonlinear_arith);
    assert(a.x * b.y + (-(a.y * b.x)) == a.x * b.y - a.y * b.x);
}

/// **Theorem 22**: Scaling negates via negative scalar.
///
/// For all vectors v: -v = (-1) * v
proof fn vec2_neg_is_scale_neg_one(v: SpecVec2)
    ensures
        vec2_neg(v) == vec2_scale(-1, v),
{
    assert(-v.x == (-1) * v.x) by(nonlinear_arith);
    assert(-v.y == (-1) * v.y) by(nonlinear_arith);
}

// =============================================================================
// EXTENDED OPERATIONS (Spec Functions)
// =============================================================================

/// Creates a vector with both components set to the same value.
pub open spec fn vec2_splat(value: int) -> SpecVec2 {
    SpecVec2 { x: value, y: value }
}

/// Component-wise minimum of two vectors.
pub open spec fn vec2_min(a: SpecVec2, b: SpecVec2) -> SpecVec2 {
    SpecVec2 {
        x: if a.x <= b.x { a.x } else { b.x },
        y: if a.y <= b.y { a.y } else { b.y },
    }
}

/// Component-wise maximum of two vectors.
pub open spec fn vec2_max(a: SpecVec2, b: SpecVec2) -> SpecVec2 {
    SpecVec2 {
        x: if a.x >= b.x { a.x } else { b.x },
        y: if a.y >= b.y { a.y } else { b.y },
    }
}

/// Component-wise absolute value.
pub open spec fn vec2_abs(v: SpecVec2) -> SpecVec2 {
    SpecVec2 {
        x: if v.x >= 0 { v.x } else { -v.x },
        y: if v.y >= 0 { v.y } else { -v.y },
    }
}

/// Component-wise clamp.
pub open spec fn vec2_clamp(v: SpecVec2, lo: SpecVec2, hi: SpecVec2) -> SpecVec2 {
    SpecVec2 {
        x: if v.x < lo.x { lo.x } else if v.x > hi.x { hi.x } else { v.x },
        y: if v.y < lo.y { lo.y } else if v.y > hi.y { hi.y } else { v.y },
    }
}

/// Squared distance between two points.
pub open spec fn vec2_distance_squared(a: SpecVec2, b: SpecVec2) -> int {
    vec2_length_squared(vec2_sub(a, b))
}

/// Reflection of v off surface with normal n: v - 2*(v·n)*n.
pub open spec fn vec2_reflect(v: SpecVec2, n: SpecVec2) -> SpecVec2 {
    vec2_sub(v, vec2_scale(2 * vec2_dot(v, n), n))
}

/// Sum of all components.
pub open spec fn vec2_element_sum(v: SpecVec2) -> int {
    v.x + v.y
}

/// Product of all components.
pub open spec fn vec2_element_product(v: SpecVec2) -> int {
    v.x * v.y
}

// =============================================================================
// SPLAT PROOFS
// =============================================================================

/// **Theorem 24**: Splat is equivalent to new(v, v).
proof fn vec2_splat_is_new(value: int)
    ensures
        vec2_splat(value) == vec2_new(value, value),
{
}

/// **Theorem 25**: Splat(0) is the zero vector.
proof fn vec2_splat_zero()
    ensures
        vec2_splat(0) == vec2_zero(),
{
}

// =============================================================================
// MIN/MAX PROOFS
// =============================================================================

/// **Theorem 26**: Component-wise min is commutative.
proof fn vec2_min_commutative(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_min(a, b) == vec2_min(b, a),
{
    // For x: if a.x <= b.x then a.x, else b.x  ==  if b.x <= a.x then b.x, else a.x
    // When a.x == b.x: both sides give a.x = b.x
    // When a.x < b.x: min(a,b).x = a.x, min(b,a).x = (b.x <= a.x? no) = a.x
    // When a.x > b.x: min(a,b).x = b.x, min(b,a).x = (b.x <= a.x? yes) = b.x
}

/// **Theorem 27**: Component-wise max is commutative.
proof fn vec2_max_commutative(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_max(a, b) == vec2_max(b, a),
{
}

/// **Theorem 28**: min(a, a) = a (idempotent).
proof fn vec2_min_idempotent(a: SpecVec2)
    ensures
        vec2_min(a, a) == a,
{
}

/// **Theorem 29**: max(a, a) = a (idempotent).
proof fn vec2_max_idempotent(a: SpecVec2)
    ensures
        vec2_max(a, a) == a,
{
}

/// **Theorem 30**: min(a, b) + max(a, b) = a + b (component-wise).
///
/// This is a key identity: the min/max partition preserves the sum.
proof fn vec2_min_max_sum(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_add(vec2_min(a, b), vec2_max(a, b)) == vec2_add(a, b),
{
    // For each component: min(a,b) + max(a,b) = a + b
    // Case a.x <= b.x: a.x + b.x = a.x + b.x (confirmed)
    // Case a.x > b.x:  b.x + a.x = a.x + b.x (confirmed)
}

/// **Theorem 31**: min(a, b) is component-wise <= a and <= b.
proof fn vec2_min_le_both(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_min(a, b).x <= a.x && vec2_min(a, b).x <= b.x,
        vec2_min(a, b).y <= a.y && vec2_min(a, b).y <= b.y,
{
}

/// **Theorem 32**: max(a, b) is component-wise >= a and >= b.
proof fn vec2_max_ge_both(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_max(a, b).x >= a.x && vec2_max(a, b).x >= b.x,
        vec2_max(a, b).y >= a.y && vec2_max(a, b).y >= b.y,
{
}

// =============================================================================
// ABS PROOFS
// =============================================================================

/// **Theorem 33**: Abs produces non-negative components.
proof fn vec2_abs_nonneg(v: SpecVec2)
    ensures
        vec2_abs(v).x >= 0 && vec2_abs(v).y >= 0,
{
}

/// **Theorem 34**: Abs is idempotent: abs(abs(v)) = abs(v).
proof fn vec2_abs_idempotent(v: SpecVec2)
    ensures
        vec2_abs(vec2_abs(v)) == vec2_abs(v),
{
    // After first abs, both components are >= 0
    // So second abs is identity
    let a = vec2_abs(v);
    assert(a.x >= 0);
    assert(a.y >= 0);
}

/// **Theorem 35**: Abs of zero is zero.
proof fn vec2_abs_zero()
    ensures
        vec2_abs(vec2_zero()) == vec2_zero(),
{
}

/// **Theorem 36**: Abs of negation equals abs: |−v| = |v|.
proof fn vec2_abs_neg(v: SpecVec2)
    ensures
        vec2_abs(vec2_neg(v)) == vec2_abs(v),
{
    // If v.x >= 0: abs(-v).x = abs(-v.x) = -(-v.x) = v.x = abs(v).x
    // If v.x < 0: abs(-v).x = abs(-v.x) = -v.x (which is > 0) = abs(v).x = -v.x
}

// =============================================================================
// CLAMP PROOFS
// =============================================================================

/// **Theorem 37**: Clamp produces values within bounds (when lo <= hi).
proof fn vec2_clamp_bounds(v: SpecVec2, lo: SpecVec2, hi: SpecVec2)
    requires
        lo.x <= hi.x && lo.y <= hi.y,
    ensures ({
        let c = vec2_clamp(v, lo, hi);
        c.x >= lo.x && c.x <= hi.x && c.y >= lo.y && c.y <= hi.y
    }),
{
}

/// **Theorem 38**: Clamp of in-range value is identity.
proof fn vec2_clamp_identity(v: SpecVec2, lo: SpecVec2, hi: SpecVec2)
    requires
        v.x >= lo.x && v.x <= hi.x && v.y >= lo.y && v.y <= hi.y,
    ensures
        vec2_clamp(v, lo, hi) == v,
{
}

/// **Theorem 39**: Clamp is idempotent (when lo <= hi).
proof fn vec2_clamp_idempotent(v: SpecVec2, lo: SpecVec2, hi: SpecVec2)
    requires
        lo.x <= hi.x && lo.y <= hi.y,
    ensures
        vec2_clamp(vec2_clamp(v, lo, hi), lo, hi) == vec2_clamp(v, lo, hi),
{
    let c = vec2_clamp(v, lo, hi);
    assert(c.x >= lo.x && c.x <= hi.x);
    assert(c.y >= lo.y && c.y <= hi.y);
}

// =============================================================================
// DISTANCE SQUARED PROOFS
// =============================================================================

/// **Theorem 40**: Distance squared is non-negative.
proof fn vec2_distance_squared_nonneg(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_distance_squared(a, b) >= 0,
{
    let d = vec2_sub(a, b);
    vec2_length_squared_nonnegative(d);
}

/// **Theorem 41**: Distance squared is symmetric.
proof fn vec2_distance_squared_symmetric(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_distance_squared(a, b) == vec2_distance_squared(b, a),
{
    let d1 = vec2_sub(a, b);
    let d2 = vec2_sub(b, a);
    // d1 = -d2 (linear arithmetic establishes this from vec2_sub definition)
    assert(d1.x == -d2.x);
    assert(d1.y == -d2.y);
    // (-x)² = x²: feed the linear relationship as a prerequisite to nonlinear_arith
    assert(d1.x * d1.x == d2.x * d2.x) by(nonlinear_arith)
        requires d1.x == -d2.x;
    assert(d1.y * d1.y == d2.y * d2.y) by(nonlinear_arith)
        requires d1.y == -d2.y;
}

/// **Theorem 42**: Distance squared to self is zero.
proof fn vec2_distance_squared_self(a: SpecVec2)
    ensures
        vec2_distance_squared(a, a) == 0,
{
    // sub(a, a) = (0, 0), length_squared((0, 0)) = 0
}

// =============================================================================
// ELEMENT SUM / PRODUCT PROOFS
// =============================================================================

/// **Theorem 43**: Element sum of zero is zero.
proof fn vec2_element_sum_zero()
    ensures
        vec2_element_sum(vec2_zero()) == 0,
{
}

/// **Theorem 44**: Element sum is additive: sum(a + b) = sum(a) + sum(b).
proof fn vec2_element_sum_additive(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_element_sum(vec2_add(a, b)) == vec2_element_sum(a) + vec2_element_sum(b),
{
    // (a.x + b.x) + (a.y + b.y) = (a.x + a.y) + (b.x + b.y)
}

/// **Theorem 45**: Element sum commutes with scaling.
proof fn vec2_element_sum_scale(s: int, v: SpecVec2)
    ensures
        vec2_element_sum(vec2_scale(s, v)) == s * vec2_element_sum(v),
{
    // s * v.x + s * v.y = s * (v.x + v.y)
    assert(s * v.x + s * v.y == s * (v.x + v.y)) by(nonlinear_arith);
}

/// **Theorem 46**: Element product of splat is value squared.
proof fn vec2_element_product_splat(value: int)
    ensures
        vec2_element_product(vec2_splat(value)) == value * value,
{
}

/// **Theorem 47**: Element product is commutative: x*y = y*x.
proof fn vec2_element_product_commutative(v: SpecVec2)
    ensures
        vec2_element_product(v) == v.y * v.x,
{
    assert(v.x * v.y == v.y * v.x) by(nonlinear_arith);
}

// =============================================================================
// REFLECT PROOFS
// =============================================================================

/// **Theorem 48**: Reflecting a vector parallel to normal negates it.
///
/// If v is a scalar multiple of n, reflect(v, n) = -v when |n|² divides appropriately.
/// Special case: reflect(n, n) = n - 2*(n·n)*n for unit-length normal.
/// For integer model with |n|²=1: reflect(n, n) = n - 2n = -n.
proof fn vec2_reflect_along_unit_normal(n: SpecVec2)
    requires
        vec2_dot(n, n) == 1,
    ensures
        vec2_reflect(n, n) == vec2_neg(n),
{
    // reflect(n, n) = n - 2*(n·n)*n = n - 2*1*n = n - 2n = -n
    assert(2 * vec2_dot(n, n) == 2);
    assert(2 * n.x == 2 * 1 * n.x) by(nonlinear_arith);
    assert(2 * n.y == 2 * 1 * n.y) by(nonlinear_arith);
}

/// **Theorem 49**: Reflecting a vector perpendicular to normal preserves it.
///
/// If v · n = 0, then reflect(v, n) = v.
proof fn vec2_reflect_perpendicular(v: SpecVec2, n: SpecVec2)
    requires
        vec2_dot(v, n) == 0,
    ensures
        vec2_reflect(v, n) == v,
{
    // reflect(v, n) = v - 2*(v·n)*n = v - 2*0*n = v - 0 = v
    assert(2 * 0 == 0);
    assert(0 * n.x == 0) by(nonlinear_arith);
    assert(0 * n.y == 0) by(nonlinear_arith);
}

// =============================================================================
// LERP PROOFS
// =============================================================================

/// Integer model of linear interpolation: lerp(a, b, t) = a + (b - a) * t.
pub open spec fn vec2_lerp(a: SpecVec2, b: SpecVec2, t: int) -> SpecVec2 {
    SpecVec2 {
        x: a.x + (b.x - a.x) * t,
        y: a.y + (b.y - a.y) * t,
    }
}

/// **Theorem 50**: lerp(a, b, 0) = a.
proof fn vec2_lerp_zero(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_lerp(a, b, 0) == a,
{
}

/// **Theorem 51**: lerp(a, b, 1) = b.
proof fn vec2_lerp_one(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_lerp(a, b, 1) == b,
{
}

/// **Theorem 52**: lerp(v, v, t) = v for any t.
proof fn vec2_lerp_identity(v: SpecVec2, t: int)
    ensures
        vec2_lerp(v, v, t) == v,
{
    assert((v.x - v.x) * t == 0) by(nonlinear_arith);
    assert((v.y - v.y) * t == 0) by(nonlinear_arith);
}

/// **Theorem 53**: lerp at t=2 extrapolates: lerp(a, b, 2) = 2b - a.
proof fn vec2_lerp_two(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_lerp(a, b, 2) == vec2_sub(vec2_scale(2, b), a),
{
}

/// **Theorem 54**: lerp at t=-1 extrapolates: lerp(a, b, -1) = 2a - b.
proof fn vec2_lerp_neg_one(a: SpecVec2, b: SpecVec2)
    ensures
        vec2_lerp(a, b, -1 as int) == vec2_sub(vec2_scale(2, a), b),
{
}

/// **Theorem 55**: lerp of zero endpoints gives zero: lerp(zero, zero, t) = zero.
proof fn vec2_lerp_zero_zero(t: int)
    ensures
        vec2_lerp(vec2_zero(), vec2_zero(), t) == vec2_zero(),
{
    vec2_lerp_identity(vec2_zero(), t);
}

// =============================================================================
// VECTOR SPACE STRUCTURE
// =============================================================================

/// **Theorem 56**: Vec2 forms a vector space.
///
/// This proof invokes all the vector space axioms to demonstrate Vec2
/// satisfies the complete definition of a vector space over integers.
proof fn vec2_is_vector_space(a: SpecVec2, b: SpecVec2, c: SpecVec2, s: int, t: int)
    ensures
        // Axiom 1: Additive commutativity
        vec2_add(a, b) == vec2_add(b, a),
        // Axiom 2: Additive associativity
        vec2_add(vec2_add(a, b), c) == vec2_add(a, vec2_add(b, c)),
        // Axiom 3: Additive identity
        vec2_add(a, vec2_zero()) == a,
        // Axiom 4: Additive inverse
        vec2_add(a, vec2_neg(a)) == vec2_zero(),
        // Axiom 5: Scalar associativity
        vec2_scale(s * t, a) == vec2_scale(s, vec2_scale(t, a)),
        // Axiom 6: Scalar distribution over vector addition
        vec2_scale(s, vec2_add(a, b)) == vec2_add(vec2_scale(s, a), vec2_scale(s, b)),
        // Axiom 7: Vector distribution over scalar addition
        vec2_scale(s + t, a) == vec2_add(vec2_scale(s, a), vec2_scale(t, a)),
        // Axiom 8: Scalar identity
        vec2_scale(1, a) == a,
{
    vec2_add_commutative(a, b);
    vec2_add_associative(a, b, c);
    vec2_add_identity(a);
    vec2_add_inverse(a);
    vec2_scale_associative(s, t, a);
    vec2_scale_distributes_over_add(s, a, b);
    vec2_add_scalars_distributes(s, t, a);
    vec2_scale_identity(a);
}

// =============================================================================
// MIN/MAX ELEMENT PROOFS
// =============================================================================

/// Spec: min_element(v) = min(v.x, v.y).
pub open spec fn vec2_min_element(v: SpecVec2) -> int {
    if v.x <= v.y { v.x } else { v.y }
}

/// Spec: max_element(v) = max(v.x, v.y).
pub open spec fn vec2_max_element(v: SpecVec2) -> int {
    if v.x >= v.y { v.x } else { v.y }
}

/// **Theorem 56**: min_element <= max_element.
proof fn vec2_min_le_max_element(v: SpecVec2)
    ensures
        vec2_min_element(v) <= vec2_max_element(v),
{
}

/// **Theorem 57**: min_element is a lower bound.
proof fn vec2_min_element_bound(v: SpecVec2)
    ensures
        vec2_min_element(v) <= v.x,
        vec2_min_element(v) <= v.y,
{
}

/// **Theorem 58**: max_element is an upper bound.
proof fn vec2_max_element_bound(v: SpecVec2)
    ensures
        vec2_max_element(v) >= v.x,
        vec2_max_element(v) >= v.y,
{
}

/// **Theorem 59**: splat min_element is the splat value.
proof fn vec2_splat_min_element(v: int)
    ensures
        vec2_min_element(vec2_splat(v)) == v,
{
}

/// **Theorem 60**: splat max_element is the splat value.
proof fn vec2_splat_max_element(v: int)
    ensures
        vec2_max_element(vec2_splat(v)) == v,
{
}

// =============================================================================
// PROJECT / REJECT PROOFS
// =============================================================================

/// Spec: project(v, w) = w * dot(v,w) / dot(w,w).
/// Integer division: the projection of v onto w.
pub open spec fn vec2_project(v: SpecVec2, w: SpecVec2) -> SpecVec2 {
    let d = vec2_dot(v, w);
    let len_sq = vec2_dot(w, w);
    if len_sq > 0 {
        SpecVec2 { x: w.x * d / len_sq, y: w.y * d / len_sq }
    } else {
        vec2_zero()
    }
}

/// Spec: reject(v, w) = v - project(v, w).
pub open spec fn vec2_reject(v: SpecVec2, w: SpecVec2) -> SpecVec2 {
    vec2_sub(v, vec2_project(v, w))
}

/// **Theorem 61**: project + reject = original.
proof fn vec2_project_reject_sum(v: SpecVec2, w: SpecVec2)
    ensures
        vec2_add(vec2_project(v, w), vec2_reject(v, w)) == v,
{
    // project + reject = project + (v - project) = v
    let p = vec2_project(v, w);
    let r = vec2_reject(v, w);
    // r = v - p, so p + r = p + (v - p) = v
    assert(p.x + (v.x - p.x) == v.x);
    assert(p.y + (v.y - p.y) == v.y);
}

fn main() {
    // Verification only
}

}

