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
// VECTOR SPACE STRUCTURE
// =============================================================================

/// **Theorem 23**: Vec2 forms a vector space.
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

fn main() {
    // Verification only
}

}

