// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Vec4 Operations
//!
//! This module contains machine-checked proofs of correctness for Vec4 operations
//! using the Verus formal verification tool.
//!
//! ## Verification Status
//!
//! All proofs in this file have been verified by Verus with zero admits.
//!
//! ## Properties Verified
//!
//! 1. **Algebraic Properties** (Vector Space Axioms, Theorems 1-9)
//!    - Addition commutativity, associativity, identity, inverse
//!    - Scalar multiplication associativity, distribution, identity
//!    - Vector distribution over scalar addition
//!
//! 2. **Dot Product Properties** (Theorems 10-13)
//!    - Commutativity: a · b = b · a
//!    - Bilinearity: (sa) · b = s(a · b), (a + b) · c = a · c + b · c
//!    - Positive semi-definiteness: v · v ≥ 0
//!    - Length squared equals self dot: |v|² = v · v
//!
//! 3. **Basis Orthonormality** (Theorems 14-17)
//!    - Unit vectors X, Y, Z, W are mutually orthogonal
//!    - Each unit vector has unit length
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/vec4_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Vec4 Specification Type
// =============================================================================

/// Mathematical specification of a 4D vector over integers.
/// Used for homogeneous coordinates, RGBA colors, etc.
#[derive(PartialEq, Eq)]
pub struct SpecVec4 {
    pub x: int,
    pub y: int,
    pub z: int,
    pub w: int,
}

// =============================================================================
// Vector Operations (Spec Functions)
// =============================================================================

/// Creates a new vector.
pub open spec fn vec4_new(x: int, y: int, z: int, w: int) -> SpecVec4 {
    SpecVec4 { x, y, z, w }
}

/// The zero vector.
pub open spec fn vec4_zero() -> SpecVec4 {
    SpecVec4 { x: 0, y: 0, z: 0, w: 0 }
}

/// Unit vector X.
pub open spec fn vec4_x() -> SpecVec4 {
    SpecVec4 { x: 1, y: 0, z: 0, w: 0 }
}

/// Unit vector Y.
pub open spec fn vec4_y() -> SpecVec4 {
    SpecVec4 { x: 0, y: 1, z: 0, w: 0 }
}

/// Unit vector Z.
pub open spec fn vec4_z() -> SpecVec4 {
    SpecVec4 { x: 0, y: 0, z: 1, w: 0 }
}

/// Unit vector W.
pub open spec fn vec4_w() -> SpecVec4 {
    SpecVec4 { x: 0, y: 0, z: 0, w: 1 }
}

/// Vector addition: a + b
pub open spec fn vec4_add(a: SpecVec4, b: SpecVec4) -> SpecVec4 {
    SpecVec4 { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z, w: a.w + b.w }
}

/// Vector subtraction: a - b
pub open spec fn vec4_sub(a: SpecVec4, b: SpecVec4) -> SpecVec4 {
    SpecVec4 { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z, w: a.w - b.w }
}

/// Scalar multiplication: s * v
pub open spec fn vec4_scale(s: int, v: SpecVec4) -> SpecVec4 {
    SpecVec4 { x: s * v.x, y: s * v.y, z: s * v.z, w: s * v.w }
}

/// Vector negation: -v
pub open spec fn vec4_neg(v: SpecVec4) -> SpecVec4 {
    SpecVec4 { x: -v.x, y: -v.y, z: -v.z, w: -v.w }
}

/// Dot product: a · b
pub open spec fn vec4_dot(a: SpecVec4, b: SpecVec4) -> int {
    a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w
}

/// Length squared: |v|²
pub open spec fn vec4_length_squared(v: SpecVec4) -> int {
    vec4_dot(v, v)
}

/// Component-wise multiplication: a * b
pub open spec fn vec4_mul(a: SpecVec4, b: SpecVec4) -> SpecVec4 {
    SpecVec4 { x: a.x * b.x, y: a.y * b.y, z: a.z * b.z, w: a.w * b.w }
}

// =============================================================================
// ALGEBRAIC PROOFS (Vector Space Axioms)
// =============================================================================

/// **Theorem 1**: Vector addition is commutative.
proof fn vec4_add_commutative(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_add(a, b) == vec4_add(b, a),
{
    assert(a.x + b.x == b.x + a.x);
    assert(a.y + b.y == b.y + a.y);
    assert(a.z + b.z == b.z + a.z);
    assert(a.w + b.w == b.w + a.w);
}

/// **Theorem 2**: Vector addition is associative.
proof fn vec4_add_associative(a: SpecVec4, b: SpecVec4, c: SpecVec4)
    ensures
        vec4_add(vec4_add(a, b), c) == vec4_add(a, vec4_add(b, c)),
{
    assert((a.x + b.x) + c.x == a.x + (b.x + c.x));
    assert((a.y + b.y) + c.y == a.y + (b.y + c.y));
    assert((a.z + b.z) + c.z == a.z + (b.z + c.z));
    assert((a.w + b.w) + c.w == a.w + (b.w + c.w));
}

/// **Theorem 3**: The zero vector is an additive identity.
proof fn vec4_add_identity(a: SpecVec4)
    ensures
        vec4_add(a, vec4_zero()) == a,
{
    assert(a.x + 0 == a.x);
    assert(a.y + 0 == a.y);
    assert(a.z + 0 == a.z);
    assert(a.w + 0 == a.w);
}

/// **Theorem 4**: Every vector has an additive inverse.
proof fn vec4_add_inverse(a: SpecVec4)
    ensures
        vec4_add(a, vec4_neg(a)) == vec4_zero(),
{
    assert(a.x + (-a.x) == 0);
    assert(a.y + (-a.y) == 0);
    assert(a.z + (-a.z) == 0);
    assert(a.w + (-a.w) == 0);
}

/// **Theorem 5**: Scalar multiplication is associative.
proof fn vec4_scale_associative(s: int, t: int, v: SpecVec4)
    ensures
        vec4_scale(s * t, v) == vec4_scale(s, vec4_scale(t, v)),
{
    assert((s * t) * v.x == s * (t * v.x)) by(nonlinear_arith);
    assert((s * t) * v.y == s * (t * v.y)) by(nonlinear_arith);
    assert((s * t) * v.z == s * (t * v.z)) by(nonlinear_arith);
    assert((s * t) * v.w == s * (t * v.w)) by(nonlinear_arith);
}

/// **Theorem 6**: Scalar multiplication distributes over vector addition.
proof fn vec4_scale_distributes_over_add(s: int, a: SpecVec4, b: SpecVec4)
    ensures
        vec4_scale(s, vec4_add(a, b)) == vec4_add(vec4_scale(s, a), vec4_scale(s, b)),
{
    assert(s * (a.x + b.x) == s * a.x + s * b.x) by(nonlinear_arith);
    assert(s * (a.y + b.y) == s * a.y + s * b.y) by(nonlinear_arith);
    assert(s * (a.z + b.z) == s * a.z + s * b.z) by(nonlinear_arith);
    assert(s * (a.w + b.w) == s * a.w + s * b.w) by(nonlinear_arith);
}

/// **Theorem 7**: Vector addition distributes over scalar addition.
proof fn vec4_add_scalars_distributes(s: int, t: int, v: SpecVec4)
    ensures
        vec4_scale(s + t, v) == vec4_add(vec4_scale(s, v), vec4_scale(t, v)),
{
    assert((s + t) * v.x == s * v.x + t * v.x) by(nonlinear_arith);
    assert((s + t) * v.y == s * v.y + t * v.y) by(nonlinear_arith);
    assert((s + t) * v.z == s * v.z + t * v.z) by(nonlinear_arith);
    assert((s + t) * v.w == s * v.w + t * v.w) by(nonlinear_arith);
}

/// **Theorem 8**: Scaling by 1 is the identity operation.
proof fn vec4_scale_identity(v: SpecVec4)
    ensures
        vec4_scale(1, v) == v,
{
    assert(1 * v.x == v.x);
    assert(1 * v.y == v.y);
    assert(1 * v.z == v.z);
    assert(1 * v.w == v.w);
}

/// **Theorem 9**: Scaling by 0 produces the zero vector.
proof fn vec4_scale_zero(v: SpecVec4)
    ensures
        vec4_scale(0, v) == vec4_zero(),
{
    assert(0 * v.x == 0);
    assert(0 * v.y == 0);
    assert(0 * v.z == 0);
    assert(0 * v.w == 0);
}

// =============================================================================
// DOT PRODUCT PROOFS
// =============================================================================

/// **Theorem 10**: Dot product is commutative.
proof fn vec4_dot_commutative(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_dot(a, b) == vec4_dot(b, a),
{
    assert(a.x * b.x == b.x * a.x) by(nonlinear_arith);
    assert(a.y * b.y == b.y * a.y) by(nonlinear_arith);
    assert(a.z * b.z == b.z * a.z) by(nonlinear_arith);
    assert(a.w * b.w == b.w * a.w) by(nonlinear_arith);
}

/// **Theorem 11**: Dot product is bilinear (linear in first argument).
proof fn vec4_dot_linear_first(s: int, a: SpecVec4, b: SpecVec4)
    ensures
        vec4_dot(vec4_scale(s, a), b) == s * vec4_dot(a, b),
{
    assert((s * a.x) * b.x == s * (a.x * b.x)) by(nonlinear_arith);
    assert((s * a.y) * b.y == s * (a.y * b.y)) by(nonlinear_arith);
    assert((s * a.z) * b.z == s * (a.z * b.z)) by(nonlinear_arith);
    assert((s * a.w) * b.w == s * (a.w * b.w)) by(nonlinear_arith);
    assert((s * a.x) * b.x + (s * a.y) * b.y + (s * a.z) * b.z + (s * a.w) * b.w
           == s * (a.x * b.x) + s * (a.y * b.y) + s * (a.z * b.z) + s * (a.w * b.w));
    assert(s * (a.x * b.x) + s * (a.y * b.y) + s * (a.z * b.z) + s * (a.w * b.w)
           == s * (a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w)) by(nonlinear_arith);
}

/// **Theorem 12**: Dot product distributes over addition.
proof fn vec4_dot_distributes(a: SpecVec4, b: SpecVec4, c: SpecVec4)
    ensures
        vec4_dot(vec4_add(a, b), c) == vec4_dot(a, c) + vec4_dot(b, c),
{
    assert((a.x + b.x) * c.x == a.x * c.x + b.x * c.x) by(nonlinear_arith);
    assert((a.y + b.y) * c.y == a.y * c.y + b.y * c.y) by(nonlinear_arith);
    assert((a.z + b.z) * c.z == a.z * c.z + b.z * c.z) by(nonlinear_arith);
    assert((a.w + b.w) * c.w == a.w * c.w + b.w * c.w) by(nonlinear_arith);
}

/// **Theorem 13**: Length squared is non-negative.
proof fn vec4_length_squared_nonnegative(a: SpecVec4)
    ensures
        vec4_length_squared(a) >= 0,
{
    assert(a.x * a.x >= 0) by(nonlinear_arith);
    assert(a.y * a.y >= 0) by(nonlinear_arith);
    assert(a.z * a.z >= 0) by(nonlinear_arith);
    assert(a.w * a.w >= 0) by(nonlinear_arith);
}

// =============================================================================
// BASIS ORTHONORMALITY PROOFS
// =============================================================================

/// **Theorem 14**: X and Y unit vectors are orthogonal.
proof fn vec4_x_y_orthogonal()
    ensures
        vec4_dot(vec4_x(), vec4_y()) == 0,
{
    // X = (1, 0, 0, 0), Y = (0, 1, 0, 0)
    // X · Y = 1*0 + 0*1 + 0*0 + 0*0 = 0
}

/// **Theorem 15**: All basis vectors are mutually orthogonal.
proof fn vec4_basis_orthogonal()
    ensures
        vec4_dot(vec4_x(), vec4_y()) == 0,
        vec4_dot(vec4_x(), vec4_z()) == 0,
        vec4_dot(vec4_x(), vec4_w()) == 0,
        vec4_dot(vec4_y(), vec4_z()) == 0,
        vec4_dot(vec4_y(), vec4_w()) == 0,
        vec4_dot(vec4_z(), vec4_w()) == 0,
{
    // All basis vectors have a 1 in different positions
}

/// **Theorem 16**: Each basis vector has unit length squared.
proof fn vec4_basis_unit_length()
    ensures
        vec4_length_squared(vec4_x()) == 1,
        vec4_length_squared(vec4_y()) == 1,
        vec4_length_squared(vec4_z()) == 1,
        vec4_length_squared(vec4_w()) == 1,
{
    // X·X = 1*1 + 0*0 + 0*0 + 0*0 = 1
    // Similarly for Y, Z, W
}

/// **Theorem 17**: Zero vector has zero length squared.
proof fn vec4_zero_length()
    ensures
        vec4_length_squared(vec4_zero()) == 0,
{
    // 0·0 + 0·0 + 0·0 + 0·0 = 0
}

// =============================================================================
// ADDITIONAL GEOMETRIC PROOFS
// =============================================================================

/// **Theorem 18**: Subtraction is equivalent to adding the negative.
proof fn vec4_sub_is_add_neg(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_sub(a, b) == vec4_add(a, vec4_neg(b)),
{
    assert(a.x - b.x == a.x + (-b.x));
    assert(a.y - b.y == a.y + (-b.y));
    assert(a.z - b.z == a.z + (-b.z));
    assert(a.w - b.w == a.w + (-b.w));
}

/// **Theorem 19**: Component-wise multiplication is commutative.
proof fn vec4_mul_commutative(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_mul(a, b) == vec4_mul(b, a),
{
    assert(a.x * b.x == b.x * a.x) by(nonlinear_arith);
    assert(a.y * b.y == b.y * a.y) by(nonlinear_arith);
    assert(a.z * b.z == b.z * a.z) by(nonlinear_arith);
    assert(a.w * b.w == b.w * a.w) by(nonlinear_arith);
}

/// **Theorem 20**: Negation is equivalent to scaling by -1.
proof fn vec4_neg_is_scale_neg_one(v: SpecVec4)
    ensures
        vec4_neg(v) == vec4_scale(-1, v),
{
    assert(-v.x == (-1) * v.x) by(nonlinear_arith);
    assert(-v.y == (-1) * v.y) by(nonlinear_arith);
    assert(-v.z == (-1) * v.z) by(nonlinear_arith);
    assert(-v.w == (-1) * v.w) by(nonlinear_arith);
}

/// **Theorem 21**: Length squared is zero iff vector is zero.
proof fn vec4_length_squared_zero_iff_zero(a: SpecVec4)
    ensures
        vec4_length_squared(a) == 0 <==> a == vec4_zero(),
{
    assert(a.x * a.x >= 0) by(nonlinear_arith);
    assert(a.y * a.y >= 0) by(nonlinear_arith);
    assert(a.z * a.z >= 0) by(nonlinear_arith);
    assert(a.w * a.w >= 0) by(nonlinear_arith);
    assert(a.x * a.x == 0 ==> a.x == 0) by(nonlinear_arith);
    assert(a.y * a.y == 0 ==> a.y == 0) by(nonlinear_arith);
    assert(a.z * a.z == 0 ==> a.z == 0) by(nonlinear_arith);
    assert(a.w * a.w == 0 ==> a.w == 0) by(nonlinear_arith);
    if a.x * a.x + a.y * a.y + a.z * a.z + a.w * a.w == 0 {
        assert(a.x * a.x == 0);
        assert(a.y * a.y == 0);
        assert(a.z * a.z == 0);
        assert(a.w * a.w == 0);
    }
}

// =============================================================================
// EXTENDED OPERATIONS (Spec Functions)
// =============================================================================

/// Creates a vector with all components set to the same value.
pub open spec fn vec4_splat(value: int) -> SpecVec4 {
    SpecVec4 { x: value, y: value, z: value, w: value }
}

/// Component-wise minimum of two vectors.
pub open spec fn vec4_min(a: SpecVec4, b: SpecVec4) -> SpecVec4 {
    SpecVec4 {
        x: if a.x <= b.x { a.x } else { b.x },
        y: if a.y <= b.y { a.y } else { b.y },
        z: if a.z <= b.z { a.z } else { b.z },
        w: if a.w <= b.w { a.w } else { b.w },
    }
}

/// Component-wise maximum of two vectors.
pub open spec fn vec4_max(a: SpecVec4, b: SpecVec4) -> SpecVec4 {
    SpecVec4 {
        x: if a.x >= b.x { a.x } else { b.x },
        y: if a.y >= b.y { a.y } else { b.y },
        z: if a.z >= b.z { a.z } else { b.z },
        w: if a.w >= b.w { a.w } else { b.w },
    }
}

/// Component-wise absolute value.
pub open spec fn vec4_abs(v: SpecVec4) -> SpecVec4 {
    SpecVec4 {
        x: if v.x >= 0 { v.x } else { -v.x },
        y: if v.y >= 0 { v.y } else { -v.y },
        z: if v.z >= 0 { v.z } else { -v.z },
        w: if v.w >= 0 { v.w } else { -v.w },
    }
}

/// Sum of all components.
pub open spec fn vec4_element_sum(v: SpecVec4) -> int {
    v.x + v.y + v.z + v.w
}

/// Squared distance between two points.
pub open spec fn vec4_distance_squared(a: SpecVec4, b: SpecVec4) -> int {
    vec4_length_squared(vec4_sub(a, b))
}

// =============================================================================
// SPLAT PROOFS
// =============================================================================

/// **Theorem 23**: Splat is equivalent to new(v, v, v, v).
proof fn vec4_splat_is_new(value: int)
    ensures
        vec4_splat(value) == vec4_new(value, value, value, value),
{
}

/// **Theorem 24**: Splat(0) is the zero vector.
proof fn vec4_splat_zero()
    ensures
        vec4_splat(0) == vec4_zero(),
{
}

// =============================================================================
// MIN/MAX PROOFS
// =============================================================================

/// **Theorem 25**: Component-wise min is commutative.
proof fn vec4_min_commutative(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_min(a, b) == vec4_min(b, a),
{
}

/// **Theorem 26**: Component-wise max is commutative.
proof fn vec4_max_commutative(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_max(a, b) == vec4_max(b, a),
{
}

/// **Theorem 27**: min(a, a) = a (idempotent).
proof fn vec4_min_idempotent(a: SpecVec4)
    ensures
        vec4_min(a, a) == a,
{
}

/// **Theorem 28**: max(a, a) = a (idempotent).
proof fn vec4_max_idempotent(a: SpecVec4)
    ensures
        vec4_max(a, a) == a,
{
}

/// **Theorem 29**: min(a, b) + max(a, b) = a + b.
proof fn vec4_min_max_sum(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_add(vec4_min(a, b), vec4_max(a, b)) == vec4_add(a, b),
{
}

/// **Theorem 30**: min(a, b) is component-wise <= both operands.
proof fn vec4_min_le_both(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_min(a, b).x <= a.x && vec4_min(a, b).x <= b.x,
        vec4_min(a, b).y <= a.y && vec4_min(a, b).y <= b.y,
        vec4_min(a, b).z <= a.z && vec4_min(a, b).z <= b.z,
        vec4_min(a, b).w <= a.w && vec4_min(a, b).w <= b.w,
{
}

// =============================================================================
// ABS PROOFS
// =============================================================================

/// **Theorem 31**: Abs produces non-negative components.
proof fn vec4_abs_nonneg(v: SpecVec4)
    ensures
        vec4_abs(v).x >= 0 && vec4_abs(v).y >= 0
        && vec4_abs(v).z >= 0 && vec4_abs(v).w >= 0,
{
}

/// **Theorem 32**: Abs is idempotent: abs(abs(v)) = abs(v).
proof fn vec4_abs_idempotent(v: SpecVec4)
    ensures
        vec4_abs(vec4_abs(v)) == vec4_abs(v),
{
    let a = vec4_abs(v);
    assert(a.x >= 0);
    assert(a.y >= 0);
    assert(a.z >= 0);
    assert(a.w >= 0);
}

/// **Theorem 33**: Abs of negation equals abs: |−v| = |v|.
proof fn vec4_abs_neg(v: SpecVec4)
    ensures
        vec4_abs(vec4_neg(v)) == vec4_abs(v),
{
}

// =============================================================================
// ELEMENT SUM PROOFS
// =============================================================================

/// **Theorem 34**: Element sum of zero is zero.
proof fn vec4_element_sum_zero()
    ensures
        vec4_element_sum(vec4_zero()) == 0,
{
}

/// **Theorem 35**: Element sum is additive: sum(a + b) = sum(a) + sum(b).
proof fn vec4_element_sum_additive(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_element_sum(vec4_add(a, b)) == vec4_element_sum(a) + vec4_element_sum(b),
{
}

/// **Theorem 36**: Element sum commutes with scaling.
proof fn vec4_element_sum_scale(s: int, v: SpecVec4)
    ensures
        vec4_element_sum(vec4_scale(s, v)) == s * vec4_element_sum(v),
{
    assert(s * v.x + s * v.y + s * v.z + s * v.w
           == s * (v.x + v.y + v.z + v.w)) by(nonlinear_arith);
}

// =============================================================================
// DISTANCE SQUARED PROOFS
// =============================================================================

/// **Theorem 37**: Distance squared is non-negative.
proof fn vec4_distance_squared_nonneg(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_distance_squared(a, b) >= 0,
{
    let d = vec4_sub(a, b);
    vec4_length_squared_nonnegative(d);
}

/// **Theorem 38**: Distance squared is symmetric.
proof fn vec4_distance_squared_symmetric(a: SpecVec4, b: SpecVec4)
    ensures
        vec4_distance_squared(a, b) == vec4_distance_squared(b, a),
{
    let d1 = vec4_sub(a, b);
    let d2 = vec4_sub(b, a);
    assert(d1.x * d1.x == d2.x * d2.x) by(nonlinear_arith);
    assert(d1.y * d1.y == d2.y * d2.y) by(nonlinear_arith);
    assert(d1.z * d1.z == d2.z * d2.z) by(nonlinear_arith);
    assert(d1.w * d1.w == d2.w * d2.w) by(nonlinear_arith);
}

/// **Theorem 39**: Distance squared to self is zero.
proof fn vec4_distance_squared_self(a: SpecVec4)
    ensures
        vec4_distance_squared(a, a) == 0,
{
}

// =============================================================================
// VECTOR SPACE STRUCTURE
// =============================================================================

/// **Theorem 40**: Vec4 forms a vector space.
///
/// This proof invokes all the vector space axioms to demonstrate Vec4
/// satisfies the complete definition of a vector space over integers.
proof fn vec4_is_vector_space(a: SpecVec4, b: SpecVec4, c: SpecVec4, s: int, t: int)
    ensures
        // Axiom 1: Additive commutativity
        vec4_add(a, b) == vec4_add(b, a),
        // Axiom 2: Additive associativity
        vec4_add(vec4_add(a, b), c) == vec4_add(a, vec4_add(b, c)),
        // Axiom 3: Additive identity
        vec4_add(a, vec4_zero()) == a,
        // Axiom 4: Additive inverse
        vec4_add(a, vec4_neg(a)) == vec4_zero(),
        // Axiom 5: Scalar associativity
        vec4_scale(s * t, a) == vec4_scale(s, vec4_scale(t, a)),
        // Axiom 6: Scalar distribution over vector addition
        vec4_scale(s, vec4_add(a, b)) == vec4_add(vec4_scale(s, a), vec4_scale(s, b)),
        // Axiom 7: Vector distribution over scalar addition
        vec4_scale(s + t, a) == vec4_add(vec4_scale(s, a), vec4_scale(t, a)),
        // Axiom 8: Scalar identity
        vec4_scale(1, a) == a,
{
    vec4_add_commutative(a, b);
    vec4_add_associative(a, b, c);
    vec4_add_identity(a);
    vec4_add_inverse(a);
    vec4_scale_associative(s, t, a);
    vec4_scale_distributes_over_add(s, a, b);
    vec4_add_scalars_distributes(s, t, a);
    vec4_scale_identity(a);
}

fn main() {
    // Verification only
}

}
