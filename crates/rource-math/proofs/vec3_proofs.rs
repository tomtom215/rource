// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Vec3 Operations
//!
//! This module contains machine-checked proofs of correctness for Vec3 operations
//! using the Verus formal verification tool.
//!
//! ## Verification Status
//!
//! All proofs in this file have been verified by Verus with zero admits.
//! Total: 24 theorems, 75 verification conditions.
//!
//! ## Properties Verified
//!
//! 1. **Algebraic Properties** (Vector Space Axioms, Theorems 1-7)
//!    - Addition commutativity, associativity, identity, inverse
//!    - Scalar multiplication associativity, distribution
//!
//! 2. **Dot Product Properties** (Theorems 8-9)
//!    - Commutativity: a · b = b · a
//!    - Length squared non-negativity: |v|² ≥ 0
//!
//! 3. **Cross Product Properties** (Theorems 10-17)
//!    - Anti-commutativity: a × b = -(b × a)
//!    - Self-cross is zero: a × a = 0
//!    - Orthogonality: (a × b) · a = 0 and (a × b) · b = 0
//!    - Right-hand rule basis: X × Y = Z, Y × Z = X, Z × X = Y
//!
//! 4. **Scalar Triple Product Properties** (Theorems 19-23)
//!    - Expansion lemmas for each cyclic form
//!    - Cyclic equality: a · (b × c) = b · (c × a) = c · (a × b)
//!
//! 5. **Vector Space Structure** (Theorem 24)
//!    - Meta-theorem combining all vector space axioms
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/vec3_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Vec3 Specification Type
// =============================================================================

/// Mathematical specification of a 3D vector over integers.
#[derive(PartialEq, Eq)]
pub struct SpecVec3 {
    pub x: int,
    pub y: int,
    pub z: int,
}

// =============================================================================
// Vector Operations (Spec Functions)
// =============================================================================

/// Creates a new vector.
pub open spec fn vec3_new(x: int, y: int, z: int) -> SpecVec3 {
    SpecVec3 { x, y, z }
}

/// The zero vector.
pub open spec fn vec3_zero() -> SpecVec3 {
    SpecVec3 { x: 0, y: 0, z: 0 }
}

/// Unit vector X.
pub open spec fn vec3_x() -> SpecVec3 {
    SpecVec3 { x: 1, y: 0, z: 0 }
}

/// Unit vector Y.
pub open spec fn vec3_y() -> SpecVec3 {
    SpecVec3 { x: 0, y: 1, z: 0 }
}

/// Unit vector Z.
pub open spec fn vec3_z() -> SpecVec3 {
    SpecVec3 { x: 0, y: 0, z: 1 }
}

/// Vector addition: a + b
pub open spec fn vec3_add(a: SpecVec3, b: SpecVec3) -> SpecVec3 {
    SpecVec3 { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }
}

/// Vector subtraction: a - b
pub open spec fn vec3_sub(a: SpecVec3, b: SpecVec3) -> SpecVec3 {
    SpecVec3 { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z }
}

/// Scalar multiplication: s * v
pub open spec fn vec3_scale(s: int, v: SpecVec3) -> SpecVec3 {
    SpecVec3 { x: s * v.x, y: s * v.y, z: s * v.z }
}

/// Vector negation: -v
pub open spec fn vec3_neg(v: SpecVec3) -> SpecVec3 {
    SpecVec3 { x: -v.x, y: -v.y, z: -v.z }
}

/// Dot product: a · b
pub open spec fn vec3_dot(a: SpecVec3, b: SpecVec3) -> int {
    a.x * b.x + a.y * b.y + a.z * b.z
}

/// Cross product: a × b
pub open spec fn vec3_cross(a: SpecVec3, b: SpecVec3) -> SpecVec3 {
    SpecVec3 {
        x: a.y * b.z - a.z * b.y,
        y: a.z * b.x - a.x * b.z,
        z: a.x * b.y - a.y * b.x,
    }
}

/// Length squared: |v|²
pub open spec fn vec3_length_squared(v: SpecVec3) -> int {
    vec3_dot(v, v)
}

// =============================================================================
// ALGEBRAIC PROOFS (Vector Space Axioms)
// =============================================================================

/// **Theorem 1**: Vector addition is commutative.
proof fn vec3_add_commutative(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_add(a, b) == vec3_add(b, a),
{
    assert(a.x + b.x == b.x + a.x);
    assert(a.y + b.y == b.y + a.y);
    assert(a.z + b.z == b.z + a.z);
}

/// **Theorem 2**: Vector addition is associative.
proof fn vec3_add_associative(a: SpecVec3, b: SpecVec3, c: SpecVec3)
    ensures
        vec3_add(vec3_add(a, b), c) == vec3_add(a, vec3_add(b, c)),
{
    assert((a.x + b.x) + c.x == a.x + (b.x + c.x));
    assert((a.y + b.y) + c.y == a.y + (b.y + c.y));
    assert((a.z + b.z) + c.z == a.z + (b.z + c.z));
}

/// **Theorem 3**: The zero vector is an additive identity.
proof fn vec3_add_identity(a: SpecVec3)
    ensures
        vec3_add(a, vec3_zero()) == a,
{
    assert(a.x + 0 == a.x);
    assert(a.y + 0 == a.y);
    assert(a.z + 0 == a.z);
}

/// **Theorem 4**: Every vector has an additive inverse.
proof fn vec3_add_inverse(a: SpecVec3)
    ensures
        vec3_add(a, vec3_neg(a)) == vec3_zero(),
{
    assert(a.x + (-a.x) == 0);
    assert(a.y + (-a.y) == 0);
    assert(a.z + (-a.z) == 0);
}

/// **Theorem 5**: Scalar multiplication is associative.
proof fn vec3_scale_associative(s: int, t: int, v: SpecVec3)
    ensures
        vec3_scale(s * t, v) == vec3_scale(s, vec3_scale(t, v)),
{
    assert((s * t) * v.x == s * (t * v.x)) by(nonlinear_arith);
    assert((s * t) * v.y == s * (t * v.y)) by(nonlinear_arith);
    assert((s * t) * v.z == s * (t * v.z)) by(nonlinear_arith);
}

/// **Theorem 6**: Scalar multiplication distributes over vector addition.
proof fn vec3_scale_distributes_over_add(s: int, a: SpecVec3, b: SpecVec3)
    ensures
        vec3_scale(s, vec3_add(a, b)) == vec3_add(vec3_scale(s, a), vec3_scale(s, b)),
{
    assert(s * (a.x + b.x) == s * a.x + s * b.x) by(nonlinear_arith);
    assert(s * (a.y + b.y) == s * a.y + s * b.y) by(nonlinear_arith);
    assert(s * (a.z + b.z) == s * a.z + s * b.z) by(nonlinear_arith);
}

/// **Theorem 7**: Scaling by 1 is identity.
proof fn vec3_scale_identity(v: SpecVec3)
    ensures
        vec3_scale(1, v) == v,
{
    assert(1 * v.x == v.x);
    assert(1 * v.y == v.y);
    assert(1 * v.z == v.z);
}

// =============================================================================
// DOT PRODUCT PROOFS
// =============================================================================

/// **Theorem 8**: Dot product is commutative.
proof fn vec3_dot_commutative(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_dot(a, b) == vec3_dot(b, a),
{
    assert(a.x * b.x == b.x * a.x) by(nonlinear_arith);
    assert(a.y * b.y == b.y * a.y) by(nonlinear_arith);
    assert(a.z * b.z == b.z * a.z) by(nonlinear_arith);
}

/// **Theorem 9**: Length squared is non-negative.
proof fn vec3_length_squared_nonnegative(a: SpecVec3)
    ensures
        vec3_length_squared(a) >= 0,
{
    assert(a.x * a.x >= 0) by(nonlinear_arith);
    assert(a.y * a.y >= 0) by(nonlinear_arith);
    assert(a.z * a.z >= 0) by(nonlinear_arith);
}

// =============================================================================
// CROSS PRODUCT PROOFS
// =============================================================================

/// **Theorem 10**: Cross product is anti-commutative.
///
/// For all vectors a, b: a × b = -(b × a)
proof fn vec3_cross_anticommutative(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_cross(a, b) == vec3_neg(vec3_cross(b, a)),
{
    // Show each component
    // x: (a.y * b.z - a.z * b.y) = -(b.y * a.z - b.z * a.y)
    assert(a.y * b.z == b.z * a.y) by(nonlinear_arith);
    assert(a.z * b.y == b.y * a.z) by(nonlinear_arith);
    // y: (a.z * b.x - a.x * b.z) = -(b.z * a.x - b.x * a.z)
    assert(a.z * b.x == b.x * a.z) by(nonlinear_arith);
    assert(a.x * b.z == b.z * a.x) by(nonlinear_arith);
    // z: (a.x * b.y - a.y * b.x) = -(b.x * a.y - b.y * a.x)
    assert(a.x * b.y == b.y * a.x) by(nonlinear_arith);
    assert(a.y * b.x == b.x * a.y) by(nonlinear_arith);
}

/// **Theorem 11**: Cross product of a vector with itself is zero.
proof fn vec3_cross_self_zero(a: SpecVec3)
    ensures
        vec3_cross(a, a) == vec3_zero(),
{
    assert(a.y * a.z == a.z * a.y) by(nonlinear_arith);
    assert(a.z * a.x == a.x * a.z) by(nonlinear_arith);
    assert(a.x * a.y == a.y * a.x) by(nonlinear_arith);
}

/// **Theorem 12**: Cross product is orthogonal to first operand.
///
/// For all vectors a, b: (a × b) · a = 0
#[verifier::rlimit(20)]
proof fn vec3_cross_orthogonal_to_first(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_dot(vec3_cross(a, b), a) == 0,
{
    // (a × b) = (a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x)
    // (a × b) · a = (a.y*b.z - a.z*b.y)*a.x + (a.z*b.x - a.x*b.z)*a.y + (a.x*b.y - a.y*b.x)*a.z
    //            = a.x*a.y*b.z - a.x*a.z*b.y + a.y*a.z*b.x - a.x*a.y*b.z + a.x*a.z*b.y - a.y*a.z*b.x
    //            = 0
    let c = vec3_cross(a, b);
    assert(c.x * a.x + c.y * a.y + c.z * a.z == 0) by(nonlinear_arith)
        requires
            c.x == a.y * b.z - a.z * b.y,
            c.y == a.z * b.x - a.x * b.z,
            c.z == a.x * b.y - a.y * b.x,
    ;
}

/// **Theorem 13**: Cross product is orthogonal to second operand.
///
/// For all vectors a, b: (a × b) · b = 0
proof fn vec3_cross_orthogonal_to_second(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_dot(vec3_cross(a, b), b) == 0,
{
    let c = vec3_cross(a, b);
    assert(c.x * b.x + c.y * b.y + c.z * b.z == 0) by(nonlinear_arith)
        requires
            c.x == a.y * b.z - a.z * b.y,
            c.y == a.z * b.x - a.x * b.z,
            c.z == a.x * b.y - a.y * b.x,
    ;
}

/// **Theorem 14**: Right-hand rule: X × Y = Z.
proof fn vec3_cross_x_y_is_z()
    ensures
        vec3_cross(vec3_x(), vec3_y()) == vec3_z(),
{
    // X = (1, 0, 0), Y = (0, 1, 0)
    // X × Y = (0*0 - 0*1, 0*0 - 1*0, 1*1 - 0*0) = (0, 0, 1) = Z
}

/// **Theorem 15**: Right-hand rule: Y × Z = X.
proof fn vec3_cross_y_z_is_x()
    ensures
        vec3_cross(vec3_y(), vec3_z()) == vec3_x(),
{
    // Y = (0, 1, 0), Z = (0, 0, 1)
    // Y × Z = (1*1 - 0*0, 0*0 - 0*1, 0*0 - 1*0) = (1, 0, 0) = X
}

/// **Theorem 16**: Right-hand rule: Z × X = Y.
proof fn vec3_cross_z_x_is_y()
    ensures
        vec3_cross(vec3_z(), vec3_x()) == vec3_y(),
{
    // Z = (0, 0, 1), X = (1, 0, 0)
    // Z × X = (0*0 - 1*0, 1*1 - 0*0, 0*0 - 0*1) = (0, 1, 0) = Y
}

/// **Theorem 17**: Reverse of right-hand rule: Y × X = -Z.
proof fn vec3_cross_y_x_is_neg_z()
    ensures
        vec3_cross(vec3_y(), vec3_x()) == vec3_neg(vec3_z()),
{
    // By anti-commutativity: Y × X = -(X × Y) = -Z
    vec3_cross_anticommutative(vec3_x(), vec3_y());
    vec3_cross_x_y_is_z();
}

// =============================================================================
// SCALAR TRIPLE PRODUCT PROOFS
// =============================================================================

/// Expanded form for b·(c×a) with explicit terms.
pub open spec fn stp_bca_expanded(a: SpecVec3, b: SpecVec3, c: SpecVec3) -> int {
    b.x * c.y * a.z - b.x * c.z * a.y +
    b.y * c.z * a.x - b.y * c.x * a.z +
    b.z * c.x * a.y - b.z * c.y * a.x
}

/// Expanded form for c·(a×b) with explicit terms.
pub open spec fn stp_cab_expanded(a: SpecVec3, b: SpecVec3, c: SpecVec3) -> int {
    c.x * a.y * b.z - c.x * a.z * b.y +
    c.y * a.z * b.x - c.y * a.x * b.z +
    c.z * a.x * b.y - c.z * a.y * b.x
}

/// Expanded form for a·(b×c) (the canonical determinant form).
pub open spec fn stp_abc_expanded(a: SpecVec3, b: SpecVec3, c: SpecVec3) -> int {
    a.x * b.y * c.z - a.x * b.z * c.y +
    a.y * b.z * c.x - a.y * b.x * c.z +
    a.z * b.x * c.y - a.z * b.y * c.x
}

/// **Theorem 19**: Expansion of a·(b×c).
///
/// Shows vec3_dot(a, vec3_cross(b, c)) equals its fully expanded 6-term form.
proof fn stp_abc_expansion(a: SpecVec3, b: SpecVec3, c: SpecVec3)
    ensures
        vec3_dot(a, vec3_cross(b, c)) == stp_abc_expanded(a, b, c),
{
    assert(a.x * (b.y * c.z - b.z * c.y) == a.x * b.y * c.z - a.x * b.z * c.y) by(nonlinear_arith);
    assert(a.y * (b.z * c.x - b.x * c.z) == a.y * b.z * c.x - a.y * b.x * c.z) by(nonlinear_arith);
    assert(a.z * (b.x * c.y - b.y * c.x) == a.z * b.x * c.y - a.z * b.y * c.x) by(nonlinear_arith);
}

/// **Theorem 20**: Expansion of b·(c×a).
proof fn stp_bca_expansion(a: SpecVec3, b: SpecVec3, c: SpecVec3)
    ensures
        vec3_dot(b, vec3_cross(c, a)) == stp_bca_expanded(a, b, c),
{
    assert(b.x * (c.y * a.z - c.z * a.y) == b.x * c.y * a.z - b.x * c.z * a.y) by(nonlinear_arith);
    assert(b.y * (c.z * a.x - c.x * a.z) == b.y * c.z * a.x - b.y * c.x * a.z) by(nonlinear_arith);
    assert(b.z * (c.x * a.y - c.y * a.x) == b.z * c.x * a.y - b.z * c.y * a.x) by(nonlinear_arith);
}

/// **Theorem 21**: Expansion of c·(a×b).
proof fn stp_cab_expansion(a: SpecVec3, b: SpecVec3, c: SpecVec3)
    ensures
        vec3_dot(c, vec3_cross(a, b)) == stp_cab_expanded(a, b, c),
{
    assert(c.x * (a.y * b.z - a.z * b.y) == c.x * a.y * b.z - c.x * a.z * b.y) by(nonlinear_arith);
    assert(c.y * (a.z * b.x - a.x * b.z) == c.y * a.z * b.x - c.y * a.x * b.z) by(nonlinear_arith);
    assert(c.z * (a.x * b.y - a.y * b.x) == c.z * a.x * b.y - c.z * a.y * b.x) by(nonlinear_arith);
}

/// **Theorem 22**: All expanded forms are equal.
///
/// This key lemma proves that the three scalar triple product expansions
/// contain exactly the same terms (possibly reordered) due to multiplication
/// commutativity. Each term is a product of three factors: one from each
/// vector (a, b, c), and the sign is preserved under cyclic permutation.
proof fn expanded_forms_equal(a: SpecVec3, b: SpecVec3, c: SpecVec3)
    ensures
        stp_abc_expanded(a, b, c) == stp_bca_expanded(a, b, c),
        stp_bca_expanded(a, b, c) == stp_cab_expanded(a, b, c),
{
    // Match stp_bca terms to stp_abc terms via commutativity:
    // Term 1: b.x*c.y*a.z = a.z*b.x*c.y (stp_abc term 5)
    assert(b.x * c.y * a.z == a.z * b.x * c.y) by(nonlinear_arith);
    // Term 2: b.x*c.z*a.y = a.y*b.x*c.z (stp_abc term 4, negated)
    assert(b.x * c.z * a.y == a.y * b.x * c.z) by(nonlinear_arith);
    // Term 3: b.y*c.z*a.x = a.x*b.y*c.z (stp_abc term 1)
    assert(b.y * c.z * a.x == a.x * b.y * c.z) by(nonlinear_arith);
    // Term 4: b.y*c.x*a.z = a.z*b.y*c.x (stp_abc term 6, negated)
    assert(b.y * c.x * a.z == a.z * b.y * c.x) by(nonlinear_arith);
    // Term 5: b.z*c.x*a.y = a.y*b.z*c.x (stp_abc term 3)
    assert(b.z * c.x * a.y == a.y * b.z * c.x) by(nonlinear_arith);
    // Term 6: b.z*c.y*a.x = a.x*b.z*c.y (stp_abc term 2, negated)
    assert(b.z * c.y * a.x == a.x * b.z * c.y) by(nonlinear_arith);

    // Match stp_cab terms to stp_abc terms:
    // Term 1: c.x*a.y*b.z = a.y*b.z*c.x (stp_abc term 3)
    assert(c.x * a.y * b.z == a.y * b.z * c.x) by(nonlinear_arith);
    // Term 2: c.x*a.z*b.y = a.z*b.y*c.x (stp_abc term 6, negated)
    assert(c.x * a.z * b.y == a.z * b.y * c.x) by(nonlinear_arith);
    // Term 3: c.y*a.z*b.x = a.z*b.x*c.y (stp_abc term 5)
    assert(c.y * a.z * b.x == a.z * b.x * c.y) by(nonlinear_arith);
    // Term 4: c.y*a.x*b.z = a.x*b.z*c.y (stp_abc term 2, negated)
    assert(c.y * a.x * b.z == a.x * b.z * c.y) by(nonlinear_arith);
    // Term 5: c.z*a.x*b.y = a.x*b.y*c.z (stp_abc term 1)
    assert(c.z * a.x * b.y == a.x * b.y * c.z) by(nonlinear_arith);
    // Term 6: c.z*a.y*b.x = a.y*b.x*c.z (stp_abc term 4, negated)
    assert(c.z * a.y * b.x == a.y * b.x * c.z) by(nonlinear_arith);
}

/// **Theorem 23**: Scalar triple product is cyclic.
///
/// For all vectors a, b, c: a · (b × c) = b · (c × a) = c · (a × b)
///
/// This proves that the scalar triple product (the signed volume of the
/// parallelepiped formed by three vectors) is invariant under cyclic
/// permutation of its arguments.
proof fn vec3_scalar_triple_cyclic(a: SpecVec3, b: SpecVec3, c: SpecVec3)
    ensures
        vec3_dot(a, vec3_cross(b, c)) == vec3_dot(b, vec3_cross(c, a)),
        vec3_dot(b, vec3_cross(c, a)) == vec3_dot(c, vec3_cross(a, b)),
{
    stp_abc_expansion(a, b, c);
    stp_bca_expansion(a, b, c);
    stp_cab_expansion(a, b, c);
    expanded_forms_equal(a, b, c);
}

// =============================================================================
// EXTENDED OPERATIONS (Spec Functions)
// =============================================================================

/// Creates a vector with all components set to the same value.
pub open spec fn vec3_splat(value: int) -> SpecVec3 {
    SpecVec3 { x: value, y: value, z: value }
}

/// Component-wise minimum of two vectors.
pub open spec fn vec3_min(a: SpecVec3, b: SpecVec3) -> SpecVec3 {
    SpecVec3 {
        x: if a.x <= b.x { a.x } else { b.x },
        y: if a.y <= b.y { a.y } else { b.y },
        z: if a.z <= b.z { a.z } else { b.z },
    }
}

/// Component-wise maximum of two vectors.
pub open spec fn vec3_max(a: SpecVec3, b: SpecVec3) -> SpecVec3 {
    SpecVec3 {
        x: if a.x >= b.x { a.x } else { b.x },
        y: if a.y >= b.y { a.y } else { b.y },
        z: if a.z >= b.z { a.z } else { b.z },
    }
}

/// Component-wise absolute value.
pub open spec fn vec3_abs(v: SpecVec3) -> SpecVec3 {
    SpecVec3 {
        x: if v.x >= 0 { v.x } else { -v.x },
        y: if v.y >= 0 { v.y } else { -v.y },
        z: if v.z >= 0 { v.z } else { -v.z },
    }
}

/// Sum of all components.
pub open spec fn vec3_element_sum(v: SpecVec3) -> int {
    v.x + v.y + v.z
}

/// Product of all components.
pub open spec fn vec3_element_product(v: SpecVec3) -> int {
    v.x * v.y * v.z
}

/// Squared distance between two points.
pub open spec fn vec3_distance_squared(a: SpecVec3, b: SpecVec3) -> int {
    vec3_length_squared(vec3_sub(a, b))
}

// =============================================================================
// SPLAT PROOFS
// =============================================================================

/// **Theorem 25**: Splat is equivalent to new(v, v, v).
proof fn vec3_splat_is_new(value: int)
    ensures
        vec3_splat(value) == vec3_new(value, value, value),
{
}

/// **Theorem 26**: Splat(0) is the zero vector.
proof fn vec3_splat_zero()
    ensures
        vec3_splat(0) == vec3_zero(),
{
}

// =============================================================================
// MIN/MAX PROOFS
// =============================================================================

/// **Theorem 27**: Component-wise min is commutative.
proof fn vec3_min_commutative(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_min(a, b) == vec3_min(b, a),
{
}

/// **Theorem 28**: Component-wise max is commutative.
proof fn vec3_max_commutative(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_max(a, b) == vec3_max(b, a),
{
}

/// **Theorem 29**: min(a, a) = a (idempotent).
proof fn vec3_min_idempotent(a: SpecVec3)
    ensures
        vec3_min(a, a) == a,
{
}

/// **Theorem 30**: max(a, a) = a (idempotent).
proof fn vec3_max_idempotent(a: SpecVec3)
    ensures
        vec3_max(a, a) == a,
{
}

/// **Theorem 31**: min(a, b) + max(a, b) = a + b.
proof fn vec3_min_max_sum(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_add(vec3_min(a, b), vec3_max(a, b)) == vec3_add(a, b),
{
}

/// **Theorem 32**: min(a, b) is component-wise <= both operands.
proof fn vec3_min_le_both(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_min(a, b).x <= a.x && vec3_min(a, b).x <= b.x,
        vec3_min(a, b).y <= a.y && vec3_min(a, b).y <= b.y,
        vec3_min(a, b).z <= a.z && vec3_min(a, b).z <= b.z,
{
}

// =============================================================================
// ABS PROOFS
// =============================================================================

/// **Theorem 33**: Abs produces non-negative components.
proof fn vec3_abs_nonneg(v: SpecVec3)
    ensures
        vec3_abs(v).x >= 0 && vec3_abs(v).y >= 0 && vec3_abs(v).z >= 0,
{
}

/// **Theorem 34**: Abs is idempotent: abs(abs(v)) = abs(v).
proof fn vec3_abs_idempotent(v: SpecVec3)
    ensures
        vec3_abs(vec3_abs(v)) == vec3_abs(v),
{
    let a = vec3_abs(v);
    assert(a.x >= 0);
    assert(a.y >= 0);
    assert(a.z >= 0);
}

/// **Theorem 35**: Abs of negation equals abs: |−v| = |v|.
proof fn vec3_abs_neg(v: SpecVec3)
    ensures
        vec3_abs(vec3_neg(v)) == vec3_abs(v),
{
}

// =============================================================================
// ELEMENT SUM / PRODUCT PROOFS
// =============================================================================

/// **Theorem 36**: Element sum of zero is zero.
proof fn vec3_element_sum_zero()
    ensures
        vec3_element_sum(vec3_zero()) == 0,
{
}

/// **Theorem 37**: Element sum is additive: sum(a + b) = sum(a) + sum(b).
proof fn vec3_element_sum_additive(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_element_sum(vec3_add(a, b)) == vec3_element_sum(a) + vec3_element_sum(b),
{
}

/// **Theorem 38**: Element sum commutes with scaling.
proof fn vec3_element_sum_scale(s: int, v: SpecVec3)
    ensures
        vec3_element_sum(vec3_scale(s, v)) == s * vec3_element_sum(v),
{
    assert(s * v.x + s * v.y + s * v.z == s * (v.x + v.y + v.z)) by(nonlinear_arith);
}

// =============================================================================
// DISTANCE SQUARED PROOFS
// =============================================================================

/// **Theorem 39**: Distance squared is non-negative.
proof fn vec3_distance_squared_nonneg(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_distance_squared(a, b) >= 0,
{
    let d = vec3_sub(a, b);
    vec3_length_squared_nonnegative(d);
}

/// **Theorem 40**: Distance squared is symmetric.
proof fn vec3_distance_squared_symmetric(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_distance_squared(a, b) == vec3_distance_squared(b, a),
{
    let d1 = vec3_sub(a, b);
    let d2 = vec3_sub(b, a);
    // d1 = -d2 (linear arithmetic from vec3_sub definition)
    assert(d1.x == -d2.x);
    assert(d1.y == -d2.y);
    assert(d1.z == -d2.z);
    // (-x)² = x²: feed linear relationship as prerequisite to nonlinear_arith
    assert(d1.x * d1.x == d2.x * d2.x) by(nonlinear_arith)
        requires d1.x == -d2.x;
    assert(d1.y * d1.y == d2.y * d2.y) by(nonlinear_arith)
        requires d1.y == -d2.y;
    assert(d1.z * d1.z == d2.z * d2.z) by(nonlinear_arith)
        requires d1.z == -d2.z;
}

/// **Theorem 41**: Distance squared to self is zero.
proof fn vec3_distance_squared_self(a: SpecVec3)
    ensures
        vec3_distance_squared(a, a) == 0,
{
}

// =============================================================================
// VECTOR SPACE STRUCTURE
// =============================================================================

/// **Theorem 42**: Vec3 forms a vector space.
proof fn vec3_is_vector_space(a: SpecVec3, b: SpecVec3, c: SpecVec3, s: int, t: int)
    ensures
        vec3_add(a, b) == vec3_add(b, a),
        vec3_add(vec3_add(a, b), c) == vec3_add(a, vec3_add(b, c)),
        vec3_add(a, vec3_zero()) == a,
        vec3_add(a, vec3_neg(a)) == vec3_zero(),
        vec3_scale(s * t, a) == vec3_scale(s, vec3_scale(t, a)),
        vec3_scale(s, vec3_add(a, b)) == vec3_add(vec3_scale(s, a), vec3_scale(s, b)),
        vec3_scale(1, a) == a,
{
    vec3_add_commutative(a, b);
    vec3_add_associative(a, b, c);
    vec3_add_identity(a);
    vec3_add_inverse(a);
    vec3_scale_associative(s, t, a);
    vec3_scale_distributes_over_add(s, a, b);
    vec3_scale_identity(a);
}

// =============================================================================
// CLAMP OPERATIONS (Spec Functions)
// =============================================================================

/// Component-wise clamp.
pub open spec fn vec3_clamp(v: SpecVec3, lo: SpecVec3, hi: SpecVec3) -> SpecVec3 {
    SpecVec3 {
        x: if v.x < lo.x { lo.x } else if v.x > hi.x { hi.x } else { v.x },
        y: if v.y < lo.y { lo.y } else if v.y > hi.y { hi.y } else { v.y },
        z: if v.z < lo.z { lo.z } else if v.z > hi.z { hi.z } else { v.z },
    }
}

/// Reflection of v off surface with normal n: v - 2*(v·n)*n.
pub open spec fn vec3_reflect(v: SpecVec3, n: SpecVec3) -> SpecVec3 {
    vec3_sub(v, vec3_scale(2 * vec3_dot(v, n), n))
}

// =============================================================================
// CLAMP PROOFS
// =============================================================================

/// **Theorem 43**: Clamp produces values within bounds (when lo <= hi).
proof fn vec3_clamp_bounds(v: SpecVec3, lo: SpecVec3, hi: SpecVec3)
    requires
        lo.x <= hi.x && lo.y <= hi.y && lo.z <= hi.z,
    ensures ({
        let c = vec3_clamp(v, lo, hi);
        c.x >= lo.x && c.x <= hi.x
        && c.y >= lo.y && c.y <= hi.y
        && c.z >= lo.z && c.z <= hi.z
    }),
{
}

/// **Theorem 44**: Clamp of in-range value is identity.
proof fn vec3_clamp_identity(v: SpecVec3, lo: SpecVec3, hi: SpecVec3)
    requires
        v.x >= lo.x && v.x <= hi.x
        && v.y >= lo.y && v.y <= hi.y
        && v.z >= lo.z && v.z <= hi.z,
    ensures
        vec3_clamp(v, lo, hi) == v,
{
}

/// **Theorem 45**: Clamp is idempotent (when lo <= hi).
proof fn vec3_clamp_idempotent(v: SpecVec3, lo: SpecVec3, hi: SpecVec3)
    requires
        lo.x <= hi.x && lo.y <= hi.y && lo.z <= hi.z,
    ensures
        vec3_clamp(vec3_clamp(v, lo, hi), lo, hi) == vec3_clamp(v, lo, hi),
{
    let c = vec3_clamp(v, lo, hi);
    assert(c.x >= lo.x && c.x <= hi.x);
    assert(c.y >= lo.y && c.y <= hi.y);
    assert(c.z >= lo.z && c.z <= hi.z);
}

/// **Theorem 46**: Clamping to [v, v] always returns v (squeeze property).
proof fn vec3_clamp_squeeze(v: SpecVec3, target: SpecVec3)
    ensures
        vec3_clamp(v, target, target) == target,
{
}

// =============================================================================
// REFLECT PROOFS
// =============================================================================

/// **Theorem 47**: Reflecting a vector perpendicular to normal preserves it.
///
/// If v · n = 0, then reflect(v, n) = v.
proof fn vec3_reflect_perpendicular(v: SpecVec3, n: SpecVec3)
    requires
        vec3_dot(v, n) == 0,
    ensures
        vec3_reflect(v, n) == v,
{
    // reflect(v, n) = v - 2*(v·n)*n = v - 2*0*n = v - 0 = v
    assert(2 * 0 == 0);
    assert(0 * n.x == 0) by(nonlinear_arith);
    assert(0 * n.y == 0) by(nonlinear_arith);
    assert(0 * n.z == 0) by(nonlinear_arith);
}

/// **Theorem 48**: Reflecting a vector along a unit normal negates it.
///
/// If v · n = v · v (i.e., v = n scaled) and |n|² = 1, then reflect(v, n) = -v.
proof fn vec3_reflect_along_unit_normal(n: SpecVec3)
    requires
        vec3_dot(n, n) == 1,
    ensures
        vec3_reflect(n, n) == vec3_neg(n),
{
    // reflect(n, n) = n - 2*(n·n)*n = n - 2*1*n = n - 2n = -n
    assert(2 * vec3_dot(n, n) == 2);
    assert(2 * n.x == 2 * 1 * n.x) by(nonlinear_arith);
    assert(2 * n.y == 2 * 1 * n.y) by(nonlinear_arith);
    assert(2 * n.z == 2 * 1 * n.z) by(nonlinear_arith);
}

/// **Theorem 49**: Reflecting the zero vector always yields zero.
///
/// reflect(0, n) = 0 for any normal n.
proof fn vec3_reflect_zero(n: SpecVec3)
    ensures
        vec3_reflect(vec3_zero(), n) == vec3_zero(),
{
    // dot(0, n) = 0, so reflect(0, n) = 0 - 2*0*n = 0
    assert(0 * n.x == 0) by(nonlinear_arith);
    assert(0 * n.y == 0) by(nonlinear_arith);
    assert(0 * n.z == 0) by(nonlinear_arith);
}

// =============================================================================
// ELEMENT PRODUCT PROOFS
// =============================================================================

/// **Theorem 50**: Element product of zero vector is zero.
proof fn vec3_element_product_zero()
    ensures
        vec3_element_product(vec3_zero()) == 0,
{
}

/// **Theorem 51**: Element product of splat(v) is v³.
proof fn vec3_element_product_splat(v: int)
    ensures
        vec3_element_product(vec3_splat(v)) == v * v * v,
{
    assert(v * v * v == v * v * v) by(nonlinear_arith);
}

/// **Theorem 52**: Element product of unit basis vectors is zero.
///
/// Any standard basis vector (1,0,0), (0,1,0), (0,0,1) has element product = 0
/// because one component is zero.
proof fn vec3_element_product_basis_zero()
    ensures
        vec3_element_product(vec3_x()) == 0,
        vec3_element_product(vec3_y()) == 0,
        vec3_element_product(vec3_z()) == 0,
{
}

// =============================================================================
// LERP PROOFS
// =============================================================================

/// Integer model of linear interpolation: lerp(a, b, t) = a + (b - a) * t.
pub open spec fn vec3_lerp(a: SpecVec3, b: SpecVec3, t: int) -> SpecVec3 {
    SpecVec3 {
        x: a.x + (b.x - a.x) * t,
        y: a.y + (b.y - a.y) * t,
        z: a.z + (b.z - a.z) * t,
    }
}

/// **Theorem 53**: lerp(a, b, 0) = a.
proof fn vec3_lerp_zero(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_lerp(a, b, 0) == a,
{
}

/// **Theorem 54**: lerp(a, b, 1) = b.
proof fn vec3_lerp_one(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_lerp(a, b, 1) == b,
{
}

/// **Theorem 55**: lerp(v, v, t) = v for any t.
proof fn vec3_lerp_identity(v: SpecVec3, t: int)
    ensures
        vec3_lerp(v, v, t) == v,
{
    assert((v.x - v.x) * t == 0) by(nonlinear_arith);
    assert((v.y - v.y) * t == 0) by(nonlinear_arith);
    assert((v.z - v.z) * t == 0) by(nonlinear_arith);
}

/// **Theorem 56**: lerp at t=2 extrapolates: lerp(a, b, 2) = 2b - a.
proof fn vec3_lerp_two(a: SpecVec3, b: SpecVec3)
    ensures
        vec3_lerp(a, b, 2) == vec3_sub(vec3_scale(2, b), a),
{
}

/// **Theorem 57**: lerp of zero endpoints gives zero: lerp(zero, zero, t) = zero.
proof fn vec3_lerp_zero_zero(t: int)
    ensures
        vec3_lerp(vec3_zero(), vec3_zero(), t) == vec3_zero(),
{
    vec3_lerp_identity(vec3_zero(), t);
}

fn main() {
    // Verification only
}

}

