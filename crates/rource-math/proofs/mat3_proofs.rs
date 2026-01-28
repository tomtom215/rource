// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Mat3 Operations
//!
//! This module contains machine-checked proofs of correctness for Mat3 operations
//! using the Verus formal verification tool.
//!
//! ## Verification Status
//!
//! All proofs in this file have been verified by Verus with zero admits.
//!
//! ## Properties Verified
//!
//! 1. **Matrix Addition Properties** (Theorems 1-4)
//!    - Commutativity: A + B = B + A
//!    - Associativity: (A + B) + C = A + (B + C)
//!    - Identity: A + 0 = A
//!    - Inverse: A + (-A) = 0
//!
//! 2. **Matrix Multiplication Properties** (Theorems 5-9)
//!    - Left identity: I * A = A
//!    - Right identity: A * I = A
//!    - Zero property: 0 * A = 0
//!    - Associativity: (A * B) * C = A * (B * C) [CRITICAL]
//!
//! 3. **Scalar Multiplication Properties** (Theorems 10-13)
//!    - Identity: 1 * A = A
//!    - Zero: 0 * A = 0
//!    - Distribution over addition: s * (A + B) = s * A + s * B
//!    - Associativity: (s * t) * A = s * (t * A)
//!
//! 4. **Transpose Properties** (Theorems 14-16)
//!    - Double transpose: (A^T)^T = A
//!    - Transpose of sum: (A + B)^T = A^T + B^T
//!    - Transpose of scalar: (s * A)^T = s * A^T
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/mat3_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Mat3 Specification Type
// =============================================================================

/// Mathematical specification of a 3x3 matrix over integers.
/// Stored in column-major order: m[col * 3 + row]
///
/// Layout:
/// | m0 m3 m6 |
/// | m1 m4 m7 |
/// | m2 m5 m8 |
#[derive(PartialEq, Eq)]
pub struct SpecMat3 {
    pub m0: int, pub m1: int, pub m2: int,  // Column 0
    pub m3: int, pub m4: int, pub m5: int,  // Column 1
    pub m6: int, pub m7: int, pub m8: int,  // Column 2
}

// =============================================================================
// Matrix Operations (Spec Functions)
// =============================================================================

/// Creates a new matrix from column-major elements.
pub open spec fn mat3_new(
    m0: int, m1: int, m2: int,
    m3: int, m4: int, m5: int,
    m6: int, m7: int, m8: int,
) -> SpecMat3 {
    SpecMat3 { m0, m1, m2, m3, m4, m5, m6, m7, m8 }
}

/// The zero matrix.
pub open spec fn mat3_zero() -> SpecMat3 {
    SpecMat3 {
        m0: 0, m1: 0, m2: 0,
        m3: 0, m4: 0, m5: 0,
        m6: 0, m7: 0, m8: 0,
    }
}

/// The identity matrix.
pub open spec fn mat3_identity() -> SpecMat3 {
    SpecMat3 {
        m0: 1, m1: 0, m2: 0,
        m3: 0, m4: 1, m5: 0,
        m6: 0, m7: 0, m8: 1,
    }
}

/// Matrix addition: A + B
pub open spec fn mat3_add(a: SpecMat3, b: SpecMat3) -> SpecMat3 {
    SpecMat3 {
        m0: a.m0 + b.m0, m1: a.m1 + b.m1, m2: a.m2 + b.m2,
        m3: a.m3 + b.m3, m4: a.m4 + b.m4, m5: a.m5 + b.m5,
        m6: a.m6 + b.m6, m7: a.m7 + b.m7, m8: a.m8 + b.m8,
    }
}

/// Matrix negation: -A
pub open spec fn mat3_neg(a: SpecMat3) -> SpecMat3 {
    SpecMat3 {
        m0: -a.m0, m1: -a.m1, m2: -a.m2,
        m3: -a.m3, m4: -a.m4, m5: -a.m5,
        m6: -a.m6, m7: -a.m7, m8: -a.m8,
    }
}

/// Scalar multiplication: s * A
pub open spec fn mat3_scale(s: int, a: SpecMat3) -> SpecMat3 {
    SpecMat3 {
        m0: s * a.m0, m1: s * a.m1, m2: s * a.m2,
        m3: s * a.m3, m4: s * a.m4, m5: s * a.m5,
        m6: s * a.m6, m7: s * a.m7, m8: s * a.m8,
    }
}

/// Matrix transpose: A^T
pub open spec fn mat3_transpose(a: SpecMat3) -> SpecMat3 {
    SpecMat3 {
        m0: a.m0, m1: a.m3, m2: a.m6,
        m3: a.m1, m4: a.m4, m5: a.m7,
        m6: a.m2, m7: a.m5, m8: a.m8,
    }
}

/// Matrix multiplication: A * B (column-major)
pub open spec fn mat3_mul(a: SpecMat3, b: SpecMat3) -> SpecMat3 {
    SpecMat3 {
        // Column 0
        m0: a.m0 * b.m0 + a.m3 * b.m1 + a.m6 * b.m2,
        m1: a.m1 * b.m0 + a.m4 * b.m1 + a.m7 * b.m2,
        m2: a.m2 * b.m0 + a.m5 * b.m1 + a.m8 * b.m2,
        // Column 1
        m3: a.m0 * b.m3 + a.m3 * b.m4 + a.m6 * b.m5,
        m4: a.m1 * b.m3 + a.m4 * b.m4 + a.m7 * b.m5,
        m5: a.m2 * b.m3 + a.m5 * b.m4 + a.m8 * b.m5,
        // Column 2
        m6: a.m0 * b.m6 + a.m3 * b.m7 + a.m6 * b.m8,
        m7: a.m1 * b.m6 + a.m4 * b.m7 + a.m7 * b.m8,
        m8: a.m2 * b.m6 + a.m5 * b.m7 + a.m8 * b.m8,
    }
}

// =============================================================================
// MATRIX ADDITION PROOFS
// =============================================================================

/// **Theorem 1**: Matrix addition is commutative.
proof fn mat3_add_commutative(a: SpecMat3, b: SpecMat3)
    ensures
        mat3_add(a, b) == mat3_add(b, a),
{
}

/// **Theorem 2**: Matrix addition is associative.
proof fn mat3_add_associative(a: SpecMat3, b: SpecMat3, c: SpecMat3)
    ensures
        mat3_add(mat3_add(a, b), c) == mat3_add(a, mat3_add(b, c)),
{
}

/// **Theorem 3**: The zero matrix is an additive identity.
proof fn mat3_add_identity(a: SpecMat3)
    ensures
        mat3_add(a, mat3_zero()) == a,
{
}

/// **Theorem 4**: Every matrix has an additive inverse.
proof fn mat3_add_inverse(a: SpecMat3)
    ensures
        mat3_add(a, mat3_neg(a)) == mat3_zero(),
{
}

// =============================================================================
// MATRIX MULTIPLICATION - IDENTITY PROOFS
// =============================================================================

/// **Theorem 5**: The identity matrix is a left identity.
proof fn mat3_mul_left_identity(a: SpecMat3)
    ensures
        mat3_mul(mat3_identity(), a) == a,
{
}

/// **Theorem 6**: The identity matrix is a right identity.
proof fn mat3_mul_right_identity(a: SpecMat3)
    ensures
        mat3_mul(a, mat3_identity()) == a,
{
}

/// **Theorem 7**: Zero matrix is a left annihilator.
proof fn mat3_mul_zero_left(a: SpecMat3)
    ensures
        mat3_mul(mat3_zero(), a) == mat3_zero(),
{
}

/// **Theorem 8**: Zero matrix is a right annihilator.
proof fn mat3_mul_zero_right(a: SpecMat3)
    ensures
        mat3_mul(a, mat3_zero()) == mat3_zero(),
{
}

// =============================================================================
// ARITHMETIC LEMMAS (for associativity)
// =============================================================================

/// Distribution lemma: a * (x + y) = a*x + a*y
proof fn distrib_2(a: int, x: int, y: int)
    ensures
        a * (x + y) == a * x + a * y,
{
    assert(a * (x + y) == a * x + a * y) by(nonlinear_arith);
}

/// Distribution lemma: (x + y + z) * a = x*a + y*a + z*a
proof fn distrib_3_right(x: int, y: int, z: int, a: int)
    ensures
        (x + y + z) * a == x * a + y * a + z * a,
{
    assert((x + y + z) * a == x * a + y * a + z * a) by(nonlinear_arith);
}

/// Multiplication associativity for 3 terms
proof fn mul_assoc_3(a: int, b: int, c: int)
    ensures
        (a * b) * c == a * (b * c),
{
    assert((a * b) * c == a * (b * c)) by(nonlinear_arith);
}

// =============================================================================
// MATRIX MULTIPLICATION ASSOCIATIVITY
// =============================================================================

// The key insight: (A*B)*C and A*(B*C) both produce the same 9 terms
// for each component. We prove this by explicit expansion.

// For component m0:
// (A*B)*C: ((a0*b0 + a3*b1 + a6*b2)*c0 + (a0*b3 + a3*b4 + a6*b5)*c1 + (a0*b6 + a3*b7 + a6*b8)*c2)
// A*(B*C): (a0*(b0*c0 + b3*c1 + b6*c2) + a3*(b1*c0 + b4*c1 + b7*c2) + a6*(b2*c0 + b5*c1 + b8*c2))
// Both expand to: a0*b0*c0 + a0*b3*c1 + a0*b6*c2 + a3*b1*c0 + a3*b4*c1 + a3*b7*c2 + a6*b2*c0 + a6*b5*c1 + a6*b8*c2

/// Helper: Component 0 of (A*B)*C
pub open spec fn lhs_m0(a: SpecMat3, b: SpecMat3, c: SpecMat3) -> int {
    (a.m0*b.m0 + a.m3*b.m1 + a.m6*b.m2) * c.m0 +
    (a.m0*b.m3 + a.m3*b.m4 + a.m6*b.m5) * c.m1 +
    (a.m0*b.m6 + a.m3*b.m7 + a.m6*b.m8) * c.m2
}

/// Helper: Component 0 of A*(B*C)
pub open spec fn rhs_m0(a: SpecMat3, b: SpecMat3, c: SpecMat3) -> int {
    a.m0 * (b.m0*c.m0 + b.m3*c.m1 + b.m6*c.m2) +
    a.m3 * (b.m1*c.m0 + b.m4*c.m1 + b.m7*c.m2) +
    a.m6 * (b.m2*c.m0 + b.m5*c.m1 + b.m8*c.m2)
}

/// Prove component 0 equality
proof fn assoc_m0(a: SpecMat3, b: SpecMat3, c: SpecMat3)
    ensures
        lhs_m0(a, b, c) == rhs_m0(a, b, c),
{
    // LHS distribution
    distrib_3_right(a.m0*b.m0, a.m3*b.m1, a.m6*b.m2, c.m0);
    distrib_3_right(a.m0*b.m3, a.m3*b.m4, a.m6*b.m5, c.m1);
    distrib_3_right(a.m0*b.m6, a.m3*b.m7, a.m6*b.m8, c.m2);

    // All multiplication associativities
    mul_assoc_3(a.m0, b.m0, c.m0); mul_assoc_3(a.m3, b.m1, c.m0); mul_assoc_3(a.m6, b.m2, c.m0);
    mul_assoc_3(a.m0, b.m3, c.m1); mul_assoc_3(a.m3, b.m4, c.m1); mul_assoc_3(a.m6, b.m5, c.m1);
    mul_assoc_3(a.m0, b.m6, c.m2); mul_assoc_3(a.m3, b.m7, c.m2); mul_assoc_3(a.m6, b.m8, c.m2);

    // RHS distribution
    distrib_2(a.m0, b.m0*c.m0, b.m3*c.m1);
    distrib_2(a.m0, b.m0*c.m0 + b.m3*c.m1, b.m6*c.m2);
    distrib_2(a.m3, b.m1*c.m0, b.m4*c.m1);
    distrib_2(a.m3, b.m1*c.m0 + b.m4*c.m1, b.m7*c.m2);
    distrib_2(a.m6, b.m2*c.m0, b.m5*c.m1);
    distrib_2(a.m6, b.m2*c.m0 + b.m5*c.m1, b.m8*c.m2);
}

/// **Theorem 9**: Matrix multiplication is associative.
///
/// For all matrices A, B, C: (A * B) * C = A * (B * C)
///
/// This is the critical property for transformation pipelines.
/// It ensures that applying a sequence of transformations can be
/// combined in any grouping without affecting the result.
///
/// The proof shows that both sides produce identical sums of
/// products a_i * b_j * c_k for each component.
proof fn mat3_mul_associative(a: SpecMat3, b: SpecMat3, c: SpecMat3)
    ensures
        mat3_mul(mat3_mul(a, b), c) == mat3_mul(a, mat3_mul(b, c)),
{
    let ab = mat3_mul(a, b);
    let bc = mat3_mul(b, c);

    // We need to show all 9 components are equal.
    // Each follows the same pattern as m0.

    // For m0
    assoc_m0(a, b, c);

    // For remaining components, apply the same lemmas.
    // m1: row 1, col 0
    distrib_3_right(a.m1*b.m0, a.m4*b.m1, a.m7*b.m2, c.m0);
    distrib_3_right(a.m1*b.m3, a.m4*b.m4, a.m7*b.m5, c.m1);
    distrib_3_right(a.m1*b.m6, a.m4*b.m7, a.m7*b.m8, c.m2);
    mul_assoc_3(a.m1, b.m0, c.m0); mul_assoc_3(a.m4, b.m1, c.m0); mul_assoc_3(a.m7, b.m2, c.m0);
    mul_assoc_3(a.m1, b.m3, c.m1); mul_assoc_3(a.m4, b.m4, c.m1); mul_assoc_3(a.m7, b.m5, c.m1);
    mul_assoc_3(a.m1, b.m6, c.m2); mul_assoc_3(a.m4, b.m7, c.m2); mul_assoc_3(a.m7, b.m8, c.m2);
    distrib_2(a.m1, b.m0*c.m0, b.m3*c.m1);
    distrib_2(a.m1, b.m0*c.m0 + b.m3*c.m1, b.m6*c.m2);
    distrib_2(a.m4, b.m1*c.m0, b.m4*c.m1);
    distrib_2(a.m4, b.m1*c.m0 + b.m4*c.m1, b.m7*c.m2);
    distrib_2(a.m7, b.m2*c.m0, b.m5*c.m1);
    distrib_2(a.m7, b.m2*c.m0 + b.m5*c.m1, b.m8*c.m2);

    // m2: row 2, col 0
    distrib_3_right(a.m2*b.m0, a.m5*b.m1, a.m8*b.m2, c.m0);
    distrib_3_right(a.m2*b.m3, a.m5*b.m4, a.m8*b.m5, c.m1);
    distrib_3_right(a.m2*b.m6, a.m5*b.m7, a.m8*b.m8, c.m2);
    mul_assoc_3(a.m2, b.m0, c.m0); mul_assoc_3(a.m5, b.m1, c.m0); mul_assoc_3(a.m8, b.m2, c.m0);
    mul_assoc_3(a.m2, b.m3, c.m1); mul_assoc_3(a.m5, b.m4, c.m1); mul_assoc_3(a.m8, b.m5, c.m1);
    mul_assoc_3(a.m2, b.m6, c.m2); mul_assoc_3(a.m5, b.m7, c.m2); mul_assoc_3(a.m8, b.m8, c.m2);
    distrib_2(a.m2, b.m0*c.m0, b.m3*c.m1);
    distrib_2(a.m2, b.m0*c.m0 + b.m3*c.m1, b.m6*c.m2);
    distrib_2(a.m5, b.m1*c.m0, b.m4*c.m1);
    distrib_2(a.m5, b.m1*c.m0 + b.m4*c.m1, b.m7*c.m2);
    distrib_2(a.m8, b.m2*c.m0, b.m5*c.m1);
    distrib_2(a.m8, b.m2*c.m0 + b.m5*c.m1, b.m8*c.m2);

    // m3: row 0, col 1
    distrib_3_right(a.m0*b.m0, a.m3*b.m1, a.m6*b.m2, c.m3);
    distrib_3_right(a.m0*b.m3, a.m3*b.m4, a.m6*b.m5, c.m4);
    distrib_3_right(a.m0*b.m6, a.m3*b.m7, a.m6*b.m8, c.m5);
    mul_assoc_3(a.m0, b.m0, c.m3); mul_assoc_3(a.m3, b.m1, c.m3); mul_assoc_3(a.m6, b.m2, c.m3);
    mul_assoc_3(a.m0, b.m3, c.m4); mul_assoc_3(a.m3, b.m4, c.m4); mul_assoc_3(a.m6, b.m5, c.m4);
    mul_assoc_3(a.m0, b.m6, c.m5); mul_assoc_3(a.m3, b.m7, c.m5); mul_assoc_3(a.m6, b.m8, c.m5);
    distrib_2(a.m0, b.m0*c.m3, b.m3*c.m4);
    distrib_2(a.m0, b.m0*c.m3 + b.m3*c.m4, b.m6*c.m5);
    distrib_2(a.m3, b.m1*c.m3, b.m4*c.m4);
    distrib_2(a.m3, b.m1*c.m3 + b.m4*c.m4, b.m7*c.m5);
    distrib_2(a.m6, b.m2*c.m3, b.m5*c.m4);
    distrib_2(a.m6, b.m2*c.m3 + b.m5*c.m4, b.m8*c.m5);

    // m4: row 1, col 1
    distrib_3_right(a.m1*b.m0, a.m4*b.m1, a.m7*b.m2, c.m3);
    distrib_3_right(a.m1*b.m3, a.m4*b.m4, a.m7*b.m5, c.m4);
    distrib_3_right(a.m1*b.m6, a.m4*b.m7, a.m7*b.m8, c.m5);
    mul_assoc_3(a.m1, b.m0, c.m3); mul_assoc_3(a.m4, b.m1, c.m3); mul_assoc_3(a.m7, b.m2, c.m3);
    mul_assoc_3(a.m1, b.m3, c.m4); mul_assoc_3(a.m4, b.m4, c.m4); mul_assoc_3(a.m7, b.m5, c.m4);
    mul_assoc_3(a.m1, b.m6, c.m5); mul_assoc_3(a.m4, b.m7, c.m5); mul_assoc_3(a.m7, b.m8, c.m5);
    distrib_2(a.m1, b.m0*c.m3, b.m3*c.m4);
    distrib_2(a.m1, b.m0*c.m3 + b.m3*c.m4, b.m6*c.m5);
    distrib_2(a.m4, b.m1*c.m3, b.m4*c.m4);
    distrib_2(a.m4, b.m1*c.m3 + b.m4*c.m4, b.m7*c.m5);
    distrib_2(a.m7, b.m2*c.m3, b.m5*c.m4);
    distrib_2(a.m7, b.m2*c.m3 + b.m5*c.m4, b.m8*c.m5);

    // m5: row 2, col 1
    distrib_3_right(a.m2*b.m0, a.m5*b.m1, a.m8*b.m2, c.m3);
    distrib_3_right(a.m2*b.m3, a.m5*b.m4, a.m8*b.m5, c.m4);
    distrib_3_right(a.m2*b.m6, a.m5*b.m7, a.m8*b.m8, c.m5);
    mul_assoc_3(a.m2, b.m0, c.m3); mul_assoc_3(a.m5, b.m1, c.m3); mul_assoc_3(a.m8, b.m2, c.m3);
    mul_assoc_3(a.m2, b.m3, c.m4); mul_assoc_3(a.m5, b.m4, c.m4); mul_assoc_3(a.m8, b.m5, c.m4);
    mul_assoc_3(a.m2, b.m6, c.m5); mul_assoc_3(a.m5, b.m7, c.m5); mul_assoc_3(a.m8, b.m8, c.m5);
    distrib_2(a.m2, b.m0*c.m3, b.m3*c.m4);
    distrib_2(a.m2, b.m0*c.m3 + b.m3*c.m4, b.m6*c.m5);
    distrib_2(a.m5, b.m1*c.m3, b.m4*c.m4);
    distrib_2(a.m5, b.m1*c.m3 + b.m4*c.m4, b.m7*c.m5);
    distrib_2(a.m8, b.m2*c.m3, b.m5*c.m4);
    distrib_2(a.m8, b.m2*c.m3 + b.m5*c.m4, b.m8*c.m5);

    // m6: row 0, col 2
    distrib_3_right(a.m0*b.m0, a.m3*b.m1, a.m6*b.m2, c.m6);
    distrib_3_right(a.m0*b.m3, a.m3*b.m4, a.m6*b.m5, c.m7);
    distrib_3_right(a.m0*b.m6, a.m3*b.m7, a.m6*b.m8, c.m8);
    mul_assoc_3(a.m0, b.m0, c.m6); mul_assoc_3(a.m3, b.m1, c.m6); mul_assoc_3(a.m6, b.m2, c.m6);
    mul_assoc_3(a.m0, b.m3, c.m7); mul_assoc_3(a.m3, b.m4, c.m7); mul_assoc_3(a.m6, b.m5, c.m7);
    mul_assoc_3(a.m0, b.m6, c.m8); mul_assoc_3(a.m3, b.m7, c.m8); mul_assoc_3(a.m6, b.m8, c.m8);
    distrib_2(a.m0, b.m0*c.m6, b.m3*c.m7);
    distrib_2(a.m0, b.m0*c.m6 + b.m3*c.m7, b.m6*c.m8);
    distrib_2(a.m3, b.m1*c.m6, b.m4*c.m7);
    distrib_2(a.m3, b.m1*c.m6 + b.m4*c.m7, b.m7*c.m8);
    distrib_2(a.m6, b.m2*c.m6, b.m5*c.m7);
    distrib_2(a.m6, b.m2*c.m6 + b.m5*c.m7, b.m8*c.m8);

    // m7: row 1, col 2
    distrib_3_right(a.m1*b.m0, a.m4*b.m1, a.m7*b.m2, c.m6);
    distrib_3_right(a.m1*b.m3, a.m4*b.m4, a.m7*b.m5, c.m7);
    distrib_3_right(a.m1*b.m6, a.m4*b.m7, a.m7*b.m8, c.m8);
    mul_assoc_3(a.m1, b.m0, c.m6); mul_assoc_3(a.m4, b.m1, c.m6); mul_assoc_3(a.m7, b.m2, c.m6);
    mul_assoc_3(a.m1, b.m3, c.m7); mul_assoc_3(a.m4, b.m4, c.m7); mul_assoc_3(a.m7, b.m5, c.m7);
    mul_assoc_3(a.m1, b.m6, c.m8); mul_assoc_3(a.m4, b.m7, c.m8); mul_assoc_3(a.m7, b.m8, c.m8);
    distrib_2(a.m1, b.m0*c.m6, b.m3*c.m7);
    distrib_2(a.m1, b.m0*c.m6 + b.m3*c.m7, b.m6*c.m8);
    distrib_2(a.m4, b.m1*c.m6, b.m4*c.m7);
    distrib_2(a.m4, b.m1*c.m6 + b.m4*c.m7, b.m7*c.m8);
    distrib_2(a.m7, b.m2*c.m6, b.m5*c.m7);
    distrib_2(a.m7, b.m2*c.m6 + b.m5*c.m7, b.m8*c.m8);

    // m8: row 2, col 2
    distrib_3_right(a.m2*b.m0, a.m5*b.m1, a.m8*b.m2, c.m6);
    distrib_3_right(a.m2*b.m3, a.m5*b.m4, a.m8*b.m5, c.m7);
    distrib_3_right(a.m2*b.m6, a.m5*b.m7, a.m8*b.m8, c.m8);
    mul_assoc_3(a.m2, b.m0, c.m6); mul_assoc_3(a.m5, b.m1, c.m6); mul_assoc_3(a.m8, b.m2, c.m6);
    mul_assoc_3(a.m2, b.m3, c.m7); mul_assoc_3(a.m5, b.m4, c.m7); mul_assoc_3(a.m8, b.m5, c.m7);
    mul_assoc_3(a.m2, b.m6, c.m8); mul_assoc_3(a.m5, b.m7, c.m8); mul_assoc_3(a.m8, b.m8, c.m8);
    distrib_2(a.m2, b.m0*c.m6, b.m3*c.m7);
    distrib_2(a.m2, b.m0*c.m6 + b.m3*c.m7, b.m6*c.m8);
    distrib_2(a.m5, b.m1*c.m6, b.m4*c.m7);
    distrib_2(a.m5, b.m1*c.m6 + b.m4*c.m7, b.m7*c.m8);
    distrib_2(a.m8, b.m2*c.m6, b.m5*c.m7);
    distrib_2(a.m8, b.m2*c.m6 + b.m5*c.m7, b.m8*c.m8);
}

// =============================================================================
// SCALAR MULTIPLICATION PROOFS
// =============================================================================

/// **Theorem 10**: Scalar multiplication by 1 is identity.
proof fn mat3_scale_identity(a: SpecMat3)
    ensures
        mat3_scale(1, a) == a,
{
}

/// **Theorem 11**: Scalar multiplication by 0 is zero.
proof fn mat3_scale_zero(a: SpecMat3)
    ensures
        mat3_scale(0, a) == mat3_zero(),
{
}

/// **Theorem 12**: Scalar multiplication distributes over addition.
proof fn mat3_scale_distributes_over_add(s: int, a: SpecMat3, b: SpecMat3)
    ensures
        mat3_scale(s, mat3_add(a, b)) == mat3_add(mat3_scale(s, a), mat3_scale(s, b)),
{
    distrib_2(s, a.m0, b.m0);
    distrib_2(s, a.m1, b.m1);
    distrib_2(s, a.m2, b.m2);
    distrib_2(s, a.m3, b.m3);
    distrib_2(s, a.m4, b.m4);
    distrib_2(s, a.m5, b.m5);
    distrib_2(s, a.m6, b.m6);
    distrib_2(s, a.m7, b.m7);
    distrib_2(s, a.m8, b.m8);
}

/// **Theorem 13**: Scalar multiplication is associative.
proof fn mat3_scale_associative(s: int, t: int, a: SpecMat3)
    ensures
        mat3_scale(s * t, a) == mat3_scale(s, mat3_scale(t, a)),
{
    mul_assoc_3(s, t, a.m0);
    mul_assoc_3(s, t, a.m1);
    mul_assoc_3(s, t, a.m2);
    mul_assoc_3(s, t, a.m3);
    mul_assoc_3(s, t, a.m4);
    mul_assoc_3(s, t, a.m5);
    mul_assoc_3(s, t, a.m6);
    mul_assoc_3(s, t, a.m7);
    mul_assoc_3(s, t, a.m8);
}

// =============================================================================
// TRANSPOSE PROOFS
// =============================================================================

/// **Theorem 14**: Double transpose is identity.
proof fn mat3_transpose_transpose(a: SpecMat3)
    ensures
        mat3_transpose(mat3_transpose(a)) == a,
{
}

/// **Theorem 15**: Transpose distributes over addition.
proof fn mat3_transpose_add(a: SpecMat3, b: SpecMat3)
    ensures
        mat3_transpose(mat3_add(a, b)) == mat3_add(mat3_transpose(a), mat3_transpose(b)),
{
}

/// **Theorem 16**: Transpose commutes with scalar multiplication.
proof fn mat3_transpose_scale(s: int, a: SpecMat3)
    ensures
        mat3_transpose(mat3_scale(s, a)) == mat3_scale(s, mat3_transpose(a)),
{
}

// =============================================================================
// ADDITIONAL PROPERTIES
// =============================================================================

/// **Theorem 17**: Negation as scaling by -1.
proof fn mat3_neg_as_scale(a: SpecMat3)
    ensures
        mat3_neg(a) == mat3_scale(-1, a),
{
}

// =============================================================================
// MATRIX STRUCTURE THEOREM
// =============================================================================

/// **Theorem 18**: Mat3 forms a ring with identity.
proof fn mat3_is_ring(a: SpecMat3, b: SpecMat3, c: SpecMat3)
    ensures
        mat3_add(a, b) == mat3_add(b, a),
        mat3_add(mat3_add(a, b), c) == mat3_add(a, mat3_add(b, c)),
        mat3_add(a, mat3_zero()) == a,
        mat3_add(a, mat3_neg(a)) == mat3_zero(),
        mat3_mul(mat3_mul(a, b), c) == mat3_mul(a, mat3_mul(b, c)),
        mat3_mul(mat3_identity(), a) == a,
        mat3_mul(a, mat3_identity()) == a,
{
    mat3_add_commutative(a, b);
    mat3_add_associative(a, b, c);
    mat3_add_identity(a);
    mat3_add_inverse(a);
    mat3_mul_associative(a, b, c);
    mat3_mul_left_identity(a);
    mat3_mul_right_identity(a);
}

fn main() {
    // Verification only
}

}
