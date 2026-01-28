// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Mat4 Operations
//!
//! This module contains machine-checked proofs of correctness for Mat4 operations
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
//!    - Zero property (left): 0 * A = 0
//!    - Zero property (right): A * 0 = 0
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
//! 5. **Additional Properties** (Theorems 17-18)
//!    - Negation as scaling: -A = (-1) * A
//!    - Ring structure verification
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus --rlimit 30000000 crates/rource-math/proofs/mat4_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Mat4 Specification Type
// =============================================================================

/// Mathematical specification of a 4x4 matrix over integers.
/// Stored in column-major order: m[col * 4 + row]
///
/// Layout:
/// | m0  m4  m8  m12 |
/// | m1  m5  m9  m13 |
/// | m2  m6  m10 m14 |
/// | m3  m7  m11 m15 |
#[derive(PartialEq, Eq)]
pub struct SpecMat4 {
    pub m0: int, pub m1: int, pub m2: int, pub m3: int,     // Column 0
    pub m4: int, pub m5: int, pub m6: int, pub m7: int,     // Column 1
    pub m8: int, pub m9: int, pub m10: int, pub m11: int,   // Column 2
    pub m12: int, pub m13: int, pub m14: int, pub m15: int, // Column 3
}

// =============================================================================
// Matrix Operations (Spec Functions)
// =============================================================================

/// The zero matrix.
pub open spec fn mat4_zero() -> SpecMat4 {
    SpecMat4 {
        m0: 0, m1: 0, m2: 0, m3: 0,
        m4: 0, m5: 0, m6: 0, m7: 0,
        m8: 0, m9: 0, m10: 0, m11: 0,
        m12: 0, m13: 0, m14: 0, m15: 0,
    }
}

/// The identity matrix.
pub open spec fn mat4_identity() -> SpecMat4 {
    SpecMat4 {
        m0: 1, m1: 0, m2: 0, m3: 0,
        m4: 0, m5: 1, m6: 0, m7: 0,
        m8: 0, m9: 0, m10: 1, m11: 0,
        m12: 0, m13: 0, m14: 0, m15: 1,
    }
}

/// Matrix addition: A + B
pub open spec fn mat4_add(a: SpecMat4, b: SpecMat4) -> SpecMat4 {
    SpecMat4 {
        m0: a.m0 + b.m0, m1: a.m1 + b.m1, m2: a.m2 + b.m2, m3: a.m3 + b.m3,
        m4: a.m4 + b.m4, m5: a.m5 + b.m5, m6: a.m6 + b.m6, m7: a.m7 + b.m7,
        m8: a.m8 + b.m8, m9: a.m9 + b.m9, m10: a.m10 + b.m10, m11: a.m11 + b.m11,
        m12: a.m12 + b.m12, m13: a.m13 + b.m13, m14: a.m14 + b.m14, m15: a.m15 + b.m15,
    }
}

/// Matrix negation: -A
pub open spec fn mat4_neg(a: SpecMat4) -> SpecMat4 {
    SpecMat4 {
        m0: -a.m0, m1: -a.m1, m2: -a.m2, m3: -a.m3,
        m4: -a.m4, m5: -a.m5, m6: -a.m6, m7: -a.m7,
        m8: -a.m8, m9: -a.m9, m10: -a.m10, m11: -a.m11,
        m12: -a.m12, m13: -a.m13, m14: -a.m14, m15: -a.m15,
    }
}

/// Scalar multiplication: s * A
pub open spec fn mat4_scale(s: int, a: SpecMat4) -> SpecMat4 {
    SpecMat4 {
        m0: s * a.m0, m1: s * a.m1, m2: s * a.m2, m3: s * a.m3,
        m4: s * a.m4, m5: s * a.m5, m6: s * a.m6, m7: s * a.m7,
        m8: s * a.m8, m9: s * a.m9, m10: s * a.m10, m11: s * a.m11,
        m12: s * a.m12, m13: s * a.m13, m14: s * a.m14, m15: s * a.m15,
    }
}

/// Matrix transpose: A^T
pub open spec fn mat4_transpose(a: SpecMat4) -> SpecMat4 {
    SpecMat4 {
        m0: a.m0, m1: a.m4, m2: a.m8, m3: a.m12,
        m4: a.m1, m5: a.m5, m6: a.m9, m7: a.m13,
        m8: a.m2, m9: a.m6, m10: a.m10, m11: a.m14,
        m12: a.m3, m13: a.m7, m14: a.m11, m15: a.m15,
    }
}

/// Matrix multiplication: A * B (column-major)
/// C[col*4 + row] = sum over k of A[k*4 + row] * B[col*4 + k]
pub open spec fn mat4_mul(a: SpecMat4, b: SpecMat4) -> SpecMat4 {
    SpecMat4 {
        // Column 0
        m0: a.m0 * b.m0 + a.m4 * b.m1 + a.m8 * b.m2 + a.m12 * b.m3,
        m1: a.m1 * b.m0 + a.m5 * b.m1 + a.m9 * b.m2 + a.m13 * b.m3,
        m2: a.m2 * b.m0 + a.m6 * b.m1 + a.m10 * b.m2 + a.m14 * b.m3,
        m3: a.m3 * b.m0 + a.m7 * b.m1 + a.m11 * b.m2 + a.m15 * b.m3,
        // Column 1
        m4: a.m0 * b.m4 + a.m4 * b.m5 + a.m8 * b.m6 + a.m12 * b.m7,
        m5: a.m1 * b.m4 + a.m5 * b.m5 + a.m9 * b.m6 + a.m13 * b.m7,
        m6: a.m2 * b.m4 + a.m6 * b.m5 + a.m10 * b.m6 + a.m14 * b.m7,
        m7: a.m3 * b.m4 + a.m7 * b.m5 + a.m11 * b.m6 + a.m15 * b.m7,
        // Column 2
        m8: a.m0 * b.m8 + a.m4 * b.m9 + a.m8 * b.m10 + a.m12 * b.m11,
        m9: a.m1 * b.m8 + a.m5 * b.m9 + a.m9 * b.m10 + a.m13 * b.m11,
        m10: a.m2 * b.m8 + a.m6 * b.m9 + a.m10 * b.m10 + a.m14 * b.m11,
        m11: a.m3 * b.m8 + a.m7 * b.m9 + a.m11 * b.m10 + a.m15 * b.m11,
        // Column 3
        m12: a.m0 * b.m12 + a.m4 * b.m13 + a.m8 * b.m14 + a.m12 * b.m15,
        m13: a.m1 * b.m12 + a.m5 * b.m13 + a.m9 * b.m14 + a.m13 * b.m15,
        m14: a.m2 * b.m12 + a.m6 * b.m13 + a.m10 * b.m14 + a.m14 * b.m15,
        m15: a.m3 * b.m12 + a.m7 * b.m13 + a.m11 * b.m14 + a.m15 * b.m15,
    }
}

// =============================================================================
// MATRIX ADDITION PROOFS
// =============================================================================

/// **Theorem 1**: Matrix addition is commutative.
proof fn mat4_add_commutative(a: SpecMat4, b: SpecMat4)
    ensures
        mat4_add(a, b) == mat4_add(b, a),
{
}

/// **Theorem 2**: Matrix addition is associative.
proof fn mat4_add_associative(a: SpecMat4, b: SpecMat4, c: SpecMat4)
    ensures
        mat4_add(mat4_add(a, b), c) == mat4_add(a, mat4_add(b, c)),
{
}

/// **Theorem 3**: The zero matrix is an additive identity.
proof fn mat4_add_identity(a: SpecMat4)
    ensures
        mat4_add(a, mat4_zero()) == a,
{
}

/// **Theorem 4**: Every matrix has an additive inverse.
proof fn mat4_add_inverse(a: SpecMat4)
    ensures
        mat4_add(a, mat4_neg(a)) == mat4_zero(),
{
}

// =============================================================================
// MATRIX MULTIPLICATION - IDENTITY PROOFS
// =============================================================================

/// **Theorem 5**: The identity matrix is a left identity.
proof fn mat4_mul_left_identity(a: SpecMat4)
    ensures
        mat4_mul(mat4_identity(), a) == a,
{
}

/// **Theorem 6**: The identity matrix is a right identity.
proof fn mat4_mul_right_identity(a: SpecMat4)
    ensures
        mat4_mul(a, mat4_identity()) == a,
{
}

/// **Theorem 7**: Zero matrix is a left annihilator.
proof fn mat4_mul_zero_left(a: SpecMat4)
    ensures
        mat4_mul(mat4_zero(), a) == mat4_zero(),
{
}

/// **Theorem 8**: Zero matrix is a right annihilator.
proof fn mat4_mul_zero_right(a: SpecMat4)
    ensures
        mat4_mul(a, mat4_zero()) == mat4_zero(),
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

/// Distribution lemma for 4 terms (right): (w + x + y + z) * a = w*a + x*a + y*a + z*a
proof fn distrib_4_right(w: int, x: int, y: int, z: int, a: int)
    ensures
        (w + x + y + z) * a == w * a + x * a + y * a + z * a,
{
    assert((w + x + y + z) * a == w * a + x * a + y * a + z * a) by(nonlinear_arith);
}

/// Distribution lemma for 4 terms (left): a * (w + x + y + z) = a*w + a*x + a*y + a*z
proof fn distrib_4_left(a: int, w: int, x: int, y: int, z: int)
    ensures
        a * (w + x + y + z) == a * w + a * x + a * y + a * z,
{
    assert(a * (w + x + y + z) == a * w + a * x + a * y + a * z) by(nonlinear_arith);
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

// The key insight: (A*B)*C and A*(B*C) both produce the same 16 terms
// for each component. We prove this by explicit expansion.
//
// For 4x4 matrices, each result component is a sum of 4 products from A*B
// (or B*C), where each of those products is itself a sum of 4 terms.
// Total: 16 triple products per component.

/// **Theorem 9**: Matrix multiplication is associative.
///
/// For all matrices A, B, C: (A * B) * C = A * (B * C)
///
/// This is the critical property for transformation pipelines.
/// It ensures that applying a sequence of transformations can be
/// combined in any grouping without affecting the result.
proof fn mat4_mul_associative(a: SpecMat4, b: SpecMat4, c: SpecMat4)
    ensures
        mat4_mul(mat4_mul(a, b), c) == mat4_mul(a, mat4_mul(b, c)),
{
    let ab = mat4_mul(a, b);
    let bc = mat4_mul(b, c);

    // We need to show all 16 components are equal.
    // Each requires expanding and showing the 16 triple products match.
    //
    // For component m0 (row 0, col 0):
    // LHS: (ab.m0)*c.m0 + (ab.m4)*c.m1 + (ab.m8)*c.m2 + (ab.m12)*c.m3
    // RHS: a.m0*(bc.m0) + a.m4*(bc.m1) + a.m8*(bc.m2) + a.m12*(bc.m3)

    // Apply lemmas for all 16 components:

    // m0: row 0, col 0
    distrib_4_right(a.m0*b.m0, a.m4*b.m1, a.m8*b.m2, a.m12*b.m3, c.m0);
    distrib_4_right(a.m0*b.m4, a.m4*b.m5, a.m8*b.m6, a.m12*b.m7, c.m1);
    distrib_4_right(a.m0*b.m8, a.m4*b.m9, a.m8*b.m10, a.m12*b.m11, c.m2);
    distrib_4_right(a.m0*b.m12, a.m4*b.m13, a.m8*b.m14, a.m12*b.m15, c.m3);
    mul_assoc_3(a.m0, b.m0, c.m0); mul_assoc_3(a.m4, b.m1, c.m0);
    mul_assoc_3(a.m8, b.m2, c.m0); mul_assoc_3(a.m12, b.m3, c.m0);
    mul_assoc_3(a.m0, b.m4, c.m1); mul_assoc_3(a.m4, b.m5, c.m1);
    mul_assoc_3(a.m8, b.m6, c.m1); mul_assoc_3(a.m12, b.m7, c.m1);
    mul_assoc_3(a.m0, b.m8, c.m2); mul_assoc_3(a.m4, b.m9, c.m2);
    mul_assoc_3(a.m8, b.m10, c.m2); mul_assoc_3(a.m12, b.m11, c.m2);
    mul_assoc_3(a.m0, b.m12, c.m3); mul_assoc_3(a.m4, b.m13, c.m3);
    mul_assoc_3(a.m8, b.m14, c.m3); mul_assoc_3(a.m12, b.m15, c.m3);
    distrib_4_left(a.m0, b.m0*c.m0, b.m4*c.m1, b.m8*c.m2, b.m12*c.m3);
    distrib_4_left(a.m4, b.m1*c.m0, b.m5*c.m1, b.m9*c.m2, b.m13*c.m3);
    distrib_4_left(a.m8, b.m2*c.m0, b.m6*c.m1, b.m10*c.m2, b.m14*c.m3);
    distrib_4_left(a.m12, b.m3*c.m0, b.m7*c.m1, b.m11*c.m2, b.m15*c.m3);

    // m1: row 1, col 0
    distrib_4_right(a.m1*b.m0, a.m5*b.m1, a.m9*b.m2, a.m13*b.m3, c.m0);
    distrib_4_right(a.m1*b.m4, a.m5*b.m5, a.m9*b.m6, a.m13*b.m7, c.m1);
    distrib_4_right(a.m1*b.m8, a.m5*b.m9, a.m9*b.m10, a.m13*b.m11, c.m2);
    distrib_4_right(a.m1*b.m12, a.m5*b.m13, a.m9*b.m14, a.m13*b.m15, c.m3);
    mul_assoc_3(a.m1, b.m0, c.m0); mul_assoc_3(a.m5, b.m1, c.m0);
    mul_assoc_3(a.m9, b.m2, c.m0); mul_assoc_3(a.m13, b.m3, c.m0);
    mul_assoc_3(a.m1, b.m4, c.m1); mul_assoc_3(a.m5, b.m5, c.m1);
    mul_assoc_3(a.m9, b.m6, c.m1); mul_assoc_3(a.m13, b.m7, c.m1);
    mul_assoc_3(a.m1, b.m8, c.m2); mul_assoc_3(a.m5, b.m9, c.m2);
    mul_assoc_3(a.m9, b.m10, c.m2); mul_assoc_3(a.m13, b.m11, c.m2);
    mul_assoc_3(a.m1, b.m12, c.m3); mul_assoc_3(a.m5, b.m13, c.m3);
    mul_assoc_3(a.m9, b.m14, c.m3); mul_assoc_3(a.m13, b.m15, c.m3);
    distrib_4_left(a.m1, b.m0*c.m0, b.m4*c.m1, b.m8*c.m2, b.m12*c.m3);
    distrib_4_left(a.m5, b.m1*c.m0, b.m5*c.m1, b.m9*c.m2, b.m13*c.m3);
    distrib_4_left(a.m9, b.m2*c.m0, b.m6*c.m1, b.m10*c.m2, b.m14*c.m3);
    distrib_4_left(a.m13, b.m3*c.m0, b.m7*c.m1, b.m11*c.m2, b.m15*c.m3);

    // m2: row 2, col 0
    distrib_4_right(a.m2*b.m0, a.m6*b.m1, a.m10*b.m2, a.m14*b.m3, c.m0);
    distrib_4_right(a.m2*b.m4, a.m6*b.m5, a.m10*b.m6, a.m14*b.m7, c.m1);
    distrib_4_right(a.m2*b.m8, a.m6*b.m9, a.m10*b.m10, a.m14*b.m11, c.m2);
    distrib_4_right(a.m2*b.m12, a.m6*b.m13, a.m10*b.m14, a.m14*b.m15, c.m3);
    mul_assoc_3(a.m2, b.m0, c.m0); mul_assoc_3(a.m6, b.m1, c.m0);
    mul_assoc_3(a.m10, b.m2, c.m0); mul_assoc_3(a.m14, b.m3, c.m0);
    mul_assoc_3(a.m2, b.m4, c.m1); mul_assoc_3(a.m6, b.m5, c.m1);
    mul_assoc_3(a.m10, b.m6, c.m1); mul_assoc_3(a.m14, b.m7, c.m1);
    mul_assoc_3(a.m2, b.m8, c.m2); mul_assoc_3(a.m6, b.m9, c.m2);
    mul_assoc_3(a.m10, b.m10, c.m2); mul_assoc_3(a.m14, b.m11, c.m2);
    mul_assoc_3(a.m2, b.m12, c.m3); mul_assoc_3(a.m6, b.m13, c.m3);
    mul_assoc_3(a.m10, b.m14, c.m3); mul_assoc_3(a.m14, b.m15, c.m3);
    distrib_4_left(a.m2, b.m0*c.m0, b.m4*c.m1, b.m8*c.m2, b.m12*c.m3);
    distrib_4_left(a.m6, b.m1*c.m0, b.m5*c.m1, b.m9*c.m2, b.m13*c.m3);
    distrib_4_left(a.m10, b.m2*c.m0, b.m6*c.m1, b.m10*c.m2, b.m14*c.m3);
    distrib_4_left(a.m14, b.m3*c.m0, b.m7*c.m1, b.m11*c.m2, b.m15*c.m3);

    // m3: row 3, col 0
    distrib_4_right(a.m3*b.m0, a.m7*b.m1, a.m11*b.m2, a.m15*b.m3, c.m0);
    distrib_4_right(a.m3*b.m4, a.m7*b.m5, a.m11*b.m6, a.m15*b.m7, c.m1);
    distrib_4_right(a.m3*b.m8, a.m7*b.m9, a.m11*b.m10, a.m15*b.m11, c.m2);
    distrib_4_right(a.m3*b.m12, a.m7*b.m13, a.m11*b.m14, a.m15*b.m15, c.m3);
    mul_assoc_3(a.m3, b.m0, c.m0); mul_assoc_3(a.m7, b.m1, c.m0);
    mul_assoc_3(a.m11, b.m2, c.m0); mul_assoc_3(a.m15, b.m3, c.m0);
    mul_assoc_3(a.m3, b.m4, c.m1); mul_assoc_3(a.m7, b.m5, c.m1);
    mul_assoc_3(a.m11, b.m6, c.m1); mul_assoc_3(a.m15, b.m7, c.m1);
    mul_assoc_3(a.m3, b.m8, c.m2); mul_assoc_3(a.m7, b.m9, c.m2);
    mul_assoc_3(a.m11, b.m10, c.m2); mul_assoc_3(a.m15, b.m11, c.m2);
    mul_assoc_3(a.m3, b.m12, c.m3); mul_assoc_3(a.m7, b.m13, c.m3);
    mul_assoc_3(a.m11, b.m14, c.m3); mul_assoc_3(a.m15, b.m15, c.m3);
    distrib_4_left(a.m3, b.m0*c.m0, b.m4*c.m1, b.m8*c.m2, b.m12*c.m3);
    distrib_4_left(a.m7, b.m1*c.m0, b.m5*c.m1, b.m9*c.m2, b.m13*c.m3);
    distrib_4_left(a.m11, b.m2*c.m0, b.m6*c.m1, b.m10*c.m2, b.m14*c.m3);
    distrib_4_left(a.m15, b.m3*c.m0, b.m7*c.m1, b.m11*c.m2, b.m15*c.m3);

    // m4: row 0, col 1
    distrib_4_right(a.m0*b.m0, a.m4*b.m1, a.m8*b.m2, a.m12*b.m3, c.m4);
    distrib_4_right(a.m0*b.m4, a.m4*b.m5, a.m8*b.m6, a.m12*b.m7, c.m5);
    distrib_4_right(a.m0*b.m8, a.m4*b.m9, a.m8*b.m10, a.m12*b.m11, c.m6);
    distrib_4_right(a.m0*b.m12, a.m4*b.m13, a.m8*b.m14, a.m12*b.m15, c.m7);
    mul_assoc_3(a.m0, b.m0, c.m4); mul_assoc_3(a.m4, b.m1, c.m4);
    mul_assoc_3(a.m8, b.m2, c.m4); mul_assoc_3(a.m12, b.m3, c.m4);
    mul_assoc_3(a.m0, b.m4, c.m5); mul_assoc_3(a.m4, b.m5, c.m5);
    mul_assoc_3(a.m8, b.m6, c.m5); mul_assoc_3(a.m12, b.m7, c.m5);
    mul_assoc_3(a.m0, b.m8, c.m6); mul_assoc_3(a.m4, b.m9, c.m6);
    mul_assoc_3(a.m8, b.m10, c.m6); mul_assoc_3(a.m12, b.m11, c.m6);
    mul_assoc_3(a.m0, b.m12, c.m7); mul_assoc_3(a.m4, b.m13, c.m7);
    mul_assoc_3(a.m8, b.m14, c.m7); mul_assoc_3(a.m12, b.m15, c.m7);
    distrib_4_left(a.m0, b.m0*c.m4, b.m4*c.m5, b.m8*c.m6, b.m12*c.m7);
    distrib_4_left(a.m4, b.m1*c.m4, b.m5*c.m5, b.m9*c.m6, b.m13*c.m7);
    distrib_4_left(a.m8, b.m2*c.m4, b.m6*c.m5, b.m10*c.m6, b.m14*c.m7);
    distrib_4_left(a.m12, b.m3*c.m4, b.m7*c.m5, b.m11*c.m6, b.m15*c.m7);

    // m5: row 1, col 1
    distrib_4_right(a.m1*b.m0, a.m5*b.m1, a.m9*b.m2, a.m13*b.m3, c.m4);
    distrib_4_right(a.m1*b.m4, a.m5*b.m5, a.m9*b.m6, a.m13*b.m7, c.m5);
    distrib_4_right(a.m1*b.m8, a.m5*b.m9, a.m9*b.m10, a.m13*b.m11, c.m6);
    distrib_4_right(a.m1*b.m12, a.m5*b.m13, a.m9*b.m14, a.m13*b.m15, c.m7);
    mul_assoc_3(a.m1, b.m0, c.m4); mul_assoc_3(a.m5, b.m1, c.m4);
    mul_assoc_3(a.m9, b.m2, c.m4); mul_assoc_3(a.m13, b.m3, c.m4);
    mul_assoc_3(a.m1, b.m4, c.m5); mul_assoc_3(a.m5, b.m5, c.m5);
    mul_assoc_3(a.m9, b.m6, c.m5); mul_assoc_3(a.m13, b.m7, c.m5);
    mul_assoc_3(a.m1, b.m8, c.m6); mul_assoc_3(a.m5, b.m9, c.m6);
    mul_assoc_3(a.m9, b.m10, c.m6); mul_assoc_3(a.m13, b.m11, c.m6);
    mul_assoc_3(a.m1, b.m12, c.m7); mul_assoc_3(a.m5, b.m13, c.m7);
    mul_assoc_3(a.m9, b.m14, c.m7); mul_assoc_3(a.m13, b.m15, c.m7);
    distrib_4_left(a.m1, b.m0*c.m4, b.m4*c.m5, b.m8*c.m6, b.m12*c.m7);
    distrib_4_left(a.m5, b.m1*c.m4, b.m5*c.m5, b.m9*c.m6, b.m13*c.m7);
    distrib_4_left(a.m9, b.m2*c.m4, b.m6*c.m5, b.m10*c.m6, b.m14*c.m7);
    distrib_4_left(a.m13, b.m3*c.m4, b.m7*c.m5, b.m11*c.m6, b.m15*c.m7);

    // m6: row 2, col 1
    distrib_4_right(a.m2*b.m0, a.m6*b.m1, a.m10*b.m2, a.m14*b.m3, c.m4);
    distrib_4_right(a.m2*b.m4, a.m6*b.m5, a.m10*b.m6, a.m14*b.m7, c.m5);
    distrib_4_right(a.m2*b.m8, a.m6*b.m9, a.m10*b.m10, a.m14*b.m11, c.m6);
    distrib_4_right(a.m2*b.m12, a.m6*b.m13, a.m10*b.m14, a.m14*b.m15, c.m7);
    mul_assoc_3(a.m2, b.m0, c.m4); mul_assoc_3(a.m6, b.m1, c.m4);
    mul_assoc_3(a.m10, b.m2, c.m4); mul_assoc_3(a.m14, b.m3, c.m4);
    mul_assoc_3(a.m2, b.m4, c.m5); mul_assoc_3(a.m6, b.m5, c.m5);
    mul_assoc_3(a.m10, b.m6, c.m5); mul_assoc_3(a.m14, b.m7, c.m5);
    mul_assoc_3(a.m2, b.m8, c.m6); mul_assoc_3(a.m6, b.m9, c.m6);
    mul_assoc_3(a.m10, b.m10, c.m6); mul_assoc_3(a.m14, b.m11, c.m6);
    mul_assoc_3(a.m2, b.m12, c.m7); mul_assoc_3(a.m6, b.m13, c.m7);
    mul_assoc_3(a.m10, b.m14, c.m7); mul_assoc_3(a.m14, b.m15, c.m7);
    distrib_4_left(a.m2, b.m0*c.m4, b.m4*c.m5, b.m8*c.m6, b.m12*c.m7);
    distrib_4_left(a.m6, b.m1*c.m4, b.m5*c.m5, b.m9*c.m6, b.m13*c.m7);
    distrib_4_left(a.m10, b.m2*c.m4, b.m6*c.m5, b.m10*c.m6, b.m14*c.m7);
    distrib_4_left(a.m14, b.m3*c.m4, b.m7*c.m5, b.m11*c.m6, b.m15*c.m7);

    // m7: row 3, col 1
    distrib_4_right(a.m3*b.m0, a.m7*b.m1, a.m11*b.m2, a.m15*b.m3, c.m4);
    distrib_4_right(a.m3*b.m4, a.m7*b.m5, a.m11*b.m6, a.m15*b.m7, c.m5);
    distrib_4_right(a.m3*b.m8, a.m7*b.m9, a.m11*b.m10, a.m15*b.m11, c.m6);
    distrib_4_right(a.m3*b.m12, a.m7*b.m13, a.m11*b.m14, a.m15*b.m15, c.m7);
    mul_assoc_3(a.m3, b.m0, c.m4); mul_assoc_3(a.m7, b.m1, c.m4);
    mul_assoc_3(a.m11, b.m2, c.m4); mul_assoc_3(a.m15, b.m3, c.m4);
    mul_assoc_3(a.m3, b.m4, c.m5); mul_assoc_3(a.m7, b.m5, c.m5);
    mul_assoc_3(a.m11, b.m6, c.m5); mul_assoc_3(a.m15, b.m7, c.m5);
    mul_assoc_3(a.m3, b.m8, c.m6); mul_assoc_3(a.m7, b.m9, c.m6);
    mul_assoc_3(a.m11, b.m10, c.m6); mul_assoc_3(a.m15, b.m11, c.m6);
    mul_assoc_3(a.m3, b.m12, c.m7); mul_assoc_3(a.m7, b.m13, c.m7);
    mul_assoc_3(a.m11, b.m14, c.m7); mul_assoc_3(a.m15, b.m15, c.m7);
    distrib_4_left(a.m3, b.m0*c.m4, b.m4*c.m5, b.m8*c.m6, b.m12*c.m7);
    distrib_4_left(a.m7, b.m1*c.m4, b.m5*c.m5, b.m9*c.m6, b.m13*c.m7);
    distrib_4_left(a.m11, b.m2*c.m4, b.m6*c.m5, b.m10*c.m6, b.m14*c.m7);
    distrib_4_left(a.m15, b.m3*c.m4, b.m7*c.m5, b.m11*c.m6, b.m15*c.m7);

    // m8: row 0, col 2
    distrib_4_right(a.m0*b.m0, a.m4*b.m1, a.m8*b.m2, a.m12*b.m3, c.m8);
    distrib_4_right(a.m0*b.m4, a.m4*b.m5, a.m8*b.m6, a.m12*b.m7, c.m9);
    distrib_4_right(a.m0*b.m8, a.m4*b.m9, a.m8*b.m10, a.m12*b.m11, c.m10);
    distrib_4_right(a.m0*b.m12, a.m4*b.m13, a.m8*b.m14, a.m12*b.m15, c.m11);
    mul_assoc_3(a.m0, b.m0, c.m8); mul_assoc_3(a.m4, b.m1, c.m8);
    mul_assoc_3(a.m8, b.m2, c.m8); mul_assoc_3(a.m12, b.m3, c.m8);
    mul_assoc_3(a.m0, b.m4, c.m9); mul_assoc_3(a.m4, b.m5, c.m9);
    mul_assoc_3(a.m8, b.m6, c.m9); mul_assoc_3(a.m12, b.m7, c.m9);
    mul_assoc_3(a.m0, b.m8, c.m10); mul_assoc_3(a.m4, b.m9, c.m10);
    mul_assoc_3(a.m8, b.m10, c.m10); mul_assoc_3(a.m12, b.m11, c.m10);
    mul_assoc_3(a.m0, b.m12, c.m11); mul_assoc_3(a.m4, b.m13, c.m11);
    mul_assoc_3(a.m8, b.m14, c.m11); mul_assoc_3(a.m12, b.m15, c.m11);
    distrib_4_left(a.m0, b.m0*c.m8, b.m4*c.m9, b.m8*c.m10, b.m12*c.m11);
    distrib_4_left(a.m4, b.m1*c.m8, b.m5*c.m9, b.m9*c.m10, b.m13*c.m11);
    distrib_4_left(a.m8, b.m2*c.m8, b.m6*c.m9, b.m10*c.m10, b.m14*c.m11);
    distrib_4_left(a.m12, b.m3*c.m8, b.m7*c.m9, b.m11*c.m10, b.m15*c.m11);

    // m9: row 1, col 2
    distrib_4_right(a.m1*b.m0, a.m5*b.m1, a.m9*b.m2, a.m13*b.m3, c.m8);
    distrib_4_right(a.m1*b.m4, a.m5*b.m5, a.m9*b.m6, a.m13*b.m7, c.m9);
    distrib_4_right(a.m1*b.m8, a.m5*b.m9, a.m9*b.m10, a.m13*b.m11, c.m10);
    distrib_4_right(a.m1*b.m12, a.m5*b.m13, a.m9*b.m14, a.m13*b.m15, c.m11);
    mul_assoc_3(a.m1, b.m0, c.m8); mul_assoc_3(a.m5, b.m1, c.m8);
    mul_assoc_3(a.m9, b.m2, c.m8); mul_assoc_3(a.m13, b.m3, c.m8);
    mul_assoc_3(a.m1, b.m4, c.m9); mul_assoc_3(a.m5, b.m5, c.m9);
    mul_assoc_3(a.m9, b.m6, c.m9); mul_assoc_3(a.m13, b.m7, c.m9);
    mul_assoc_3(a.m1, b.m8, c.m10); mul_assoc_3(a.m5, b.m9, c.m10);
    mul_assoc_3(a.m9, b.m10, c.m10); mul_assoc_3(a.m13, b.m11, c.m10);
    mul_assoc_3(a.m1, b.m12, c.m11); mul_assoc_3(a.m5, b.m13, c.m11);
    mul_assoc_3(a.m9, b.m14, c.m11); mul_assoc_3(a.m13, b.m15, c.m11);
    distrib_4_left(a.m1, b.m0*c.m8, b.m4*c.m9, b.m8*c.m10, b.m12*c.m11);
    distrib_4_left(a.m5, b.m1*c.m8, b.m5*c.m9, b.m9*c.m10, b.m13*c.m11);
    distrib_4_left(a.m9, b.m2*c.m8, b.m6*c.m9, b.m10*c.m10, b.m14*c.m11);
    distrib_4_left(a.m13, b.m3*c.m8, b.m7*c.m9, b.m11*c.m10, b.m15*c.m11);

    // m10: row 2, col 2
    distrib_4_right(a.m2*b.m0, a.m6*b.m1, a.m10*b.m2, a.m14*b.m3, c.m8);
    distrib_4_right(a.m2*b.m4, a.m6*b.m5, a.m10*b.m6, a.m14*b.m7, c.m9);
    distrib_4_right(a.m2*b.m8, a.m6*b.m9, a.m10*b.m10, a.m14*b.m11, c.m10);
    distrib_4_right(a.m2*b.m12, a.m6*b.m13, a.m10*b.m14, a.m14*b.m15, c.m11);
    mul_assoc_3(a.m2, b.m0, c.m8); mul_assoc_3(a.m6, b.m1, c.m8);
    mul_assoc_3(a.m10, b.m2, c.m8); mul_assoc_3(a.m14, b.m3, c.m8);
    mul_assoc_3(a.m2, b.m4, c.m9); mul_assoc_3(a.m6, b.m5, c.m9);
    mul_assoc_3(a.m10, b.m6, c.m9); mul_assoc_3(a.m14, b.m7, c.m9);
    mul_assoc_3(a.m2, b.m8, c.m10); mul_assoc_3(a.m6, b.m9, c.m10);
    mul_assoc_3(a.m10, b.m10, c.m10); mul_assoc_3(a.m14, b.m11, c.m10);
    mul_assoc_3(a.m2, b.m12, c.m11); mul_assoc_3(a.m6, b.m13, c.m11);
    mul_assoc_3(a.m10, b.m14, c.m11); mul_assoc_3(a.m14, b.m15, c.m11);
    distrib_4_left(a.m2, b.m0*c.m8, b.m4*c.m9, b.m8*c.m10, b.m12*c.m11);
    distrib_4_left(a.m6, b.m1*c.m8, b.m5*c.m9, b.m9*c.m10, b.m13*c.m11);
    distrib_4_left(a.m10, b.m2*c.m8, b.m6*c.m9, b.m10*c.m10, b.m14*c.m11);
    distrib_4_left(a.m14, b.m3*c.m8, b.m7*c.m9, b.m11*c.m10, b.m15*c.m11);

    // m11: row 3, col 2
    distrib_4_right(a.m3*b.m0, a.m7*b.m1, a.m11*b.m2, a.m15*b.m3, c.m8);
    distrib_4_right(a.m3*b.m4, a.m7*b.m5, a.m11*b.m6, a.m15*b.m7, c.m9);
    distrib_4_right(a.m3*b.m8, a.m7*b.m9, a.m11*b.m10, a.m15*b.m11, c.m10);
    distrib_4_right(a.m3*b.m12, a.m7*b.m13, a.m11*b.m14, a.m15*b.m15, c.m11);
    mul_assoc_3(a.m3, b.m0, c.m8); mul_assoc_3(a.m7, b.m1, c.m8);
    mul_assoc_3(a.m11, b.m2, c.m8); mul_assoc_3(a.m15, b.m3, c.m8);
    mul_assoc_3(a.m3, b.m4, c.m9); mul_assoc_3(a.m7, b.m5, c.m9);
    mul_assoc_3(a.m11, b.m6, c.m9); mul_assoc_3(a.m15, b.m7, c.m9);
    mul_assoc_3(a.m3, b.m8, c.m10); mul_assoc_3(a.m7, b.m9, c.m10);
    mul_assoc_3(a.m11, b.m10, c.m10); mul_assoc_3(a.m15, b.m11, c.m10);
    mul_assoc_3(a.m3, b.m12, c.m11); mul_assoc_3(a.m7, b.m13, c.m11);
    mul_assoc_3(a.m11, b.m14, c.m11); mul_assoc_3(a.m15, b.m15, c.m11);
    distrib_4_left(a.m3, b.m0*c.m8, b.m4*c.m9, b.m8*c.m10, b.m12*c.m11);
    distrib_4_left(a.m7, b.m1*c.m8, b.m5*c.m9, b.m9*c.m10, b.m13*c.m11);
    distrib_4_left(a.m11, b.m2*c.m8, b.m6*c.m9, b.m10*c.m10, b.m14*c.m11);
    distrib_4_left(a.m15, b.m3*c.m8, b.m7*c.m9, b.m11*c.m10, b.m15*c.m11);

    // m12: row 0, col 3
    distrib_4_right(a.m0*b.m0, a.m4*b.m1, a.m8*b.m2, a.m12*b.m3, c.m12);
    distrib_4_right(a.m0*b.m4, a.m4*b.m5, a.m8*b.m6, a.m12*b.m7, c.m13);
    distrib_4_right(a.m0*b.m8, a.m4*b.m9, a.m8*b.m10, a.m12*b.m11, c.m14);
    distrib_4_right(a.m0*b.m12, a.m4*b.m13, a.m8*b.m14, a.m12*b.m15, c.m15);
    mul_assoc_3(a.m0, b.m0, c.m12); mul_assoc_3(a.m4, b.m1, c.m12);
    mul_assoc_3(a.m8, b.m2, c.m12); mul_assoc_3(a.m12, b.m3, c.m12);
    mul_assoc_3(a.m0, b.m4, c.m13); mul_assoc_3(a.m4, b.m5, c.m13);
    mul_assoc_3(a.m8, b.m6, c.m13); mul_assoc_3(a.m12, b.m7, c.m13);
    mul_assoc_3(a.m0, b.m8, c.m14); mul_assoc_3(a.m4, b.m9, c.m14);
    mul_assoc_3(a.m8, b.m10, c.m14); mul_assoc_3(a.m12, b.m11, c.m14);
    mul_assoc_3(a.m0, b.m12, c.m15); mul_assoc_3(a.m4, b.m13, c.m15);
    mul_assoc_3(a.m8, b.m14, c.m15); mul_assoc_3(a.m12, b.m15, c.m15);
    distrib_4_left(a.m0, b.m0*c.m12, b.m4*c.m13, b.m8*c.m14, b.m12*c.m15);
    distrib_4_left(a.m4, b.m1*c.m12, b.m5*c.m13, b.m9*c.m14, b.m13*c.m15);
    distrib_4_left(a.m8, b.m2*c.m12, b.m6*c.m13, b.m10*c.m14, b.m14*c.m15);
    distrib_4_left(a.m12, b.m3*c.m12, b.m7*c.m13, b.m11*c.m14, b.m15*c.m15);

    // m13: row 1, col 3
    distrib_4_right(a.m1*b.m0, a.m5*b.m1, a.m9*b.m2, a.m13*b.m3, c.m12);
    distrib_4_right(a.m1*b.m4, a.m5*b.m5, a.m9*b.m6, a.m13*b.m7, c.m13);
    distrib_4_right(a.m1*b.m8, a.m5*b.m9, a.m9*b.m10, a.m13*b.m11, c.m14);
    distrib_4_right(a.m1*b.m12, a.m5*b.m13, a.m9*b.m14, a.m13*b.m15, c.m15);
    mul_assoc_3(a.m1, b.m0, c.m12); mul_assoc_3(a.m5, b.m1, c.m12);
    mul_assoc_3(a.m9, b.m2, c.m12); mul_assoc_3(a.m13, b.m3, c.m12);
    mul_assoc_3(a.m1, b.m4, c.m13); mul_assoc_3(a.m5, b.m5, c.m13);
    mul_assoc_3(a.m9, b.m6, c.m13); mul_assoc_3(a.m13, b.m7, c.m13);
    mul_assoc_3(a.m1, b.m8, c.m14); mul_assoc_3(a.m5, b.m9, c.m14);
    mul_assoc_3(a.m9, b.m10, c.m14); mul_assoc_3(a.m13, b.m11, c.m14);
    mul_assoc_3(a.m1, b.m12, c.m15); mul_assoc_3(a.m5, b.m13, c.m15);
    mul_assoc_3(a.m9, b.m14, c.m15); mul_assoc_3(a.m13, b.m15, c.m15);
    distrib_4_left(a.m1, b.m0*c.m12, b.m4*c.m13, b.m8*c.m14, b.m12*c.m15);
    distrib_4_left(a.m5, b.m1*c.m12, b.m5*c.m13, b.m9*c.m14, b.m13*c.m15);
    distrib_4_left(a.m9, b.m2*c.m12, b.m6*c.m13, b.m10*c.m14, b.m14*c.m15);
    distrib_4_left(a.m13, b.m3*c.m12, b.m7*c.m13, b.m11*c.m14, b.m15*c.m15);

    // m14: row 2, col 3
    distrib_4_right(a.m2*b.m0, a.m6*b.m1, a.m10*b.m2, a.m14*b.m3, c.m12);
    distrib_4_right(a.m2*b.m4, a.m6*b.m5, a.m10*b.m6, a.m14*b.m7, c.m13);
    distrib_4_right(a.m2*b.m8, a.m6*b.m9, a.m10*b.m10, a.m14*b.m11, c.m14);
    distrib_4_right(a.m2*b.m12, a.m6*b.m13, a.m10*b.m14, a.m14*b.m15, c.m15);
    mul_assoc_3(a.m2, b.m0, c.m12); mul_assoc_3(a.m6, b.m1, c.m12);
    mul_assoc_3(a.m10, b.m2, c.m12); mul_assoc_3(a.m14, b.m3, c.m12);
    mul_assoc_3(a.m2, b.m4, c.m13); mul_assoc_3(a.m6, b.m5, c.m13);
    mul_assoc_3(a.m10, b.m6, c.m13); mul_assoc_3(a.m14, b.m7, c.m13);
    mul_assoc_3(a.m2, b.m8, c.m14); mul_assoc_3(a.m6, b.m9, c.m14);
    mul_assoc_3(a.m10, b.m10, c.m14); mul_assoc_3(a.m14, b.m11, c.m14);
    mul_assoc_3(a.m2, b.m12, c.m15); mul_assoc_3(a.m6, b.m13, c.m15);
    mul_assoc_3(a.m10, b.m14, c.m15); mul_assoc_3(a.m14, b.m15, c.m15);
    distrib_4_left(a.m2, b.m0*c.m12, b.m4*c.m13, b.m8*c.m14, b.m12*c.m15);
    distrib_4_left(a.m6, b.m1*c.m12, b.m5*c.m13, b.m9*c.m14, b.m13*c.m15);
    distrib_4_left(a.m10, b.m2*c.m12, b.m6*c.m13, b.m10*c.m14, b.m14*c.m15);
    distrib_4_left(a.m14, b.m3*c.m12, b.m7*c.m13, b.m11*c.m14, b.m15*c.m15);

    // m15: row 3, col 3
    distrib_4_right(a.m3*b.m0, a.m7*b.m1, a.m11*b.m2, a.m15*b.m3, c.m12);
    distrib_4_right(a.m3*b.m4, a.m7*b.m5, a.m11*b.m6, a.m15*b.m7, c.m13);
    distrib_4_right(a.m3*b.m8, a.m7*b.m9, a.m11*b.m10, a.m15*b.m11, c.m14);
    distrib_4_right(a.m3*b.m12, a.m7*b.m13, a.m11*b.m14, a.m15*b.m15, c.m15);
    mul_assoc_3(a.m3, b.m0, c.m12); mul_assoc_3(a.m7, b.m1, c.m12);
    mul_assoc_3(a.m11, b.m2, c.m12); mul_assoc_3(a.m15, b.m3, c.m12);
    mul_assoc_3(a.m3, b.m4, c.m13); mul_assoc_3(a.m7, b.m5, c.m13);
    mul_assoc_3(a.m11, b.m6, c.m13); mul_assoc_3(a.m15, b.m7, c.m13);
    mul_assoc_3(a.m3, b.m8, c.m14); mul_assoc_3(a.m7, b.m9, c.m14);
    mul_assoc_3(a.m11, b.m10, c.m14); mul_assoc_3(a.m15, b.m11, c.m14);
    mul_assoc_3(a.m3, b.m12, c.m15); mul_assoc_3(a.m7, b.m13, c.m15);
    mul_assoc_3(a.m11, b.m14, c.m15); mul_assoc_3(a.m15, b.m15, c.m15);
    distrib_4_left(a.m3, b.m0*c.m12, b.m4*c.m13, b.m8*c.m14, b.m12*c.m15);
    distrib_4_left(a.m7, b.m1*c.m12, b.m5*c.m13, b.m9*c.m14, b.m13*c.m15);
    distrib_4_left(a.m11, b.m2*c.m12, b.m6*c.m13, b.m10*c.m14, b.m14*c.m15);
    distrib_4_left(a.m15, b.m3*c.m12, b.m7*c.m13, b.m11*c.m14, b.m15*c.m15);
}

// =============================================================================
// SCALAR MULTIPLICATION PROOFS
// =============================================================================

/// **Theorem 10**: Scalar multiplication by 1 is identity.
proof fn mat4_scale_identity(a: SpecMat4)
    ensures
        mat4_scale(1, a) == a,
{
}

/// **Theorem 11**: Scalar multiplication by 0 is zero.
proof fn mat4_scale_zero(a: SpecMat4)
    ensures
        mat4_scale(0, a) == mat4_zero(),
{
}

/// **Theorem 12**: Scalar multiplication distributes over addition.
proof fn mat4_scale_distributes_over_add(s: int, a: SpecMat4, b: SpecMat4)
    ensures
        mat4_scale(s, mat4_add(a, b)) == mat4_add(mat4_scale(s, a), mat4_scale(s, b)),
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
    distrib_2(s, a.m9, b.m9);
    distrib_2(s, a.m10, b.m10);
    distrib_2(s, a.m11, b.m11);
    distrib_2(s, a.m12, b.m12);
    distrib_2(s, a.m13, b.m13);
    distrib_2(s, a.m14, b.m14);
    distrib_2(s, a.m15, b.m15);
}

/// **Theorem 13**: Scalar multiplication is associative.
proof fn mat4_scale_associative(s: int, t: int, a: SpecMat4)
    ensures
        mat4_scale(s * t, a) == mat4_scale(s, mat4_scale(t, a)),
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
    mul_assoc_3(s, t, a.m9);
    mul_assoc_3(s, t, a.m10);
    mul_assoc_3(s, t, a.m11);
    mul_assoc_3(s, t, a.m12);
    mul_assoc_3(s, t, a.m13);
    mul_assoc_3(s, t, a.m14);
    mul_assoc_3(s, t, a.m15);
}

// =============================================================================
// TRANSPOSE PROOFS
// =============================================================================

/// **Theorem 14**: Double transpose is identity.
proof fn mat4_transpose_transpose(a: SpecMat4)
    ensures
        mat4_transpose(mat4_transpose(a)) == a,
{
}

/// **Theorem 15**: Transpose distributes over addition.
proof fn mat4_transpose_add(a: SpecMat4, b: SpecMat4)
    ensures
        mat4_transpose(mat4_add(a, b)) == mat4_add(mat4_transpose(a), mat4_transpose(b)),
{
}

/// **Theorem 16**: Transpose commutes with scalar multiplication.
proof fn mat4_transpose_scale(s: int, a: SpecMat4)
    ensures
        mat4_transpose(mat4_scale(s, a)) == mat4_scale(s, mat4_transpose(a)),
{
}

// =============================================================================
// ADDITIONAL PROPERTIES
// =============================================================================

/// **Theorem 17**: Negation as scaling by -1.
proof fn mat4_neg_as_scale(a: SpecMat4)
    ensures
        mat4_neg(a) == mat4_scale(-1, a),
{
}

// =============================================================================
// MATRIX STRUCTURE THEOREM
// =============================================================================

/// **Theorem 18**: Mat4 forms a ring with identity.
proof fn mat4_is_ring(a: SpecMat4, b: SpecMat4, c: SpecMat4)
    ensures
        mat4_add(a, b) == mat4_add(b, a),
        mat4_add(mat4_add(a, b), c) == mat4_add(a, mat4_add(b, c)),
        mat4_add(a, mat4_zero()) == a,
        mat4_add(a, mat4_neg(a)) == mat4_zero(),
        mat4_mul(mat4_mul(a, b), c) == mat4_mul(a, mat4_mul(b, c)),
        mat4_mul(mat4_identity(), a) == a,
        mat4_mul(a, mat4_identity()) == a,
{
    mat4_add_commutative(a, b);
    mat4_add_associative(a, b, c);
    mat4_add_identity(a);
    mat4_add_inverse(a);
    mat4_mul_associative(a, b, c);
    mat4_mul_left_identity(a);
    mat4_mul_right_identity(a);
}

fn main() {
    // Verification only
}

}
