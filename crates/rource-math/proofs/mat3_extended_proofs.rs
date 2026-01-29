// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Mat3 Extended Operations
//!
//! This module contains machine-checked proofs for Mat3 determinant,
//! transformation, translation, scaling, and shearing operations.
//!
//! Separated from mat3_proofs.rs because the combination of the matrix
//! multiplication associativity proof (200+ lemma calls) with nonlinear_arith
//! proofs exceeds Z3's resource limits in a single verification run.
//!
//! ## Properties Verified
//!
//! - Determinant Properties (Theorems 19-23)
//! - Translation Properties (Theorems 24-28)
//! - Scaling Properties (Theorems 29-33)
//! - Shearing Properties (Theorems 34-36)
//! - Transform Properties (Theorems 37-40)
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/mat3_extended_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Specification Types (duplicated for independent verification)
// =============================================================================

#[derive(PartialEq, Eq)]
pub struct SpecMat3 {
    pub m0: int, pub m1: int, pub m2: int,
    pub m3: int, pub m4: int, pub m5: int,
    pub m6: int, pub m7: int, pub m8: int,
}

#[derive(PartialEq, Eq)]
pub struct SpecVec2 {
    pub x: int,
    pub y: int,
}

// =============================================================================
// Spec Functions
// =============================================================================

pub open spec fn mat3_new(
    m0: int, m1: int, m2: int,
    m3: int, m4: int, m5: int,
    m6: int, m7: int, m8: int,
) -> SpecMat3 {
    SpecMat3 { m0, m1, m2, m3, m4, m5, m6, m7, m8 }
}

pub open spec fn mat3_zero() -> SpecMat3 {
    SpecMat3 { m0: 0, m1: 0, m2: 0, m3: 0, m4: 0, m5: 0, m6: 0, m7: 0, m8: 0 }
}

pub open spec fn mat3_identity() -> SpecMat3 {
    SpecMat3 { m0: 1, m1: 0, m2: 0, m3: 0, m4: 1, m5: 0, m6: 0, m7: 0, m8: 1 }
}

pub open spec fn mat3_mul(a: SpecMat3, b: SpecMat3) -> SpecMat3 {
    SpecMat3 {
        m0: a.m0 * b.m0 + a.m3 * b.m1 + a.m6 * b.m2,
        m1: a.m1 * b.m0 + a.m4 * b.m1 + a.m7 * b.m2,
        m2: a.m2 * b.m0 + a.m5 * b.m1 + a.m8 * b.m2,
        m3: a.m0 * b.m3 + a.m3 * b.m4 + a.m6 * b.m5,
        m4: a.m1 * b.m3 + a.m4 * b.m4 + a.m7 * b.m5,
        m5: a.m2 * b.m3 + a.m5 * b.m4 + a.m8 * b.m5,
        m6: a.m0 * b.m6 + a.m3 * b.m7 + a.m6 * b.m8,
        m7: a.m1 * b.m6 + a.m4 * b.m7 + a.m7 * b.m8,
        m8: a.m2 * b.m6 + a.m5 * b.m7 + a.m8 * b.m8,
    }
}

pub open spec fn mat3_transpose(a: SpecMat3) -> SpecMat3 {
    SpecMat3 {
        m0: a.m0, m1: a.m3, m2: a.m6,
        m3: a.m1, m4: a.m4, m5: a.m7,
        m6: a.m2, m7: a.m5, m8: a.m8,
    }
}

pub open spec fn mat3_determinant(a: SpecMat3) -> int {
    a.m0 * (a.m4 * a.m8 - a.m5 * a.m7)
    - a.m3 * (a.m1 * a.m8 - a.m2 * a.m7)
    + a.m6 * (a.m1 * a.m5 - a.m2 * a.m4)
}

pub open spec fn mat3_translation(tx: int, ty: int) -> SpecMat3 {
    SpecMat3 { m0: 1, m1: 0, m2: 0, m3: 0, m4: 1, m5: 0, m6: tx, m7: ty, m8: 1 }
}

pub open spec fn mat3_scaling(sx: int, sy: int) -> SpecMat3 {
    SpecMat3 { m0: sx, m1: 0, m2: 0, m3: 0, m4: sy, m5: 0, m6: 0, m7: 0, m8: 1 }
}

pub open spec fn mat3_shearing(shx: int, shy: int) -> SpecMat3 {
    SpecMat3 { m0: 1, m1: shy, m2: 0, m3: shx, m4: 1, m5: 0, m6: 0, m7: 0, m8: 1 }
}

pub open spec fn mat3_transform_point(m: SpecMat3, p: SpecVec2) -> SpecVec2 {
    SpecVec2 {
        x: m.m0 * p.x + m.m3 * p.y + m.m6,
        y: m.m1 * p.x + m.m4 * p.y + m.m7,
    }
}

pub open spec fn mat3_transform_vector(m: SpecMat3, v: SpecVec2) -> SpecVec2 {
    SpecVec2 {
        x: m.m0 * v.x + m.m3 * v.y,
        y: m.m1 * v.x + m.m4 * v.y,
    }
}

// =============================================================================
// DETERMINANT PROOFS (Theorems 19-23)
// =============================================================================

/// **Theorem 19**: det(I) = 1
proof fn mat3_det_identity()
    ensures mat3_determinant(mat3_identity()) == 1,
{ }

/// **Theorem 20**: det(0) = 0
proof fn mat3_det_zero()
    ensures mat3_determinant(mat3_zero()) == 0,
{ }

// =============================================================================
// HELPER LEMMAS for determinant proofs
// =============================================================================

/// Distribution: a * (b - c) = a*b - a*c
proof fn distrib_sub(a: int, b: int, c: int)
    ensures a * (b - c) == a * b - a * c,
{
    assert(a * (b - c) == a * b - a * c) by(nonlinear_arith);
}

/// Triple product commutativity: (a*b)*c = (b*a)*c
proof fn mul_comm_left(a: int, b: int, c: int)
    ensures (a * b) * c == (b * a) * c,
{
    assert(a * b == b * a) by(nonlinear_arith);
}

/// Triple product commutativity: a*(b*c) = a*(c*b)
proof fn mul_comm_right(a: int, b: int, c: int)
    ensures a * (b * c) == a * (c * b),
{
    assert(b * c == c * b) by(nonlinear_arith);
}

/// Associativity: (a*b)*c = a*(b*c)
proof fn mul_assoc(a: int, b: int, c: int)
    ensures (a * b) * c == a * (b * c),
{
    assert((a * b) * c == a * (b * c)) by(nonlinear_arith);
}

/// **Theorem 21**: det(A^T) = det(A)
///
/// Proof strategy: expand both determinants into 6 triple products via
/// distribution, assert their expanded forms, prove each differing
/// triple-product pair equal, then use nonlinear_arith with expanded
/// forms as requires to close the proof.
proof fn mat3_det_transpose(a: SpecMat3)
    ensures mat3_determinant(mat3_transpose(a)) == mat3_determinant(a),
{
    let at = mat3_transpose(a);
    let da = mat3_determinant(a);
    let dat = mat3_determinant(at);

    // Phase 1: Distribution to expand det(A) into 6 triple products
    distrib_sub(a.m0, a.m4 * a.m8, a.m5 * a.m7);
    distrib_sub(a.m3, a.m1 * a.m8, a.m2 * a.m7);
    distrib_sub(a.m6, a.m1 * a.m5, a.m2 * a.m4);

    assert(da == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m5 * a.m7)
              - a.m3 * (a.m1 * a.m8) + a.m3 * (a.m2 * a.m7)
              + a.m6 * (a.m1 * a.m5) - a.m6 * (a.m2 * a.m4));

    // Phase 2: Distribution to expand det(A^T) into 6 triple products
    // Transpose maps: m0=m0, m1=m3, m2=m6, m3=m1, m4=m4, m5=m7, m6=m2, m7=m5, m8=m8
    distrib_sub(a.m0, a.m4 * a.m8, a.m7 * a.m5);
    distrib_sub(a.m1, a.m3 * a.m8, a.m6 * a.m5);
    distrib_sub(a.m2, a.m3 * a.m7, a.m6 * a.m4);

    assert(dat == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m7 * a.m5)
               - a.m1 * (a.m3 * a.m8) + a.m1 * (a.m6 * a.m5)
               + a.m2 * (a.m3 * a.m7) - a.m2 * (a.m6 * a.m4));

    // Phase 3: Prove each differing triple-product pair equal
    assert(a.m0 * (a.m7 * a.m5) == a.m0 * (a.m5 * a.m7)) by(nonlinear_arith);
    assert(a.m1 * (a.m3 * a.m8) == a.m3 * (a.m1 * a.m8)) by(nonlinear_arith);
    assert(a.m1 * (a.m6 * a.m5) == a.m6 * (a.m1 * a.m5)) by(nonlinear_arith);
    assert(a.m2 * (a.m3 * a.m7) == a.m3 * (a.m2 * a.m7)) by(nonlinear_arith);
    assert(a.m2 * (a.m6 * a.m4) == a.m6 * (a.m2 * a.m4)) by(nonlinear_arith);

    // Phase 4: Close with nonlinear_arith using expanded forms as axioms
    assert(dat == da) by(nonlinear_arith)
        requires
            da == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m5 * a.m7)
                  - a.m3 * (a.m1 * a.m8) + a.m3 * (a.m2 * a.m7)
                  + a.m6 * (a.m1 * a.m5) - a.m6 * (a.m2 * a.m4),
            dat == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m7 * a.m5)
                   - a.m1 * (a.m3 * a.m8) + a.m1 * (a.m6 * a.m5)
                   + a.m2 * (a.m3 * a.m7) - a.m2 * (a.m6 * a.m4);
}

/// **Theorem 22**: Swapping columns 0 and 1 negates the determinant.
///
/// Proof: expand both determinants into 6 triple products, then show the
/// sign-swapped terms are pairwise equal.
proof fn mat3_det_swap_cols01(a: SpecMat3)
    ensures ({
        let swapped = mat3_new(a.m3, a.m4, a.m5, a.m0, a.m1, a.m2, a.m6, a.m7, a.m8);
        mat3_determinant(swapped) == -mat3_determinant(a)
    }),
{
    let s = mat3_new(a.m3, a.m4, a.m5, a.m0, a.m1, a.m2, a.m6, a.m7, a.m8);

    // Establish swapped field values
    assert(s.m0 == a.m3);
    assert(s.m1 == a.m4);
    assert(s.m2 == a.m5);
    assert(s.m3 == a.m0);
    assert(s.m4 == a.m1);
    assert(s.m5 == a.m2);
    assert(s.m6 == a.m6);
    assert(s.m7 == a.m7);
    assert(s.m8 == a.m8);

    // Expand det(A) cofactors
    distrib_sub(a.m0, a.m4 * a.m8, a.m5 * a.m7);
    distrib_sub(a.m3, a.m1 * a.m8, a.m2 * a.m7);
    distrib_sub(a.m6, a.m1 * a.m5, a.m2 * a.m4);

    // Expand det(swapped) cofactors
    distrib_sub(a.m3, a.m1 * a.m8, a.m2 * a.m7);
    distrib_sub(a.m0, a.m4 * a.m8, a.m5 * a.m7);
    distrib_sub(a.m6, a.m4 * a.m2, a.m5 * a.m1);

    // Triple product commutativity for the third cofactor
    // a.m6*(a.m4*a.m2) vs a.m6*(a.m2*a.m4)
    mul_comm_right(a.m6, a.m4, a.m2);
    // a.m6*(a.m5*a.m1) vs a.m6*(a.m1*a.m5)
    mul_comm_right(a.m6, a.m5, a.m1);
}

/// **Theorem 23**: det(diag(d0,d1,d2)) = d0*d1*d2
proof fn mat3_det_diagonal(d0: int, d1: int, d2: int)
    ensures ({
        let m = mat3_new(d0, 0, 0, 0, d1, 0, 0, 0, d2);
        mat3_determinant(m) == d0 * d1 * d2
    }),
{
    assert(mat3_determinant(mat3_new(d0, 0, 0, 0, d1, 0, 0, 0, d2))
           == d0 * d1 * d2) by(nonlinear_arith);
}

// =============================================================================
// TRANSLATION PROOFS (Theorems 24-28)
// =============================================================================

/// **Theorem 22**: Translation matrix structure.
proof fn mat3_translation_structure(tx: int, ty: int)
    ensures ({
        let t = mat3_translation(tx, ty);
        t.m0 == 1 && t.m1 == 0 && t.m2 == 0 &&
        t.m3 == 0 && t.m4 == 1 && t.m5 == 0 &&
        t.m6 == tx && t.m7 == ty && t.m8 == 1
    }),
{ }

/// **Theorem 23**: det(translate(tx,ty)) = 1
proof fn mat3_det_translation(tx: int, ty: int)
    ensures mat3_determinant(mat3_translation(tx, ty)) == 1,
{
    assert(mat3_determinant(mat3_translation(tx, ty)) == 1) by(nonlinear_arith);
}

/// **Theorem 24**: Translating origin gives offset.
proof fn mat3_translate_origin(tx: int, ty: int)
    ensures ({
        let origin = SpecVec2 { x: 0, y: 0 };
        let result = mat3_transform_point(mat3_translation(tx, ty), origin);
        result.x == tx && result.y == ty
    }),
{ }

/// **Theorem 25**: Translation preserves vectors (w=0).
proof fn mat3_translate_preserves_vectors(tx: int, ty: int, v: SpecVec2)
    ensures ({
        let result = mat3_transform_vector(mat3_translation(tx, ty), v);
        result.x == v.x && result.y == v.y
    }),
{ }

/// **Theorem 26**: Translation composes additively.
proof fn mat3_translation_compose(tx1: int, ty1: int, tx2: int, ty2: int)
    ensures ({
        mat3_mul(mat3_translation(tx2, ty2), mat3_translation(tx1, ty1))
            == mat3_translation(tx1 + tx2, ty1 + ty2)
    }),
{
    assert(mat3_mul(mat3_translation(tx2, ty2), mat3_translation(tx1, ty1))
           == mat3_translation(tx1 + tx2, ty1 + ty2)) by(nonlinear_arith);
}

// =============================================================================
// SCALING PROOFS (Theorems 29-33)
// =============================================================================

/// **Theorem 27**: Scaling matrix structure.
proof fn mat3_scaling_structure(sx: int, sy: int)
    ensures ({
        let s = mat3_scaling(sx, sy);
        s.m0 == sx && s.m1 == 0 && s.m2 == 0 &&
        s.m3 == 0 && s.m4 == sy && s.m5 == 0 &&
        s.m6 == 0 && s.m7 == 0 && s.m8 == 1
    }),
{ }

/// **Theorem 28**: det(scale(sx,sy)) = sx*sy
proof fn mat3_det_scaling(sx: int, sy: int)
    ensures mat3_determinant(mat3_scaling(sx, sy)) == sx * sy,
{
    assert(mat3_determinant(mat3_scaling(sx, sy)) == sx * sy) by(nonlinear_arith);
}

/// **Theorem 29**: scale(1,1) = identity
proof fn mat3_scaling_identity()
    ensures mat3_scaling(1, 1) == mat3_identity(),
{ }

/// **Theorem 30**: Scaling composes multiplicatively.
proof fn mat3_scaling_compose(sx1: int, sy1: int, sx2: int, sy2: int)
    ensures ({
        mat3_mul(mat3_scaling(sx2, sy2), mat3_scaling(sx1, sy1))
            == mat3_scaling(sx1 * sx2, sy1 * sy2)
    }),
{
    assert(mat3_mul(mat3_scaling(sx2, sy2), mat3_scaling(sx1, sy1))
           == mat3_scaling(sx1 * sx2, sy1 * sy2)) by(nonlinear_arith);
}

/// **Theorem 31**: Scaling transforms points correctly.
proof fn mat3_scaling_transforms_point(sx: int, sy: int, p: SpecVec2)
    ensures ({
        mat3_transform_point(mat3_scaling(sx, sy), p)
            == SpecVec2 { x: sx * p.x, y: sy * p.y }
    }),
{
    assert(mat3_transform_point(mat3_scaling(sx, sy), p)
           == SpecVec2 { x: sx * p.x, y: sy * p.y }) by(nonlinear_arith);
}

// =============================================================================
// SHEARING PROOFS (Theorems 34-36)
// =============================================================================

/// **Theorem 32**: Shearing matrix structure.
proof fn mat3_shearing_structure(shx: int, shy: int)
    ensures ({
        let s = mat3_shearing(shx, shy);
        s.m0 == 1 && s.m1 == shy && s.m2 == 0 &&
        s.m3 == shx && s.m4 == 1 && s.m5 == 0 &&
        s.m6 == 0 && s.m7 == 0 && s.m8 == 1
    }),
{ }

/// **Theorem 33**: det(shear(shx,shy)) = 1 - shx*shy
proof fn mat3_det_shearing(shx: int, shy: int)
    ensures mat3_determinant(mat3_shearing(shx, shy)) == 1 - shx * shy,
{
    assert(mat3_determinant(mat3_shearing(shx, shy)) == 1 - shx * shy) by(nonlinear_arith);
}

/// **Theorem 34**: shear(0,0) = identity
proof fn mat3_shearing_zero()
    ensures mat3_shearing(0, 0) == mat3_identity(),
{ }

// =============================================================================
// TRANSFORM PROOFS (Theorems 37-40)
// =============================================================================

/// **Theorem 35**: Identity doesn't change points.
proof fn mat3_identity_transforms_point(p: SpecVec2)
    ensures mat3_transform_point(mat3_identity(), p) == p,
{ }

/// **Theorem 36**: Identity doesn't change vectors.
proof fn mat3_identity_transforms_vector(v: SpecVec2)
    ensures mat3_transform_vector(mat3_identity(), v) == v,
{ }

/// **Theorem 37**: Translation transforms points by adding offset.
proof fn mat3_translation_transforms_point(tx: int, ty: int, p: SpecVec2)
    ensures ({
        let result = mat3_transform_point(mat3_translation(tx, ty), p);
        result.x == p.x + tx && result.y == p.y + ty
    }),
{ }

/// **Theorem 38**: Shearing transforms points correctly.
proof fn mat3_shearing_transforms_point(shx: int, shy: int, p: SpecVec2)
    ensures ({
        mat3_transform_point(mat3_shearing(shx, shy), p)
            == SpecVec2 { x: p.x + shx * p.y, y: shy * p.x + p.y }
    }),
{
    assert(mat3_transform_point(mat3_shearing(shx, shy), p)
           == SpecVec2 { x: p.x + shx * p.y, y: shy * p.x + p.y }) by(nonlinear_arith);
}

fn main() {
    // Verification only
}

}
