// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Mat4 Extended Operations
//!
//! This module contains machine-checked proofs for Mat4 translation, scaling,
//! uniform scaling, transform_point, transform_vector, determinant properties,
//! and trace properties.
//!
//! Separated from mat4_proofs.rs because combining the multiplication
//! associativity proof (300+ lemma calls) with nonlinear_arith proofs
//! exceeds Z3's resource limits in a single verification run.
//!
//! ## Properties Verified
//!
//! - Translation Properties (Theorems 19-25)
//! - Scaling Properties (Theorems 26-32)
//! - Transform Properties (Theorems 33-38)
//! - Determinant Properties (Theorems 39-46)
//! - Trace Properties (Theorems 47-50)
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/mat4_extended_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Specification Types (duplicated for independent verification)
// =============================================================================

#[derive(PartialEq, Eq)]
pub struct SpecMat4 {
    pub m0: int, pub m1: int, pub m2: int, pub m3: int,     // Column 0
    pub m4: int, pub m5: int, pub m6: int, pub m7: int,     // Column 1
    pub m8: int, pub m9: int, pub m10: int, pub m11: int,   // Column 2
    pub m12: int, pub m13: int, pub m14: int, pub m15: int, // Column 3
}

#[derive(PartialEq, Eq)]
pub struct SpecVec3 {
    pub x: int,
    pub y: int,
    pub z: int,
}

#[derive(PartialEq, Eq)]
pub struct SpecVec4 {
    pub x: int,
    pub y: int,
    pub z: int,
    pub w: int,
}

// =============================================================================
// Spec Functions
// =============================================================================

pub open spec fn mat4_zero() -> SpecMat4 {
    SpecMat4 {
        m0: 0, m1: 0, m2: 0, m3: 0,
        m4: 0, m5: 0, m6: 0, m7: 0,
        m8: 0, m9: 0, m10: 0, m11: 0,
        m12: 0, m13: 0, m14: 0, m15: 0,
    }
}

pub open spec fn mat4_identity() -> SpecMat4 {
    SpecMat4 {
        m0: 1, m1: 0, m2: 0, m3: 0,
        m4: 0, m5: 1, m6: 0, m7: 0,
        m8: 0, m9: 0, m10: 1, m11: 0,
        m12: 0, m13: 0, m14: 0, m15: 1,
    }
}

pub open spec fn mat4_translation(tx: int, ty: int, tz: int) -> SpecMat4 {
    SpecMat4 {
        m0: 1, m1: 0, m2: 0, m3: 0,
        m4: 0, m5: 1, m6: 0, m7: 0,
        m8: 0, m9: 0, m10: 1, m11: 0,
        m12: tx, m13: ty, m14: tz, m15: 1,
    }
}

pub open spec fn mat4_scaling(sx: int, sy: int, sz: int) -> SpecMat4 {
    SpecMat4 {
        m0: sx, m1: 0, m2: 0, m3: 0,
        m4: 0, m5: sy, m6: 0, m7: 0,
        m8: 0, m9: 0, m10: sz, m11: 0,
        m12: 0, m13: 0, m14: 0, m15: 1,
    }
}

pub open spec fn mat4_uniform_scaling(s: int) -> SpecMat4 {
    mat4_scaling(s, s, s)
}

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

pub open spec fn mat4_transpose(a: SpecMat4) -> SpecMat4 {
    SpecMat4 {
        m0: a.m0, m1: a.m4, m2: a.m8, m3: a.m12,
        m4: a.m1, m5: a.m5, m6: a.m9, m7: a.m13,
        m8: a.m2, m9: a.m6, m10: a.m10, m11: a.m14,
        m12: a.m3, m13: a.m7, m14: a.m11, m15: a.m15,
    }
}

/// Mat4 determinant via Laplace expansion along first two columns.
/// det = s0*c5 - s1*c4 + s2*c3 + s3*c2 - s4*c1 + s5*c0
/// where s_i are 2x2 minors from columns 0-1, c_i from columns 2-3.
pub open spec fn mat4_determinant(a: SpecMat4) -> int {
    let s0 = a.m0 * a.m5 - a.m4 * a.m1;
    let s1 = a.m0 * a.m6 - a.m4 * a.m2;
    let s2 = a.m0 * a.m7 - a.m4 * a.m3;
    let s3 = a.m1 * a.m6 - a.m5 * a.m2;
    let s4 = a.m1 * a.m7 - a.m5 * a.m3;
    let s5 = a.m2 * a.m7 - a.m6 * a.m3;

    let c5 = a.m10 * a.m15 - a.m14 * a.m11;
    let c4 = a.m9 * a.m15 - a.m13 * a.m11;
    let c3 = a.m9 * a.m14 - a.m13 * a.m10;
    let c2 = a.m8 * a.m15 - a.m12 * a.m11;
    let c1 = a.m8 * a.m14 - a.m12 * a.m10;
    let c0 = a.m8 * a.m13 - a.m12 * a.m9;

    s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0
}

/// Trace: sum of diagonal elements.
pub open spec fn mat4_trace(a: SpecMat4) -> int {
    a.m0 + a.m5 + a.m10 + a.m15
}

/// Transform a point (w=1) by a matrix. For affine matrices (m3=m7=m11=0, m15=1),
/// no perspective division needed.
pub open spec fn mat4_transform_point_affine(m: SpecMat4, p: SpecVec3) -> SpecVec3 {
    SpecVec3 {
        x: m.m0 * p.x + m.m4 * p.y + m.m8 * p.z + m.m12,
        y: m.m1 * p.x + m.m5 * p.y + m.m9 * p.z + m.m13,
        z: m.m2 * p.x + m.m6 * p.y + m.m10 * p.z + m.m14,
    }
}

/// Transform a vector (w=0) by a matrix.
pub open spec fn mat4_transform_vector(m: SpecMat4, v: SpecVec3) -> SpecVec3 {
    SpecVec3 {
        x: m.m0 * v.x + m.m4 * v.y + m.m8 * v.z,
        y: m.m1 * v.x + m.m5 * v.y + m.m9 * v.z,
        z: m.m2 * v.x + m.m6 * v.y + m.m10 * v.z,
    }
}

/// Transform a Vec4 by a matrix.
pub open spec fn mat4_transform_vec4(m: SpecMat4, v: SpecVec4) -> SpecVec4 {
    SpecVec4 {
        x: m.m0 * v.x + m.m4 * v.y + m.m8 * v.z + m.m12 * v.w,
        y: m.m1 * v.x + m.m5 * v.y + m.m9 * v.z + m.m13 * v.w,
        z: m.m2 * v.x + m.m6 * v.y + m.m10 * v.z + m.m14 * v.w,
        w: m.m3 * v.x + m.m7 * v.y + m.m11 * v.z + m.m15 * v.w,
    }
}

/// Get translation component from a matrix.
pub open spec fn mat4_get_translation(m: SpecMat4) -> SpecVec3 {
    SpecVec3 { x: m.m12, y: m.m13, z: m.m14 }
}

// =============================================================================
// TRANSLATION PROOFS (Theorems 19-25)
// =============================================================================

/// **Theorem 19**: Translation matrix structure.
proof fn mat4_translation_structure(tx: int, ty: int, tz: int)
    ensures ({
        let t = mat4_translation(tx, ty, tz);
        t.m0 == 1 && t.m1 == 0 && t.m2 == 0 && t.m3 == 0 &&
        t.m4 == 0 && t.m5 == 1 && t.m6 == 0 && t.m7 == 0 &&
        t.m8 == 0 && t.m9 == 0 && t.m10 == 1 && t.m11 == 0 &&
        t.m12 == tx && t.m13 == ty && t.m14 == tz && t.m15 == 1
    }),
{ }

/// **Theorem 20**: det(translate(tx,ty,tz)) = 1.
proof fn mat4_det_translation(tx: int, ty: int, tz: int)
    ensures mat4_determinant(mat4_translation(tx, ty, tz)) == 1,
{
    assert(mat4_determinant(mat4_translation(tx, ty, tz)) == 1) by(nonlinear_arith);
}

/// **Theorem 21**: Translating the origin gives the offset vector.
proof fn mat4_translate_origin(tx: int, ty: int, tz: int)
    ensures ({
        let origin = SpecVec3 { x: 0, y: 0, z: 0 };
        let result = mat4_transform_point_affine(mat4_translation(tx, ty, tz), origin);
        result.x == tx && result.y == ty && result.z == tz
    }),
{ }

/// **Theorem 22**: Translation preserves vectors (w=0).
proof fn mat4_translate_preserves_vectors(tx: int, ty: int, tz: int, v: SpecVec3)
    ensures ({
        let result = mat4_transform_vector(mat4_translation(tx, ty, tz), v);
        result.x == v.x && result.y == v.y && result.z == v.z
    }),
{ }

/// **Theorem 23**: Translation composes additively.
proof fn mat4_translation_compose(tx1: int, ty1: int, tz1: int, tx2: int, ty2: int, tz2: int)
    ensures ({
        mat4_mul(mat4_translation(tx2, ty2, tz2), mat4_translation(tx1, ty1, tz1))
            == mat4_translation(tx1 + tx2, ty1 + ty2, tz1 + tz2)
    }),
{
    assert(mat4_mul(mat4_translation(tx2, ty2, tz2), mat4_translation(tx1, ty1, tz1))
           == mat4_translation(tx1 + tx2, ty1 + ty2, tz1 + tz2)) by(nonlinear_arith);
}

/// **Theorem 24**: Translation of (0,0,0) is identity.
proof fn mat4_translation_zero_is_identity()
    ensures mat4_translation(0, 0, 0) == mat4_identity(),
{ }

/// **Theorem 25**: get_translation recovers translation components.
proof fn mat4_get_translation_correct(tx: int, ty: int, tz: int)
    ensures ({
        let t = mat4_get_translation(mat4_translation(tx, ty, tz));
        t.x == tx && t.y == ty && t.z == tz
    }),
{ }

// =============================================================================
// SCALING PROOFS (Theorems 26-32)
// =============================================================================

/// **Theorem 26**: Scaling matrix structure.
proof fn mat4_scaling_structure(sx: int, sy: int, sz: int)
    ensures ({
        let s = mat4_scaling(sx, sy, sz);
        s.m0 == sx && s.m1 == 0 && s.m2 == 0 && s.m3 == 0 &&
        s.m4 == 0 && s.m5 == sy && s.m6 == 0 && s.m7 == 0 &&
        s.m8 == 0 && s.m9 == 0 && s.m10 == sz && s.m11 == 0 &&
        s.m12 == 0 && s.m13 == 0 && s.m14 == 0 && s.m15 == 1
    }),
{ }

/// **Theorem 27**: det(scale(sx,sy,sz)) = sx*sy*sz.
proof fn mat4_det_scaling(sx: int, sy: int, sz: int)
    ensures mat4_determinant(mat4_scaling(sx, sy, sz)) == sx * sy * sz,
{
    assert(mat4_determinant(mat4_scaling(sx, sy, sz)) == sx * sy * sz) by(nonlinear_arith);
}

/// **Theorem 28**: scale(1,1,1) = identity.
proof fn mat4_scaling_identity()
    ensures mat4_scaling(1, 1, 1) == mat4_identity(),
{ }

/// **Theorem 29**: Scaling composes multiplicatively.
proof fn mat4_scaling_compose(sx1: int, sy1: int, sz1: int, sx2: int, sy2: int, sz2: int)
    ensures ({
        mat4_mul(mat4_scaling(sx2, sy2, sz2), mat4_scaling(sx1, sy1, sz1))
            == mat4_scaling(sx1 * sx2, sy1 * sy2, sz1 * sz2)
    }),
{
    assert(mat4_mul(mat4_scaling(sx2, sy2, sz2), mat4_scaling(sx1, sy1, sz1))
           == mat4_scaling(sx1 * sx2, sy1 * sy2, sz1 * sz2)) by(nonlinear_arith);
}

/// **Theorem 30**: Scaling transforms points correctly.
proof fn mat4_scaling_transforms_point(sx: int, sy: int, sz: int, p: SpecVec3)
    ensures ({
        mat4_transform_point_affine(mat4_scaling(sx, sy, sz), p)
            == SpecVec3 { x: sx * p.x, y: sy * p.y, z: sz * p.z }
    }),
{
    assert(mat4_transform_point_affine(mat4_scaling(sx, sy, sz), p)
           == SpecVec3 { x: sx * p.x, y: sy * p.y, z: sz * p.z }) by(nonlinear_arith);
}

/// **Theorem 31**: Uniform scaling is a special case of scaling.
proof fn mat4_uniform_scaling_is_scaling(s: int)
    ensures mat4_uniform_scaling(s) == mat4_scaling(s, s, s),
{ }

/// **Theorem 32**: det(uniform_scale(s)) = s^3.
proof fn mat4_det_uniform_scaling(s: int)
    ensures mat4_determinant(mat4_uniform_scaling(s)) == s * s * s,
{
    assert(mat4_determinant(mat4_uniform_scaling(s)) == s * s * s) by(nonlinear_arith);
}

// =============================================================================
// TRANSFORM PROOFS (Theorems 33-38)
// =============================================================================

/// **Theorem 33**: Identity doesn't change points.
proof fn mat4_identity_transforms_point(p: SpecVec3)
    ensures mat4_transform_point_affine(mat4_identity(), p) == p,
{ }

/// **Theorem 34**: Identity doesn't change vectors.
proof fn mat4_identity_transforms_vector(v: SpecVec3)
    ensures mat4_transform_vector(mat4_identity(), v) == v,
{ }

/// **Theorem 35**: Translation transforms points by adding offset.
proof fn mat4_translation_transforms_point(tx: int, ty: int, tz: int, p: SpecVec3)
    ensures ({
        let result = mat4_transform_point_affine(mat4_translation(tx, ty, tz), p);
        result.x == p.x + tx && result.y == p.y + ty && result.z == p.z + tz
    }),
{ }

/// **Theorem 36**: Scaling transforms vectors correctly.
proof fn mat4_scaling_transforms_vector(sx: int, sy: int, sz: int, v: SpecVec3)
    ensures ({
        mat4_transform_vector(mat4_scaling(sx, sy, sz), v)
            == SpecVec3 { x: sx * v.x, y: sy * v.y, z: sz * v.z }
    }),
{
    assert(mat4_transform_vector(mat4_scaling(sx, sy, sz), v)
           == SpecVec3 { x: sx * v.x, y: sy * v.y, z: sz * v.z }) by(nonlinear_arith);
}

/// **Theorem 37**: Identity transforms Vec4 correctly.
proof fn mat4_identity_transforms_vec4(v: SpecVec4)
    ensures mat4_transform_vec4(mat4_identity(), v) == v,
{ }

/// **Theorem 38**: Zero matrix maps all points to origin.
proof fn mat4_zero_transforms_to_origin(p: SpecVec3)
    ensures ({
        let result = mat4_transform_point_affine(mat4_zero(), p);
        result.x == 0 && result.y == 0 && result.z == 0
    }),
{ }

// =============================================================================
// DETERMINANT PROOFS (Theorems 39-46)
// =============================================================================

/// **Theorem 39**: det(I) = 1.
proof fn mat4_det_identity()
    ensures mat4_determinant(mat4_identity()) == 1,
{
    assert(mat4_determinant(mat4_identity()) == 1) by(nonlinear_arith);
}

/// **Theorem 40**: det(0) = 0.
proof fn mat4_det_zero()
    ensures mat4_determinant(mat4_zero()) == 0,
{ }

/// **Theorem 41**: det(diag(d0,d1,d2,d3)) = d0*d1*d2*d3.
proof fn mat4_det_diagonal(d0: int, d1: int, d2: int, d3: int)
    ensures ({
        let m = SpecMat4 {
            m0: d0, m1: 0, m2: 0, m3: 0,
            m4: 0, m5: d1, m6: 0, m7: 0,
            m8: 0, m9: 0, m10: d2, m11: 0,
            m12: 0, m13: 0, m14: 0, m15: d3,
        };
        mat4_determinant(m) == d0 * d1 * d2 * d3
    }),
{
    let m = SpecMat4 {
        m0: d0, m1: 0, m2: 0, m3: 0,
        m4: 0, m5: d1, m6: 0, m7: 0,
        m8: 0, m9: 0, m10: d2, m11: 0,
        m12: 0, m13: 0, m14: 0, m15: d3,
    };
    // Phase 1: Expand 2x2 minors (outer Z3 expands spec function)
    let s0 = m.m0 * m.m5 - m.m4 * m.m1;  // d0*d1
    let c5 = m.m10 * m.m15 - m.m14 * m.m11;  // d2*d3
    // Phase 2: Assert minor values (outer Z3 verifies)
    assert(s0 == d0 * d1);
    assert(c5 == d2 * d3);
    // Phase 3: Nonlinear step - (d0*d1)*(d2*d3) = d0*d1*d2*d3
    assert(s0 * c5 == d0 * d1 * d2 * d3) by(nonlinear_arith)
        requires s0 == d0 * d1, c5 == d2 * d3;
}

/// **Theorem 42**: det(-A) = det(A) for 4x4 matrices.
/// (Since (-1)^4 = 1, negating all entries preserves the determinant.)
proof fn mat4_det_neg(a: SpecMat4)
    ensures ({
        let neg_a = SpecMat4 {
            m0: -a.m0, m1: -a.m1, m2: -a.m2, m3: -a.m3,
            m4: -a.m4, m5: -a.m5, m6: -a.m6, m7: -a.m7,
            m8: -a.m8, m9: -a.m9, m10: -a.m10, m11: -a.m11,
            m12: -a.m12, m13: -a.m13, m14: -a.m14, m15: -a.m15,
        };
        mat4_determinant(neg_a) == mat4_determinant(a)
    }),
{
    let neg_a = SpecMat4 {
        m0: -a.m0, m1: -a.m1, m2: -a.m2, m3: -a.m3,
        m4: -a.m4, m5: -a.m5, m6: -a.m6, m7: -a.m7,
        m8: -a.m8, m9: -a.m9, m10: -a.m10, m11: -a.m11,
        m12: -a.m12, m13: -a.m13, m14: -a.m14, m15: -a.m15,
    };
    // Each 2x2 minor s_i from neg_a picks up (-1)(-1)=1 factor.
    // Each 2x2 minor c_i also picks up (-1)(-1)=1 factor.
    // So s_i(neg_a) = s_i(a) and c_i(neg_a) = c_i(a).
    // det(neg_a) = same linear combination = det(a).
    assert((-a.m0) * (-a.m5) - (-a.m4) * (-a.m1) == a.m0 * a.m5 - a.m4 * a.m1) by(nonlinear_arith);
    assert((-a.m0) * (-a.m6) - (-a.m4) * (-a.m2) == a.m0 * a.m6 - a.m4 * a.m2) by(nonlinear_arith);
    assert((-a.m0) * (-a.m7) - (-a.m4) * (-a.m3) == a.m0 * a.m7 - a.m4 * a.m3) by(nonlinear_arith);
    assert((-a.m1) * (-a.m6) - (-a.m5) * (-a.m2) == a.m1 * a.m6 - a.m5 * a.m2) by(nonlinear_arith);
    assert((-a.m1) * (-a.m7) - (-a.m5) * (-a.m3) == a.m1 * a.m7 - a.m5 * a.m3) by(nonlinear_arith);
    assert((-a.m2) * (-a.m7) - (-a.m6) * (-a.m3) == a.m2 * a.m7 - a.m6 * a.m3) by(nonlinear_arith);
    assert((-a.m10) * (-a.m15) - (-a.m14) * (-a.m11) == a.m10 * a.m15 - a.m14 * a.m11) by(nonlinear_arith);
    assert((-a.m9) * (-a.m15) - (-a.m13) * (-a.m11) == a.m9 * a.m15 - a.m13 * a.m11) by(nonlinear_arith);
    assert((-a.m9) * (-a.m14) - (-a.m13) * (-a.m10) == a.m9 * a.m14 - a.m13 * a.m10) by(nonlinear_arith);
    assert((-a.m8) * (-a.m15) - (-a.m12) * (-a.m11) == a.m8 * a.m15 - a.m12 * a.m11) by(nonlinear_arith);
    assert((-a.m8) * (-a.m14) - (-a.m12) * (-a.m10) == a.m8 * a.m14 - a.m12 * a.m10) by(nonlinear_arith);
    assert((-a.m8) * (-a.m13) - (-a.m12) * (-a.m9) == a.m8 * a.m13 - a.m12 * a.m9) by(nonlinear_arith);
}

/// **Theorem 43**: Trace of identity is 4.
proof fn mat4_trace_identity()
    ensures mat4_trace(mat4_identity()) == 4,
{ }

/// **Theorem 44**: Trace of zero is 0.
proof fn mat4_trace_zero()
    ensures mat4_trace(mat4_zero()) == 0,
{ }

/// **Theorem 45**: Trace is additive: tr(A+B) = tr(A) + tr(B).
proof fn mat4_trace_additive(a: SpecMat4, b: SpecMat4)
    ensures ({
        let sum = SpecMat4 {
            m0: a.m0 + b.m0, m1: a.m1 + b.m1, m2: a.m2 + b.m2, m3: a.m3 + b.m3,
            m4: a.m4 + b.m4, m5: a.m5 + b.m5, m6: a.m6 + b.m6, m7: a.m7 + b.m7,
            m8: a.m8 + b.m8, m9: a.m9 + b.m9, m10: a.m10 + b.m10, m11: a.m11 + b.m11,
            m12: a.m12 + b.m12, m13: a.m13 + b.m13, m14: a.m14 + b.m14, m15: a.m15 + b.m15,
        };
        mat4_trace(sum) == mat4_trace(a) + mat4_trace(b)
    }),
{ }

/// **Theorem 46**: Trace of scaling matrix is sx+sy+sz+1.
proof fn mat4_trace_scaling(sx: int, sy: int, sz: int)
    ensures mat4_trace(mat4_scaling(sx, sy, sz)) == sx + sy + sz + 1,
{ }

/// **Theorem 47**: Trace of transpose: tr(A^T) = tr(A).
proof fn mat4_trace_transpose(a: SpecMat4)
    ensures mat4_trace(mat4_transpose(a)) == mat4_trace(a),
{ }

/// **Theorem 48**: Trace of translation: tr(T) = 4.
proof fn mat4_trace_translation(tx: int, ty: int, tz: int)
    ensures mat4_trace(mat4_translation(tx, ty, tz)) == 4,
{ }

/// **Theorem 49**: from_translation get_translation roundtrip.
proof fn mat4_from_translation_roundtrip(tx: int, ty: int, tz: int)
    ensures ({
        let t = mat4_translation(tx, ty, tz);
        let got = mat4_get_translation(t);
        got.x == tx && got.y == ty && got.z == tz
    }),
{ }

/// **Theorem 50**: Translation and scaling commute in determinant.
/// det(T * S) = det(S) = sx*sy*sz, since det(T) = 1.
proof fn mat4_det_translation_scaling(
    tx: int, ty: int, tz: int,
    sx: int, sy: int, sz: int,
)
    ensures ({
        let ts = mat4_mul(mat4_translation(tx, ty, tz), mat4_scaling(sx, sy, sz));
        mat4_determinant(ts) == sx * sy * sz
    }),
{
    let t = mat4_translation(tx, ty, tz);
    let s = mat4_scaling(sx, sy, sz);
    let ts = mat4_mul(t, s);
    // Phase 1: Assert T*S element values (outer Z3 expands mat4_mul)
    assert(ts.m0 == sx);
    assert(ts.m1 == 0int);
    assert(ts.m2 == 0int);
    assert(ts.m3 == 0int);
    assert(ts.m4 == 0int);
    assert(ts.m5 == sy);
    assert(ts.m6 == 0int);
    assert(ts.m7 == 0int);
    assert(ts.m8 == 0int);
    assert(ts.m9 == 0int);
    assert(ts.m10 == sz);
    assert(ts.m11 == 0int);
    assert(ts.m15 == 1int);
    // Phase 2: Expand all 12 minors (matching the spec function)
    let s0 = ts.m0 * ts.m5 - ts.m4 * ts.m1;
    let s1 = ts.m0 * ts.m6 - ts.m4 * ts.m2;
    let s2 = ts.m0 * ts.m7 - ts.m4 * ts.m3;
    let s3 = ts.m1 * ts.m6 - ts.m5 * ts.m2;
    let s4 = ts.m1 * ts.m7 - ts.m5 * ts.m3;
    let s5 = ts.m2 * ts.m7 - ts.m6 * ts.m3;
    let c5 = ts.m10 * ts.m15 - ts.m14 * ts.m11;
    let c4 = ts.m9 * ts.m15 - ts.m13 * ts.m11;
    let c3 = ts.m9 * ts.m14 - ts.m13 * ts.m10;
    let c2 = ts.m8 * ts.m15 - ts.m12 * ts.m11;
    let c1 = ts.m8 * ts.m14 - ts.m12 * ts.m10;
    let c0 = ts.m8 * ts.m13 - ts.m12 * ts.m9;
    // Phase 3: Assert minor values
    assert(s0 == sx * sy);
    assert(s1 == 0int);
    assert(s2 == 0int);
    assert(s3 == 0int);
    assert(s4 == 0int);
    assert(s5 == 0int);
    assert(c5 == sz);
    // Phase 4: det formula = s0*c5 - s1*c4 + s2*c3 + s3*c2 - s4*c1 + s5*c0
    // = sx*sy*sz - 0 + 0 + 0 - 0 + 0 = sx*sy*sz
    assert(s0 * c5 == sx * sy * sz) by(nonlinear_arith)
        requires s0 == sx * sy, c5 == sz;
}

fn main() {
    // Verification only
}

}
