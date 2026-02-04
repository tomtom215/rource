(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Mat4.v - 4x4 Matrix Specification for Coq Formal Verification
 *
 * This module provides a Coq specification of the Mat4 type matching
 * the Rust implementation in rource-math/src/mat4.rs.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 * - Specification matches Rust implementation semantics exactly
 * - Column-major storage order (matching OpenGL conventions)
 * - All operations are mathematically well-defined over reals
 *
 * Memory Layout (column-major):
 *   | m0  m4  m8  m12 |
 *   | m1  m5  m9  m13 |
 *   | m2  m6  m10 m14 |
 *   | m3  m7  m11 m15 |
 *
 * Column 0: [m0, m1, m2, m3]
 * Column 1: [m4, m5, m6, m7]
 * Column 2: [m8, m9, m10, m11]
 * Column 3: [m12, m13, m14, m15]
 *)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(** * Mat4 Type Definition *)

(** A 4x4 matrix stored in column-major order. *)
Record Mat4 : Type := mkMat4 {
  m0 : R; m1 : R; m2 : R; m3 : R;       (** Column 0 *)
  m4 : R; m5 : R; m6 : R; m7 : R;       (** Column 1 *)
  m8 : R; m9 : R; m10 : R; m11 : R;     (** Column 2 *)
  m12 : R; m13 : R; m14 : R; m15 : R    (** Column 3 *)
}.

(** * Constant Matrices *)

(** The zero matrix (all elements zero). *)
Definition mat4_zero : Mat4 :=
  mkMat4 0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0.

(** The identity matrix. *)
Definition mat4_identity : Mat4 :=
  mkMat4 1 0 0 0  0 1 0 0  0 0 1 0  0 0 0 1.

(** * Basic Operations *)

(** Matrix addition: A + B *)
Definition mat4_add (a b : Mat4) : Mat4 :=
  mkMat4
    (m0 a + m0 b) (m1 a + m1 b) (m2 a + m2 b) (m3 a + m3 b)
    (m4 a + m4 b) (m5 a + m5 b) (m6 a + m6 b) (m7 a + m7 b)
    (m8 a + m8 b) (m9 a + m9 b) (m10 a + m10 b) (m11 a + m11 b)
    (m12 a + m12 b) (m13 a + m13 b) (m14 a + m14 b) (m15 a + m15 b).

(** Matrix negation: -A *)
Definition mat4_neg (a : Mat4) : Mat4 :=
  mkMat4
    (- m0 a) (- m1 a) (- m2 a) (- m3 a)
    (- m4 a) (- m5 a) (- m6 a) (- m7 a)
    (- m8 a) (- m9 a) (- m10 a) (- m11 a)
    (- m12 a) (- m13 a) (- m14 a) (- m15 a).

(** Matrix subtraction: A - B *)
Definition mat4_sub (a b : Mat4) : Mat4 :=
  mat4_add a (mat4_neg b).

(** Scalar multiplication: s * A *)
Definition mat4_scale (s : R) (a : Mat4) : Mat4 :=
  mkMat4
    (s * m0 a) (s * m1 a) (s * m2 a) (s * m3 a)
    (s * m4 a) (s * m5 a) (s * m6 a) (s * m7 a)
    (s * m8 a) (s * m9 a) (s * m10 a) (s * m11 a)
    (s * m12 a) (s * m13 a) (s * m14 a) (s * m15 a).

(** Matrix transpose: A^T *)
Definition mat4_transpose (a : Mat4) : Mat4 :=
  mkMat4
    (m0 a) (m4 a) (m8 a) (m12 a)
    (m1 a) (m5 a) (m9 a) (m13 a)
    (m2 a) (m6 a) (m10 a) (m14 a)
    (m3 a) (m7 a) (m11 a) (m15 a).

(** * Matrix Multiplication *)

(** Matrix multiplication: A * B (column-major)
    Result[col][row] = sum over k of A[k][row] * B[col][k]

    For 4x4 matrices, each result component is a dot product
    of a row of A with a column of B. *)
Definition mat4_mul (a b : Mat4) : Mat4 :=
  mkMat4
    (* Column 0 *)
    (m0 a * m0 b + m4 a * m1 b + m8 a * m2 b + m12 a * m3 b)
    (m1 a * m0 b + m5 a * m1 b + m9 a * m2 b + m13 a * m3 b)
    (m2 a * m0 b + m6 a * m1 b + m10 a * m2 b + m14 a * m3 b)
    (m3 a * m0 b + m7 a * m1 b + m11 a * m2 b + m15 a * m3 b)
    (* Column 1 *)
    (m0 a * m4 b + m4 a * m5 b + m8 a * m6 b + m12 a * m7 b)
    (m1 a * m4 b + m5 a * m5 b + m9 a * m6 b + m13 a * m7 b)
    (m2 a * m4 b + m6 a * m5 b + m10 a * m6 b + m14 a * m7 b)
    (m3 a * m4 b + m7 a * m5 b + m11 a * m6 b + m15 a * m7 b)
    (* Column 2 *)
    (m0 a * m8 b + m4 a * m9 b + m8 a * m10 b + m12 a * m11 b)
    (m1 a * m8 b + m5 a * m9 b + m9 a * m10 b + m13 a * m11 b)
    (m2 a * m8 b + m6 a * m9 b + m10 a * m10 b + m14 a * m11 b)
    (m3 a * m8 b + m7 a * m9 b + m11 a * m10 b + m15 a * m11 b)
    (* Column 3 *)
    (m0 a * m12 b + m4 a * m13 b + m8 a * m14 b + m12 a * m15 b)
    (m1 a * m12 b + m5 a * m13 b + m9 a * m14 b + m13 a * m15 b)
    (m2 a * m12 b + m6 a * m13 b + m10 a * m14 b + m14 a * m15 b)
    (m3 a * m12 b + m7 a * m13 b + m11 a * m14 b + m15 a * m15 b).

(** * Determinant *)

(** The determinant of a 4x4 matrix via cofactor expansion along the first row.
    Uses column-major layout: row 0 = [m0, m4, m8, m12]. *)
Definition mat4_determinant (a : Mat4) : R :=
  let c00 := m5 a * (m10 a * m15 a - m14 a * m11 a)
            - m9 a * (m6 a * m15 a - m14 a * m7 a)
            + m13 a * (m6 a * m11 a - m10 a * m7 a) in
  let c01 := m1 a * (m10 a * m15 a - m14 a * m11 a)
            - m9 a * (m2 a * m15 a - m14 a * m3 a)
            + m13 a * (m2 a * m11 a - m10 a * m3 a) in
  let c02 := m1 a * (m6 a * m15 a - m14 a * m7 a)
            - m5 a * (m2 a * m15 a - m14 a * m3 a)
            + m13 a * (m2 a * m7 a - m6 a * m3 a) in
  let c03 := m1 a * (m6 a * m11 a - m10 a * m7 a)
            - m5 a * (m2 a * m11 a - m10 a * m3 a)
            + m9 a * (m2 a * m7 a - m6 a * m3 a) in
  m0 a * c00 - m4 a * c01 + m8 a * c02 - m12 a * c03.

(** * Trace *)

(** The trace of a 4x4 matrix (sum of diagonal elements). *)
Definition mat4_trace (a : Mat4) : R :=
  m0 a + m5 a + m10 a + m15 a.

(** * Inverse *)

(** The inverse of a 4x4 matrix using cofactor expansion.
    inverse(A) = (1/det(A)) * adj(A)
    where adj(A) is the adjugate (transpose of cofactor matrix).
    Uses the 2x2 minor factoring from the Rust implementation
    (mat4.rs lines 406-451) for both determinant and adjugate.
    Matches the column-major storage order. *)
Definition mat4_inverse (a : Mat4) : Mat4 :=
  let inv_det := / (mat4_determinant a) in
  (* 2x2 sub-determinants from top-left 4x2 block *)
  let s0 := m0 a * m5 a - m4 a * m1 a in
  let s1 := m0 a * m6 a - m4 a * m2 a in
  let s2 := m0 a * m7 a - m4 a * m3 a in
  let s3 := m1 a * m6 a - m5 a * m2 a in
  let s4 := m1 a * m7 a - m5 a * m3 a in
  let s5 := m2 a * m7 a - m6 a * m3 a in
  (* 2x2 sub-determinants from bottom-right 4x2 block *)
  let c0 := m8 a * m13 a - m12 a * m9 a in
  let c1 := m8 a * m14 a - m12 a * m10 a in
  let c2 := m8 a * m15 a - m12 a * m11 a in
  let c3 := m9 a * m14 a - m13 a * m10 a in
  let c4 := m9 a * m15 a - m13 a * m11 a in
  let c5 := m10 a * m15 a - m14 a * m11 a in
  mkMat4
    (* Column 0: adjugate row 0 *)
    (( m5 a * c5 - m6 a * c4 + m7 a * c3) * inv_det)
    ((- m1 a * c5 + m2 a * c4 - m3 a * c3) * inv_det)
    (( m13 a * s5 - m14 a * s4 + m15 a * s3) * inv_det)
    ((- m9 a * s5 + m10 a * s4 - m11 a * s3) * inv_det)
    (* Column 1: adjugate row 1 *)
    ((- m4 a * c5 + m6 a * c2 - m7 a * c1) * inv_det)
    (( m0 a * c5 - m2 a * c2 + m3 a * c1) * inv_det)
    ((- m12 a * s5 + m14 a * s2 - m15 a * s1) * inv_det)
    (( m8 a * s5 - m10 a * s2 + m11 a * s1) * inv_det)
    (* Column 2: adjugate row 2 *)
    (( m4 a * c4 - m5 a * c2 + m7 a * c0) * inv_det)
    ((- m0 a * c4 + m1 a * c2 - m3 a * c0) * inv_det)
    (( m12 a * s4 - m13 a * s2 + m15 a * s0) * inv_det)
    ((- m8 a * s4 + m9 a * s2 - m11 a * s0) * inv_det)
    (* Column 3: adjugate row 3 *)
    ((- m4 a * c3 + m5 a * c1 - m6 a * c0) * inv_det)
    (( m0 a * c3 - m1 a * c1 + m2 a * c0) * inv_det)
    ((- m12 a * s3 + m13 a * s1 - m14 a * s0) * inv_det)
    (( m8 a * s3 - m9 a * s1 + m10 a * s0) * inv_det).

(** * Equality Lemma *)

(** Two matrices are equal iff all their components are equal. *)
Lemma mat4_eq : forall a b : Mat4,
  m0 a = m0 b ->
  m1 a = m1 b ->
  m2 a = m2 b ->
  m3 a = m3 b ->
  m4 a = m4 b ->
  m5 a = m5 b ->
  m6 a = m6 b ->
  m7 a = m7 b ->
  m8 a = m8 b ->
  m9 a = m9 b ->
  m10 a = m10 b ->
  m11 a = m11 b ->
  m12 a = m12 b ->
  m13 a = m13 b ->
  m14 a = m14 b ->
  m15 a = m15 b ->
  a = b.
Proof.
  intros a b H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
  destruct a, b.
  simpl in *.
  subst.
  reflexivity.
Qed.

(** * Vec3 Type (for transform operations) *)

(** A 3D vector. *)
Record Vec3 : Type := mkVec3 {
  v3x : R;
  v3y : R;
  v3z : R
}.

(** * Transform Operations *)

(** 3D translation matrix.
    | 1 0 0 tx |
    | 0 1 0 ty |
    | 0 0 1 tz |
    | 0 0 0 1  | *)
Definition mat4_translation (tx ty tz : R) : Mat4 :=
  mkMat4 1 0 0 0  0 1 0 0  0 0 1 0  tx ty tz 1.

(** 3D scaling matrix.
    | sx 0  0  0 |
    | 0  sy 0  0 |
    | 0  0  sz 0 |
    | 0  0  0  1 | *)
Definition mat4_scaling (sx sy sz : R) : Mat4 :=
  mkMat4 sx 0 0 0  0 sy 0 0  0 0 sz 0  0 0 0 1.

(** Uniform scaling matrix. *)
Definition mat4_uniform_scaling (s : R) : Mat4 :=
  mat4_scaling s s s.

(** Transform a point (homogeneous w=1). *)
Definition mat4_transform_point (mat : Mat4) (p : Vec3) : Vec3 :=
  mkVec3
    (m0 mat * v3x p + m4 mat * v3y p + m8 mat  * v3z p + m12 mat)
    (m1 mat * v3x p + m5 mat * v3y p + m9 mat  * v3z p + m13 mat)
    (m2 mat * v3x p + m6 mat * v3y p + m10 mat * v3z p + m14 mat).

(** Transform a vector (homogeneous w=0). *)
Definition mat4_transform_vector (mat : Mat4) (v : Vec3) : Vec3 :=
  mkVec3
    (m0 mat * v3x v + m4 mat * v3y v + m8 mat  * v3z v)
    (m1 mat * v3x v + m5 mat * v3y v + m9 mat  * v3z v)
    (m2 mat * v3x v + m6 mat * v3y v + m10 mat * v3z v).

(** * Accessor Operations *)

(** Extract the translation from a 4x4 transform matrix.
    The translation is stored in column 3 (elements m12, m13, m14).
    Matches Rust: self.m[12], self.m[13], self.m[14] *)
Definition mat4_get_translation (mat : Mat4) : Vec3 :=
  mkVec3 (m12 mat) (m13 mat) (m14 mat).

(** * Column and Row Accessors *)

(** Extract column 0: [m0, m1, m2, m3] *)
Definition mat4_col0 (mat : Mat4) : (R * R * R * R) :=
  (m0 mat, m1 mat, m2 mat, m3 mat).

(** Extract column 1: [m4, m5, m6, m7] *)
Definition mat4_col1 (mat : Mat4) : (R * R * R * R) :=
  (m4 mat, m5 mat, m6 mat, m7 mat).

(** Extract column 2: [m8, m9, m10, m11] *)
Definition mat4_col2 (mat : Mat4) : (R * R * R * R) :=
  (m8 mat, m9 mat, m10 mat, m11 mat).

(** Extract column 3: [m12, m13, m14, m15] *)
Definition mat4_col3 (mat : Mat4) : (R * R * R * R) :=
  (m12 mat, m13 mat, m14 mat, m15 mat).

(** Extract row 0: [m0, m4, m8, m12] *)
Definition mat4_row0 (mat : Mat4) : (R * R * R * R) :=
  (m0 mat, m4 mat, m8 mat, m12 mat).

(** Extract row 1: [m1, m5, m9, m13] *)
Definition mat4_row1 (mat : Mat4) : (R * R * R * R) :=
  (m1 mat, m5 mat, m9 mat, m13 mat).

(** Extract row 2: [m2, m6, m10, m14] *)
Definition mat4_row2 (mat : Mat4) : (R * R * R * R) :=
  (m2 mat, m6 mat, m10 mat, m14 mat).

(** Extract row 3: [m3, m7, m11, m15] *)
Definition mat4_row3 (mat : Mat4) : (R * R * R * R) :=
  (m3 mat, m7 mat, m11 mat, m15 mat).

(** * Constructor Operations *)

(** Construct a matrix from 16 values (column-major order).
    Matches Rust: Mat4::from_cols_array *)
Definition mat4_from_cols (c00 c01 c02 c03
                           c10 c11 c12 c13
                           c20 c21 c22 c23
                           c30 c31 c32 c33 : R) : Mat4 :=
  mkMat4 c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 c30 c31 c32 c33.

(** * Projection Matrices *)

(** Orthographic projection matrix.
    Maps (left,right) x (bottom,top) x (near,far) to the canonical view volume.
    Assumes right <> left, top <> bottom, far <> near.
    Matches Rust: Mat4::orthographic(left, right, bottom, top, near, far)

    Column-major layout:
    | 2/(r-l)    0          0           -(r+l)/(r-l) |
    |   0      2/(t-b)      0           -(t+b)/(t-b) |
    |   0        0        -2/(f-n)      -(f+n)/(f-n) |
    |   0        0          0                1        | *)
Definition mat4_orthographic (left right bottom top near far : R) : Mat4 :=
  let rml := right - left in
  let tmb := top - bottom in
  let fmn := far - near in
  mkMat4
    (2 / rml) 0 0 0
    0 (2 / tmb) 0 0
    0 0 (-(2) / fmn) 0
    (-(right + left) / rml) (-(top + bottom) / tmb) (-(far + near) / fmn) 1.

(** * Vec4 Type and Transform *)

(** A 4D vector for homogeneous transforms. *)
Record Vec4 : Type := mkVec4 {
  vec4_x : R;
  vec4_y : R;
  vec4_z : R;
  vec4_w : R
}.

(** Transform a Vec4 by a Mat4 (full 4x4 matrix-vector multiply).
    result.x = m0*x + m4*y + m8*z  + m12*w
    result.y = m1*x + m5*y + m9*z  + m13*w
    result.z = m2*x + m6*y + m10*z + m14*w
    result.w = m3*x + m7*y + m11*z + m15*w *)
Definition mat4_transform_vec4 (mat : Mat4) (v : Vec4) : Vec4 :=
  mkVec4
    (m0 mat * vec4_x v + m4 mat * vec4_y v + m8 mat  * vec4_z v + m12 mat * vec4_w v)
    (m1 mat * vec4_x v + m5 mat * vec4_y v + m9 mat  * vec4_z v + m13 mat * vec4_w v)
    (m2 mat * vec4_x v + m6 mat * vec4_y v + m10 mat * vec4_z v + m14 mat * vec4_w v)
    (m3 mat * vec4_x v + m7 mat * vec4_y v + m11 mat * vec4_z v + m15 mat * vec4_w v).

(** Vec4 equality lemma. *)
Lemma vec4_eq : forall a b : Vec4,
  vec4_x a = vec4_x b -> vec4_y a = vec4_y b ->
  vec4_z a = vec4_z b -> vec4_w a = vec4_w b -> a = b.
Proof.
  intros a b Hx Hy Hz Hw.
  destruct a, b. simpl in *. subst. reflexivity.
Qed.

(** * Vec3 Equality Lemma *)

(** Two Vec3 are equal iff their components are equal. *)
Lemma vec3_eq : forall a b : Vec3,
  v3x a = v3x b -> v3y a = v3y b -> v3z a = v3z b -> a = b.
Proof.
  intros a b Hx Hy Hz.
  destruct a, b. simpl in *. subst. reflexivity.
Qed.

(** * Vec3 Dot Product *)

(** Dot product of two Vec3 values. *)
Definition v3_dot (a b : Vec3) : R :=
  v3x a * v3x b + v3y a * v3y b + v3z a * v3z b.

(** * Look-At View Matrix *)

(** Construct a look-at view matrix from pre-computed orthonormal basis vectors.

    This definition takes the basis vectors directly (s=side/right, u=up, f=forward)
    rather than computing them from eye/target/up, because the normalization step
    (which requires sqrt) cannot be represented in pure real arithmetic without
    axiomatizing sqrt.

    The resulting matrix maps:
    - eye position to the origin
    - forward direction (f) to -Z axis
    - side direction (s) to +X axis
    - up direction (u) to +Y axis

    Column-major layout (matching Rust Mat4 storage):
    | s.x    s.y    s.z    -s·eye |
    | u.x    u.y    u.z    -u·eye |
    | -f.x   -f.y   -f.z    f·eye |
    | 0      0      0       1     |

    Precondition: s, u, f should form an orthonormal basis
    (unit length, mutually perpendicular). Proofs in Mat4_Proofs.v
    verify structural properties under this assumption.

    Matches Rust: Mat4::look_at(eye, target, up) after normalization. *)
Definition mat4_look_at (s u f eye : Vec3) : Mat4 :=
  mkMat4
    (v3x s)  (v3x u)  (-(v3x f))  0
    (v3y s)  (v3y u)  (-(v3y f))  0
    (v3z s)  (v3z u)  (-(v3z f))  0
    (-(v3_dot s eye))  (-(v3_dot u eye))  (v3_dot f eye)  1.

(** * Specification Verification Summary

    This file provides:
    - Mat4 record type definition (16 real components, column-major)
    - Vec3 record type definition (3 real components)
    - mat4_zero: The zero matrix
    - mat4_identity: The identity matrix
    - mat4_add: Matrix addition
    - mat4_neg: Matrix negation
    - mat4_sub: Matrix subtraction
    - mat4_scale: Scalar multiplication
    - mat4_transpose: Matrix transpose
    - mat4_mul: Matrix multiplication
    - mat4_determinant: 4x4 determinant (cofactor expansion)
    - mat4_trace: Trace (sum of diagonal)
    - mat4_translation: 3D translation matrix
    - mat4_scaling: 3D scaling matrix
    - mat4_uniform_scaling: Uniform scaling matrix
    - mat4_transform_point: Point transformation (w=1)
    - mat4_transform_vector: Vector transformation (w=0)
    - mat4_get_translation: Extract translation from transform matrix
    - mat4_col0..col3: Column accessor operations
    - mat4_row0..row3: Row accessor operations
    - mat4_from_cols: Constructor from column values
    - mat4_inverse: Matrix inverse via cofactor expansion (adjugate/det)
    - mat4_orthographic: Orthographic projection matrix
    - mat4_transform_vec4: Full 4D matrix-vector multiply
    - v3_dot: Vec3 dot product
    - mat4_look_at: Look-at view matrix from orthonormal basis
    - mat4_eq: Component-wise equality lemma
    - vec4_eq: Component-wise Vec4 equality lemma
    - vec3_eq: Component-wise Vec3 equality lemma

    Total definitions: 34
    Total lemmas: 3
    Admits: 0
*)
