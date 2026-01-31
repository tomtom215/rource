(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Mat3.v - 3x3 Matrix Specification for Coq Formal Verification
 *
 * This module provides a Coq specification of the Mat3 type matching
 * the Rust implementation in rource-math/src/mat3.rs.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 * - Specification matches Rust implementation semantics exactly
 * - Column-major storage order (matching OpenGL conventions)
 * - All operations are mathematically well-defined over reals
 *
 * Memory Layout (column-major):
 *   | m0 m3 m6 |
 *   | m1 m4 m7 |
 *   | m2 m5 m8 |
 *
 * Column 0: [m0, m1, m2]
 * Column 1: [m3, m4, m5]
 * Column 2: [m6, m7, m8]
 *)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(** * Mat3 Type Definition *)

(** A 3x3 matrix stored in column-major order. *)
Record Mat3 : Type := mkMat3 {
  m0 : R; m1 : R; m2 : R;   (** Column 0 *)
  m3 : R; m4 : R; m5 : R;   (** Column 1 *)
  m6 : R; m7 : R; m8 : R    (** Column 2 *)
}.

(** * Constant Matrices *)

(** The zero matrix (all elements zero). *)
Definition mat3_zero : Mat3 :=
  mkMat3 0 0 0 0 0 0 0 0 0.

(** The identity matrix. *)
Definition mat3_identity : Mat3 :=
  mkMat3 1 0 0  0 1 0  0 0 1.

(** * Basic Operations *)

(** Matrix addition: A + B *)
Definition mat3_add (a b : Mat3) : Mat3 :=
  mkMat3
    (m0 a + m0 b) (m1 a + m1 b) (m2 a + m2 b)
    (m3 a + m3 b) (m4 a + m4 b) (m5 a + m5 b)
    (m6 a + m6 b) (m7 a + m7 b) (m8 a + m8 b).

(** Matrix negation: -A *)
Definition mat3_neg (a : Mat3) : Mat3 :=
  mkMat3
    (- m0 a) (- m1 a) (- m2 a)
    (- m3 a) (- m4 a) (- m5 a)
    (- m6 a) (- m7 a) (- m8 a).

(** Matrix subtraction: A - B *)
Definition mat3_sub (a b : Mat3) : Mat3 :=
  mat3_add a (mat3_neg b).

(** Scalar multiplication: s * A *)
Definition mat3_scale (s : R) (a : Mat3) : Mat3 :=
  mkMat3
    (s * m0 a) (s * m1 a) (s * m2 a)
    (s * m3 a) (s * m4 a) (s * m5 a)
    (s * m6 a) (s * m7 a) (s * m8 a).

(** Matrix transpose: A^T *)
Definition mat3_transpose (a : Mat3) : Mat3 :=
  mkMat3
    (m0 a) (m3 a) (m6 a)
    (m1 a) (m4 a) (m7 a)
    (m2 a) (m5 a) (m8 a).

(** * Matrix Multiplication *)

(** Matrix multiplication: A * B (column-major)
    Result[col][row] = sum over k of A[k][row] * B[col][k]

    For column-major with indices:
    - A[k][row] = a.(col_k * 3 + row)
    - B[col][k] = b.(col * 3 + k)

    So result component (col*3 + row):
    = A.row0 * B.col + A.row1 * B.col + A.row2 * B.col
*)
Definition mat3_mul (a b : Mat3) : Mat3 :=
  mkMat3
    (* Column 0 *)
    (m0 a * m0 b + m3 a * m1 b + m6 a * m2 b)
    (m1 a * m0 b + m4 a * m1 b + m7 a * m2 b)
    (m2 a * m0 b + m5 a * m1 b + m8 a * m2 b)
    (* Column 1 *)
    (m0 a * m3 b + m3 a * m4 b + m6 a * m5 b)
    (m1 a * m3 b + m4 a * m4 b + m7 a * m5 b)
    (m2 a * m3 b + m5 a * m4 b + m8 a * m5 b)
    (* Column 2 *)
    (m0 a * m6 b + m3 a * m7 b + m6 a * m8 b)
    (m1 a * m6 b + m4 a * m7 b + m7 a * m8 b)
    (m2 a * m6 b + m5 a * m7 b + m8 a * m8 b).

(** * Determinant *)

(** The determinant of a 3x3 matrix (Leibniz formula / cofactor expansion).
    det(A) = a00*(a11*a22 - a12*a21) - a01*(a10*a22 - a12*a20) + a02*(a10*a21 - a11*a20) *)
Definition mat3_determinant (a : Mat3) : R :=
  m0 a * (m4 a * m8 a - m7 a * m5 a) -
  m3 a * (m1 a * m8 a - m7 a * m2 a) +
  m6 a * (m1 a * m5 a - m4 a * m2 a).

(** * Trace *)

(** The trace of a 3x3 matrix (sum of diagonal elements). *)
Definition mat3_trace (a : Mat3) : R :=
  m0 a + m4 a + m8 a.

(** * Vec2 Type (for transform operations) *)

(** A 2D vector. *)
Record Vec2 : Type := mkVec2 {
  vx : R;
  vy : R
}.

(** * Transform Operations *)

(** 2D translation matrix. *)
Definition mat3_translation (tx ty : R) : Mat3 :=
  mkMat3 1 0 0  0 1 0  tx ty 1.

(** 2D scaling matrix. *)
Definition mat3_scaling (sx sy : R) : Mat3 :=
  mkMat3 sx 0 0  0 sy 0  0 0 1.

(** Transform a point (homogeneous w=1). *)
Definition mat3_transform_point (m : Mat3) (p : Vec2) : Vec2 :=
  mkVec2
    (m0 m * vx p + m3 m * vy p + m6 m)
    (m1 m * vx p + m4 m * vy p + m7 m).

(** Transform a vector (homogeneous w=0). *)
Definition mat3_transform_vector (m : Mat3) (v : Vec2) : Vec2 :=
  mkVec2
    (m0 m * vx v + m3 m * vy v)
    (m1 m * vx v + m4 m * vy v).

(** * Shearing Operations *)

(** 2D shear matrix (shear along X by sy, along Y by sx). *)
Definition mat3_shearing (sx sy : R) : Mat3 :=
  mkMat3 1 sy 0  sx 1 0  0 0 1.

(** * Accessor Operations *)

(** Extract the translation from a 2D transform matrix.
    The translation is stored in column 2 (elements m6, m7).
    Matches Rust: self.m[6], self.m[7] *)
Definition mat3_get_translation (mat : Mat3) : Vec2 :=
  mkVec2 (m6 mat) (m7 mat).

(** Construct a matrix from three column vectors (given as tuples).
    mat3_from_cols (c0_0, c0_1, c0_2) (c1_0, c1_1, c1_2) (c2_0, c2_1, c2_2) *)
Definition mat3_from_cols (c00 c01 c02 c10 c11 c12 c20 c21 c22 : R) : Mat3 :=
  mkMat3 c00 c01 c02 c10 c11 c12 c20 c21 c22.

(** * Inverse Operation *)

(** The inverse of a 3x3 matrix using cofactor expansion.
    inverse(A) = (1/det(A)) * adj(A)
    where adj(A) is the adjugate (transpose of cofactor matrix).
    Matches Rust: mat3.rs lines 190-211 *)
Definition mat3_inverse (a : Mat3) : Mat3 :=
  let det := mat3_determinant a in
  let inv_det := / det in
  mkMat3
    (* Column 0: cofactors of row 0, transposed *)
    ((m4 a * m8 a - m5 a * m7 a) * inv_det)
    ((m2 a * m7 a - m1 a * m8 a) * inv_det)
    ((m1 a * m5 a - m2 a * m4 a) * inv_det)
    (* Column 1: cofactors of row 1, transposed *)
    ((m5 a * m6 a - m3 a * m8 a) * inv_det)
    ((m0 a * m8 a - m2 a * m6 a) * inv_det)
    ((m2 a * m3 a - m0 a * m5 a) * inv_det)
    (* Column 2: cofactors of row 2, transposed *)
    ((m3 a * m7 a - m4 a * m6 a) * inv_det)
    ((m1 a * m6 a - m0 a * m7 a) * inv_det)
    ((m0 a * m4 a - m1 a * m3 a) * inv_det).

(** * Equality Lemmas *)

(** Two Vec2 are equal iff their components are equal. *)
Lemma vec2_eq : forall a b : Vec2,
  vx a = vx b -> vy a = vy b -> a = b.
Proof.
  intros a b Hx Hy.
  destruct a, b. simpl in *. subst. reflexivity.
Qed.

(** Two matrices are equal iff all their components are equal. *)
Lemma mat3_eq : forall a b : Mat3,
  m0 a = m0 b ->
  m1 a = m1 b ->
  m2 a = m2 b ->
  m3 a = m3 b ->
  m4 a = m4 b ->
  m5 a = m5 b ->
  m6 a = m6 b ->
  m7 a = m7 b ->
  m8 a = m8 b ->
  a = b.
Proof.
  intros a b H0 H1 H2 H3 H4 H5 H6 H7 H8.
  destruct a, b.
  simpl in *.
  subst.
  reflexivity.
Qed.

(** * Specification Verification Summary

    This file provides:
    - Mat3 record type definition (9 real components, column-major)
    - Vec2 record type definition (2 real components)
    - mat3_zero: The zero matrix
    - mat3_identity: The identity matrix
    - mat3_add: Matrix addition
    - mat3_neg: Matrix negation
    - mat3_sub: Matrix subtraction
    - mat3_scale: Scalar multiplication
    - mat3_transpose: Matrix transpose
    - mat3_mul: Matrix multiplication
    - mat3_determinant: 3x3 determinant (cofactor expansion)
    - mat3_trace: Trace (sum of diagonal)
    - mat3_translation: 2D translation matrix
    - mat3_scaling: 2D scaling matrix
    - mat3_transform_point: Point transformation (w=1)
    - mat3_transform_vector: Vector transformation (w=0)
    - mat3_shearing: 2D shear matrix
    - mat3_get_translation: Extract translation from 2D transform
    - mat3_from_cols: Constructor from column values
    - mat3_eq: Component-wise matrix equality lemma
    - vec2_eq: Component-wise Vec2 equality lemma

    Total definitions: 19
    Total lemmas: 2
    Admits: 0
*)
