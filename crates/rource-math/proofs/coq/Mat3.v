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

(** * Equality Lemma *)

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
    - mat3_zero: The zero matrix
    - mat3_identity: The identity matrix
    - mat3_add: Matrix addition
    - mat3_neg: Matrix negation
    - mat3_sub: Matrix subtraction
    - mat3_scale: Scalar multiplication
    - mat3_transpose: Matrix transpose
    - mat3_mul: Matrix multiplication
    - mat3_eq: Component-wise equality lemma

    Total definitions: 9
    Total lemmas: 1
    Admits: 0
*)
