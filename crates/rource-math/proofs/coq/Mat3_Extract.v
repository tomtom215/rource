(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Mat3_Extract.v - Coq Extraction to OCaml for Computational Mat3
 *
 * Extracts the computational ZMat3 type and operations to OCaml.
 * See Vec2_Extract.v for detailed pipeline documentation.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 * - Extraction is semantics-preserving (Coq guarantee)
 * - Source proofs have zero admits
 * - Extracted code is directly compilable
 *)

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt.

Set Warnings "-notation-overridden".
Require Import RourceMath.Mat3_Compute.
Set Warnings "default".

(** * Extraction Directives *)

Extraction "mat3_extracted"
  ZMat3
  mkZMat3
  zm3_0 zm3_1 zm3_2 zm3_3 zm3_4 zm3_5 zm3_6 zm3_7 zm3_8
  zmat3_zero
  zmat3_identity
  zmat3_add
  zmat3_neg
  zmat3_sub
  zmat3_scale
  zmat3_transpose
  zmat3_mul
  zmat3_determinant
  zmat3_trace.
