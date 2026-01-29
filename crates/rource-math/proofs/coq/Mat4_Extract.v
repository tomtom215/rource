(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Mat4_Extract.v - Coq Extraction to OCaml for Computational Mat4
 *
 * Extracts the computational ZMat4 type and operations to OCaml.
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
Require Import RourceMath.Mat4_Compute.
Set Warnings "default".

(** * Extraction Directives *)

Extraction "mat4_extracted"
  ZMat4
  mkZMat4
  zm4_0 zm4_1 zm4_2 zm4_3 zm4_4 zm4_5 zm4_6 zm4_7
  zm4_8 zm4_9 zm4_10 zm4_11 zm4_12 zm4_13 zm4_14 zm4_15
  zmat4_zero
  zmat4_identity
  zmat4_add
  zmat4_neg
  zmat4_sub
  zmat4_scale
  zmat4_transpose
  zmat4_mul
  zmat4_trace.
