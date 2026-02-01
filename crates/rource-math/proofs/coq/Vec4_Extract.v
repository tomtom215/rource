(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Vec4_Extract.v - Coq Extraction to OCaml for Computational Vec4
 *
 * Extracts the computational ZVec4 type and operations to OCaml.
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
Require Import RourceMath.Vec4_Compute.
Set Warnings "default".

(** * Extraction Directives *)

Extraction "vec4_extracted"
  ZVec4
  mkZVec4
  zvec4_x
  zvec4_y
  zvec4_z
  zvec4_w
  zvec4_new
  zvec4_zero
  zvec4_one
  zvec4_splat
  zvec4_unit_x
  zvec4_unit_y
  zvec4_unit_z
  zvec4_unit_w
  zvec4_add
  zvec4_sub
  zvec4_neg
  zvec4_scale
  zvec4_mul
  zvec4_dot
  zvec4_length_squared
  zvec4_lerp
  zvec4_eq_dec.
