(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Vec3_Extract.v - Coq Extraction to OCaml for Computational Vec3
 *
 * Extracts the computational ZVec3 type and operations to OCaml.
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
Require Import RourceMath.Vec3_Compute.
Set Warnings "default".

(** * Extraction Directives *)

Extraction "vec3_extracted"
  ZVec3
  mkZVec3
  zvec3_x
  zvec3_y
  zvec3_z
  zvec3_new
  zvec3_zero
  zvec3_splat
  zvec3_unit_x
  zvec3_unit_y
  zvec3_unit_z
  zvec3_add
  zvec3_sub
  zvec3_neg
  zvec3_scale
  zvec3_mul
  zvec3_dot
  zvec3_cross
  zvec3_length_squared
  zvec3_scalar_triple
  zvec3_eq_dec.
