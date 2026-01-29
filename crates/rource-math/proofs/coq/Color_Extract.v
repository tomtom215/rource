(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Color_Extract.v - Coq Extraction to OCaml for Computational Color
 *
 * Extracts the Z-based ZColor type and operations to OCaml.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt.

Set Warnings "-notation-overridden".
Require Import RourceMath.Color_Compute.
Set Warnings "default".

(** * Extraction Directives *)

Extraction "color_extracted"
  ZColor
  mkZColor
  zcolor_r
  zcolor_g
  zcolor_b
  zcolor_a
  zcolor_new
  zcolor_rgb
  zcolor_gray
  zcolor_transparent
  zcolor_black
  zcolor_white
  zcolor_with_alpha
  zcolor_fade
  zcolor_lerp
  zcolor_premultiplied
  zcolor_blend_over
  zcolor_luminance
  zcolor_clamp
  zcolor_eq_dec.
