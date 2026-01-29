(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Rect_Extract.v - Coq Extraction to OCaml for Computational Rect
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt.

Set Warnings "-notation-overridden".
Require Import RourceMath.Rect_Compute.
Set Warnings "default".

(** * Extraction Directives *)

Extraction "rect_extracted"
  ZRect
  mkZRect
  zrect_x
  zrect_y
  zrect_w
  zrect_h
  zrect_new
  zrect_zero
  zrect_right
  zrect_bottom
  zrect_area
  zrect_perimeter
  zrect_center_x
  zrect_center_y
  zrect_is_valid
  zrect_is_empty
  zrect_contains_point
  zrect_contains_rect
  zrect_intersects
  zrect_translate
  zrect_expand
  zrect_shrink
  zrect_union
  zrect_eq_dec.
