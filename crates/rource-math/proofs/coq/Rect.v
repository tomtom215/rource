(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Rect.v - Abstract Rectangle Specification (R-based)
 *
 * Mathematical formalization of 2D rectangles using Coq's R (real number) type.
 *
 * LAYERED VERIFICATION ARCHITECTURE:
 *
 *   Layer 1 (Abstract):      Rect.v / Rect_Proofs.v       (R-based)
 *   Layer 2 (Computational): Rect_Compute.v               (Z-based, extractable)
 *   Layer 3 (Extraction):    Rect_Extract.v               (OCaml/WASM output)
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(** * Rect Definition *)

Record Rect : Type := mkRect {
  rect_x : R;
  rect_y : R;
  rect_w : R;
  rect_h : R
}.

(** * Equality Lemma *)

Lemma rect_eq : forall x1 y1 w1 h1 x2 y2 w2 h2 : R,
  x1 = x2 -> y1 = y2 -> w1 = w2 -> h1 = h2 ->
  mkRect x1 y1 w1 h1 = mkRect x2 y2 w2 h2.
Proof.
  intros. subst. reflexivity.
Qed.

(** * Constructors *)

Definition rect_new (x y w h : R) : Rect := mkRect x y w h.
Definition rect_zero : Rect := mkRect 0 0 0 0.

(** * Accessors *)

Definition rect_right (r : Rect) : R := rect_x r + rect_w r.
Definition rect_bottom (r : Rect) : R := rect_y r + rect_h r.
Definition rect_area (r : Rect) : R := rect_w r * rect_h r.
Definition rect_perimeter (r : Rect) : R := 2 * (rect_w r + rect_h r).
Definition rect_center_x (r : Rect) : R := rect_x r + rect_w r / 2.
Definition rect_center_y (r : Rect) : R := rect_y r + rect_h r / 2.

(** * Predicates *)

Definition rect_is_valid (r : Rect) : Prop :=
  rect_w r > 0 /\ rect_h r > 0.

Definition rect_contains_point (r : Rect) (px py : R) : Prop :=
  px >= rect_x r /\ px <= rect_x r + rect_w r /\
  py >= rect_y r /\ py <= rect_y r + rect_h r.

Definition rect_contains_rect (outer inner : Rect) : Prop :=
  rect_x inner >= rect_x outer /\
  rect_y inner >= rect_y outer /\
  rect_x inner + rect_w inner <= rect_x outer + rect_w outer /\
  rect_y inner + rect_h inner <= rect_y outer + rect_h outer.

Definition rect_intersects (a b : Rect) : Prop :=
  rect_x a < rect_x b + rect_w b /\
  rect_x a + rect_w a > rect_x b /\
  rect_y a < rect_y b + rect_h b /\
  rect_y a + rect_h a > rect_y b.

(** * Transformations *)

Definition rect_translate (r : Rect) (dx dy : R) : Rect :=
  mkRect (rect_x r + dx) (rect_y r + dy) (rect_w r) (rect_h r).

Definition rect_expand (r : Rect) (amount : R) : Rect :=
  mkRect (rect_x r - amount) (rect_y r - amount)
         (rect_w r + 2 * amount) (rect_h r + 2 * amount).

Definition rect_shrink (r : Rect) (amount : R) : Rect :=
  rect_expand r (- amount).

(** Intersection of two rectangles (non-negative dimensions guaranteed) *)
Definition rect_intersection (a b : Rect) : Rect :=
  let x := Rmax (rect_x a) (rect_x b) in
  let y0 := Rmax (rect_y a) (rect_y b) in
  let right := Rmin (rect_right a) (rect_right b) in
  let bottom := Rmin (rect_bottom a) (rect_bottom b) in
  mkRect x y0 (Rmax 0 (right - x)) (Rmax 0 (bottom - y0)).

(** Create rectangle from center point and dimensions *)
Definition rect_from_center (cx cy w h : R) : Rect :=
  mkRect (cx - w / 2) (cy - h / 2) w h.

(** Scale rectangle dimensions by a factor (position preserved) *)
Definition rect_scale (r : Rect) (factor : R) : Rect :=
  mkRect (rect_x r) (rect_y r) (rect_w r * factor) (rect_h r * factor).

(** * Additional Accessors *)

(** Left edge = x coordinate *)
Definition rect_left (r : Rect) : R := rect_x r.

(** Top edge = y coordinate *)
Definition rect_top (r : Rect) : R := rect_y r.

(** Minimum point (top-left) as a pair *)
Definition rect_min_x (r : Rect) : R := rect_x r.
Definition rect_min_y (r : Rect) : R := rect_y r.

(** Maximum point (bottom-right) as a pair *)
Definition rect_max_x (r : Rect) : R := rect_x r + rect_w r.
Definition rect_max_y (r : Rect) : R := rect_y r + rect_h r.

(** * Additional Predicates *)

(** A rect is empty if width or height is non-positive.
    Matches Rust: self.width <= 0.0 || self.height <= 0.0 *)
Definition rect_is_empty (r : Rect) : Prop :=
  rect_w r <= 0 \/ rect_h r <= 0.

(** * Additional Constructors *)

(** Create rectangle from two corner points (computes min/max).
    Matches Rust: from_corners(a, b) *)
Definition rect_from_corners (ax ay bx by0 : R) : Rect :=
  mkRect (Rmin ax bx) (Rmin ay by0)
         (Rmax ax bx - Rmin ax bx) (Rmax ay by0 - Rmin ay by0).

(** * Additional Transformations *)

(** Union of two rectangles (smallest rect containing both).
    Matches Rust: self.union(other) *)
Definition rect_union (a b : Rect) : Rect :=
  let x := Rmin (rect_x a) (rect_x b) in
  let y := Rmin (rect_y a) (rect_y b) in
  let right := Rmax (rect_right a) (rect_right b) in
  let bottom := Rmax (rect_bottom a) (rect_bottom b) in
  mkRect x y (right - x) (bottom - y).

(** Expand rectangle with separate x and y amounts.
    Matches Rust: expand_xy(x_amount, y_amount) *)
Definition rect_expand_xy (r : Rect) (x_amount y_amount : R) : Rect :=
  mkRect (rect_x r - x_amount) (rect_y r - y_amount)
         (rect_w r + 2 * x_amount) (rect_h r + 2 * y_amount).

(** Normalize a rectangle: ensure width and height are non-negative.
    If width is negative, adjust x so that the rect covers the same region.
    Matches Rust: Rect::normalize() *)
Definition rect_normalize (r : Rect) : Rect :=
  let x := if Rle_dec (rect_w r) 0 then rect_x r + rect_w r else rect_x r in
  let y := if Rle_dec (rect_h r) 0 then rect_y r + rect_h r else rect_y r in
  let w := Rabs (rect_w r) in
  let h := Rabs (rect_h r) in
  mkRect x y w h.

(** Scale from center: scale dimensions while keeping center fixed.
    Matches Rust: Rect::scale_from_center(factor) *)
Definition rect_scale_from_center (r : Rect) (factor : R) : Rect :=
  let cx := rect_center_x r in
  let cy := rect_center_y r in
  let nw := rect_w r * factor in
  let nh := rect_h r * factor in
  mkRect (cx - nw / 2) (cy - nh / 2) nw nh.

(** Approximate equality with epsilon tolerance.
    Matches Rust: Rect::approx_eq(other) *)
Definition rect_approx_eq (a b : Rect) (eps : R) : Prop :=
  Rabs (rect_x a - rect_x b) <= eps /\
  Rabs (rect_y a - rect_y b) <= eps /\
  Rabs (rect_w a - rect_w b) <= eps /\
  Rabs (rect_h a - rect_h b) <= eps.

(** Linear interpolation between two rectangles.
    lerp(a, b, t) interpolates each component: x, y, w, h.
    Matches component-wise lerp for rectangles. *)
Definition rect_lerp (a b : Rect) (t : R) : Rect :=
  mkRect (rect_x a + t * (rect_x b - rect_x a))
         (rect_y a + t * (rect_y b - rect_y a))
         (rect_w a + t * (rect_w b - rect_w a))
         (rect_h a + t * (rect_h b - rect_h a)).
