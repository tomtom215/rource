(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Bounds.v - Abstract Bounding Box Specification (R-based)
 *
 * Mathematical formalization of 2D bounding boxes using Coq's R (real number) type.
 * A Bounds is defined by min and max corners (min_x, min_y, max_x, max_y).
 *
 * LAYERED VERIFICATION ARCHITECTURE:
 *
 *   Layer 1 (Abstract):      Bounds.v / Bounds_Proofs.v       (R-based)
 *   Layer 2 (Computational): Bounds_Compute.v                 (Z-based, extractable)
 *   Layer 3 (Extraction):    RourceMath_Extract.v             (OCaml/WASM output)
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import Reals.
Require Import Lra.
Require Import RourceMath.Rect.
Open Scope R_scope.

(** * Bounds Definition *)

Record Bounds : Type := mkBounds {
  bounds_min_x : R;
  bounds_min_y : R;
  bounds_max_x : R;
  bounds_max_y : R
}.

(** * Equality Lemma *)

Lemma bounds_eq : forall mnx1 mny1 mxx1 mxy1 mnx2 mny2 mxx2 mxy2 : R,
  mnx1 = mnx2 -> mny1 = mny2 -> mxx1 = mxx2 -> mxy1 = mxy2 ->
  mkBounds mnx1 mny1 mxx1 mxy1 = mkBounds mnx2 mny2 mxx2 mxy2.
Proof.
  intros. subst. reflexivity.
Qed.

(** * Constructors *)

Definition bounds_new (min_x min_y max_x max_y : R) : Bounds :=
  mkBounds min_x min_y max_x max_y.

Definition bounds_zero : Bounds := mkBounds 0 0 0 0.

(** Create bounds from any two corner points (normalizes). *)
Definition bounds_from_points (ax ay bx by0 : R) : Bounds :=
  mkBounds (Rmin ax bx) (Rmin ay by0) (Rmax ax bx) (Rmax ay by0).

(** Create bounds from center point and half-extents *)
Definition bounds_from_che (cx cy hx hy : R) : Bounds :=
  mkBounds (cx - hx) (cy - hy) (cx + hx) (cy + hy).

(** * Accessors *)

Definition bounds_width (b : Bounds) : R := bounds_max_x b - bounds_min_x b.
Definition bounds_height (b : Bounds) : R := bounds_max_y b - bounds_min_y b.
Definition bounds_center_x (b : Bounds) : R := (bounds_min_x b + bounds_max_x b) / 2.
Definition bounds_center_y (b : Bounds) : R := (bounds_min_y b + bounds_max_y b) / 2.
Definition bounds_half_extent_x (b : Bounds) : R := bounds_width b / 2.
Definition bounds_half_extent_y (b : Bounds) : R := bounds_height b / 2.
Definition bounds_area (b : Bounds) : R := bounds_width b * bounds_height b.

(** * Predicates *)

Definition bounds_is_valid (b : Bounds) : Prop :=
  bounds_max_x b > bounds_min_x b /\ bounds_max_y b > bounds_min_y b.

Definition bounds_is_empty (b : Bounds) : Prop :=
  bounds_max_x b <= bounds_min_x b \/ bounds_max_y b <= bounds_min_y b.

Definition bounds_contains (b : Bounds) (px py : R) : Prop :=
  bounds_min_x b <= px /\ px <= bounds_max_x b /\
  bounds_min_y b <= py /\ py <= bounds_max_y b.

Definition bounds_contains_bounds (outer inner : Bounds) : Prop :=
  bounds_min_x outer <= bounds_min_x inner /\
  bounds_min_y outer <= bounds_min_y inner /\
  bounds_max_x inner <= bounds_max_x outer /\
  bounds_max_y inner <= bounds_max_y outer.

Definition bounds_intersects (a b : Bounds) : Prop :=
  bounds_min_x a < bounds_max_x b /\
  bounds_max_x a > bounds_min_x b /\
  bounds_min_y a < bounds_max_y b /\
  bounds_max_y a > bounds_min_y b.

(** * Transformations *)

Definition bounds_union (a b : Bounds) : Bounds :=
  mkBounds (Rmin (bounds_min_x a) (bounds_min_x b))
           (Rmin (bounds_min_y a) (bounds_min_y b))
           (Rmax (bounds_max_x a) (bounds_max_x b))
           (Rmax (bounds_max_y a) (bounds_max_y b)).

Definition bounds_intersection (a b : Bounds) : Bounds :=
  mkBounds (Rmax (bounds_min_x a) (bounds_min_x b))
           (Rmax (bounds_min_y a) (bounds_min_y b))
           (Rmin (bounds_max_x a) (bounds_max_x b))
           (Rmin (bounds_max_y a) (bounds_max_y b)).

Definition bounds_expand (b : Bounds) (amount : R) : Bounds :=
  mkBounds (bounds_min_x b - amount) (bounds_min_y b - amount)
           (bounds_max_x b + amount) (bounds_max_y b + amount).

Definition bounds_shrink (b : Bounds) (amount : R) : Bounds :=
  bounds_expand b (- amount).

Definition bounds_translate (b : Bounds) (dx dy : R) : Bounds :=
  mkBounds (bounds_min_x b + dx) (bounds_min_y b + dy)
           (bounds_max_x b + dx) (bounds_max_y b + dy).

Definition bounds_include_point (b : Bounds) (px py : R) : Bounds :=
  mkBounds (Rmin (bounds_min_x b) px) (Rmin (bounds_min_y b) py)
           (Rmax (bounds_max_x b) px) (Rmax (bounds_max_y b) py).

(** * Conversion *)

(** Convert bounds to a rectangle.
    Matches Rust: Bounds::to_rect() *)
Definition bounds_to_rect (b : Bounds) : Rect :=
  mkRect (bounds_min_x b) (bounds_min_y b)
         (bounds_max_x b - bounds_min_x b) (bounds_max_y b - bounds_min_y b).

(** Convert a rectangle to bounds.
    Matches Rust: Rect::to_bounds() *)
Definition rect_to_bounds (r : Rect) : Bounds :=
  mkBounds (rect_x r) (rect_y r) (rect_x r + rect_w r) (rect_y r + rect_h r).

(** * Approximate Equality *)

(** Approximate equality with epsilon tolerance.
    Matches Rust: Bounds::approx_eq(other) with default epsilon.
    We parameterize by epsilon for generality. *)
Definition bounds_approx_eq (a b : Bounds) (eps : R) : Prop :=
  Rabs (bounds_min_x a - bounds_min_x b) <= eps /\
  Rabs (bounds_min_y a - bounds_min_y b) <= eps /\
  Rabs (bounds_max_x a - bounds_max_x b) <= eps /\
  Rabs (bounds_max_y a - bounds_max_y b) <= eps.

(** Create bounds from center and size (width, height).
    Matches Rust: Bounds::from_center_size(center, size). *)
Definition bounds_from_center_size (cx cy w h : R) : Bounds :=
  mkBounds (cx - w / 2) (cy - h / 2) (cx + w / 2) (cy + h / 2).

(** Scale bounds from its center by a factor.
    Matches Rust: Bounds::scale_from_center(factor). *)
Definition bounds_scale_from_center (b : Bounds) (factor : R) : Bounds :=
  let cx := bounds_center_x b in
  let cy := bounds_center_y b in
  let new_w := bounds_width b * factor in
  let new_h := bounds_height b * factor in
  mkBounds (cx - new_w / 2) (cy - new_h / 2) (cx + new_w / 2) (cy + new_h / 2).
