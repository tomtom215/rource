(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Rect_Proofs.v - Formal Proofs of Rectangle Properties (R-based)
 *
 * Machine-checked proofs of spatial and algebraic properties of rectangles.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 * - Zero admits
 * - All proofs machine-checked by Coq
 *)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Set Warnings "-notation-overridden".
Require Import RourceMath.Rect.
Set Warnings "default".

(** * Containment Properties *)

(** Theorem 1: A rect with non-negative dimensions contains its top-left corner. *)
Theorem rect_contains_top_left : forall (r : Rect),
  rect_w r >= 0 -> rect_h r >= 0 ->
  rect_contains_point r (rect_x r) (rect_y r).
Proof.
  intros [x y0 w h] Hw Hh. simpl in *.
  unfold rect_contains_point. simpl. lra.
Qed.

(** Theorem 2: A rect with non-negative dimensions contains its bottom-right. *)
Theorem rect_contains_bottom_right : forall (r : Rect),
  rect_w r >= 0 -> rect_h r >= 0 ->
  rect_contains_point r (rect_x r + rect_w r) (rect_y r + rect_h r).
Proof.
  intros [x y0 w h] Hw Hh. simpl in *.
  unfold rect_contains_point. simpl. lra.
Qed.

(** Theorem 3: A rect contains its center. *)
Theorem rect_contains_center : forall (r : Rect),
  rect_w r >= 0 -> rect_h r >= 0 ->
  rect_contains_point r (rect_center_x r) (rect_center_y r).
Proof.
  intros [x y0 w h] Hw Hh. simpl in *.
  unfold rect_contains_point, rect_center_x, rect_center_y. simpl. lra.
Qed.

(** Theorem 4: contains_rect is reflexive. *)
Theorem rect_contains_rect_refl : forall (r : Rect),
  rect_contains_rect r r.
Proof.
  intros [x y0 w h]. unfold rect_contains_rect. simpl. lra.
Qed.

(** Theorem 5: contains_rect is transitive. *)
Theorem rect_contains_rect_trans : forall (a b c : Rect),
  rect_contains_rect a b -> rect_contains_rect b c ->
  rect_contains_rect a c.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh] [cx cy cw ch].
  unfold rect_contains_rect. simpl. lra.
Qed.

(** * Intersection Properties *)

(** Theorem 6: intersects is symmetric. *)
Theorem rect_intersects_symmetric : forall (a b : Rect),
  rect_intersects a b -> rect_intersects b a.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold rect_intersects. simpl. lra.
Qed.

(** Theorem 7: A valid rect intersects itself. *)
Theorem rect_intersects_self : forall (r : Rect),
  rect_is_valid r -> rect_intersects r r.
Proof.
  intros [x y0 w h] [Hw Hh]. simpl in *.
  unfold rect_intersects. simpl. lra.
Qed.

(** Theorem 8: contains_rect implies intersects (for valid inner rect). *)
Theorem rect_contains_implies_intersects : forall (a b : Rect),
  rect_contains_rect a b -> rect_is_valid b ->
  rect_intersects a b.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold rect_contains_rect, rect_is_valid, rect_intersects.
  simpl. lra.
Qed.

(** * Transformation Properties *)

(** Theorem 9: translate preserves width and height. *)
Theorem rect_translate_preserves_size : forall (r : Rect) (dx dy : R),
  rect_w (rect_translate r dx dy) = rect_w r /\
  rect_h (rect_translate r dx dy) = rect_h r.
Proof.
  intros [x y0 w h] dx dy. simpl. split; reflexivity.
Qed.

(** Theorem 10: translate by (0,0) is identity. *)
Theorem rect_translate_identity : forall (r : Rect),
  rect_translate r 0 0 = r.
Proof.
  intros [x y0 w h]. unfold rect_translate. simpl.
  apply rect_eq; lra.
Qed.

(** Theorem 11: translate composition. *)
Theorem rect_translate_compose : forall (r : Rect) (dx1 dy1 dx2 dy2 : R),
  rect_translate (rect_translate r dx1 dy1) dx2 dy2 =
  rect_translate r (dx1 + dx2) (dy1 + dy2).
Proof.
  intros [x y0 w h] dx1 dy1 dx2 dy2.
  unfold rect_translate. simpl.
  apply rect_eq; lra.
Qed.

(** Theorem 12: expand then shrink by same amount is identity. *)
Theorem rect_expand_shrink_inverse : forall (r : Rect) (amount : R),
  rect_expand (rect_shrink r amount) amount = r.
Proof.
  intros [x y0 w h] amount.
  unfold rect_shrink, rect_expand. simpl.
  apply rect_eq; lra.
Qed.

(** Theorem 13: shrink then expand by same amount is identity. *)
Theorem rect_shrink_expand_inverse : forall (r : Rect) (amount : R),
  rect_shrink (rect_expand r amount) amount = r.
Proof.
  intros [x y0 w h] amount.
  unfold rect_shrink, rect_expand. simpl.
  apply rect_eq; lra.
Qed.

(** * Area and Perimeter Properties *)

(** Theorem 14: area is non-negative for valid rects. *)
Theorem rect_area_nonneg : forall (r : Rect),
  rect_w r >= 0 -> rect_h r >= 0 -> rect_area r >= 0.
Proof.
  intros [x y0 w h] Hw Hh. simpl in *.
  unfold rect_area. simpl. nra.
Qed.

(** Theorem 15: perimeter is non-negative for valid rects. *)
Theorem rect_perimeter_nonneg : forall (r : Rect),
  rect_w r >= 0 -> rect_h r >= 0 -> rect_perimeter r >= 0.
Proof.
  intros [x y0 w h] Hw Hh. simpl in *.
  unfold rect_perimeter. simpl. lra.
Qed.

(** Theorem 16: perimeter of square = 4 * side. *)
Theorem rect_square_perimeter : forall (side : R),
  rect_perimeter (rect_new 0 0 side side) = 4 * side.
Proof.
  intros. unfold rect_perimeter, rect_new. simpl. lra.
Qed.

(** Theorem 17: area of square = side^2. *)
Theorem rect_square_area : forall (side : R),
  rect_area (rect_new 0 0 side side) = side * side.
Proof.
  intros. unfold rect_area, rect_new. simpl. lra.
Qed.

(** * Validity Properties *)

(** Theorem 18: is_valid implies non-empty. *)
Theorem rect_valid_nonempty : forall (r : Rect),
  rect_is_valid r -> rect_area r > 0.
Proof.
  intros [x y0 w h] [Hw Hh]. simpl in *.
  unfold rect_area. simpl. nra.
Qed.

(** Theorem 19: zero rect has zero area. *)
Theorem rect_zero_area :
  rect_area rect_zero = 0.
Proof.
  unfold rect_area, rect_zero. simpl. lra.
Qed.

(** Theorem 20: expand by positive amount preserves validity. *)
Theorem rect_expand_preserves_valid : forall (r : Rect) (amount : R),
  rect_is_valid r -> amount >= 0 ->
  rect_is_valid (rect_expand r amount).
Proof.
  intros [x y0 w h] amount [Hw Hh] Ha. simpl in *.
  unfold rect_is_valid, rect_expand. simpl. lra.
Qed.

(** * From-Center Properties *)

(** Theorem 21: from_center preserves dimensions.
    ∀ cx cy w h, from_center(cx, cy, w, h).w = w *)
Theorem rect_from_center_dimensions : forall cx cy w h : R,
  rect_w (rect_from_center cx cy w h) = w /\
  rect_h (rect_from_center cx cy w h) = h.
Proof.
  intros. unfold rect_from_center. simpl. split; reflexivity.
Qed.

(** Theorem 22: from_center center_x matches.
    ∀ cx cy w h, center_x(from_center(cx, cy, w, h)) = cx *)
Theorem rect_from_center_center_x : forall cx cy w h : R,
  rect_center_x (rect_from_center cx cy w h) = cx.
Proof.
  intros. unfold rect_center_x, rect_from_center. simpl. lra.
Qed.

(** Theorem 23: from_center center_y matches.
    ∀ cx cy w h, center_y(from_center(cx, cy, w, h)) = cy *)
Theorem rect_from_center_center_y : forall cx cy w h : R,
  rect_center_y (rect_from_center cx cy w h) = cy.
Proof.
  intros. unfold rect_center_y, rect_from_center. simpl. lra.
Qed.

(** * Scale Properties *)

(** Theorem 24: scale by 1 is identity.
    ∀ r : Rect, scale(r, 1) = r *)
Theorem rect_scale_identity : forall (r : Rect),
  rect_scale r 1 = r.
Proof.
  intros [x y0 w h].
  unfold rect_scale. simpl.
  apply rect_eq; lra.
Qed.

(** Theorem 25: scale preserves position.
    ∀ r : Rect, ∀ f : R, scale(r, f).x = r.x ∧ scale(r, f).y = r.y *)
Theorem rect_scale_preserves_position : forall (r : Rect) (factor : R),
  rect_x (rect_scale r factor) = rect_x r /\
  rect_y (rect_scale r factor) = rect_y r.
Proof.
  intros [x y0 w h] factor. simpl. split; reflexivity.
Qed.

(** Theorem 26: scale area = factor² × original area.
    ∀ r : Rect, ∀ f : R, area(scale(r, f)) = f² × area(r) *)
Theorem rect_scale_area : forall (r : Rect) (factor : R),
  rect_area (rect_scale r factor) = factor * factor * rect_area r.
Proof.
  intros [x y0 w h] factor.
  unfold rect_area, rect_scale. simpl. ring.
Qed.

(** Theorem 27: scale by 0 produces zero dimensions.
    ∀ r : Rect, area(scale(r, 0)) = 0 *)
Theorem rect_scale_zero_area : forall (r : Rect),
  rect_area (rect_scale r 0) = 0.
Proof.
  intros [x y0 w h].
  unfold rect_area, rect_scale. simpl. ring.
Qed.

(** * Intersection Properties *)

(** Theorem 28: intersection has non-negative dimensions.
    ∀ a b : Rect, intersection(a, b).w ≥ 0 ∧ intersection(a, b).h ≥ 0 *)
Theorem rect_intersection_nonneg : forall (a b : Rect),
  rect_w (rect_intersection a b) >= 0 /\
  rect_h (rect_intersection a b) >= 0.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold rect_intersection, rect_right, rect_bottom. simpl.
  split; unfold Rmax; destruct (Rle_dec _ _); lra.
Qed.

(** Theorem 29: intersection is commutative (dimensions).
    The width and height of intersection(a,b) equal those of intersection(b,a). *)
Theorem rect_intersection_comm_dims : forall (a b : Rect),
  rect_w (rect_intersection a b) = rect_w (rect_intersection b a) /\
  rect_h (rect_intersection a b) = rect_h (rect_intersection b a).
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold rect_intersection, rect_right, rect_bottom. simpl.
  split;
    unfold Rmax, Rmin;
    repeat (destruct (Rle_dec _ _)); lra.
Qed.

(** Theorem 30: intersection with itself preserves the rect (for valid rects). *)
Theorem rect_intersection_self : forall (r : Rect),
  rect_is_valid r ->
  rect_intersection r r = r.
Proof.
  intros [x y0 w h] [Hw Hh]. simpl in *.
  unfold rect_intersection, rect_right, rect_bottom. simpl.
  unfold Rmax, Rmin. repeat (destruct (Rle_dec _ _)); try lra.
  apply rect_eq; lra.
Qed.

(** Theorem 31: intersection area is commutative. *)
Theorem rect_intersection_area_comm : forall (a b : Rect),
  rect_area (rect_intersection a b) = rect_area (rect_intersection b a).
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold rect_area, rect_intersection, rect_right, rect_bottom. simpl.
  unfold Rmax, Rmin.
  repeat (destruct (Rle_dec _ _)); try nra.
Qed.

(** Theorem 32: intersection of non-overlapping rects has zero area. *)
Theorem rect_disjoint_intersection_zero_area : forall (a b : Rect),
  rect_x a + rect_w a <= rect_x b ->
  rect_area (rect_intersection a b) = 0.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh] Hdisj.
  unfold rect_area, rect_intersection, rect_right, rect_bottom. simpl in *.
  unfold Rmax, Rmin.
  repeat (destruct (Rle_dec _ _)); try lra; nra.
Qed.
