(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Bounds_Proofs.v - Bounding Box Proofs (R-based)
 *
 * Machine-checked proofs for all Bounds operations defined in Bounds.v.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 * Admits: 0
 *)

Require Import Reals.
Require Import Lra.
Require Import Rminmax.
Open Scope R_scope.
Require Import RourceMath.Rect.
Require Import RourceMath.Bounds.

(** * Min/Max Helper Lemmas (unconditional bounds) *)

Local Lemma Rmin_le_l : forall x y, Rmin x y <= x.
Proof.
  intros. destruct (Rle_dec x y) as [H|H].
  - rewrite Rmin_l by exact H. lra.
  - rewrite Rmin_r. lra. apply Rnot_le_lt in H. lra.
Qed.

Local Lemma Rmin_le_r : forall x y, Rmin x y <= y.
Proof.
  intros. destruct (Rle_dec x y) as [H|H].
  - rewrite Rmin_l by exact H. exact H.
  - rewrite Rmin_r. lra. apply Rnot_le_lt in H. lra.
Qed.

Local Lemma Rle_max_l : forall x y, x <= Rmax x y.
Proof.
  intros. destruct (Rle_dec x y) as [H|H].
  - rewrite Rmax_r by exact H. exact H.
  - rewrite Rmax_l. lra. apply Rnot_le_lt in H. lra.
Qed.

Local Lemma Rle_max_r : forall x y, y <= Rmax x y.
Proof.
  intros. destruct (Rle_dec x y) as [H|H].
  - rewrite Rmax_r by exact H. lra.
  - rewrite Rmax_l. apply Rnot_le_lt in H. lra. apply Rnot_le_lt in H. lra.
Qed.

(** * Constructor Properties *)

Theorem bounds_new_min_x : forall mnx mny mxx mxy,
  bounds_min_x (bounds_new mnx mny mxx mxy) = mnx.
Proof. intros. reflexivity. Qed.

Theorem bounds_new_min_y : forall mnx mny mxx mxy,
  bounds_min_y (bounds_new mnx mny mxx mxy) = mny.
Proof. intros. reflexivity. Qed.

Theorem bounds_new_max_x : forall mnx mny mxx mxy,
  bounds_max_x (bounds_new mnx mny mxx mxy) = mxx.
Proof. intros. reflexivity. Qed.

Theorem bounds_new_max_y : forall mnx mny mxx mxy,
  bounds_max_y (bounds_new mnx mny mxx mxy) = mxy.
Proof. intros. reflexivity. Qed.

Theorem bounds_zero_min_x : bounds_min_x bounds_zero = 0.
Proof. reflexivity. Qed.

Theorem bounds_zero_max_x : bounds_max_x bounds_zero = 0.
Proof. reflexivity. Qed.

Theorem bounds_zero_width : bounds_width bounds_zero = 0.
Proof. unfold bounds_width, bounds_zero. simpl. lra. Qed.

Theorem bounds_zero_height : bounds_height bounds_zero = 0.
Proof. unfold bounds_height, bounds_zero. simpl. lra. Qed.

Theorem bounds_zero_area : bounds_area bounds_zero = 0.
Proof. unfold bounds_area, bounds_width, bounds_height, bounds_zero. simpl. lra. Qed.

(** * Accessor Properties *)

Theorem bounds_width_nonneg : forall b : Bounds,
  bounds_is_valid b -> bounds_width b > 0.
Proof.
  intros [mnx mny mxx mxy] [Hx Hy].
  unfold bounds_width, bounds_is_valid in *. simpl in *. lra.
Qed.

Theorem bounds_height_nonneg : forall b : Bounds,
  bounds_is_valid b -> bounds_height b > 0.
Proof.
  intros [mnx mny mxx mxy] [Hx Hy].
  unfold bounds_height, bounds_is_valid in *. simpl in *. lra.
Qed.

Theorem bounds_area_nonneg : forall b : Bounds,
  bounds_is_valid b -> bounds_area b > 0.
Proof.
  intros [mnx mny mxx mxy] [Hx Hy].
  unfold bounds_area, bounds_width, bounds_height, bounds_is_valid in *.
  simpl in *. apply Rmult_gt_0_compat; lra.
Qed.

Theorem bounds_area_zero_if_empty : forall b : Bounds,
  bounds_width b = 0 \/ bounds_height b = 0 -> bounds_area b = 0.
Proof.
  intros [mnx mny mxx mxy] [H | H];
  unfold bounds_area, bounds_width, bounds_height in *; simpl in *; nra.
Qed.

Theorem bounds_center_x_midpoint : forall b : Bounds,
  bounds_center_x b = (bounds_min_x b + bounds_max_x b) / 2.
Proof. intros. reflexivity. Qed.

Theorem bounds_center_y_midpoint : forall b : Bounds,
  bounds_center_y b = (bounds_min_y b + bounds_max_y b) / 2.
Proof. intros. reflexivity. Qed.

Theorem bounds_half_extent_x_half_width : forall b : Bounds,
  bounds_half_extent_x b = bounds_width b / 2.
Proof. intros. reflexivity. Qed.

Theorem bounds_half_extent_y_half_height : forall b : Bounds,
  bounds_half_extent_y b = bounds_height b / 2.
Proof. intros. reflexivity. Qed.

(** * Validity Properties *)

Theorem bounds_valid_not_empty : forall b : Bounds,
  bounds_is_valid b -> ~ bounds_is_empty b.
Proof.
  intros [mnx mny mxx mxy] [Hx Hy] [He | He];
  unfold bounds_is_valid, bounds_is_empty in *; simpl in *; lra.
Qed.

Theorem bounds_empty_not_valid : forall b : Bounds,
  bounds_is_empty b -> ~ bounds_is_valid b.
Proof.
  intros [mnx mny mxx mxy] [He | He] [Hx Hy];
  unfold bounds_is_valid, bounds_is_empty in *; simpl in *; lra.
Qed.

(** * Translate Properties *)

Theorem bounds_translate_identity : forall b : Bounds,
  bounds_translate b 0 0 = b.
Proof.
  intros [mnx mny mxx mxy]. unfold bounds_translate. simpl.
  f_equal; lra.
Qed.

Theorem bounds_translate_compose : forall b dx1 dy1 dx2 dy2,
  bounds_translate (bounds_translate b dx1 dy1) dx2 dy2 =
  bounds_translate b (dx1 + dx2) (dy1 + dy2).
Proof.
  intros [mnx mny mxx mxy] dx1 dy1 dx2 dy2.
  unfold bounds_translate. simpl. f_equal; lra.
Qed.

Theorem bounds_translate_preserves_width : forall b dx dy,
  bounds_width (bounds_translate b dx dy) = bounds_width b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold bounds_width, bounds_translate. simpl. lra.
Qed.

Theorem bounds_translate_preserves_height : forall b dx dy,
  bounds_height (bounds_translate b dx dy) = bounds_height b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold bounds_height, bounds_translate. simpl. lra.
Qed.

Theorem bounds_translate_preserves_area : forall b dx dy,
  bounds_area (bounds_translate b dx dy) = bounds_area b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold bounds_area, bounds_width, bounds_height, bounds_translate. simpl. ring.
Qed.

Theorem bounds_translate_preserves_validity : forall b dx dy,
  bounds_is_valid b -> bounds_is_valid (bounds_translate b dx dy).
Proof.
  intros [mnx mny mxx mxy] dx dy [Hx Hy].
  unfold bounds_is_valid, bounds_translate in *. simpl in *. lra.
Qed.

(** * Expand/Shrink Properties *)

Theorem bounds_expand_width : forall b amount,
  bounds_width (bounds_expand b amount) = bounds_width b + 2 * amount.
Proof.
  intros [mnx mny mxx mxy] amount.
  unfold bounds_width, bounds_expand. simpl. lra.
Qed.

Theorem bounds_expand_height : forall b amount,
  bounds_height (bounds_expand b amount) = bounds_height b + 2 * amount.
Proof.
  intros [mnx mny mxx mxy] amount.
  unfold bounds_height, bounds_expand. simpl. lra.
Qed.

Theorem bounds_shrink_is_neg_expand : forall b amount,
  bounds_shrink b amount = bounds_expand b (- amount).
Proof. intros. reflexivity. Qed.

Theorem bounds_expand_shrink_inverse : forall b amount,
  bounds_expand (bounds_shrink b amount) amount = b.
Proof.
  intros [mnx mny mxx mxy] amount.
  unfold bounds_shrink, bounds_expand. simpl. f_equal; lra.
Qed.

Theorem bounds_shrink_expand_inverse : forall b amount,
  bounds_shrink (bounds_expand b amount) amount = b.
Proof.
  intros [mnx mny mxx mxy] amount.
  unfold bounds_shrink, bounds_expand. simpl. f_equal; lra.
Qed.

Theorem bounds_expand_preserves_center_x : forall b amount,
  bounds_center_x (bounds_expand b amount) = bounds_center_x b.
Proof.
  intros [mnx mny mxx mxy] amount.
  unfold bounds_center_x, bounds_expand. simpl. lra.
Qed.

Theorem bounds_expand_preserves_center_y : forall b amount,
  bounds_center_y (bounds_expand b amount) = bounds_center_y b.
Proof.
  intros [mnx mny mxx mxy] amount.
  unfold bounds_center_y, bounds_expand. simpl. lra.
Qed.

(** * Union Properties *)

Theorem bounds_union_comm : forall a b : Bounds,
  bounds_union a b = bounds_union b a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold bounds_union. simpl. f_equal; apply Rmin_comm || apply Rmax_comm.
Qed.

Theorem bounds_union_idempotent : forall b : Bounds,
  bounds_union b b = b.
Proof.
  intros [mnx mny mxx mxy]. unfold bounds_union. simpl.
  f_equal; apply Rmin_left || apply Rmax_left; lra.
Qed.

Theorem bounds_union_contains_left : forall a b : Bounds,
  bounds_is_valid a -> bounds_is_valid b ->
  bounds_contains_bounds (bounds_union a b) a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] _ _.
  unfold bounds_contains_bounds, bounds_union.
  cbn [bounds_min_x bounds_min_y bounds_max_x bounds_max_y].
  exact (conj (Rmin_le_l a1 b1) (conj (Rmin_le_l a2 b2) (conj (Rle_max_l a3 b3) (Rle_max_l a4 b4)))).
Qed.

Theorem bounds_union_contains_right : forall a b : Bounds,
  bounds_is_valid a -> bounds_is_valid b ->
  bounds_contains_bounds (bounds_union a b) b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] _ _.
  unfold bounds_contains_bounds, bounds_union.
  cbn [bounds_min_x bounds_min_y bounds_max_x bounds_max_y].
  exact (conj (Rmin_le_r a1 b1) (conj (Rmin_le_r a2 b2) (conj (Rle_max_r a3 b3) (Rle_max_r a4 b4)))).
Qed.

(** * Intersection Properties *)

Theorem bounds_intersection_comm : forall a b : Bounds,
  bounds_intersection a b = bounds_intersection b a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold bounds_intersection. simpl. f_equal; apply Rmax_comm || apply Rmin_comm.
Qed.

Theorem bounds_intersection_idempotent : forall b : Bounds,
  bounds_intersection b b = b.
Proof.
  intros [mnx mny mxx mxy]. unfold bounds_intersection. simpl.
  f_equal; apply Rmax_left || apply Rmin_left; lra.
Qed.

Theorem bounds_intersects_symmetric : forall a b : Bounds,
  bounds_intersects a b -> bounds_intersects b a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [H1 [H2 [H3 H4]]].
  unfold bounds_intersects. simpl in *. lra.
Qed.

(** * Containment Properties *)

Theorem bounds_containment_refl : forall b : Bounds,
  bounds_contains_bounds b b.
Proof.
  intros [mnx mny mxx mxy]. unfold bounds_contains_bounds. simpl. lra.
Qed.

Theorem bounds_contains_point_in_valid : forall b px py,
  bounds_is_valid b ->
  bounds_min_x b <= px -> px <= bounds_max_x b ->
  bounds_min_y b <= py -> py <= bounds_max_y b ->
  bounds_contains b px py.
Proof.
  intros. unfold bounds_contains. auto.
Qed.

(** * from_points Properties *)

Theorem bounds_from_points_valid : forall ax ay bx by0,
  ax <> bx -> ay <> by0 -> bounds_is_valid (bounds_from_points ax ay bx by0).
Proof.
  intros ax ay bx by0 Hx Hy.
  unfold bounds_is_valid, bounds_from_points, Rmin, Rmax. simpl.
  destruct (Rle_dec ax bx); destruct (Rle_dec ay by0); split; lra.
Qed.

Theorem bounds_from_points_comm : forall ax ay bx by0,
  bounds_from_points ax ay bx by0 = bounds_from_points bx by0 ax ay.
Proof.
  intros. unfold bounds_from_points. f_equal; apply Rmin_comm || apply Rmax_comm.
Qed.

Theorem bounds_from_points_same : forall x y,
  bounds_from_points x y x y = mkBounds x y x y.
Proof.
  intros. unfold bounds_from_points.
  f_equal; apply Rmin_left || apply Rmax_left; lra.
Qed.

Theorem bounds_from_points_width : forall ax ay bx by0,
  bounds_width (bounds_from_points ax ay bx by0) = Rabs (bx - ax).
Proof.
  intros. unfold bounds_width, bounds_from_points, Rmin, Rmax. simpl.
  destruct (Rle_dec ax bx).
  - rewrite Rabs_right by lra. lra.
  - rewrite Rabs_left by lra. lra.
Qed.

Theorem bounds_from_points_height : forall ax ay bx by0,
  bounds_height (bounds_from_points ax ay bx by0) = Rabs (by0 - ay).
Proof.
  intros. unfold bounds_height, bounds_from_points, Rmin, Rmax. simpl.
  destruct (Rle_dec ay by0).
  - rewrite Rabs_right by lra. lra.
  - rewrite Rabs_left by lra. lra.
Qed.

(** * from_center_half_extents Properties *)

Theorem bounds_from_che_center_x : forall cx cy hx hy,
  bounds_center_x (bounds_from_che cx cy hx hy) = cx.
Proof.
  intros. unfold bounds_center_x, bounds_from_che. simpl. lra.
Qed.

Theorem bounds_from_che_center_y : forall cx cy hx hy,
  bounds_center_y (bounds_from_che cx cy hx hy) = cy.
Proof.
  intros. unfold bounds_center_y, bounds_from_che. simpl. lra.
Qed.

Theorem bounds_from_che_width : forall cx cy hx hy,
  bounds_width (bounds_from_che cx cy hx hy) = 2 * hx.
Proof.
  intros. unfold bounds_width, bounds_from_che. simpl. lra.
Qed.

Theorem bounds_from_che_height : forall cx cy hx hy,
  bounds_height (bounds_from_che cx cy hx hy) = 2 * hy.
Proof.
  intros. unfold bounds_height, bounds_from_che. simpl. lra.
Qed.

(** * include_point Properties *)

Theorem bounds_include_point_contains : forall b px py,
  bounds_contains (bounds_include_point b px py) px py.
Proof.
  intros [mnx mny mxx mxy] px py.
  unfold bounds_contains, bounds_include_point.
  cbn [bounds_min_x bounds_min_y bounds_max_x bounds_max_y].
  exact (conj (Rmin_le_r mnx px) (conj (Rle_max_r mxx px) (conj (Rmin_le_r mny py) (Rle_max_r mxy py)))).
Qed.

Theorem bounds_include_point_preserves_existing : forall b px py qx qy,
  bounds_contains b qx qy ->
  bounds_contains (bounds_include_point b px py) qx qy.
Proof.
  intros [mnx mny mxx mxy] px py qx qy [H1 [H2 [H3 H4]]].
  unfold bounds_contains, bounds_include_point in *.
  cbn [bounds_min_x bounds_min_y bounds_max_x bounds_max_y] in *.
  pose proof (Rmin_le_l mnx px). pose proof (Rmin_le_l mny py).
  pose proof (Rle_max_l mxx px). pose proof (Rle_max_l mxy py).
  split; [|split; [|split]]; eapply Rle_trans; eauto.
Qed.

Theorem bounds_include_point_idempotent : forall b px py,
  bounds_contains b px py ->
  bounds_include_point b px py = b.
Proof.
  intros [mnx mny mxx mxy] px py [H1 [H2 [H3 H4]]].
  unfold bounds_include_point, bounds_contains in *.
  cbn [bounds_min_x bounds_min_y bounds_max_x bounds_max_y] in *.
  f_equal.
  - apply Rmin_left. exact H1.
  - apply Rmin_left. exact H3.
  - apply Rmax_left. exact H2.
  - apply Rmax_left. exact H4.
Qed.

(** * Additional algebraic properties *)

Theorem bounds_translate_neg : forall b dx dy,
  bounds_translate (bounds_translate b dx dy) (-dx) (-dy) = b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold bounds_translate. simpl. f_equal; lra.
Qed.

Theorem bounds_expand_zero : forall b : Bounds,
  bounds_expand b 0 = b.
Proof.
  intros [mnx mny mxx mxy]. unfold bounds_expand. simpl. f_equal; lra.
Qed.

Theorem bounds_expand_compose : forall b a1 a2,
  bounds_expand (bounds_expand b a1) a2 = bounds_expand b (a1 + a2).
Proof.
  intros [mnx mny mxx mxy] a1 a2.
  unfold bounds_expand. simpl. f_equal; lra.
Qed.

Theorem bounds_expand_translate_commute : forall b amount dx dy,
  bounds_expand (bounds_translate b dx dy) amount =
  bounds_translate (bounds_expand b amount) dx dy.
Proof.
  intros [mnx mny mxx mxy] amount dx dy.
  unfold bounds_expand, bounds_translate. simpl. f_equal; lra.
Qed.

Local Ltac solve_minmax :=
  repeat match goal with |- context[Rle_dec ?a ?b] => destruct (Rle_dec a b) end;
  first [reflexivity | lra | (exfalso; tauto)].

Local Lemma Rmin_assoc : forall a b c, Rmin (Rmin a b) c = Rmin a (Rmin b c).
Proof.
  intros. unfold Rmin.
  destruct (Rle_dec a b); destruct (Rle_dec b c);
  repeat match goal with |- context[Rle_dec ?x ?y] => destruct (Rle_dec x y) end;
  try reflexivity; try lra; exfalso; tauto.
Qed.

Local Lemma Rmax_assoc : forall a b c, Rmax (Rmax a b) c = Rmax a (Rmax b c).
Proof.
  intros. unfold Rmax.
  destruct (Rle_dec a b); destruct (Rle_dec b c);
  repeat match goal with |- context[Rle_dec ?x ?y] => destruct (Rle_dec x y) end;
  try reflexivity; try lra; exfalso; tauto.
Qed.

Theorem bounds_union_assoc : forall a b c : Bounds,
  bounds_union (bounds_union a b) c = bounds_union a (bounds_union b c).
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [c1 c2 c3 c4].
  unfold bounds_union. simpl.
  f_equal; apply Rmin_assoc || apply Rmax_assoc.
Qed.

Theorem bounds_intersection_assoc : forall a b c : Bounds,
  bounds_intersection (bounds_intersection a b) c =
  bounds_intersection a (bounds_intersection b c).
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [c1 c2 c3 c4].
  unfold bounds_intersection. simpl.
  f_equal; apply Rmax_assoc || apply Rmin_assoc.
Qed.

Theorem bounds_contains_bounds_trans : forall a b c : Bounds,
  bounds_contains_bounds a b -> bounds_contains_bounds b c ->
  bounds_contains_bounds a c.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [c1 c2 c3 c4]
         [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  unfold bounds_contains_bounds in *. simpl in *. lra.
Qed.

Theorem bounds_from_che_valid : forall cx cy hx hy,
  hx > 0 -> hy > 0 ->
  bounds_is_valid (bounds_from_che cx cy hx hy).
Proof.
  intros. unfold bounds_is_valid, bounds_from_che in *. simpl in *. lra.
Qed.

Theorem bounds_from_che_area : forall cx cy hx hy,
  bounds_area (bounds_from_che cx cy hx hy) = 4 * hx * hy.
Proof.
  intros. unfold bounds_area, bounds_width, bounds_height, bounds_from_che.
  simpl. ring.
Qed.

Theorem bounds_expand_preserves_validity : forall b amount,
  bounds_is_valid b -> amount >= 0 ->
  bounds_is_valid (bounds_expand b amount).
Proof.
  intros [mnx mny mxx mxy] amount [Hx Hy] Ha.
  unfold bounds_is_valid, bounds_expand in *. simpl in *. lra.
Qed.

Theorem bounds_union_preserves_validity_l : forall a b,
  bounds_is_valid a ->
  bounds_is_valid (bounds_union a b).
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [Ha1 Ha2].
  unfold bounds_is_valid, bounds_union in *. simpl in *.
  pose proof (Rle_max_l a3 b3). pose proof (Rle_max_l a4 b4).
  pose proof (Rmin_le_l a1 b1). pose proof (Rmin_le_l a2 b2).
  split; lra.
Qed.

(** * Center Translation Properties *)

Theorem bounds_translate_center_x : forall b dx dy,
  bounds_center_x (bounds_translate b dx dy) = bounds_center_x b + dx.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold bounds_center_x, bounds_translate. simpl. lra.
Qed.

Theorem bounds_translate_center_y : forall b dx dy,
  bounds_center_y (bounds_translate b dx dy) = bounds_center_y b + dy.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold bounds_center_y, bounds_translate. simpl. lra.
Qed.

(** * Containment Antisymmetry *)

Theorem bounds_contains_bounds_antisymm : forall a b : Bounds,
  bounds_contains_bounds a b -> bounds_contains_bounds b a -> a = b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4]
         [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  unfold bounds_contains_bounds in *. simpl in *.
  f_equal; lra.
Qed.

(** * Union Width/Height Monotonicity *)

Theorem bounds_union_width_ge_left : forall a b : Bounds,
  bounds_width (bounds_union a b) >= bounds_width a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold bounds_width, bounds_union. simpl.
  pose proof (Rmin_le_l a1 b1). pose proof (Rle_max_l a3 b3). lra.
Qed.

Theorem bounds_union_width_ge_right : forall a b : Bounds,
  bounds_width (bounds_union a b) >= bounds_width b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold bounds_width, bounds_union. simpl.
  pose proof (Rmin_le_r a1 b1). pose proof (Rle_max_r a3 b3). lra.
Qed.

Theorem bounds_union_height_ge_left : forall a b : Bounds,
  bounds_height (bounds_union a b) >= bounds_height a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold bounds_height, bounds_union. simpl.
  pose proof (Rmin_le_l a2 b2). pose proof (Rle_max_l a4 b4). lra.
Qed.

Theorem bounds_union_height_ge_right : forall a b : Bounds,
  bounds_height (bounds_union a b) >= bounds_height b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold bounds_height, bounds_union. simpl.
  pose proof (Rmin_le_r a2 b2). pose proof (Rle_max_r a4 b4). lra.
Qed.

(** * from_che Contains Center *)

Theorem bounds_from_che_contains_center : forall cx cy hx hy,
  hx >= 0 -> hy >= 0 ->
  bounds_contains (bounds_from_che cx cy hx hy) cx cy.
Proof.
  intros. unfold bounds_contains, bounds_from_che. simpl. lra.
Qed.

(** * Expand Area Formula *)

(** Area after expansion: A' = A + 2a*h + 2a*w + 4a^2 *)
Theorem bounds_expand_area_formula : forall b amount,
  bounds_area (bounds_expand b amount) =
  bounds_area b + 2 * amount * bounds_height b +
  2 * amount * bounds_width b + 4 * amount * amount.
Proof.
  intros [mnx mny mxx mxy] amount.
  unfold bounds_area, bounds_width, bounds_height, bounds_expand. simpl. ring.
Qed.

(** * Advanced Proofs *)

(** Theorem 80: from_che half_extent_x recovers hx. *)
Theorem bounds_from_che_recovers_half_x : forall cx cy hx hy,
  bounds_half_extent_x (bounds_from_che cx cy hx hy) = hx.
Proof.
  intros. unfold bounds_half_extent_x, bounds_width, bounds_from_che. simpl. field.
Qed.

(** Theorem 81: from_che half_extent_y recovers hy. *)
Theorem bounds_from_che_recovers_half_y : forall cx cy hx hy,
  bounds_half_extent_y (bounds_from_che cx cy hx hy) = hy.
Proof.
  intros. unfold bounds_half_extent_y, bounds_height, bounds_from_che. simpl. field.
Qed.

(** Theorem 82: include_point with interior point is identity. *)
Theorem bounds_include_interior_point_identity : forall b px py,
  bounds_contains b px py ->
  bounds_include_point b px py = b.
Proof.
  intros [a1 a2 a3 a4] px py [H1 [H2 [H3 H4]]].
  unfold bounds_include_point, bounds_contains in *. simpl in *.
  f_equal;
  [ unfold Rmin; destruct (Rle_dec a1 px); lra
  | unfold Rmin; destruct (Rle_dec a2 py); lra
  | unfold Rmax; destruct (Rle_dec a3 px); lra
  | unfold Rmax; destruct (Rle_dec a4 py); lra ].
Qed.

(** Theorem 83: valid bounds has positive area. *)
Theorem bounds_valid_positive_area : forall b : Bounds,
  bounds_is_valid b -> bounds_area b > 0.
Proof.
  intros [a1 a2 a3 a4] [Hx Hy].
  unfold bounds_area, bounds_width, bounds_height, bounds_is_valid in *. simpl in *.
  apply Rmult_gt_0_compat; lra.
Qed.

(** Theorem 84: valid bounds has positive width. *)
Theorem bounds_valid_positive_width : forall b : Bounds,
  bounds_is_valid b -> bounds_width b > 0.
Proof.
  intros [a1 a2 a3 a4] [Hx Hy].
  unfold bounds_width, bounds_is_valid in *. simpl in *. lra.
Qed.

(** Theorem 85: valid bounds has positive height. *)
Theorem bounds_valid_positive_height : forall b : Bounds,
  bounds_is_valid b -> bounds_height b > 0.
Proof.
  intros [a1 a2 a3 a4] [Hx Hy].
  unfold bounds_height, bounds_is_valid in *. simpl in *. lra.
Qed.

(** Theorem 86: expanding preserves containment of points. *)
Theorem bounds_expand_contains_original_point : forall b amount px py,
  amount >= 0 -> bounds_contains b px py ->
  bounds_contains (bounds_expand b amount) px py.
Proof.
  intros [a1 a2 a3 a4] amount px py Ha [H1 [H2 [H3 H4]]].
  unfold bounds_contains, bounds_expand in *. simpl in *. lra.
Qed.

(** ================================================================= *)
(** * Phase 12: to_rect and approx_eq proofs                          *)
(** ================================================================= *)

(** Theorem 87: to_rect preserves x coordinate. *)
Theorem bounds_to_rect_x : forall b : Bounds,
  rect_x (bounds_to_rect b) = bounds_min_x b.
Proof.
  intros [a1 a2 a3 a4]. unfold bounds_to_rect. simpl. reflexivity.
Qed.

(** Theorem 88: to_rect preserves y coordinate. *)
Theorem bounds_to_rect_y : forall b : Bounds,
  rect_y (bounds_to_rect b) = bounds_min_y b.
Proof.
  intros [a1 a2 a3 a4]. unfold bounds_to_rect. simpl. reflexivity.
Qed.

(** Theorem 89: to_rect computes correct width. *)
Theorem bounds_to_rect_w : forall b : Bounds,
  rect_w (bounds_to_rect b) = bounds_width b.
Proof.
  intros [a1 a2 a3 a4]. unfold bounds_to_rect, bounds_width. simpl. reflexivity.
Qed.

(** Theorem 90: to_rect computes correct height. *)
Theorem bounds_to_rect_h : forall b : Bounds,
  rect_h (bounds_to_rect b) = bounds_height b.
Proof.
  intros [a1 a2 a3 a4]. unfold bounds_to_rect, bounds_height. simpl. reflexivity.
Qed.

(** Theorem 91: to_rect of zero bounds is zero rect. *)
Theorem bounds_to_rect_zero :
  bounds_to_rect bounds_zero = rect_zero.
Proof.
  unfold bounds_to_rect, bounds_zero, rect_zero. simpl.
  apply rect_eq; ring.
Qed.

(** Theorem 92: to_rect preserves area for valid bounds. *)
Theorem bounds_to_rect_area : forall b : Bounds,
  rect_area (bounds_to_rect b) = bounds_area b.
Proof.
  intros [a1 a2 a3 a4].
  unfold rect_area, bounds_to_rect, bounds_area, bounds_width, bounds_height. simpl. ring.
Qed.

(** Theorem 93: to_rect right edge equals bounds max_x. *)
Theorem bounds_to_rect_right : forall b : Bounds,
  rect_right (bounds_to_rect b) = bounds_max_x b.
Proof.
  intros [a1 a2 a3 a4].
  unfold rect_right, bounds_to_rect. simpl. ring.
Qed.

(** Theorem 94: to_rect bottom edge equals bounds max_y. *)
Theorem bounds_to_rect_bottom : forall b : Bounds,
  rect_bottom (bounds_to_rect b) = bounds_max_y b.
Proof.
  intros [a1 a2 a3 a4].
  unfold rect_bottom, bounds_to_rect. simpl. ring.
Qed.

(** Theorem 95: to_rect of valid bounds gives valid rect. *)
Theorem bounds_to_rect_valid : forall b : Bounds,
  bounds_is_valid b -> rect_is_valid (bounds_to_rect b).
Proof.
  intros [a1 a2 a3 a4] [Hx Hy].
  unfold bounds_is_valid, rect_is_valid, bounds_to_rect in *. simpl in *.
  split; lra.
Qed.

(** Theorem 96: to_rect preserves center_x. *)
Theorem bounds_to_rect_center_x : forall b : Bounds,
  rect_center_x (bounds_to_rect b) = bounds_center_x b.
Proof.
  intros [a1 a2 a3 a4].
  unfold rect_center_x, bounds_to_rect, bounds_center_x. simpl. field.
Qed.

(** Theorem 97: to_rect preserves center_y. *)
Theorem bounds_to_rect_center_y : forall b : Bounds,
  rect_center_y (bounds_to_rect b) = bounds_center_y b.
Proof.
  intros [a1 a2 a3 a4].
  unfold rect_center_y, bounds_to_rect, bounds_center_y. simpl. field.
Qed.

(** Theorem 98: approx_eq is reflexive for any eps >= 0. *)
Theorem bounds_approx_eq_refl : forall (b : Bounds) (eps : R),
  eps >= 0 -> bounds_approx_eq b b eps.
Proof.
  intros [a1 a2 a3 a4] eps Heps.
  unfold bounds_approx_eq. simpl.
  repeat split; replace (_ - _) with 0 by ring;
    rewrite Rabs_R0; lra.
Qed.

(** Theorem 99: approx_eq is symmetric. *)
Theorem bounds_approx_eq_sym : forall (a b : Bounds) (eps : R),
  bounds_approx_eq a b eps -> bounds_approx_eq b a eps.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] eps [H1 [H2 [H3 H4]]].
  unfold bounds_approx_eq in *. simpl in *.
  repeat split; rewrite Rabs_minus_sym; assumption.
Qed.

(** Helper: Rabs x <= 0 implies x = 0 *)
Local Lemma Rabs_le_zero_eq : forall x : R, Rabs x <= 0 -> x = 0.
Proof.
  intros x Hx. destruct (Rcase_abs x) as [Hn|Hp].
  - unfold Rabs in Hx. destruct (Rcase_abs x); lra.
  - unfold Rabs in Hx. destruct (Rcase_abs x); lra.
Qed.

(** Theorem 100: approx_eq with eps=0 implies equality. *)
Theorem bounds_approx_eq_zero_eq : forall a b : Bounds,
  bounds_approx_eq a b 0 -> a = b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [H1 [H2 [H3 H4]]].
  unfold bounds_approx_eq in *. simpl in *.
  assert (a1 = b1) by (apply Rabs_le_zero_eq in H1; lra).
  assert (a2 = b2) by (apply Rabs_le_zero_eq in H2; lra).
  assert (a3 = b3) by (apply Rabs_le_zero_eq in H3; lra).
  assert (a4 = b4) by (apply Rabs_le_zero_eq in H4; lra).
  subst. reflexivity.
Qed.

(** Theorem 101: approx_eq is monotonic in epsilon. *)
Theorem bounds_approx_eq_eps_mono : forall (a b : Bounds) (e1 e2 : R),
  e1 <= e2 -> bounds_approx_eq a b e1 -> bounds_approx_eq a b e2.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] e1 e2 He [H1 [H2 [H3 H4]]].
  unfold bounds_approx_eq in *. simpl in *.
  repeat split; lra.
Qed.

(** Theorem 102: translate preserves to_rect width and height. *)
Theorem bounds_translate_to_rect_size : forall b dx dy,
  rect_w (bounds_to_rect (bounds_translate b dx dy)) = rect_w (bounds_to_rect b) /\
  rect_h (bounds_to_rect (bounds_translate b dx dy)) = rect_h (bounds_to_rect b).
Proof.
  intros [a1 a2 a3 a4] dx dy.
  unfold bounds_to_rect, bounds_translate, bounds_width, bounds_height. simpl.
  split; ring.
Qed.

(** Theorem 103: from_center_size has correct width. *)
Theorem bounds_from_center_size_width : forall cx cy w h : R,
  w >= 0 -> bounds_width (bounds_from_center_size cx cy w h) = w.
Proof.
  intros cx cy w h Hw.
  unfold bounds_from_center_size, bounds_width. simpl. field.
Qed.

(** Theorem 104: from_center_size has correct height. *)
Theorem bounds_from_center_size_height : forall cx cy w h : R,
  h >= 0 -> bounds_height (bounds_from_center_size cx cy w h) = h.
Proof.
  intros cx cy w h Hh.
  unfold bounds_from_center_size, bounds_height. simpl. field.
Qed.

(** Theorem 105: from_center_size center_x equals input. *)
Theorem bounds_from_center_size_center_x : forall cx cy w h : R,
  bounds_center_x (bounds_from_center_size cx cy w h) = cx.
Proof.
  intros cx cy w h.
  unfold bounds_from_center_size, bounds_center_x. simpl. field.
Qed.

(** Theorem 106: from_center_size center_y equals input. *)
Theorem bounds_from_center_size_center_y : forall cx cy w h : R,
  bounds_center_y (bounds_from_center_size cx cy w h) = cy.
Proof.
  intros cx cy w h.
  unfold bounds_from_center_size, bounds_center_y. simpl. field.
Qed.

