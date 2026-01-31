(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Bounds_Compute.v - Computational Bounding Box (Z-based, Extractable)
 *
 * Z-based computational formalization of 2D bounding boxes.
 * Defined by min/max corners (min_x, min_y, max_x, max_y).
 * Uses scaled integer arithmetic (1000 = 1.0).
 *
 * NOTE: Proofs involving definitions with Z subtraction in constructors
 * (zbounds_expand, zbounds_from_che) must avoid Coq's `simpl` tactic,
 * which over-reduces Z.sub into a form that `lia` cannot parse.
 * Use explicit projection unfolding or `cbv delta [...] beta iota` instead.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

(** * ZBounds Definition *)

Record ZBounds : Type := mkZBounds {
  zbounds_min_x : Z;
  zbounds_min_y : Z;
  zbounds_max_x : Z;
  zbounds_max_y : Z
}.

(** * Equality *)

Lemma zbounds_eq : forall mnx1 mny1 mxx1 mxy1 mnx2 mny2 mxx2 mxy2 : Z,
  mnx1 = mnx2 -> mny1 = mny2 -> mxx1 = mxx2 -> mxy1 = mxy2 ->
  mkZBounds mnx1 mny1 mxx1 mxy1 = mkZBounds mnx2 mny2 mxx2 mxy2.
Proof. intros. subst. reflexivity. Qed.

(** * Constructors *)

Definition zbounds_new (min_x min_y max_x max_y : Z) : ZBounds :=
  mkZBounds min_x min_y max_x max_y.

Definition zbounds_zero : ZBounds := mkZBounds 0 0 0 0.

Definition zbounds_from_points (ax ay bx by0 : Z) : ZBounds :=
  mkZBounds (Z.min ax bx) (Z.min ay by0) (Z.max ax bx) (Z.max ay by0).

Definition zbounds_from_che (cx cy hx hy : Z) : ZBounds :=
  mkZBounds (cx - hx) (cy - hy) (cx + hx) (cy + hy).

(** * Accessors *)

Definition zbounds_width (b : ZBounds) : Z := zbounds_max_x b - zbounds_min_x b.
Definition zbounds_height (b : ZBounds) : Z := zbounds_max_y b - zbounds_min_y b.
Definition zbounds_center_x (b : ZBounds) : Z := (zbounds_min_x b + zbounds_max_x b) / 2.
Definition zbounds_center_y (b : ZBounds) : Z := (zbounds_min_y b + zbounds_max_y b) / 2.
Definition zbounds_area (b : ZBounds) : Z := zbounds_width b * zbounds_height b.

(** * Predicates *)

Definition zbounds_is_valid (b : ZBounds) : Prop :=
  zbounds_max_x b > zbounds_min_x b /\ zbounds_max_y b > zbounds_min_y b.

Definition zbounds_contains (b : ZBounds) (px py : Z) : Prop :=
  zbounds_min_x b <= px /\ px <= zbounds_max_x b /\
  zbounds_min_y b <= py /\ py <= zbounds_max_y b.

Definition zbounds_contains_bounds (outer inner : ZBounds) : Prop :=
  zbounds_min_x outer <= zbounds_min_x inner /\
  zbounds_min_y outer <= zbounds_min_y inner /\
  zbounds_max_x inner <= zbounds_max_x outer /\
  zbounds_max_y inner <= zbounds_max_y outer.

(** * Transformations *)

Definition zbounds_translate (b : ZBounds) (dx dy : Z) : ZBounds :=
  mkZBounds (zbounds_min_x b + dx) (zbounds_min_y b + dy)
            (zbounds_max_x b + dx) (zbounds_max_y b + dy).

Definition zbounds_expand (b : ZBounds) (amount : Z) : ZBounds :=
  mkZBounds (zbounds_min_x b - amount) (zbounds_min_y b - amount)
            (zbounds_max_x b + amount) (zbounds_max_y b + amount).

Definition zbounds_shrink (b : ZBounds) (amount : Z) : ZBounds :=
  zbounds_expand b (- amount).

Definition zbounds_union (a b : ZBounds) : ZBounds :=
  mkZBounds (Z.min (zbounds_min_x a) (zbounds_min_x b))
            (Z.min (zbounds_min_y a) (zbounds_min_y b))
            (Z.max (zbounds_max_x a) (zbounds_max_x b))
            (Z.max (zbounds_max_y a) (zbounds_max_y b)).

Definition zbounds_intersection (a b : ZBounds) : ZBounds :=
  mkZBounds (Z.max (zbounds_min_x a) (zbounds_min_x b))
            (Z.max (zbounds_min_y a) (zbounds_min_y b))
            (Z.min (zbounds_max_x a) (zbounds_max_x b))
            (Z.min (zbounds_max_y a) (zbounds_max_y b)).

Definition zbounds_include_point (b : ZBounds) (px py : Z) : ZBounds :=
  mkZBounds (Z.min (zbounds_min_x b) px) (Z.min (zbounds_min_y b) py)
            (Z.max (zbounds_max_x b) px) (Z.max (zbounds_max_y b) py).

(** * Local tactic for subtraction-safe unfolding *)
(** Coq's [simpl] over-reduces Z.sub into forms [lia] cannot parse.
    This tactic unfolds all ZBounds definitions + projections without [simpl]. *)
Local Ltac zb_unfold :=
  unfold zbounds_width, zbounds_height, zbounds_area,
         zbounds_expand, zbounds_shrink, zbounds_translate,
         zbounds_union, zbounds_intersection, zbounds_include_point,
         zbounds_from_che, zbounds_from_points, zbounds_new, zbounds_zero,
         zbounds_is_valid, zbounds_contains, zbounds_contains_bounds,
         zbounds_center_x, zbounds_center_y,
         zbounds_min_x, zbounds_min_y, zbounds_max_x, zbounds_max_y.

(** * Constructor Properties *)

Theorem zbounds_new_min_x : forall mnx mny mxx mxy,
  zbounds_min_x (zbounds_new mnx mny mxx mxy) = mnx.
Proof. intros. reflexivity. Qed.

Theorem zbounds_new_min_y : forall mnx mny mxx mxy,
  zbounds_min_y (zbounds_new mnx mny mxx mxy) = mny.
Proof. intros. reflexivity. Qed.

Theorem zbounds_new_max_x : forall mnx mny mxx mxy,
  zbounds_max_x (zbounds_new mnx mny mxx mxy) = mxx.
Proof. intros. reflexivity. Qed.

Theorem zbounds_new_max_y : forall mnx mny mxx mxy,
  zbounds_max_y (zbounds_new mnx mny mxx mxy) = mxy.
Proof. intros. reflexivity. Qed.

Theorem zbounds_zero_width : zbounds_width zbounds_zero = 0.
Proof. reflexivity. Qed.

Theorem zbounds_zero_height : zbounds_height zbounds_zero = 0.
Proof. reflexivity. Qed.

Theorem zbounds_zero_area : zbounds_area zbounds_zero = 0.
Proof. reflexivity. Qed.

(** * Accessor Properties *)

Theorem zbounds_width_valid : forall b,
  zbounds_is_valid b -> zbounds_width b > 0.
Proof.
  intros [mnx mny mxx mxy] [Hx Hy].
  unfold zbounds_width, zbounds_is_valid in *. simpl in *. lia.
Qed.

Theorem zbounds_height_valid : forall b,
  zbounds_is_valid b -> zbounds_height b > 0.
Proof.
  intros [mnx mny mxx mxy] [Hx Hy].
  unfold zbounds_height, zbounds_is_valid in *. simpl in *. lia.
Qed.

Theorem zbounds_area_valid : forall b,
  zbounds_is_valid b -> zbounds_area b > 0.
Proof.
  intros [mnx mny mxx mxy] [Hx Hy].
  unfold zbounds_area, zbounds_width, zbounds_height, zbounds_is_valid in *.
  simpl in *. nia.
Qed.

Theorem zbounds_width_nonneg_of_le : forall b,
  zbounds_min_x b <= zbounds_max_x b -> zbounds_width b >= 0.
Proof.
  intros [mnx mny mxx mxy] H. unfold zbounds_width. simpl in *. lia.
Qed.

Theorem zbounds_height_nonneg_of_le : forall b,
  zbounds_min_y b <= zbounds_max_y b -> zbounds_height b >= 0.
Proof.
  intros [mnx mny mxx mxy] H. unfold zbounds_height. simpl in *. lia.
Qed.

(** * Translate Properties *)

Theorem zbounds_translate_identity : forall b,
  zbounds_translate b 0 0 = b.
Proof.
  intros [mnx mny mxx mxy]. unfold zbounds_translate. simpl. f_equal; lia.
Qed.

Theorem zbounds_translate_compose : forall b dx1 dy1 dx2 dy2,
  zbounds_translate (zbounds_translate b dx1 dy1) dx2 dy2 =
  zbounds_translate b (dx1 + dx2) (dy1 + dy2).
Proof.
  intros [mnx mny mxx mxy] dx1 dy1 dx2 dy2.
  unfold zbounds_translate. simpl. f_equal; lia.
Qed.

Theorem zbounds_translate_commute : forall b dx1 dy1 dx2 dy2,
  zbounds_translate (zbounds_translate b dx1 dy1) dx2 dy2 =
  zbounds_translate (zbounds_translate b dx2 dy2) dx1 dy1.
Proof.
  intros [mnx mny mxx mxy] dx1 dy1 dx2 dy2.
  unfold zbounds_translate. simpl. f_equal; lia.
Qed.

Theorem zbounds_translate_preserves_width : forall b dx dy,
  zbounds_width (zbounds_translate b dx dy) = zbounds_width b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold zbounds_width, zbounds_translate. simpl. lia.
Qed.

Theorem zbounds_translate_preserves_height : forall b dx dy,
  zbounds_height (zbounds_translate b dx dy) = zbounds_height b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold zbounds_height, zbounds_translate. simpl. lia.
Qed.

Theorem zbounds_translate_preserves_area : forall b dx dy,
  zbounds_area (zbounds_translate b dx dy) = zbounds_area b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold zbounds_area, zbounds_width, zbounds_height, zbounds_translate.
  simpl. f_equal; lia.
Qed.

Theorem zbounds_translate_neg : forall b dx dy,
  zbounds_translate (zbounds_translate b dx dy) (-dx) (-dy) = b.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold zbounds_translate. simpl. f_equal; lia.
Qed.

Theorem zbounds_translate_preserves_validity : forall b dx dy,
  zbounds_is_valid b -> zbounds_is_valid (zbounds_translate b dx dy).
Proof.
  intros [mnx mny mxx mxy] dx dy [Hx Hy].
  unfold zbounds_is_valid, zbounds_translate in *. simpl in *. lia.
Qed.

Theorem zbounds_translate_preserves_contains : forall b px py dx dy,
  zbounds_contains b px py ->
  zbounds_contains (zbounds_translate b dx dy) (px + dx) (py + dy).
Proof.
  intros [mnx mny mxx mxy] px py dx dy [H1 [H2 [H3 H4]]].
  unfold zbounds_contains, zbounds_translate in *. simpl in *. lia.
Qed.

(** * Expand Properties *)

Theorem zbounds_expand_width : forall b amount,
  zbounds_width (zbounds_expand b amount) = zbounds_width b + 2 * amount.
Proof.
  intros [mnx mny mxx mxy] amount. zb_unfold. lia.
Qed.

Theorem zbounds_expand_height : forall b amount,
  zbounds_height (zbounds_expand b amount) = zbounds_height b + 2 * amount.
Proof.
  intros [mnx mny mxx mxy] amount. zb_unfold. lia.
Qed.

Theorem zbounds_expand_zero : forall b,
  zbounds_expand b 0 = b.
Proof.
  intros [mnx mny mxx mxy]. zb_unfold. f_equal; lia.
Qed.

Theorem zbounds_expand_compose : forall b a1 a2,
  zbounds_expand (zbounds_expand b a1) a2 = zbounds_expand b (a1 + a2).
Proof.
  intros [mnx mny mxx mxy] a1 a2. zb_unfold. f_equal; lia.
Qed.

Theorem zbounds_expand_preserves_validity : forall b amount,
  zbounds_is_valid b -> amount >= 0 ->
  zbounds_is_valid (zbounds_expand b amount).
Proof.
  intros [mnx mny mxx mxy] amount [Hx Hy] Ha.
  unfold zbounds_is_valid, zbounds_expand in *. simpl in *. lia.
Qed.

Theorem zbounds_expand_wider : forall b amount,
  amount >= 0 ->
  zbounds_width (zbounds_expand b amount) >= zbounds_width b.
Proof.
  intros [mnx mny mxx mxy] amount Ha. zb_unfold. lia.
Qed.

Theorem zbounds_expand_taller : forall b amount,
  amount >= 0 ->
  zbounds_height (zbounds_expand b amount) >= zbounds_height b.
Proof.
  intros [mnx mny mxx mxy] amount Ha. zb_unfold. lia.
Qed.

Theorem zbounds_expand_contains_original : forall b amount px py,
  amount >= 0 -> zbounds_contains b px py ->
  zbounds_contains (zbounds_expand b amount) px py.
Proof.
  intros [mnx mny mxx mxy] amount px py Ha [H1 [H2 [H3 H4]]].
  unfold zbounds_contains, zbounds_expand in *. simpl in *. lia.
Qed.

Theorem zbounds_expand_contains_bounds : forall b amount,
  amount >= 0 -> zbounds_contains_bounds (zbounds_expand b amount) b.
Proof.
  intros [mnx mny mxx mxy] amount Ha.
  unfold zbounds_contains_bounds, zbounds_expand in *. simpl in *. lia.
Qed.

(** * Shrink Properties *)

Theorem zbounds_shrink_zero : forall b,
  zbounds_shrink b 0 = b.
Proof.
  intros. unfold zbounds_shrink.
  replace (- 0) with 0 by lia. apply zbounds_expand_zero.
Qed.

Theorem zbounds_shrink_expand_inverse : forall b amount,
  zbounds_shrink (zbounds_expand b amount) amount = b.
Proof.
  intros. unfold zbounds_shrink.
  rewrite zbounds_expand_compose.
  replace (amount + - amount) with 0 by lia. apply zbounds_expand_zero.
Qed.

Theorem zbounds_expand_shrink_inverse : forall b amount,
  zbounds_expand (zbounds_shrink b amount) amount = b.
Proof.
  intros. unfold zbounds_shrink.
  rewrite zbounds_expand_compose.
  replace (- amount + amount) with 0 by lia. apply zbounds_expand_zero.
Qed.

Theorem zbounds_shrink_width : forall b amount,
  zbounds_width (zbounds_shrink b amount) = zbounds_width b - 2 * amount.
Proof.
  intros. unfold zbounds_shrink.
  rewrite zbounds_expand_width. lia.
Qed.

Theorem zbounds_shrink_height : forall b amount,
  zbounds_height (zbounds_shrink b amount) = zbounds_height b - 2 * amount.
Proof.
  intros. unfold zbounds_shrink.
  rewrite zbounds_expand_height. lia.
Qed.

(** * Union Properties *)

Theorem zbounds_union_comm : forall a b,
  zbounds_union a b = zbounds_union b a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_union. simpl. f_equal; lia.
Qed.

Theorem zbounds_union_idempotent : forall b,
  zbounds_union b b = b.
Proof.
  intros [mnx mny mxx mxy]. unfold zbounds_union. simpl. f_equal; lia.
Qed.

Theorem zbounds_union_assoc : forall a b c,
  zbounds_union (zbounds_union a b) c = zbounds_union a (zbounds_union b c).
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [c1 c2 c3 c4].
  unfold zbounds_union. simpl. f_equal; lia.
Qed.

Theorem zbounds_union_contains_left : forall a b,
  zbounds_contains_bounds (zbounds_union a b) a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_contains_bounds, zbounds_union. simpl.
  repeat split; lia.
Qed.

Theorem zbounds_union_contains_right : forall a b,
  zbounds_contains_bounds (zbounds_union a b) b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_contains_bounds, zbounds_union. simpl.
  repeat split; lia.
Qed.

(** * Intersection Properties *)

Theorem zbounds_intersection_comm : forall a b,
  zbounds_intersection a b = zbounds_intersection b a.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_intersection. simpl. f_equal; lia.
Qed.

Theorem zbounds_intersection_idempotent : forall b,
  zbounds_intersection b b = b.
Proof.
  intros [mnx mny mxx mxy]. unfold zbounds_intersection. simpl. f_equal; lia.
Qed.

Theorem zbounds_intersection_assoc : forall a b c,
  zbounds_intersection (zbounds_intersection a b) c =
  zbounds_intersection a (zbounds_intersection b c).
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [c1 c2 c3 c4].
  unfold zbounds_intersection. simpl. f_equal; lia.
Qed.

Theorem zbounds_intersection_sub_left : forall a b,
  zbounds_contains_bounds a (zbounds_intersection a b).
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_contains_bounds, zbounds_intersection. simpl.
  repeat split; lia.
Qed.

Theorem zbounds_intersection_sub_right : forall a b,
  zbounds_contains_bounds b (zbounds_intersection a b).
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_contains_bounds, zbounds_intersection. simpl.
  repeat split; lia.
Qed.

(** * Include Point Properties *)

Theorem zbounds_include_point_contains : forall b px py,
  zbounds_contains (zbounds_include_point b px py) px py.
Proof.
  intros [mnx mny mxx mxy] px py.
  unfold zbounds_contains, zbounds_include_point. simpl.
  repeat split; lia.
Qed.

Theorem zbounds_include_point_preserves : forall b px py qx qy,
  zbounds_contains b qx qy ->
  zbounds_contains (zbounds_include_point b px py) qx qy.
Proof.
  intros [mnx mny mxx mxy] px py qx qy [H1 [H2 [H3 H4]]].
  unfold zbounds_contains, zbounds_include_point in *. simpl in *.
  repeat split; lia.
Qed.

Theorem zbounds_include_point_idempotent : forall b px py,
  zbounds_contains b px py ->
  zbounds_include_point b px py = b.
Proof.
  intros [mnx mny mxx mxy] px py [H1 [H2 [H3 H4]]].
  unfold zbounds_include_point, zbounds_contains in *. simpl in *.
  f_equal; lia.
Qed.

(** * from_che Properties *)

Theorem zbounds_from_che_width : forall cx cy hx hy,
  zbounds_width (zbounds_from_che cx cy hx hy) = 2 * hx.
Proof.
  intros. zb_unfold. lia.
Qed.

Theorem zbounds_from_che_height : forall cx cy hx hy,
  zbounds_height (zbounds_from_che cx cy hx hy) = 2 * hy.
Proof.
  intros. zb_unfold. lia.
Qed.

Theorem zbounds_from_che_valid : forall cx cy hx hy,
  hx > 0 -> hy > 0 ->
  zbounds_is_valid (zbounds_from_che cx cy hx hy).
Proof.
  intros cx cy hx hy Hhx Hhy. zb_unfold. lia.
Qed.

Theorem zbounds_from_che_symmetric : forall cx cy hx hy,
  zbounds_from_che cx cy hx hy =
  mkZBounds (cx - hx) (cy - hy) (cx + hx) (cy + hy).
Proof. intros. reflexivity. Qed.

(** * from_points Properties *)

Theorem zbounds_from_points_comm : forall ax ay bx by0,
  zbounds_from_points ax ay bx by0 = zbounds_from_points bx by0 ax ay.
Proof.
  intros. unfold zbounds_from_points. f_equal; lia.
Qed.

Theorem zbounds_from_points_valid : forall ax ay bx by0,
  ax <> bx -> ay <> by0 ->
  zbounds_is_valid (zbounds_from_points ax ay bx by0).
Proof.
  intros ax ay bx by0 Hx Hy.
  unfold zbounds_is_valid, zbounds_from_points. simpl. split; lia.
Qed.

Theorem zbounds_from_points_contains_first : forall ax ay bx by0,
  zbounds_contains (zbounds_from_points ax ay bx by0) ax ay.
Proof.
  intros. unfold zbounds_contains, zbounds_from_points. simpl.
  repeat split; lia.
Qed.

Theorem zbounds_from_points_contains_second : forall ax ay bx by0,
  zbounds_contains (zbounds_from_points ax ay bx by0) bx by0.
Proof.
  intros. unfold zbounds_contains, zbounds_from_points. simpl.
  repeat split; lia.
Qed.

Theorem zbounds_from_points_idempotent : forall ax ay,
  zbounds_from_points ax ay ax ay = zbounds_new ax ay ax ay.
Proof.
  intros. unfold zbounds_from_points, zbounds_new. f_equal; lia.
Qed.

(** * Contains Properties *)

Theorem zbounds_contains_bounds_refl : forall b,
  zbounds_contains_bounds b b.
Proof.
  intros [mnx mny mxx mxy].
  unfold zbounds_contains_bounds. simpl. lia.
Qed.

Theorem zbounds_contains_bounds_trans : forall a b c,
  zbounds_contains_bounds a b -> zbounds_contains_bounds b c ->
  zbounds_contains_bounds a c.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4] [c1 c2 c3 c4]
         [Ha1 [Ha2 [Ha3 Ha4]]] [Hb1 [Hb2 [Hb3 Hb4]]].
  unfold zbounds_contains_bounds in *. simpl in *. lia.
Qed.

Theorem zbounds_contains_point_of_bounds : forall outer inner px py,
  zbounds_contains_bounds outer inner ->
  zbounds_contains inner px py ->
  zbounds_contains outer px py.
Proof.
  intros [o1 o2 o3 o4] [i1 i2 i3 i4] px py
         [Ho1 [Ho2 [Ho3 Ho4]]] [Hi1 [Hi2 [Hi3 Hi4]]].
  unfold zbounds_contains_bounds, zbounds_contains in *. simpl in *. lia.
Qed.

(** * Mixed Transform Properties *)

Theorem zbounds_translate_expand_comm : forall b dx dy amount,
  zbounds_translate (zbounds_expand b amount) dx dy =
  zbounds_expand (zbounds_translate b dx dy) amount.
Proof.
  intros [mnx mny mxx mxy] dx dy amount. zb_unfold. f_equal; lia.
Qed.

(** * Computational Tests *)

Example zbounds_new_test :
  zbounds_min_x (zbounds_new 100 200 500 600) = 100.
Proof. reflexivity. Qed.

Example zbounds_width_test :
  zbounds_width (zbounds_new 100 200 500 600) = 400.
Proof. reflexivity. Qed.

Example zbounds_height_test :
  zbounds_height (zbounds_new 100 200 500 600) = 400.
Proof. reflexivity. Qed.

Example zbounds_area_test :
  zbounds_area (zbounds_new 100 200 500 600) = 160000.
Proof. reflexivity. Qed.

Example zbounds_translate_test :
  zbounds_translate (zbounds_new 100 200 500 600) 50 50 =
  zbounds_new 150 250 550 650.
Proof. reflexivity. Qed.

Example zbounds_expand_test :
  zbounds_expand (zbounds_new 100 200 500 600) 10 =
  zbounds_new 90 190 510 610.
Proof. reflexivity. Qed.

Example zbounds_union_test :
  zbounds_union (zbounds_new 0 0 100 100) (zbounds_new 50 50 200 200) =
  zbounds_new 0 0 200 200.
Proof. reflexivity. Qed.

Example zbounds_intersection_test :
  zbounds_intersection (zbounds_new 0 0 100 100) (zbounds_new 50 50 200 200) =
  zbounds_new 50 50 100 100.
Proof. reflexivity. Qed.

Example zbounds_from_che_test :
  zbounds_from_che 500 500 200 100 = zbounds_new 300 400 700 600.
Proof. reflexivity. Qed.

Example zbounds_from_points_test :
  zbounds_from_points 500 600 100 200 = zbounds_new 100 200 500 600.
Proof. reflexivity. Qed.

Example zbounds_include_point_test :
  zbounds_include_point (zbounds_new 100 100 200 200) 300 50 =
  zbounds_new 100 50 300 200.
Proof. reflexivity. Qed.

Example zbounds_shrink_test :
  zbounds_shrink (zbounds_new 100 200 500 600) 10 =
  zbounds_new 110 210 490 590.
Proof. reflexivity. Qed.

(** * Center Translation Properties *)

Theorem zbounds_translate_center_x : forall b dx dy,
  zbounds_center_x (zbounds_translate b dx dy) = zbounds_center_x b + dx.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold zbounds_center_x, zbounds_translate. simpl.
  replace (mnx + dx + (mxx + dx)) with (dx * 2 + (mnx + mxx)) by lia.
  rewrite Z.div_add_l by lia.
  lia.
Qed.

Theorem zbounds_translate_center_y : forall b dx dy,
  zbounds_center_y (zbounds_translate b dx dy) = zbounds_center_y b + dy.
Proof.
  intros [mnx mny mxx mxy] dx dy.
  unfold zbounds_center_y, zbounds_translate. simpl.
  replace (mny + dy + (mxy + dy)) with (dy * 2 + (mny + mxy)) by lia.
  rewrite Z.div_add_l by lia.
  lia.
Qed.

(** * Containment Antisymmetry *)

Theorem zbounds_contains_bounds_antisymm : forall a b : ZBounds,
  zbounds_contains_bounds a b -> zbounds_contains_bounds b a -> a = b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4]
         [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]].
  unfold zbounds_contains_bounds in *. simpl in *.
  f_equal; lia.
Qed.

(** * Union Width/Height Monotonicity *)

Theorem zbounds_union_wider : forall a b : ZBounds,
  zbounds_width (zbounds_union a b) >= zbounds_width a /\
  zbounds_width (zbounds_union a b) >= zbounds_width b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_width, zbounds_union. simpl.
  split; lia.
Qed.

Theorem zbounds_union_taller : forall a b : ZBounds,
  zbounds_height (zbounds_union a b) >= zbounds_height a /\
  zbounds_height (zbounds_union a b) >= zbounds_height b.
Proof.
  intros [a1 a2 a3 a4] [b1 b2 b3 b4].
  unfold zbounds_height, zbounds_union. simpl.
  split; lia.
Qed.

(** * from_che Area and Contains Center *)

Theorem zbounds_from_che_area : forall cx cy hx hy,
  zbounds_area (zbounds_from_che cx cy hx hy) = 4 * hx * hy.
Proof.
  intros cx cy hx hy.
  unfold zbounds_area.
  rewrite zbounds_from_che_width.
  rewrite zbounds_from_che_height.
  ring.
Qed.

Theorem zbounds_from_che_contains_center : forall cx cy hx hy,
  hx >= 0 -> hy >= 0 ->
  zbounds_contains (zbounds_from_che cx cy hx hy) cx cy.
Proof.
  intros cx cy hx hy Hhx Hhy.
  unfold zbounds_contains, zbounds_from_che. simpl. lia.
Qed.

(** * Expand Area Formula *)

Theorem zbounds_expand_area_formula : forall b amount,
  zbounds_area (zbounds_expand b amount) =
  zbounds_area b + 2 * amount * zbounds_height b +
  2 * amount * zbounds_width b + 4 * amount * amount.
Proof.
  intros b amount. unfold zbounds_area at 1.
  rewrite zbounds_expand_width.
  rewrite zbounds_expand_height.
  unfold zbounds_area. ring.
Qed.
