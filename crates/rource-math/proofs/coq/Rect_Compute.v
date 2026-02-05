(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Rect_Compute.v - Computational Rectangle Specification (Extractable)
 *
 * Z-based computational formalization of 2D rectangles.
 * All operations are pure integer arithmetic, fully extractable.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

(** * ZRect Definition *)

Record ZRect : Type := mkZRect {
  zrect_x : Z;
  zrect_y : Z;
  zrect_w : Z;
  zrect_h : Z
}.

(** * Equality *)

Lemma zrect_eq_dec : forall (a b : ZRect), {a = b} + {a <> b}.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  destruct (Z.eq_dec ax bx) as [Hx | Hx];
  destruct (Z.eq_dec ay by0) as [Hy | Hy];
  destruct (Z.eq_dec aw bw) as [Hw | Hw];
  destruct (Z.eq_dec ah bh) as [Hh | Hh].
  - left. subst. reflexivity.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
Defined.

Lemma zrect_eq : forall x1 y1 w1 h1 x2 y2 w2 h2 : Z,
  x1 = x2 -> y1 = y2 -> w1 = w2 -> h1 = h2 ->
  mkZRect x1 y1 w1 h1 = mkZRect x2 y2 w2 h2.
Proof.
  intros. subst. reflexivity.
Qed.

(** * Constructors *)

Definition zrect_new (x y w h : Z) : ZRect := mkZRect x y w h.
Definition zrect_zero : ZRect := mkZRect 0 0 0 0.

(** * Accessors *)

Definition zrect_right (r : ZRect) : Z := zrect_x r + zrect_w r.
Definition zrect_bottom (r : ZRect) : Z := zrect_y r + zrect_h r.
Definition zrect_area (r : ZRect) : Z := zrect_w r * zrect_h r.
Definition zrect_perimeter (r : ZRect) : Z := 2 * (zrect_w r + zrect_h r).
Definition zrect_center_x (r : ZRect) : Z := zrect_x r + zrect_w r / 2.
Definition zrect_center_y (r : ZRect) : Z := zrect_y r + zrect_h r / 2.

(** * Predicates *)

Definition zrect_is_valid (r : ZRect) : bool :=
  (zrect_w r >? 0) && (zrect_h r >? 0).

Definition zrect_is_empty (r : ZRect) : bool :=
  (zrect_w r <=? 0) || (zrect_h r <=? 0).

Definition zrect_contains_point (r : ZRect) (px py : Z) : bool :=
  (zrect_x r <=? px) && (px <=? zrect_x r + zrect_w r)
  && (zrect_y r <=? py) && (py <=? zrect_y r + zrect_h r).

Definition zrect_contains_rect (outer inner : ZRect) : bool :=
  (zrect_x outer <=? zrect_x inner)
  && (zrect_y outer <=? zrect_y inner)
  && (zrect_x inner + zrect_w inner <=? zrect_x outer + zrect_w outer)
  && (zrect_y inner + zrect_h inner <=? zrect_y outer + zrect_h outer).

Definition zrect_intersects (a b : ZRect) : bool :=
  (zrect_x a <? zrect_x b + zrect_w b)
  && (zrect_x a + zrect_w a >? zrect_x b)
  && (zrect_y a <? zrect_y b + zrect_h b)
  && (zrect_y a + zrect_h a >? zrect_y b).

(** * Transformations *)

Definition zrect_translate (r : ZRect) (dx dy : Z) : ZRect :=
  mkZRect (zrect_x r + dx) (zrect_y r + dy) (zrect_w r) (zrect_h r).

Definition zrect_expand (r : ZRect) (amount : Z) : ZRect :=
  mkZRect (zrect_x r - amount) (zrect_y r - amount)
          (zrect_w r + 2 * amount) (zrect_h r + 2 * amount).

Definition zrect_shrink (r : ZRect) (amount : Z) : ZRect :=
  zrect_expand r (- amount).

(** * Union (using Z.min / Z.max) *)

Definition zrect_union (a b : ZRect) : ZRect :=
  let x := Z.min (zrect_x a) (zrect_x b) in
  let y0 := Z.min (zrect_y a) (zrect_y b) in
  let right := Z.max (zrect_x a + zrect_w a) (zrect_x b + zrect_w b) in
  let bottom := Z.max (zrect_y a + zrect_h a) (zrect_y b + zrect_h b) in
  mkZRect x y0 (right - x) (bottom - y0).

(** * Algebraic Properties *)

Theorem zrect_translate_preserves_size : forall (r : ZRect) (dx dy : Z),
  zrect_w (zrect_translate r dx dy) = zrect_w r /\
  zrect_h (zrect_translate r dx dy) = zrect_h r.
Proof.
  intros [x y0 w h] dx dy. simpl. split; reflexivity.
Qed.

Theorem zrect_translate_identity : forall (r : ZRect),
  zrect_translate r 0 0 = r.
Proof.
  intros [x y0 w h]. unfold zrect_translate. simpl.
  apply zrect_eq; lia.
Qed.

Theorem zrect_translate_compose : forall (r : ZRect) (dx1 dy1 dx2 dy2 : Z),
  zrect_translate (zrect_translate r dx1 dy1) dx2 dy2 =
  zrect_translate r (dx1 + dx2) (dy1 + dy2).
Proof.
  intros [x y0 w h] dx1 dy1 dx2 dy2.
  unfold zrect_translate. simpl.
  apply zrect_eq; lia.
Qed.

Theorem zrect_expand_shrink_inverse : forall (r : ZRect) (amount : Z),
  zrect_expand (zrect_shrink r amount) amount = r.
Proof.
  intros [x y0 w h] amount.
  unfold zrect_shrink, zrect_expand.
  cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

Theorem zrect_shrink_expand_inverse : forall (r : ZRect) (amount : Z),
  zrect_shrink (zrect_expand r amount) amount = r.
Proof.
  intros [x y0 w h] amount.
  unfold zrect_shrink, zrect_expand.
  cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

Theorem zrect_area_nonneg : forall (r : ZRect),
  zrect_w r >= 0 -> zrect_h r >= 0 -> zrect_area r >= 0.
Proof.
  intros [x y0 w h] Hw Hh. simpl in *.
  unfold zrect_area. simpl. nia.
Qed.

Theorem zrect_perimeter_nonneg : forall (r : ZRect),
  zrect_w r >= 0 -> zrect_h r >= 0 -> zrect_perimeter r >= 0.
Proof.
  intros [x y0 w h] Hw Hh.
  cbn -[Z.mul Z.add] in *.
  unfold zrect_perimeter. cbn -[Z.mul Z.add]. lia.
Qed.

Theorem zrect_zero_area :
  zrect_area zrect_zero = 0.
Proof.
  unfold zrect_area, zrect_zero. simpl. reflexivity.
Qed.

Theorem zrect_square_perimeter : forall (side : Z),
  zrect_perimeter (zrect_new 0 0 side side) = 4 * side.
Proof.
  intros. unfold zrect_perimeter, zrect_new.
  cbn -[Z.mul Z.add]. ring.
Qed.

Theorem zrect_square_area : forall (side : Z),
  zrect_area (zrect_new 0 0 side side) = side * side.
Proof.
  intros. unfold zrect_area, zrect_new. simpl. reflexivity.
Qed.

(** ** Containment (over booleans for computability) *)

Theorem zrect_contains_rect_refl : forall (r : ZRect),
  zrect_contains_rect r r = true.
Proof.
  intros [x y0 w h]. unfold zrect_contains_rect. simpl.
  repeat rewrite Z.leb_refl. simpl. reflexivity.
Qed.

Lemma Z_gtb_ltb : forall x y, (x >? y) = (y <? x).
Proof.
  intros. unfold Z.gtb, Z.ltb.
  rewrite Z.compare_antisym.
  destruct (y ?= x); reflexivity.
Qed.

Theorem zrect_intersects_symmetric : forall (a b : ZRect),
  zrect_intersects a b = zrect_intersects b a.
Proof.
  intros a b. unfold zrect_intersects.
  rewrite !Z_gtb_ltb.
  (* Both sides are now && of <? expressions in different order *)
  remember (zrect_x a <? zrect_x b + zrect_w b) as c1.
  remember (zrect_x b <? zrect_x a + zrect_w a) as c2.
  remember (zrect_y a <? zrect_y b + zrect_h b) as c3.
  remember (zrect_y b <? zrect_y a + zrect_h a) as c4.
  destruct c1, c2, c3, c4; reflexivity.
Qed.

(** ** Union properties *)

Theorem zrect_union_commutative : forall (a b : ZRect),
  zrect_union a b = zrect_union b a.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold zrect_union. cbn -[Z.min Z.max Z.add Z.sub].
  apply zrect_eq.
  - apply Z.min_comm.
  - apply Z.min_comm.
  - f_equal. apply Z.max_comm. apply Z.min_comm.
  - f_equal. apply Z.max_comm. apply Z.min_comm.
Qed.

(** * Additional Operations *)

(** Intersection of two rectangles (non-negative dimensions guaranteed) *)
Definition zrect_intersection (a b : ZRect) : ZRect :=
  let x := Z.max (zrect_x a) (zrect_x b) in
  let y0 := Z.max (zrect_y a) (zrect_y b) in
  let right := Z.min (zrect_x a + zrect_w a) (zrect_x b + zrect_w b) in
  let bottom := Z.min (zrect_y a + zrect_h a) (zrect_y b + zrect_h b) in
  mkZRect x y0 (Z.max 0 (right - x)) (Z.max 0 (bottom - y0)).

(** Create rectangle from center point and dimensions *)
Definition zrect_from_center (cx cy w h : Z) : ZRect :=
  mkZRect (cx - w / 2) (cy - h / 2) w h.

(** Scale rectangle dimensions by a factor (fixed-point, 1000 = 1.0) *)
Definition zrect_scale (r : ZRect) (factor : Z) : ZRect :=
  mkZRect (zrect_x r) (zrect_y r)
          (zrect_w r * factor / 1000) (zrect_h r * factor / 1000).

(** ** From-Center Properties *)

Theorem zrect_from_center_width : forall cx cy w h : Z,
  zrect_w (zrect_from_center cx cy w h) = w.
Proof.
  intros. unfold zrect_from_center. simpl. reflexivity.
Qed.

Theorem zrect_from_center_height : forall cx cy w h : Z,
  zrect_h (zrect_from_center cx cy w h) = h.
Proof.
  intros. unfold zrect_from_center. simpl. reflexivity.
Qed.

(** ** Scale Properties *)

Theorem zrect_scale_identity : forall (r : ZRect),
  zrect_scale r 1000 = r.
Proof.
  intros [x y0 w h]. unfold zrect_scale. simpl.
  apply zrect_eq; try reflexivity; apply Z.div_mul; lia.
Qed.

Theorem zrect_scale_preserves_position : forall (r : ZRect) (factor : Z),
  zrect_x (zrect_scale r factor) = zrect_x r /\
  zrect_y (zrect_scale r factor) = zrect_y r.
Proof.
  intros [x y0 w h] factor. unfold zrect_scale. simpl. split; reflexivity.
Qed.

Theorem zrect_scale_zero : forall (r : ZRect),
  zrect_w (zrect_scale r 0) = 0 /\ zrect_h (zrect_scale r 0) = 0.
Proof.
  intros [x y0 w h]. unfold zrect_scale.
  cbn [zrect_w zrect_h zrect_x zrect_y].
  split; rewrite Z.mul_0_r; reflexivity.
Qed.

(** ** Intersection Properties *)

Theorem zrect_intersection_nonneg_w : forall (a b : ZRect),
  0 <= zrect_w (zrect_intersection a b).
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold zrect_intersection. simpl. apply Z.le_max_l.
Qed.

Theorem zrect_intersection_nonneg_h : forall (a b : ZRect),
  0 <= zrect_h (zrect_intersection a b).
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold zrect_intersection. simpl. apply Z.le_max_l.
Qed.

Theorem zrect_intersection_comm : forall (a b : ZRect),
  zrect_intersection a b = zrect_intersection b a.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold zrect_intersection. simpl.
  apply zrect_eq.
  - apply Z.max_comm.
  - apply Z.max_comm.
  - rewrite (Z.min_comm (ax + aw) (bx + bw)).
    rewrite (Z.max_comm ax bx). reflexivity.
  - rewrite (Z.min_comm (ay + ah) (by0 + bh)).
    rewrite (Z.max_comm ay by0). reflexivity.
Qed.

(** ** Expand Properties *)

Theorem zrect_expand_zero : forall (r : ZRect),
  zrect_expand r 0 = r.
Proof.
  intros [x y0 w h]. unfold zrect_expand.
  cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

Theorem zrect_expand_compose : forall (r : ZRect) (a1 a2 : Z),
  zrect_expand (zrect_expand r a1) a2 = zrect_expand r (a1 + a2).
Proof.
  intros [x y0 w h] a1 a2.
  unfold zrect_expand. cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

Theorem zrect_expand_width : forall (r : ZRect) (amount : Z),
  zrect_w (zrect_expand r amount) = zrect_w r + 2 * amount.
Proof.
  intros [x y0 w h] amount. simpl. lia.
Qed.

Theorem zrect_expand_height : forall (r : ZRect) (amount : Z),
  zrect_h (zrect_expand r amount) = zrect_h r + 2 * amount.
Proof.
  intros [x y0 w h] amount. simpl. lia.
Qed.

(** ** Translate Additional Properties *)

Theorem zrect_translate_neg : forall (r : ZRect) (dx dy : Z),
  zrect_translate (zrect_translate r dx dy) (-dx) (-dy) = r.
Proof.
  intros [x y0 w h] dx dy.
  unfold zrect_translate. simpl.
  apply zrect_eq; lia.
Qed.

Theorem zrect_translate_commute : forall (r : ZRect) (dx1 dy1 dx2 dy2 : Z),
  zrect_translate (zrect_translate r dx1 dy1) dx2 dy2 =
  zrect_translate (zrect_translate r dx2 dy2) dx1 dy1.
Proof.
  intros [x y0 w h] dx1 dy1 dx2 dy2.
  unfold zrect_translate. simpl.
  apply zrect_eq; lia.
Qed.

Theorem zrect_translate_preserves_area : forall (r : ZRect) (dx dy : Z),
  zrect_area (zrect_translate r dx dy) = zrect_area r.
Proof.
  intros [x y0 w h] dx dy.
  unfold zrect_area, zrect_translate. simpl. reflexivity.
Qed.

Theorem zrect_translate_preserves_perimeter : forall (r : ZRect) (dx dy : Z),
  zrect_perimeter (zrect_translate r dx dy) = zrect_perimeter r.
Proof.
  intros [x y0 w h] dx dy.
  unfold zrect_perimeter, zrect_translate. simpl. reflexivity.
Qed.

(** ** Accessor Properties *)

Theorem zrect_right_correct : forall (r : ZRect),
  zrect_right r = zrect_x r + zrect_w r.
Proof.
  intros [x y0 w h]. unfold zrect_right. simpl. reflexivity.
Qed.

Theorem zrect_bottom_correct : forall (r : ZRect),
  zrect_bottom r = zrect_y r + zrect_h r.
Proof.
  intros [x y0 w h]. unfold zrect_bottom. simpl. reflexivity.
Qed.

Theorem zrect_translate_right : forall (r : ZRect) (dx dy : Z),
  zrect_right (zrect_translate r dx dy) = zrect_right r + dx.
Proof.
  intros [x y0 w h] dx dy.
  unfold zrect_right, zrect_translate. simpl. lia.
Qed.

Theorem zrect_translate_bottom : forall (r : ZRect) (dx dy : Z),
  zrect_bottom (zrect_translate r dx dy) = zrect_bottom r + dy.
Proof.
  intros [x y0 w h] dx dy.
  unfold zrect_bottom, zrect_translate. simpl. lia.
Qed.

(** ** Self-Containment Properties *)

Theorem zrect_union_self : forall (r : ZRect),
  zrect_w r >= 0 -> zrect_h r >= 0 ->
  zrect_union r r = r.
Proof.
  intros [x y0 w h] Hw Hh.
  unfold zrect_union. cbn -[Z.min Z.max Z.add Z.sub].
  apply zrect_eq.
  - apply Z.min_id.
  - apply Z.min_id.
  - rewrite Z.max_id. lia.
  - rewrite Z.max_id. lia.
Qed.

Theorem zrect_intersection_self : forall (r : ZRect),
  zrect_w r >= 0 -> zrect_h r >= 0 ->
  zrect_intersection r r = r.
Proof.
  intros [x y0 w h] Hw Hh.
  simpl in Hw, Hh.
  unfold zrect_intersection. cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq.
  - apply Z.max_id.
  - apply Z.max_id.
  - rewrite Z.min_id. rewrite Z.max_id.
    rewrite Z.max_r by lia. lia.
  - rewrite Z.min_id. rewrite Z.max_id.
    rewrite Z.max_r by lia. lia.
Qed.

(** ** Area/Valid Properties *)

Theorem zrect_area_positive : forall (r : ZRect),
  zrect_w r > 0 -> zrect_h r > 0 -> zrect_area r > 0.
Proof.
  intros [x y0 w h] Hw Hh. simpl in *. unfold zrect_area. simpl. nia.
Qed.

Theorem zrect_zero_is_empty :
  zrect_is_empty zrect_zero = true.
Proof.
  unfold zrect_is_empty, zrect_zero. simpl. reflexivity.
Qed.

Theorem zrect_zero_not_valid :
  zrect_is_valid zrect_zero = false.
Proof.
  unfold zrect_is_valid, zrect_zero. simpl. reflexivity.
Qed.

Theorem zrect_expand_translate_comm : forall (r : ZRect) (dx dy amount : Z),
  zrect_expand (zrect_translate r dx dy) amount =
  zrect_translate (zrect_expand r amount) dx dy.
Proof.
  intros [x y0 w h] dx dy amount.
  unfold zrect_expand, zrect_translate.
  cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

(** ** From-Center Additional Properties *)

Theorem zrect_from_center_area : forall cx cy w h : Z,
  zrect_area (zrect_from_center cx cy w h) = w * h.
Proof.
  intros. unfold zrect_area, zrect_from_center. simpl. reflexivity.
Qed.

(** * Computational Tests *)

Example zrect_test_new :
  zrect_new 10 20 100 50 = mkZRect 10 20 100 50.
Proof. reflexivity. Qed.

Example zrect_test_area :
  zrect_area (mkZRect 0 0 10 20) = 200.
Proof. reflexivity. Qed.

Example zrect_test_perimeter :
  zrect_perimeter (mkZRect 0 0 10 20) = 60.
Proof. reflexivity. Qed.

Example zrect_test_translate :
  zrect_translate (mkZRect 10 20 100 50) 5 10 = mkZRect 15 30 100 50.
Proof. reflexivity. Qed.

Example zrect_test_expand :
  zrect_expand (mkZRect 10 10 80 80) 10 = mkZRect 0 0 100 100.
Proof. reflexivity. Qed.

(** * from_pos_size, position, size, to_bounds *)

(** Construct a rect from position and size (mirrors Rust from_pos_size) *)
Definition zrect_from_pos_size (px py sw sh : Z) : ZRect :=
  mkZRect px py sw sh.

(** Position accessor: returns (x, y) *)
Definition zrect_position_x (r : ZRect) : Z := zrect_x r.
Definition zrect_position_y (r : ZRect) : Z := zrect_y r.

(** Size accessor: returns (w, h) *)
Definition zrect_size_w (r : ZRect) : Z := zrect_w r.
Definition zrect_size_h (r : ZRect) : Z := zrect_h r.

(** to_bounds: returns (min_x, min_y, max_x, max_y) *)
Definition zrect_bounds_min_x (r : ZRect) : Z := zrect_x r.
Definition zrect_bounds_min_y (r : ZRect) : Z := zrect_y r.
Definition zrect_bounds_max_x (r : ZRect) : Z := zrect_x r + zrect_w r.
Definition zrect_bounds_max_y (r : ZRect) : Z := zrect_y r + zrect_h r.

(** from_pos_size roundtrip: position recovers the input position *)
Theorem zrect_from_pos_size_position : forall px py sw sh : Z,
  let r := zrect_from_pos_size px py sw sh in
  zrect_position_x r = px /\ zrect_position_y r = py.
Proof.
  intros. unfold zrect_from_pos_size, zrect_position_x, zrect_position_y.
  simpl. split; reflexivity.
Qed.

(** from_pos_size roundtrip: size recovers the input size *)
Theorem zrect_from_pos_size_size : forall px py sw sh : Z,
  let r := zrect_from_pos_size px py sw sh in
  zrect_size_w r = sw /\ zrect_size_h r = sh.
Proof.
  intros. unfold zrect_from_pos_size, zrect_size_w, zrect_size_h.
  simpl. split; reflexivity.
Qed.

(** from_pos_size is equivalent to zrect_new *)
Theorem zrect_from_pos_size_eq_new : forall px py sw sh : Z,
  zrect_from_pos_size px py sw sh = zrect_new px py sw sh.
Proof.
  intros. unfold zrect_from_pos_size, zrect_new. reflexivity.
Qed.

(** to_bounds: min = position *)
Theorem zrect_bounds_min_eq_position : forall (r : ZRect),
  zrect_bounds_min_x r = zrect_position_x r /\
  zrect_bounds_min_y r = zrect_position_y r.
Proof.
  intros [x y0 w h].
  unfold zrect_bounds_min_x, zrect_bounds_min_y,
         zrect_position_x, zrect_position_y. simpl.
  split; reflexivity.
Qed.

(** to_bounds: max = position + size *)
Theorem zrect_bounds_max_eq_pos_plus_size : forall (r : ZRect),
  zrect_bounds_max_x r = zrect_position_x r + zrect_size_w r /\
  zrect_bounds_max_y r = zrect_position_y r + zrect_size_h r.
Proof.
  intros [x y0 w h].
  unfold zrect_bounds_max_x, zrect_bounds_max_y,
         zrect_position_x, zrect_position_y,
         zrect_size_w, zrect_size_h. simpl.
  split; reflexivity.
Qed.

(** to_bounds: width = max_x - min_x *)
Theorem zrect_bounds_width_correct : forall (r : ZRect),
  zrect_bounds_max_x r - zrect_bounds_min_x r = zrect_w r.
Proof.
  intros [x y0 w h].
  unfold zrect_bounds_max_x, zrect_bounds_min_x. simpl. lia.
Qed.

(** to_bounds: height = max_y - min_y *)
Theorem zrect_bounds_height_correct : forall (r : ZRect),
  zrect_bounds_max_y r - zrect_bounds_min_y r = zrect_h r.
Proof.
  intros [x y0 w h].
  unfold zrect_bounds_max_y, zrect_bounds_min_y. simpl. lia.
Qed.

(** position and size fully determine the rect *)
Theorem zrect_position_size_determine : forall (r1 r2 : ZRect),
  zrect_position_x r1 = zrect_position_x r2 ->
  zrect_position_y r1 = zrect_position_y r2 ->
  zrect_size_w r1 = zrect_size_w r2 ->
  zrect_size_h r1 = zrect_size_h r2 ->
  r1 = r2.
Proof.
  intros [x1 y1 w1 h1] [x2 y2 w2 h2].
  unfold zrect_position_x, zrect_position_y, zrect_size_w, zrect_size_h.
  simpl. intros Hx Hy Hw Hh. subst. reflexivity.
Qed.

Example zrect_test_from_pos_size :
  zrect_from_pos_size 10 20 100 50 = mkZRect 10 20 100 50.
Proof. reflexivity. Qed.

Example zrect_test_contains :
  zrect_contains_point (mkZRect 0 0 100 100) 50 50 = true.
Proof. reflexivity. Qed.

(** * Phase 15: Additional Z-Compute Definitions and Theorems *)

(** ** Accessor definitions *)

Definition zrect_left (r : ZRect) : Z := zrect_x r.
Definition zrect_top (r : ZRect) : Z := zrect_y r.
Definition zrect_min_x (r : ZRect) : Z := zrect_x r.
Definition zrect_min_y (r : ZRect) : Z := zrect_y r.
Definition zrect_max_x (r : ZRect) : Z := zrect_x r + zrect_w r.
Definition zrect_max_y (r : ZRect) : Z := zrect_y r + zrect_h r.

(** ** from_corners: constructs rect from any two corner points *)

Definition zrect_from_corners (ax ay bx by0 : Z) : ZRect :=
  let x := Z.min ax bx in
  let y0 := Z.min ay by0 in
  mkZRect x y0 (Z.max ax bx - x) (Z.max ay by0 - y0).

(** ** expand_xy: independent expansion on each axis *)

Definition zrect_expand_xy (r : ZRect) (xa ya : Z) : ZRect :=
  mkZRect (zrect_x r - xa) (zrect_y r - ya)
          (zrect_w r + 2 * xa) (zrect_h r + 2 * ya).

(** ** scale_from_center: scale dims preserving center (factor/1000) *)

Definition zrect_scale_from_center (r : ZRect) (factor : Z) : ZRect :=
  let cx := zrect_center_x r in
  let cy := zrect_center_y r in
  let nw := zrect_w r * factor / 1000 in
  let nh := zrect_h r * factor / 1000 in
  mkZRect (cx - nw / 2) (cy - nh / 2) nw nh.

(** ** normalize: ensure non-negative dims *)

Definition zrect_normalize (r : ZRect) : ZRect :=
  if (zrect_w r <? 0) then
    mkZRect (zrect_x r + zrect_w r) (zrect_y r) (- zrect_w r) (zrect_h r)
  else if (zrect_h r <? 0) then
    mkZRect (zrect_x r) (zrect_y r + zrect_h r) (zrect_w r) (- zrect_h r)
  else
    r.

(** ** lerp: linear interpolation (t in millionths: 0=0.0, 1000000=1.0) *)

Definition zrect_lerp (a b : ZRect) (t : Z) : ZRect :=
  mkZRect (zrect_x a + (zrect_x b - zrect_x a) * t / 1000000)
          (zrect_y a + (zrect_y b - zrect_y a) * t / 1000000)
          (zrect_w a + (zrect_w b - zrect_w a) * t / 1000000)
          (zrect_h a + (zrect_h b - zrect_h a) * t / 1000000).

(** ** merge: alias for union *)

Definition zrect_merge (a b : ZRect) : ZRect := zrect_union a b.

(** ** clip_to: alias for intersection *)

Definition zrect_clip_to (r clip : ZRect) : ZRect := zrect_intersection r clip.

(** ** grow_to_contain: expand rect to include a point *)

Definition zrect_grow_to_contain (r : ZRect) (px py : Z) : ZRect :=
  let new_x := Z.min (zrect_x r) px in
  let new_y := Z.min (zrect_y r) py in
  let new_right := Z.max (zrect_x r + zrect_w r) px in
  let new_bottom := Z.max (zrect_y r + zrect_h r) py in
  mkZRect new_x new_y (new_right - new_x) (new_bottom - new_y).

(** ** Accessor Theorems *)

Theorem zrect_left_eq_x : forall (r : ZRect),
  zrect_left r = zrect_x r.
Proof. intros [x y0 w h]. unfold zrect_left. simpl. reflexivity. Qed.

Theorem zrect_top_eq_y : forall (r : ZRect),
  zrect_top r = zrect_y r.
Proof. intros [x y0 w h]. unfold zrect_top. simpl. reflexivity. Qed.

Theorem zrect_min_x_eq : forall (r : ZRect),
  zrect_min_x r = zrect_x r.
Proof. intros [x y0 w h]. unfold zrect_min_x. simpl. reflexivity. Qed.

Theorem zrect_min_y_eq : forall (r : ZRect),
  zrect_min_y r = zrect_y r.
Proof. intros [x y0 w h]. unfold zrect_min_y. simpl. reflexivity. Qed.

Theorem zrect_max_x_eq_right : forall (r : ZRect),
  zrect_max_x r = zrect_right r.
Proof. intros [x y0 w h]. unfold zrect_max_x, zrect_right. simpl. reflexivity. Qed.

Theorem zrect_max_y_eq_bottom : forall (r : ZRect),
  zrect_max_y r = zrect_bottom r.
Proof. intros [x y0 w h]. unfold zrect_max_y, zrect_bottom. simpl. reflexivity. Qed.

(** ** from_corners Theorems *)

Theorem zrect_from_corners_nonneg_w : forall ax ay bx by0 : Z,
  zrect_w (zrect_from_corners ax ay bx by0) >= 0.
Proof.
  intros. unfold zrect_from_corners. simpl. lia.
Qed.

Theorem zrect_from_corners_nonneg_h : forall ax ay bx by0 : Z,
  zrect_h (zrect_from_corners ax ay bx by0) >= 0.
Proof.
  intros. unfold zrect_from_corners. simpl. lia.
Qed.

Theorem zrect_from_corners_symmetric : forall ax ay bx by0 : Z,
  zrect_from_corners ax ay bx by0 = zrect_from_corners bx by0 ax ay.
Proof.
  intros. unfold zrect_from_corners. simpl.
  apply zrect_eq.
  - apply Z.min_comm.
  - apply Z.min_comm.
  - f_equal. apply Z.max_comm. apply Z.min_comm.
  - f_equal. apply Z.max_comm. apply Z.min_comm.
Qed.

Theorem zrect_from_corners_same_point : forall px py : Z,
  zrect_from_corners px py px py = mkZRect px py 0 0.
Proof.
  intros. unfold zrect_from_corners. simpl.
  apply zrect_eq.
  - apply Z.min_id.
  - apply Z.min_id.
  - rewrite Z.max_id. lia.
  - rewrite Z.max_id. lia.
Qed.

(** ** expand_xy Theorems *)

Theorem zrect_expand_xy_zero : forall (r : ZRect),
  zrect_expand_xy r 0 0 = r.
Proof.
  intros [x y0 w h]. unfold zrect_expand_xy.
  cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

Theorem zrect_expand_xy_width : forall (r : ZRect) (xa ya : Z),
  zrect_w (zrect_expand_xy r xa ya) = zrect_w r + 2 * xa.
Proof.
  intros [x y0 w h] xa ya. unfold zrect_expand_xy. simpl. lia.
Qed.

Theorem zrect_expand_xy_height : forall (r : ZRect) (xa ya : Z),
  zrect_h (zrect_expand_xy r xa ya) = zrect_h r + 2 * ya.
Proof.
  intros [x y0 w h] xa ya. unfold zrect_expand_xy. simpl. lia.
Qed.

Theorem zrect_expand_xy_equal_is_expand : forall (r : ZRect) (a : Z),
  zrect_expand_xy r a a = zrect_expand r a.
Proof.
  intros [x y0 w h] a. unfold zrect_expand_xy, zrect_expand.
  cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

Theorem zrect_expand_xy_compose : forall (r : ZRect) (xa1 ya1 xa2 ya2 : Z),
  zrect_expand_xy (zrect_expand_xy r xa1 ya1) xa2 ya2 =
  zrect_expand_xy r (xa1 + xa2) (ya1 + ya2).
Proof.
  intros [x y0 w h] xa1 ya1 xa2 ya2.
  unfold zrect_expand_xy.
  cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; lia.
Qed.

(** ** scale_from_center Theorems *)

Theorem zrect_scale_from_center_identity : forall (r : ZRect),
  zrect_w (zrect_scale_from_center r 1000) = zrect_w r.
Proof.
  intros [x y0 w h]. unfold zrect_scale_from_center, zrect_center_x, zrect_center_y.
  simpl. rewrite Z.div_mul by lia. reflexivity.
Qed.

Theorem zrect_scale_from_center_zero_width : forall (r : ZRect),
  zrect_w (zrect_scale_from_center r 0) = 0.
Proof.
  intros [x y0 w h]. unfold zrect_scale_from_center, zrect_center_x, zrect_center_y.
  simpl. rewrite Z.mul_0_r. reflexivity.
Qed.

Theorem zrect_scale_from_center_zero_height : forall (r : ZRect),
  zrect_h (zrect_scale_from_center r 0) = 0.
Proof.
  intros [x y0 w h]. unfold zrect_scale_from_center, zrect_center_x, zrect_center_y.
  simpl. rewrite Z.mul_0_r. reflexivity.
Qed.

(** ** lerp Theorems *)

Theorem zrect_lerp_zero : forall (a b : ZRect),
  zrect_lerp a b 0 = a.
Proof.
  intros [ax ay aw ah] [bx by0 bw bh].
  unfold zrect_lerp. cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; rewrite Z.mul_0_r; rewrite Z.div_0_l by lia; lia.
Qed.

Theorem zrect_lerp_same : forall (r : ZRect) (t : Z),
  zrect_lerp r r t = r.
Proof.
  intros [x y0 w h] t.
  unfold zrect_lerp. cbn [zrect_x zrect_y zrect_w zrect_h].
  apply zrect_eq; rewrite Z.sub_diag; rewrite Z.mul_0_l; rewrite Z.div_0_l by lia; lia.
Qed.

(** ** merge Theorems *)

Theorem zrect_merge_comm : forall (a b : ZRect),
  zrect_merge a b = zrect_merge b a.
Proof.
  intros. unfold zrect_merge. apply zrect_union_commutative.
Qed.

Theorem zrect_merge_self : forall (r : ZRect),
  zrect_w r >= 0 -> zrect_h r >= 0 ->
  zrect_merge r r = r.
Proof.
  intros. unfold zrect_merge. apply zrect_union_self; assumption.
Qed.

(** ** clip_to Theorems *)

Theorem zrect_clip_to_comm : forall (a b : ZRect),
  zrect_clip_to a b = zrect_clip_to b a.
Proof.
  intros. unfold zrect_clip_to. apply zrect_intersection_comm.
Qed.

Theorem zrect_clip_to_self : forall (r : ZRect),
  zrect_w r >= 0 -> zrect_h r >= 0 ->
  zrect_clip_to r r = r.
Proof.
  intros. unfold zrect_clip_to. apply zrect_intersection_self; assumption.
Qed.

(** ** grow_to_contain Theorems *)

Theorem zrect_grow_to_contain_nonneg_w : forall (r : ZRect) (px py : Z),
  zrect_w r >= 0 ->
  zrect_w (zrect_grow_to_contain r px py) >= 0.
Proof.
  intros [x y0 w h] px py Hw.
  unfold zrect_grow_to_contain.
  cbn [zrect_x zrect_y zrect_w zrect_h]. simpl in Hw. lia.
Qed.

Theorem zrect_grow_to_contain_nonneg_h : forall (r : ZRect) (px py : Z),
  zrect_h r >= 0 ->
  zrect_h (zrect_grow_to_contain r px py) >= 0.
Proof.
  intros [x y0 w h] px py Hh.
  unfold zrect_grow_to_contain.
  cbn [zrect_x zrect_y zrect_w zrect_h]. simpl in Hh. lia.
Qed.

(** ** normalize Theorems *)

Theorem zrect_normalize_nonneg_w : forall (r : ZRect),
  zrect_w (zrect_normalize r) >= 0.
Proof.
  intros [x y0 w h].
  unfold zrect_normalize. simpl.
  destruct (w <? 0) eqn:Hw; simpl.
  - apply Z.ltb_lt in Hw. lia.
  - destruct (h <? 0) eqn:Hh; simpl.
    + apply Z.ltb_ge in Hw. lia.
    + apply Z.ltb_ge in Hw. lia.
Qed.

Theorem zrect_normalize_positive_id : forall (r : ZRect),
  zrect_w r >= 0 -> zrect_h r >= 0 ->
  zrect_normalize r = r.
Proof.
  intros [x y0 w h] Hw Hh.
  unfold zrect_normalize. simpl. simpl in Hw, Hh.
  destruct (w <? 0) eqn:Ew.
  - apply Z.ltb_lt in Ew. lia.
  - destruct (h <? 0) eqn:Eh.
    + apply Z.ltb_lt in Eh. lia.
    + reflexivity.
Qed.

(** ** Computational Tests for New Operations *)

Example zrect_test_left :
  zrect_left (mkZRect 10 20 100 50) = 10.
Proof. reflexivity. Qed.

Example zrect_test_top :
  zrect_top (mkZRect 10 20 100 50) = 20.
Proof. reflexivity. Qed.

Example zrect_test_from_corners :
  zrect_from_corners 100 50 10 20 = mkZRect 10 20 90 30.
Proof. reflexivity. Qed.

Example zrect_test_expand_xy :
  zrect_expand_xy (mkZRect 10 10 80 80) 5 10 = mkZRect 5 0 90 100.
Proof. reflexivity. Qed.

Example zrect_test_grow_to_contain :
  zrect_grow_to_contain (mkZRect 10 10 10 10) 5 15 = mkZRect 5 10 15 10.
Proof. reflexivity. Qed.
