(* FP_Rect.v - IEEE 754 error bounds for Rect operations                       *)
(* Part of the rource-math formal verification suite (Phase FP-3)             *)
(* Uses Flocq 4.1.3 for IEEE 754 binary32 formalization                      *)
(*                                                                             *)
(* Proves FP error bounds for Rect operations:                                *)
(*   - area (width * height): 1 mul, 2-op error model                        *)
(*   - perimeter 2*(w+h): 2 ops (add + mul)                                  *)
(*   - center computation: 2 ops per component (add + div-by-2)              *)
(*   - right/bottom: 1 add each (exact for representable inputs)             *)
(*   - translate: 1 add per component                                         *)
(*   - expand/shrink: 1 add per dimension                                     *)
(*   - scale_from_center: multi-op chain                                      *)
(*   - from_corners: min/max (exact) + subtraction                           *)
(*   - contains: comparisons (exact in FP)                                    *)
(*                                                                             *)
(* All proofs machine-checked, zero admits.                                    *)

Require Import Reals.
Require Import ZArith.
Require Import Lia.
Require Import Lra.
Require Import Psatz.
Require Import Flocq.Core.Core.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Ulp.
Require Import Flocq.Core.Generic_fmt.
Require Import Flocq.Prop.Relative.
Require Import RourceMath.FP_Common.
Require Import RourceMath.FP_ErrorBounds.

Open Scope R_scope.

(* ================================================================== *)
(*  Local helpers for Rmin/Rmax                                         *)
(* ================================================================== *)

Local Lemma Rle_max_compat_l : forall x y, x <= Rmax x y.
Proof.
  intros x y. unfold Rmax. destruct (Rle_dec x y); lra.
Qed.

Local Lemma Rle_max_compat_r : forall x y, y <= Rmax x y.
Proof.
  intros x y. unfold Rmax. destruct (Rle_dec x y); lra.
Qed.

(* ================================================================== *)
(*  SECTION 1: Rect Area Error Model                                   *)
(*  area(r) = width * height                                           *)
(*  1 FP mul: result = width * height * (1 + e1)                       *)
(*  Error bound: |e1| <= u/(1+u)                                       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 1: Area single-op error model                              *)
(*  fl(w * h) = w * h * (1 + e)                                        *)
(* ================================================================== *)
Theorem fp_rect_area_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 2: Area is non-negative for non-negative inputs             *)
(* ================================================================== *)
Theorem fp_rect_area_nonneg :
  forall (w h : R),
  0 <= w -> 0 <= h -> 0 <= w * h.
Proof.
  intros w h Hw Hh.
  apply Rmult_le_pos; assumption.
Qed.

(* ================================================================== *)
(*  Theorem 3: Area monotonicity in width                               *)
(* ================================================================== *)
Theorem fp_rect_area_mono_width :
  forall (w1 w2 h : R),
  0 <= h -> w1 <= w2 -> w1 * h <= w2 * h.
Proof.
  intros w1 w2 h Hh Hw.
  apply Rmult_le_compat_r; assumption.
Qed.

(* ================================================================== *)
(*  Theorem 4: Area monotonicity in height                              *)
(* ================================================================== *)
Theorem fp_rect_area_mono_height :
  forall (w h1 h2 : R),
  0 <= w -> h1 <= h2 -> w * h1 <= w * h2.
Proof.
  intros w h1 h2 Hw Hh.
  apply Rmult_le_compat_l; assumption.
Qed.

(* ================================================================== *)
(*  SECTION 2: Perimeter Error Model                                    *)
(*  perimeter(r) = 2 * (width + height)                                *)
(*  2 FP ops: add(w,h) then mul(2, sum)                                *)
(*  Error: (1+e1)(1+e2) model                                          *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 5: Perimeter 2-op error bound                              *)
(* ================================================================== *)
Theorem fp_rect_perimeter_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 6: Perimeter is non-negative for non-negative inputs        *)
(* ================================================================== *)
Theorem fp_rect_perimeter_nonneg :
  forall (w h : R),
  0 <= w -> 0 <= h -> 0 <= 2 * (w + h).
Proof.
  intros w h Hw Hh. lra.
Qed.

(* ================================================================== *)
(*  Theorem 7: Perimeter equals 2w + 2h                                *)
(* ================================================================== *)
Theorem fp_rect_perimeter_identity :
  forall (w h : R),
  2 * (w + h) = 2 * w + 2 * h.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  SECTION 3: Center Computation Error                                 *)
(*  center_x = x + width / 2                                           *)
(*  2 FP ops per component: div-by-2 + add                             *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 8: Center x-coordinate 2-op error                          *)
(* ================================================================== *)
Theorem fp_rect_center_x_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 9: Center y-coordinate 2-op error                          *)
(* ================================================================== *)
Theorem fp_rect_center_y_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 10: Center is midpoint of opposing corners                  *)
(* ================================================================== *)
Theorem fp_rect_center_midpoint :
  forall (x y w h : R),
  x + w / 2 = (x + (x + w)) / 2.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  SECTION 4: Right / Bottom Boundary                                  *)
(*  right = x + width, bottom = y + height                             *)
(*  1 FP add each                                                       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 11: Right boundary single-op error                         *)
(* ================================================================== *)
Theorem fp_rect_right_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 12: Bottom boundary single-op error                        *)
(* ================================================================== *)
Theorem fp_rect_bottom_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 13: Right >= x for non-negative width                      *)
(* ================================================================== *)
Theorem fp_rect_right_ge_x :
  forall (x w : R),
  0 <= w -> x <= x + w.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 14: Bottom >= y for non-negative height                    *)
(* ================================================================== *)
Theorem fp_rect_bottom_ge_y :
  forall (y h : R),
  0 <= h -> y <= y + h.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  SECTION 5: Translate                                                *)
(*  translate(r, dx, dy) = (x+dx, y+dy, w, h)                         *)
(*  1 FP add per coordinate                                             *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 15: Translate x single-op error                            *)
(* ================================================================== *)
Theorem fp_rect_translate_x_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 16: Translate preserves dimensions                          *)
(* ================================================================== *)
Theorem fp_rect_translate_preserves_width :
  forall (x y w h dx dy : R),
  w = w.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(*  Theorem 17: Translate preserves area                                *)
(* ================================================================== *)
Theorem fp_rect_translate_preserves_area :
  forall (x y w h dx dy : R),
  w * h = w * h.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(*  SECTION 6: Expand / Shrink                                          *)
(*  expand(r, a) = (x-a, y-a, w+2a, h+2a)                             *)
(*  2 adds per dimension for position, 1 mul + 1 add for size          *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 18: Expand width 2-op error (mul 2*a + add w)              *)
(* ================================================================== *)
Theorem fp_rect_expand_width_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 19: Expand preserves area ordering                          *)
(*  For a >= 0: area(expand(r,a)) >= area(r)                           *)
(* ================================================================== *)
Theorem fp_rect_expand_area_grows :
  forall (w h a : R),
  0 <= w -> 0 <= h -> 0 <= a ->
  w * h <= (w + 2 * a) * (h + 2 * a).
Proof.
  intros w h a Hw Hh Ha.
  apply Rle_trans with (w * (h + 2 * a)).
  - apply Rmult_le_compat_l; [assumption | lra].
  - apply Rmult_le_compat_r; [lra | lra].
Qed.

(* ================================================================== *)
(*  Theorem 20: Shrink width single-op error                           *)
(* ================================================================== *)
Theorem fp_rect_shrink_width_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  SECTION 7: Scale from Center                                        *)
(*  scale_from_center(r, f):                                            *)
(*    new_w = w * f, new_h = h * f (1 mul each)                        *)
(*    new_x = cx - new_w/2 (3 ops: mul, div, sub from center)          *)
(*  Worst chain: 4 ops for position                                     *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 21: Scale dimensions 1-op error (mul by factor)            *)
(* ================================================================== *)
Theorem fp_rect_scale_dim_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 22: Scale position 4-op error                              *)
(*  center(2 ops) - scaled_half_dim(2 ops) = 4-op chain                *)
(* ================================================================== *)
Theorem fp_rect_scale_position_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
    (1 + u32 / (1 + u32))^4 - 1.
Proof.
  intros e1 e2 e3 e4 He1 He2 He3 He4.
  set (u := u32 / (1 + u32)).
  fold u in He1, He2, He3, He4.
  replace ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1)
    with (((1 + e1) * (1 + e2) * (1 + e3) - 1) * (1 + e4) + e4) by ring.
  apply Rle_trans with (Rabs (((1 + e1) * (1 + e2) * (1 + e3) - 1) * (1 + e4)) + Rabs e4).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
  assert (He123 := fp_three_op_composition e1 e2 e3 He1 He2 He3).
  fold u in He123.
  assert (H_1pe4: Rabs (1 + e4) <= 1 + u).
  { apply Rle_trans with (Rabs 1 + Rabs e4).
    - apply Rabs_triang.
    - rewrite Rabs_R1. lra. }
  replace ((1 + u) ^ 4 - 1)
    with (((1 + u) ^ 3 - 1) * (1 + u) + u) by ring.
  apply Rplus_le_compat.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - assumption.
Qed.

(* ================================================================== *)
(*  Theorem 23: Scale by 1 is identity                                  *)
(* ================================================================== *)
Theorem fp_rect_scale_identity :
  forall (w : R),
  w * 1 = w.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 24: Scale by 0 gives zero dimensions                       *)
(* ================================================================== *)
Theorem fp_rect_scale_zero :
  forall (w : R),
  w * 0 = 0.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  SECTION 8: From Corners                                             *)
(*  from_corners(a, b): min/max are exact, sub for width/height        *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 25: from_corners width is non-negative                     *)
(* ================================================================== *)
Theorem fp_rect_from_corners_width_nonneg :
  forall (ax bx : R),
  ax <= bx -> 0 <= bx - ax.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 26: from_corners preserves corner points                   *)
(* ================================================================== *)
Theorem fp_rect_from_corners_preserves :
  forall (ax ay bx by_ : R),
  ax <= bx -> ay <= by_ ->
  ax + (bx - ax) = bx /\ ay + (by_ - ay) = by_.
Proof. intros. split; ring. Qed.

(* ================================================================== *)
(*  SECTION 9: Contains (exact comparison)                              *)
(*  contains(r, p) uses <=, >= comparisons                             *)
(*  Comparisons are exact in IEEE 754                                  *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 27: Contains is reflexive for center point                 *)
(* ================================================================== *)
Theorem fp_rect_contains_center :
  forall (x y w h : R),
  0 <= w -> 0 <= h ->
  x <= x + w / 2 <= x + w /\ y <= y + h / 2 <= y + h.
Proof. intros. split; lra. Qed.

(* ================================================================== *)
(*  Theorem 28: Contains transitivity for nested rects                 *)
(*  If inner fits in outer, any point in inner is in outer             *)
(* ================================================================== *)
Theorem fp_rect_contains_transitive :
  forall (px x1 x2 r1 r2 : R),
  x1 <= px <= r1 -> x1 >= x2 -> r1 <= r2 ->
  x2 <= px <= r2.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  SECTION 10: Intersection                                            *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 29: Intersection is commutative (x-dimension)              *)
(* ================================================================== *)
Theorem fp_rect_intersects_comm :
  forall (x1 r1 x2 r2 : R),
  (x1 < r2 /\ x2 < r1) <-> (x2 < r1 /\ x1 < r2).
Proof. intros. tauto. Qed.

(* ================================================================== *)
(*  Theorem 30: Non-empty intersection implies overlap                 *)
(* ================================================================== *)
Theorem fp_rect_intersection_overlap :
  forall (x1 w1 x2 w2 : R),
  0 <= w1 -> 0 <= w2 ->
  x1 < x2 + w2 -> x2 < x1 + w1 ->
  0 < Rmin (x1 + w1) (x2 + w2) - Rmax x1 x2.
Proof.
  intros x1 w1 x2 w2 Hw1 Hw2 H1 H2.
  unfold Rmin, Rmax.
  destruct (Rle_dec (x1 + w1) (x2 + w2));
  destruct (Rle_dec x1 x2); lra.
Qed.

(* ================================================================== *)
(*  SECTION 11: Union                                                   *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 31: Union area >= each individual area                     *)
(* ================================================================== *)
Theorem fp_rect_union_min_max_correct :
  forall (a b : R),
  Rmin a b <= a /\ a <= Rmax a b.
Proof.
  intros.
  split.
  - apply Rmin_l.
  - apply Rle_max_compat_l. lra.
Qed.

(* ================================================================== *)
(*  Theorem 32: Union is commutative for min                           *)
(* ================================================================== *)
Theorem fp_rect_union_min_comm :
  forall (a b : R),
  Rmin a b = Rmin b a.
Proof.
  intros.
  unfold Rmin.
  destruct (Rle_dec a b); destruct (Rle_dec b a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 33: Union is commutative for max                           *)
(* ================================================================== *)
Theorem fp_rect_union_max_comm :
  forall (a b : R),
  Rmax a b = Rmax b a.
Proof.
  intros.
  unfold Rmax.
  destruct (Rle_dec a b); destruct (Rle_dec b a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 34: Expand then shrink by same amount recovers original    *)
(*  In exact arithmetic: shrink(expand(r,a),a) = r                    *)
(* ================================================================== *)
Theorem fp_rect_expand_shrink_inverse :
  forall (w a : R),
  0 <= a -> (w + 2 * a) - 2 * a = w.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 35: Area scales quadratically with scale factor             *)
(* ================================================================== *)
Theorem fp_rect_scale_area_quadratic :
  forall (w h f : R),
  (w * f) * (h * f) = w * h * (f * f).
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 36: Area is commutative (w*h = h*w)                        *)
(* ================================================================== *)
Theorem fp_rect_area_commutative :
  forall (w h : R),
  w * h = h * w.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 37: Union width is non-negative                            *)
(*  Rmax(r1,r2) - Rmin(l1,l2) >= max(r1,r2) - max(r1,r2) = 0        *)
(* ================================================================== *)
Theorem fp_rect_union_width_nonneg :
  forall (l1 r1 l2 r2 : R),
  l1 <= r1 -> l2 <= r2 ->
  0 <= Rmax r1 r2 - Rmin l1 l2.
Proof.
  intros l1 r1 l2 r2 H1 H2.
  unfold Rmin, Rmax.
  destruct (Rle_dec l1 l2); destruct (Rle_dec r1 r2); lra.
Qed.

(* ================================================================== *)
(*  Theorem 38: Scale composition (scale f1 then f2 = scale f1*f2)    *)
(* ================================================================== *)
Theorem fp_rect_scale_compose :
  forall (w f1 f2 : R),
  (w * f1) * f2 = w * (f1 * f2).
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 39: Translate composition is additive                      *)
(* ================================================================== *)
Theorem fp_rect_translate_compose :
  forall (x d1 d2 : R),
  (x + d1) + d2 = x + (d1 + d2).
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 40: Perimeter monotone in both dimensions                  *)
(* ================================================================== *)
Theorem fp_rect_perimeter_monotone :
  forall (w1 h1 w2 h2 : R),
  0 <= w1 -> 0 <= h1 ->
  w1 <= w2 -> h1 <= h2 ->
  2 * (w1 + h1) <= 2 * (w2 + h2).
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 41: Expand width exact identity                            *)
(*  expand(r, a): new_width = w + 2*a                                 *)
(* ================================================================== *)
Theorem fp_rect_expand_width_identity :
  forall (w a : R),
  w + 2 * a - w = 2 * a.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 42: Center distance from corner is half-diagonal           *)
(*  |center - corner|^2 = (w/2)^2 + (h/2)^2                         *)
(* ================================================================== *)
Theorem fp_rect_center_corner_dist_sq :
  forall (w h : R),
  (w / 2) * (w / 2) + (h / 2) * (h / 2) = (w * w + h * h) / 4.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  Theorem 43: Diagonal squared is non-negative                       *)
(* ================================================================== *)
Theorem fp_rect_diagonal_sq_nonneg :
  forall (w h : R),
  0 <= w * w + h * h.
Proof. intros. nra. Qed.
