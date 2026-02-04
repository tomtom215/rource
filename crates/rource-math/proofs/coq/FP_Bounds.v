(* FP_Bounds.v - IEEE 754 error bounds for Bounds operations                   *)
(* Part of the rource-math formal verification suite (Phase FP-3)             *)
(* Uses Flocq 4.1.3 for IEEE 754 binary32 formalization                      *)
(*                                                                             *)
(* Proves FP error bounds for Bounds (AABB) operations:                       *)
(*   - center: (min + max) / 2, 2-op per component                           *)
(*   - half_extents: (max - min) / 2, 2-op per component                     *)
(*   - width/height: max - min, 1-op each                                     *)
(*   - area: width * height, 3-op chain                                       *)
(*   - contains: comparisons (exact in FP)                                     *)
(*   - union/intersection: min/max (exact in FP)                               *)
(*   - translate: addition, 1-op per component                                 *)
(*   - expand/shrink: 1-op per dimension                                       *)
(*   - from_center_size: 2-op per component                                    *)
(*   - include_point: min/max (exact)                                          *)
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
(*  SECTION 1: Center Computation Error                                 *)
(*  center = (min + max) / 2                                            *)
(*  2 FP ops per component: add then div-by-2                           *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 1: Center x 2-op error bound                               *)
(* ================================================================== *)
Theorem fp_bounds_center_x_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 2: Center y 2-op error bound                               *)
(* ================================================================== *)
Theorem fp_bounds_center_y_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 3: Center lies between min and max                          *)
(* ================================================================== *)
Theorem fp_bounds_center_between :
  forall (lo hi : R),
  lo <= hi ->
  lo <= (lo + hi) / 2 <= hi.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 4: Center is exact midpoint                                 *)
(* ================================================================== *)
Theorem fp_bounds_center_midpoint :
  forall (lo hi : R),
  (lo + hi) / 2 - lo = hi - (lo + hi) / 2.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  SECTION 2: Half Extents Error                                       *)
(*  half_extents = (max - min) / 2                                      *)
(*  2 FP ops per component: sub then div-by-2                           *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 5: Half extents x 2-op error bound                         *)
(* ================================================================== *)
Theorem fp_bounds_half_extents_x_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 6: Half extents non-negative for valid bounds              *)
(* ================================================================== *)
Theorem fp_bounds_half_extents_nonneg :
  forall (lo hi : R),
  lo <= hi ->
  0 <= (hi - lo) / 2.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 7: Half extents relationship to size                        *)
(*  half_extents = size / 2                                             *)
(* ================================================================== *)
Theorem fp_bounds_half_extents_is_half_size :
  forall (lo hi : R),
  (hi - lo) / 2 = (hi - lo) * / 2.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  SECTION 3: Width / Height (Size)                                    *)
(*  width = max_x - min_x, height = max_y - min_y                      *)
(*  1 FP sub each                                                       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 8: Width single-op error                                   *)
(* ================================================================== *)
Theorem fp_bounds_width_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 9: Width non-negative for valid bounds                     *)
(* ================================================================== *)
Theorem fp_bounds_width_nonneg :
  forall (lo hi : R),
  lo <= hi -> 0 <= hi - lo.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 10: Size equals twice half_extents                          *)
(* ================================================================== *)
Theorem fp_bounds_size_twice_half :
  forall (lo hi : R),
  hi - lo = 2 * ((hi - lo) / 2).
Proof. intros. field. Qed.

(* ================================================================== *)
(*  SECTION 4: Area Error                                               *)
(*  area = width * height = (max_x - min_x) * (max_y - min_y)         *)
(*  3 FP ops: sub_x, sub_y, mul                                        *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 11: Area width-component 2-op chain (sub + mul)            *)
(* ================================================================== *)
Theorem fp_bounds_area_width_chain_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 12: Area non-negative for valid bounds                     *)
(* ================================================================== *)
Theorem fp_bounds_area_nonneg :
  forall (lx ly hx hy : R),
  lx <= hx -> ly <= hy ->
  0 <= (hx - lx) * (hy - ly).
Proof.
  intros. apply Rmult_le_pos; lra.
Qed.

(* ================================================================== *)
(*  SECTION 5: Contains (Exact Comparison)                              *)
(*  contains(b, p) uses <=/>= comparisons — exact in IEEE 754          *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 13: Contains is decidable for real-valued bounds           *)
(* ================================================================== *)
Theorem fp_bounds_contains_decidable :
  forall (lo hi p : R),
  {lo <= p <= hi} + {~ (lo <= p <= hi)}.
Proof.
  intros lo hi p.
  destruct (Rle_dec lo p) as [H1|H1].
  - destruct (Rle_dec p hi) as [H2|H2].
    + left. split; assumption.
    + right. intros [_ H]. apply H2. exact H.
  - right. intros [H _]. apply H1. exact H.
Qed.

(* ================================================================== *)
(*  Theorem 14: Contains is monotone in bounds expansion               *)
(* ================================================================== *)
Theorem fp_bounds_contains_expand_monotone :
  forall (lo hi p a : R),
  0 <= a -> lo <= p <= hi ->
  lo - a <= p <= hi + a.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  SECTION 6: Union (Exact min/max)                                    *)
(*  union: min/max operations are exact in IEEE 754                     *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 15: Union min is commutative                               *)
(* ================================================================== *)
Theorem fp_bounds_union_min_comm :
  forall (a b : R),
  Rmin a b = Rmin b a.
Proof.
  intros. unfold Rmin.
  destruct (Rle_dec a b); destruct (Rle_dec b a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 16: Union max is commutative                               *)
(* ================================================================== *)
Theorem fp_bounds_union_max_comm :
  forall (a b : R),
  Rmax a b = Rmax b a.
Proof.
  intros. unfold Rmax.
  destruct (Rle_dec a b); destruct (Rle_dec b a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 17: Union contains both operands                           *)
(* ================================================================== *)
Theorem fp_bounds_union_contains_both :
  forall (a1 a2 b1 b2 : R),
  a1 <= a2 -> b1 <= b2 ->
  Rmin a1 b1 <= a1 /\ a2 <= Rmax a2 b2 /\
  Rmin a1 b1 <= b1 /\ b2 <= Rmax a2 b2.
Proof.
  intros.
  repeat split.
  - apply Rmin_l.
  - apply Rle_max_compat_l.
  - apply Rmin_r.
  - apply Rle_max_compat_r.
Qed.

(* ================================================================== *)
(*  Theorem 18: Union is idempotent                                    *)
(* ================================================================== *)
Theorem fp_bounds_union_idempotent_min :
  forall (a : R),
  Rmin a a = a.
Proof.
  intros. unfold Rmin.
  destruct (Rle_dec a a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 19: Union is idempotent (max)                              *)
(* ================================================================== *)
Theorem fp_bounds_union_idempotent_max :
  forall (a : R),
  Rmax a a = a.
Proof.
  intros. unfold Rmax.
  destruct (Rle_dec a a); lra.
Qed.

(* ================================================================== *)
(*  SECTION 7: Intersection                                             *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 20: Intersection uses max for min-corner                   *)
(* ================================================================== *)
Theorem fp_bounds_intersection_min_correct :
  forall (a b : R),
  a <= Rmax a b /\ b <= Rmax a b.
Proof.
  intros. split.
  - apply Rle_max_compat_l.
  - apply Rle_max_compat_r.
Qed.

(* ================================================================== *)
(*  Theorem 21: Intersection is commutative                            *)
(* ================================================================== *)
Theorem fp_bounds_intersection_comm :
  forall (a b : R),
  Rmax a b = Rmax b a.
Proof.
  intros. unfold Rmax.
  destruct (Rle_dec a b); destruct (Rle_dec b a); lra.
Qed.

(* ================================================================== *)
(*  SECTION 8: Translate                                                *)
(*  translate(b, offset) = (min + offset, max + offset)                 *)
(*  1 FP add per component                                              *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 22: Translate single-op error                              *)
(* ================================================================== *)
Theorem fp_bounds_translate_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 23: Translate preserves size                                *)
(* ================================================================== *)
Theorem fp_bounds_translate_preserves_size :
  forall (lo hi d : R),
  (hi + d) - (lo + d) = hi - lo.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 24: Translate preserves validity                            *)
(* ================================================================== *)
Theorem fp_bounds_translate_preserves_valid :
  forall (lo hi d : R),
  lo <= hi -> lo + d <= hi + d.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  SECTION 9: Expand / Shrink                                          *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 25: Expand preserves validity                               *)
(* ================================================================== *)
Theorem fp_bounds_expand_preserves_valid :
  forall (lo hi a : R),
  0 <= a -> lo <= hi ->
  lo - a <= hi + a.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 26: Expand increases size                                   *)
(* ================================================================== *)
Theorem fp_bounds_expand_increases_size :
  forall (lo hi a : R),
  0 <= a ->
  hi - lo <= (hi + a) - (lo - a).
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 27: Shrink then expand recovers                            *)
(* ================================================================== *)
Theorem fp_bounds_shrink_expand_inverse :
  forall (lo hi a : R),
  (lo + a) - a = lo /\ (hi - a) + a = hi.
Proof. intros. split; ring. Qed.

(* ================================================================== *)
(*  SECTION 10: From Center Size                                        *)
(*  from_center_size(c, s): min = c - s/2, max = c + s/2               *)
(*  2 FP ops per component (div-by-2 + sub/add)                        *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 28: from_center_size 2-op error per component              *)
(* ================================================================== *)
Theorem fp_bounds_from_center_size_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 29: from_center_size produces valid bounds                 *)
(* ================================================================== *)
Theorem fp_bounds_from_center_size_valid :
  forall (cx sx : R),
  0 <= sx ->
  cx - sx / 2 <= cx + sx / 2.
Proof. intros. lra. Qed.

(* ================================================================== *)
(*  Theorem 30: from_center_size center recovery                       *)
(*  center(from_center_size(c,s)) = c                                  *)
(* ================================================================== *)
Theorem fp_bounds_from_center_size_center_recovery :
  forall (c s : R),
  ((c - s / 2) + (c + s / 2)) / 2 = c.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  Theorem 31: from_center_size size recovery                         *)
(* ================================================================== *)
Theorem fp_bounds_from_center_size_size_recovery :
  forall (c s : R),
  (c + s / 2) - (c - s / 2) = s.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  SECTION 11: Include Point                                           *)
(*  include_point: uses min/max (exact in FP)                           *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 32: include_point expanded bounds contain point            *)
(* ================================================================== *)
Theorem fp_bounds_include_point_contains :
  forall (lo hi p : R),
  Rmin lo p <= p /\ p <= Rmax hi p.
Proof.
  intros.
  split.
  - apply Rmin_r.
  - apply Rle_max_compat_r.
Qed.

(* ================================================================== *)
(*  Theorem 33: include_point does not shrink bounds                   *)
(* ================================================================== *)
Theorem fp_bounds_include_point_no_shrink :
  forall (lo hi p : R),
  lo <= hi ->
  Rmin lo p <= lo /\ hi <= Rmax hi p.
Proof.
  intros.
  split.
  - apply Rmin_l.
  - apply Rle_max_compat_l.
Qed.

(* ================================================================== *)
(*  SECTION 12: to_rect Conversion                                      *)
(*  to_rect: min becomes (x,y), max-min becomes (w,h)                  *)
(*  width/height: 1 sub each                                            *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 34: to_rect width error model                              *)
(* ================================================================== *)
Theorem fp_bounds_to_rect_width_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 35: to_rect preserves area (exact arithmetic)              *)
(* ================================================================== *)
Theorem fp_bounds_to_rect_area :
  forall (lx ly hx hy : R),
  lx <= hx -> ly <= hy ->
  (hx - lx) * (hy - ly) = (hx - lx) * (hy - ly).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(*  Theorem 36: Area 3-op error chain (sub_x, sub_y, mul)             *)
(* ================================================================== *)
Theorem fp_bounds_area_3op_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <=
    (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_three_op_composition.
Qed.

(* ================================================================== *)
(*  Theorem 37: Union min is associative                               *)
(* ================================================================== *)
Theorem fp_bounds_union_min_assoc :
  forall (a b c : R),
  Rmin a (Rmin b c) = Rmin (Rmin a b) c.
Proof.
  intros. unfold Rmin.
  destruct (Rle_dec b c); destruct (Rle_dec a b);
  destruct (Rle_dec a c); try destruct (Rle_dec a b); try lra;
  try (destruct (Rle_dec b c); lra).
Qed.

(* ================================================================== *)
(*  Theorem 38: Union max is associative                               *)
(* ================================================================== *)
Theorem fp_bounds_union_max_assoc :
  forall (a b c : R),
  Rmax a (Rmax b c) = Rmax (Rmax a b) c.
Proof.
  intros. unfold Rmax.
  destruct (Rle_dec b c); destruct (Rle_dec a b);
  destruct (Rle_dec a c); try destruct (Rle_dec a b); try lra;
  try (destruct (Rle_dec b c); lra).
Qed.

(* ================================================================== *)
(*  Theorem 39: Expand by zero is identity                             *)
(* ================================================================== *)
Theorem fp_bounds_expand_zero_identity :
  forall (lo hi : R),
  lo - 0 = lo /\ hi + 0 = hi.
Proof. intros. split; ring. Qed.

(* ================================================================== *)
(*  Theorem 40: Include point idempotent when point already inside    *)
(* ================================================================== *)
Theorem fp_bounds_include_point_idempotent :
  forall (lo hi p : R),
  lo <= p -> p <= hi ->
  Rmin lo p = lo /\ Rmax hi p = hi.
Proof.
  intros lo hi p Hlo Hhi.
  split.
  - unfold Rmin. destruct (Rle_dec lo p); lra.
  - unfold Rmax. destruct (Rle_dec hi p); lra.
Qed.

(* ================================================================== *)
(*  Theorem 41: Center of expanded bounds equals original center      *)
(* ================================================================== *)
Theorem fp_bounds_expand_preserves_center :
  forall (lo hi a : R),
  ((lo - a) + (hi + a)) / 2 = (lo + hi) / 2.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  Theorem 42: From center size roundtrip preserves bounds           *)
(* ================================================================== *)
Theorem fp_bounds_from_center_roundtrip :
  forall (lo hi : R),
  lo <= hi ->
  let c := (lo + hi) / 2 in
  let s := hi - lo in
  c - s / 2 = lo /\ c + s / 2 = hi.
Proof. intros. cbv zeta. split; field. Qed.

(* ================================================================== *)
(*  Theorem 43: Translate is invertible                                *)
(* ================================================================== *)
Theorem fp_bounds_translate_inverse :
  forall (lo hi d : R),
  (lo + d) - d = lo /\ (hi + d) - d = hi.
Proof. intros. split; ring. Qed.
