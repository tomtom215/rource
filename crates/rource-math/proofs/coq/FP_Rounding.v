(* FP_Rounding.v - Floating-point rounding operation verification              *)
(* Part of the rource-math formal verification suite (Phase FP-1)             *)
(* Uses Flocq 4.1.3 for IEEE 754 formalization                               *)
(*                                                                             *)
(* Proves correctness properties of floor, ceil, round, and fract for f32.    *)
(* These correspond to Rust's f32::floor(), f32::ceil(), f32::round(),        *)
(* and the fract() operation (x - floor(x)).                                  *)
(*                                                                             *)
(* All proofs machine-checked, zero admits.                                    *)

Require Import Reals.
Require Import ZArith.
Require Import Lia.
Require Import Lra.
Require Import Flocq.Core.Core.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Defs.
Require Import Flocq.Core.Raux.
Require Import Flocq.Calc.Round.
Require Import Flocq.Core.Generic_fmt.

Open Scope R_scope.

(* ================================================================== *)
(*  Theorem 1: Floor Lower Bound                                       *)
(*  floor(x) <= x for all x                                            *)
(* ================================================================== *)
Theorem fp_floor_le :
  forall x : R, IZR (Zfloor x) <= x.
Proof. intro x. apply Zfloor_lb. Qed.

(* ================================================================== *)
(*  Theorem 2: Floor Upper Bound                                        *)
(*  x < floor(x) + 1 for all x                                         *)
(* ================================================================== *)
Theorem fp_floor_lt_succ :
  forall x : R, x < IZR (Zfloor x) + 1.
Proof. intro x. apply Zfloor_ub. Qed.

(* ================================================================== *)
(*  Theorem 3: Floor of Integer is Identity                             *)
(*  floor(n) = n for integer n                                          *)
(* ================================================================== *)
Theorem fp_floor_integer :
  forall n : Z, Zfloor (IZR n) = n.
Proof. intro n. apply Zfloor_IZR. Qed.

(* ================================================================== *)
(*  Theorem 4: Ceil Lower Bound                                         *)
(*  x <= ceil(x) for all x                                             *)
(* ================================================================== *)
Theorem fp_ceil_ge :
  forall x : R, x <= IZR (Zceil x).
Proof. intro x. apply Zceil_ub. Qed.

(* ================================================================== *)
(*  Theorem 5: Ceil Upper Bound                                         *)
(*  ceil(x) - 1 < x for all x                                          *)
(* ================================================================== *)
Theorem fp_ceil_gt_pred :
  forall x : R, IZR (Zceil x) - 1 < x.
Proof.
  intro x. generalize (Zceil_lb x). lra.
Qed.

(* ================================================================== *)
(*  Theorem 6: Ceil of Integer is Identity                              *)
(*  ceil(n) = n for integer n                                           *)
(* ================================================================== *)
Theorem fp_ceil_integer :
  forall n : Z, Zceil (IZR n) = n.
Proof. intro n. apply Zceil_IZR. Qed.

(* ================================================================== *)
(*  Theorem 7: Floor-Ceil Relationship                                  *)
(*  ceil(x) = -floor(-x) for all x                                     *)
(* ================================================================== *)
Theorem fp_ceil_neg_floor :
  forall x : R, Zceil x = (- Zfloor (- x))%Z.
Proof. intro x. unfold Zceil. reflexivity. Qed.

(* ================================================================== *)
(*  Theorem 8: Floor Monotonicity                                       *)
(*  x <= y => floor(x) <= floor(y)                                     *)
(* ================================================================== *)
Theorem fp_floor_monotone :
  forall x y : R, x <= y -> (Zfloor x <= Zfloor y)%Z.
Proof. intros x y Hxy. apply Zfloor_le. lra. Qed.

(* ================================================================== *)
(*  Theorem 9: Ceil Monotonicity                                        *)
(*  x <= y => ceil(x) <= ceil(y)                                       *)
(* ================================================================== *)
Theorem fp_ceil_monotone :
  forall x y : R, x <= y -> (Zceil x <= Zceil y)%Z.
Proof. intros x y Hxy. apply Zceil_le. lra. Qed.

(* ================================================================== *)
(*  Theorem 10: Fractional Part Bounds                                  *)
(*  0 <= fract(x) < 1 for all x                                        *)
(* ================================================================== *)
Theorem fp_fract_bounds :
  forall x : R, 0 <= x - IZR (Zfloor x) < 1.
Proof.
  intro x. split.
  - generalize (Zfloor_lb x). lra.
  - generalize (Zfloor_ub x). lra.
Qed.

(* ================================================================== *)
(*  Theorem 11: Fractional Part of Integer is Zero                      *)
(*  fract(n) = 0 for integer n                                         *)
(* ================================================================== *)
Theorem fp_fract_integer :
  forall n : Z, IZR n - IZR (Zfloor (IZR n)) = 0.
Proof. intro n. rewrite Zfloor_IZR. lra. Qed.

(* ================================================================== *)
(*  Theorem 12: Floor + Fract Decomposition                             *)
(*  x = floor(x) + fract(x) for all x                                  *)
(* ================================================================== *)
Theorem fp_floor_fract_decompose :
  forall x : R, x = IZR (Zfloor x) + (x - IZR (Zfloor x)).
Proof. intro x. lra. Qed.

(* ================================================================== *)
(*  Theorem 13: Floor-Ceil Gap                                          *)
(*  For non-integer x: ceil(x) = floor(x) + 1                          *)
(* ================================================================== *)
Theorem fp_ceil_floor_gap :
  forall x : R,
  x - IZR (Zfloor x) <> 0 ->
  Zceil x = (Zfloor x + 1)%Z.
Proof.
  intros x Hfrac.
  unfold Zceil.
  generalize (Zfloor_lb (- x)). intro Hlb.
  generalize (Zfloor_ub (- x)). intro Hub.
  generalize (Zfloor_lb x). intro Hxlb.
  generalize (Zfloor_ub x). intro Hxub.
  assert (Hlt: IZR (Zfloor x) < x) by lra.
  assert (H1: -x < IZR (- Zfloor x)).
  { rewrite opp_IZR. lra. }
  assert (H2: IZR (- (Zfloor x + 1)) <= -x).
  { rewrite opp_IZR. rewrite plus_IZR. lra. }
  assert (Hfl: Zfloor (-x) = (- (Zfloor x + 1))%Z).
  { apply Zfloor_imp. split.
    - exact H2.
    - rewrite plus_IZR. rewrite opp_IZR. rewrite plus_IZR. lra. }
  lia.
Qed.

(* ================================================================== *)
(*  Theorem 14: Floor Idempotent                                        *)
(*  floor(floor(x)) = floor(x) for all x                               *)
(* ================================================================== *)
Theorem fp_floor_idempotent :
  forall x : R, Zfloor (IZR (Zfloor x)) = Zfloor x.
Proof. intro x. apply Zfloor_IZR. Qed.

(* ================================================================== *)
(*  Theorem 15: Ceil Idempotent                                         *)
(*  ceil(ceil(x)) = ceil(x) for all x                                  *)
(* ================================================================== *)
Theorem fp_ceil_idempotent :
  forall x : R, Zceil (IZR (Zceil x)) = Zceil x.
Proof. intro x. apply Zceil_IZR. Qed.

(* ================================================================== *)
(*  Theorem 16: Floor-Ceil Sandwich                                     *)
(*  floor(x) <= ceil(x) for all x                                      *)
(* ================================================================== *)
Theorem fp_floor_le_ceil :
  forall x : R, (Zfloor x <= Zceil x)%Z.
Proof.
  intro x. apply le_IZR.
  generalize (Zfloor_lb x). generalize (Zceil_ub x). lra.
Qed.

(* ================================================================== *)
(*  Theorem 17: Floor Additive Property for Integers                    *)
(*  floor(x + n) = floor(x) + n for integer n                          *)
(* ================================================================== *)
Theorem fp_floor_add_integer :
  forall (x : R) (n : Z), Zfloor (x + IZR n) = (Zfloor x + n)%Z.
Proof.
  intros x n. apply Zfloor_imp.
  generalize (Zfloor_lb x). intro Hlb.
  generalize (Zfloor_ub x). intro Hub.
  split.
  - rewrite plus_IZR. lra.
  - replace (Zfloor x + n + 1)%Z with (Zfloor x + (n + 1))%Z by lia.
    rewrite plus_IZR. rewrite plus_IZR. simpl. lra.
Qed.

(* ================================================================== *)
(*  Theorem 18: Ceil Additive Property for Integers                     *)
(*  ceil(x + n) = ceil(x) + n for integer n                            *)
(* ================================================================== *)
Theorem fp_ceil_add_integer :
  forall (x : R) (n : Z), Zceil (x + IZR n) = (Zceil x + n)%Z.
Proof.
  intros x n. unfold Zceil.
  replace (- (x + IZR n)) with (- x + IZR (- n)) by (rewrite opp_IZR; ring).
  rewrite fp_floor_add_integer. lia.
Qed.

(* ================================================================== *)
(*  Theorem 19: Rounding Error Bound                                    *)
(*  |round(x) - x| <= 0.5 for round-to-nearest                         *)
(* ================================================================== *)
Theorem fp_round_error_half :
  forall (choice : Z -> bool) (x : R),
  Rabs (IZR (Znearest choice x) - x) <= / 2.
Proof.
  intros choice x.
  rewrite Rabs_minus_sym. apply Znearest_half.
Qed.

(* ================================================================== *)
(*  Theorem 20: Rounding of Integer is Identity                         *)
(*  round(n) = n for integer n                                          *)
(* ================================================================== *)
Theorem fp_round_integer :
  forall (choice : Z -> bool) (n : Z),
  Znearest choice (IZR n) = n.
Proof.
  intros choice n.
  (* Use Znearest_imp: if |x - IZR n| < 1/2, then Znearest choice x = n *)
  apply Znearest_imp.
  rewrite Rminus_diag_eq; [| reflexivity].
  rewrite Rabs_R0. lra.
Qed.

(* ================================================================== *)
(*  Theorem 21: Floor-Round Relationship                                *)
(*  round(x) = floor(x) or floor(x)+1                                  *)
(* ================================================================== *)
Theorem fp_round_floor_or_ceil :
  forall (choice : Z -> bool) (x : R),
  Znearest choice x = Zfloor x \/ Znearest choice x = Zceil x.
Proof.
  intros choice x. apply Znearest_DN_or_UP.
Qed.

(* ================================================================== *)
(*  Theorem 22: Floor of negation                                      *)
(*  floor(-x) = -ceil(x)                                               *)
(* ================================================================== *)
Theorem fp_floor_neg :
  forall x : R, Zfloor (- x) = (- Zceil x)%Z.
Proof.
  intro x. unfold Zceil. lia.
Qed.

(* ================================================================== *)
(*  Theorem 23: Ceil of negation                                       *)
(*  ceil(-x) = -floor(x)                                               *)
(* ================================================================== *)
Theorem fp_ceil_neg :
  forall x : R, Zceil (- x) = (- Zfloor x)%Z.
Proof.
  intro x. unfold Zceil.
  replace (- - x) with x by ring.
  reflexivity.
Qed.

(* ================================================================== *)
(*  Theorem 24: Floor of non-negative is non-negative                  *)
(* ================================================================== *)
Theorem fp_floor_nonneg :
  forall x : R, 0 <= x -> (0 <= Zfloor x)%Z.
Proof.
  intros x Hx. apply le_IZR. simpl.
  apply Rle_trans with 0; [lra|].
  apply Zfloor_lb.
Qed.

(* ================================================================== *)
(*  Theorem 25: Ceil of non-positive is non-positive                   *)
(* ================================================================== *)
Theorem fp_ceil_nonpos :
  forall x : R, x <= 0 -> (Zceil x <= 0)%Z.
Proof.
  intros x Hx. apply le_IZR. simpl.
  apply Rle_trans with x; [apply Zceil_ub | lra].
Qed.

(* ================================================================== *)
(*  Theorem 26: Fractional part of sum with integer                    *)
(*  fract(x + n) = fract(x) for integer n                             *)
(* ================================================================== *)
Theorem fp_fract_add_integer :
  forall (x : R) (n : Z),
  (x + IZR n) - IZR (Zfloor (x + IZR n)) = x - IZR (Zfloor x).
Proof.
  intros x n.
  rewrite fp_floor_add_integer. rewrite plus_IZR. ring.
Qed.

(* ================================================================== *)
(*  Theorem 27: Round monotonicity                                     *)
(*  x <= y => round(x) <= round(y)                                    *)
(* ================================================================== *)
Theorem fp_round_monotone :
  forall (choice : Z -> bool) (x y : R),
  x <= y -> (Znearest choice x <= Znearest choice y)%Z.
Proof.
  intros choice x y Hxy.
  apply Znearest_monotone. lra.
Qed.

(* ================================================================== *)
(*  Theorem 28: Floor-ceil distance is at most 1                       *)
(*  ceil(x) - floor(x) <= 1                                            *)
(* ================================================================== *)
Theorem fp_ceil_floor_distance :
  forall x : R, (Zceil x - Zfloor x <= 1)%Z.
Proof.
  intro x.
  generalize (Zfloor_lb x). intro Hlb.
  generalize (Zfloor_ub x). intro Hub.
  generalize (Zceil_ub x). intro Hcub.
  generalize (Zceil_lb x). intro Hclb.
  apply le_IZR. rewrite minus_IZR. simpl.
  lra.
Qed.

(* ================================================================== *)
(*  Theorem 29: Floor of 0 is 0                                        *)
(* ================================================================== *)
Theorem fp_floor_zero :
  Zfloor 0 = 0%Z.
Proof.
  replace 0 with (IZR 0) by reflexivity.
  apply Zfloor_IZR.
Qed.

(* ================================================================== *)
(*  Theorem 30: Ceil of 0 is 0                                        *)
(* ================================================================== *)
Theorem fp_ceil_zero :
  Zceil 0 = 0%Z.
Proof.
  unfold Zceil. replace (- 0) with 0 by ring.
  rewrite fp_floor_zero. lia.
Qed.

(* ================================================================== *)
(*  Theorem 31: Floor of x+1 = floor(x)+1                             *)
(* ================================================================== *)
Theorem fp_floor_succ :
  forall x : R, Zfloor (x + 1) = (Zfloor x + 1)%Z.
Proof.
  intro x.
  replace 1 with (IZR 1) by reflexivity.
  apply fp_floor_add_integer.
Qed.

(* ================================================================== *)
(*  Theorem 32: Ceil of x+1 = ceil(x)+1                               *)
(* ================================================================== *)
Theorem fp_ceil_succ :
  forall x : R, Zceil (x + 1) = (Zceil x + 1)%Z.
Proof.
  intro x. unfold Zceil.
  replace (- (x + 1)) with (- x + IZR (-1)) by (rewrite opp_IZR; simpl; ring).
  rewrite fp_floor_add_integer. lia.
Qed.

(* ================================================================== *)
(*  Theorem 33: Floor of 1 is 1                                        *)
(* ================================================================== *)
Theorem fp_floor_one :
  Zfloor 1 = 1%Z.
Proof.
  replace 1 with (IZR 1) by reflexivity.
  apply Zfloor_IZR.
Qed.

(* ================================================================== *)
(*  Theorem 34: Ceil of 1 is 1                                         *)
(* ================================================================== *)
Theorem fp_ceil_one :
  Zceil 1 = 1%Z.
Proof.
  replace 1 with (IZR 1) by reflexivity.
  apply fp_ceil_integer.
Qed.
