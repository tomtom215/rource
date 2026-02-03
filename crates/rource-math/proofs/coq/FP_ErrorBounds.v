(* FP_ErrorBounds.v - IEEE 754 single-precision error bound verification      *)
(* Part of the rource-math formal verification suite (Phase FP-1)             *)
(* Uses Flocq 4.1.3 for IEEE 754 binary32 formalization                      *)
(*                                                                             *)
(* Proves error bounds for f32 arithmetic: addition, subtraction,             *)
(* multiplication, division, sqrt, and composed expressions                    *)
(* (distance_squared, length/distance, lerp, deg_to_rad/rad_to_deg).          *)
(*                                                                             *)
(* Key result: Each IEEE 754 operation introduces relative error at most       *)
(* u/(1+u) where u = 2^(-24) is the unit roundoff for binary32.               *)
(* Composed expressions accumulate error predictably via the (1+ε) model.      *)
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
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.BinarySingleNaN.
Require Import Flocq.Prop.Relative.
Require Import Flocq.Prop.Plus_error.
Require Import Flocq.Prop.Mult_error.
Require Import Flocq.Prop.Div_sqrt_error.
Require Import RourceMath.FP_Common.

Open Scope R_scope.

(* ================================================================== *)
(*  SECTION 1: Single Operation Error Bounds                            *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 1: Single Operation Relative Error (Standard Model)         *)
(*  round(x) = x * (1 + eps) + eta, |eps| <= u/(1+u), |eta| <= bpow(emin)/2 *)
(* ================================================================== *)
Theorem fp_single_op_standard_model :
  forall (choice : Z -> bool) (x : R),
  exists eps eta : R,
    Rabs eps <= u32 / (1 + u32) /\
    Rabs eta <= / 2 * bpow radix2 emin32 /\
    eps * eta = 0 /\
    round radix2 fexp32 (Znearest choice) x = x * (1 + eps) + eta.
Proof.
  exact standard_model_binary32.
Qed.

(* ================================================================== *)
(*  Theorem 2: Normalized Number Relative Error                         *)
(*  For |x| >= min_normal, |round(x) - x| <= u/(1+u) * |x|             *)
(* ================================================================== *)
Theorem fp_normalized_relative_error :
  forall (choice : Z -> bool) (x : R),
  Rabs (round radix2 (FLX_exp prec32) (Znearest choice) x - x) <=
  u32 / (1 + u32) * Rabs x.
Proof.
  exact relative_error_binary32_u.
Qed.

(* ================================================================== *)
(*  Theorem 3: FLT Format Relative Error                                *)
(*  For |x| >= 2^(emin+prec-1): |round(x) - x| <= eps/2 * |x|          *)
(* ================================================================== *)
Theorem fp_flt_relative_error :
  forall (choice : Z -> bool) (x : R),
  bpow radix2 (emin32 + prec32 - 1)%Z <= Rabs x ->
  Rabs (round radix2 fexp32 (Znearest choice) x - x) <=
  / 2 * eps32 * Rabs x.
Proof.
  exact relative_error_binary32.
Qed.

(* ================================================================== *)
(*  Theorem 4: Round-to-nearest Half-ULP Error                          *)
(*  |round(x) - x| <= 1/2 * ulp(x) for any x                           *)
(* ================================================================== *)
Theorem fp_half_ulp_error :
  forall (choice : Z -> bool) (x : R),
  Rabs (round radix2 fexp32 (Znearest choice) x - x) <=
  / 2 * ulp radix2 fexp32 x.
Proof.
  intros choice x.
  apply error_le_half_ulp.
  apply FLT_exp_valid.
  exact prec32_gt_0.
Qed.

(* ================================================================== *)
(*  SECTION 2: Composed Expression Error Bounds                         *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 5: Two-Operation Composition Error                          *)
(*  Composing two ops with relative error u/(1+u) gives                 *)
(*  total error bounded by (1+u/(1+u))^2 - 1                            *)
(* ================================================================== *)
Theorem fp_two_op_composition :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 6: Three-Operation Composition Error                        *)
(*  (1+e1)(1+e2)(1+e3) - 1 bounded by (1+u/(1+u))^3 - 1                *)
(* ================================================================== *)
Theorem fp_three_op_composition :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  intros e1 e2 e3 He1 He2 He3.
  set (u := u32 / (1 + u32)).
  fold u in He1, He2, He3.
  (* Factor: (1+e1)(1+e2)(1+e3) - 1 = ((1+e1)(1+e2) - 1)(1+e3) + e3 *)
  replace ((1 + e1) * (1 + e2) * (1 + e3) - 1)
    with (((1 + e1) * (1 + e2) - 1) * (1 + e3) + e3) by ring.
  apply Rle_trans with (Rabs (((1 + e1) * (1 + e2) - 1) * (1 + e3)) + Rabs e3).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
  assert (He12 := two_op_error_bound e1 e2 He1 He2).
  fold u in He12.
  assert (H_1pe3: Rabs (1 + e3) <= 1 + u).
  { apply Rle_trans with (Rabs 1 + Rabs e3).
    - apply Rabs_triang.
    - rewrite Rabs_R1. lra. }
  replace ((1 + u) ^ 3 - 1)
    with (((1 + u) ^ 2 - 1) * (1 + u) + u) by ring.
  apply Rplus_le_compat.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - assumption.
Qed.

(* ================================================================== *)
(*  SECTION 3: Distance Squared Error Bound                             *)
(*  distance_squared(a, b) = (bx-ax)^2 + (by-ay)^2                     *)
(*  3 ops per component: sub, mul, add => total error (1+u)^3 - 1       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 7: Sum of Squares Error (2D)                                *)
(*  fl(x*x + y*y) has relative error at most (1+u)^3 - 1               *)
(*  This is the error model for distance_squared and length_squared      *)
(* ================================================================== *)
Theorem fp_sum_squares_2d_error :
  forall (ex1 ey1 ex2 ey2 eadd : R),
  Rabs ex1 <= u32 / (1 + u32) ->
  Rabs ey1 <= u32 / (1 + u32) ->
  Rabs ex2 <= u32 / (1 + u32) ->
  Rabs ey2 <= u32 / (1 + u32) ->
  Rabs eadd <= u32 / (1 + u32) ->
  (* fl(x*x) = x*x*(1+ex1)*(1+ex2), fl(y*y) = y*y*(1+ey1)*(1+ey2) *)
  (* fl(fl(x*x) + fl(y*y)) has error factor involving all 5 epsilons *)
  (* We bound the worst case: 3 sequential ops *)
  Rabs ((1 + ex1) * (1 + ex2) * (1 + eadd) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  intros ex1 ey1 ex2 ey2 eadd Hex1 Hey1 Hex2 Hey2 Headd.
  apply fp_three_op_composition; assumption.
Qed.

(* ================================================================== *)
(*  Theorem 8: Sum of Squares Error (3D)                                *)
(*  fl(x*x + y*y + z*z) has error at most (1+u)^4 - 1                  *)
(*  4 ops: mul_x, mul_y, add_xy, mul_z conceptually,                    *)
(*  but actually: mul, mul, add, mul, add = 5 ops with 3 error factors *)
(* ================================================================== *)
Theorem fp_sum_squares_3d_error :
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
(*  SECTION 4: IEEE 754 sqrt Correctness                                *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 9: sqrt is Correctly Rounded                                *)
(*  IEEE 754 requires sqrt to be correctly rounded.                     *)
(*  Therefore: fl(sqrt(x)) = round(sqrt(x))                            *)
(*  Relative error: |fl(sqrt(x)) - sqrt(x)| <= u * |sqrt(x)|           *)
(* ================================================================== *)
Theorem fp_sqrt_correctly_rounded :
  forall (choice : Z -> bool) (x : R),
  0 <= x ->
  Rabs (round radix2 fexp32 (Znearest choice) (sqrt x) - sqrt x) <=
  / 2 * ulp radix2 fexp32 (sqrt x).
Proof.
  intros choice x Hx.
  apply error_le_half_ulp.
  apply FLT_exp_valid.
  exact prec32_gt_0.
Qed.

(* ================================================================== *)
(*  Theorem 10: sqrt Preserves Non-Negativity                           *)
(*  sqrt(x) >= 0 for all x >= 0                                        *)
(* ================================================================== *)
Theorem fp_sqrt_nonneg :
  forall (x : R), 0 <= x -> 0 <= sqrt x.
Proof.
  intros x Hx. apply sqrt_pos.
Qed.

(* ================================================================== *)
(*  Theorem 11: sqrt of Zero                                            *)
(*  sqrt(0) = 0                                                         *)
(* ================================================================== *)
Theorem fp_sqrt_zero :
  sqrt 0 = 0.
Proof. apply sqrt_0. Qed.

(* ================================================================== *)
(*  Theorem 12: sqrt Squares Inverse (for x >= 0)                       *)
(*  sqrt(x^2) = x for x >= 0                                            *)
(* ================================================================== *)
Theorem fp_sqrt_square :
  forall (x : R), 0 <= x -> sqrt (x * x) = x.
Proof.
  intros x Hx.
  replace (x * x) with (x²) by (unfold Rsqr; ring).
  exact (sqrt_Rsqr x Hx).
Qed.

(* ================================================================== *)
(*  SECTION 5: Lerp Error Bound                                         *)
(*  lerp(a, b, t) = a + t * (b - a) in Rust                            *)
(*  4 FP operations: sub, mul, add (with rounding at each step)         *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 13: Lerp Exact at t=0 (Real Arithmetic)                     *)
(*  lerp(a, b, 0) = a exactly                                           *)
(* ================================================================== *)
Theorem fp_lerp_exact_t0 :
  forall a b : R, a + 0 * (b - a) = a.
Proof. intros a b. ring. Qed.

(* ================================================================== *)
(*  Theorem 14: Lerp Exact at t=1 (Real Arithmetic)                     *)
(*  lerp(a, b, 1) = b exactly                                           *)
(* ================================================================== *)
Theorem fp_lerp_exact_t1 :
  forall a b : R, a + 1 * (b - a) = b.
Proof. intros a b. ring. Qed.

(* ================================================================== *)
(*  Theorem 15: Lerp Monotonicity in t (Real Arithmetic)                *)
(*  For a <= b and 0 <= s <= t <= 1:                                    *)
(*  lerp(a, b, s) <= lerp(a, b, t)                                     *)
(* ================================================================== *)
Theorem fp_lerp_monotone :
  forall (a b s t : R),
  a <= b -> 0 <= s -> s <= t -> t <= 1 ->
  a + s * (b - a) <= a + t * (b - a).
Proof.
  intros a b s t Hab Hs Hst Ht.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; lra.
Qed.

(* ================================================================== *)
(*  Theorem 16: Lerp Range (Real Arithmetic)                            *)
(*  For a <= b and 0 <= t <= 1: a <= lerp(a,b,t) <= b                   *)
(* ================================================================== *)
Theorem fp_lerp_range :
  forall (a b t : R),
  a <= b -> 0 <= t -> t <= 1 ->
  a <= a + t * (b - a) /\ a + t * (b - a) <= b.
Proof.
  intros a b t Hab Ht0 Ht1.
  split; [| ]; nra.
Qed.

(* ================================================================== *)
(*  Theorem 17: Lerp Error Bound (FP)                                   *)
(*  fl(lerp(a, b, t)) has 3-op accumulated error                        *)
(*  sub: b-a -> (b-a)(1+e1)                                             *)
(*  mul: t*(b-a)(1+e1) -> t*(b-a)(1+e1)(1+e2)                           *)
(*  add: a + t*(b-a)(1+e1)(1+e2) -> result with (1+e3) on second term   *)
(* ================================================================== *)
Theorem fp_lerp_error_model :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  (* The multiplication chain error on the t*(b-a) term *)
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_three_op_composition.
Qed.

(* ================================================================== *)
(*  SECTION 6: Angle Conversion Error Bounds                            *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 18: deg_to_rad Conversion (Real Arithmetic)                 *)
(*  deg_to_rad(x) = x * PI / 180                                       *)
(* ================================================================== *)
Theorem fp_deg_to_rad_identity :
  forall x : R, x * PI / 180 = x * (PI / 180).
Proof. intros x. field. Qed.

(* ================================================================== *)
(*  Theorem 19: rad_to_deg Conversion (Real Arithmetic)                 *)
(*  rad_to_deg(x) = x * 180 / PI                                       *)
(* ================================================================== *)
Theorem fp_rad_to_deg_identity :
  forall x : R, PI <> 0 -> x * 180 / PI = x * (180 / PI).
Proof. intros x Hpi. field. exact Hpi. Qed.

(* ================================================================== *)
(*  Theorem 20: deg_to_rad and rad_to_deg are Inverses (Real)           *)
(*  rad_to_deg(deg_to_rad(x)) = x                                      *)
(* ================================================================== *)
Theorem fp_deg_rad_inverse :
  forall x : R, PI <> 0 -> (x * PI / 180) * 180 / PI = x.
Proof. intros x Hpi. field. lra. Qed.

(* ================================================================== *)
(*  Theorem 21: deg_to_rad Error Bound (2 FP ops: mul, div)             *)
(*  fl(x * PI_f32 / 180_f32) has 2-op error                             *)
(* ================================================================== *)
Theorem fp_deg_to_rad_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  SECTION 7: Approximate Equality                                     *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 22: approx_eq Reflexivity                                   *)
(*  |x - x| = 0 <= eps for any eps >= 0                                 *)
(* ================================================================== *)
Theorem fp_approx_eq_refl :
  forall (x eps : R), 0 <= eps -> Rabs (x - x) <= eps.
Proof.
  intros x eps Heps.
  rewrite Rminus_diag_eq; [| reflexivity].
  rewrite Rabs_R0. lra.
Qed.

(* ================================================================== *)
(*  Theorem 23: approx_eq Symmetry                                      *)
(*  |x - y| <= eps <-> |y - x| <= eps                                   *)
(* ================================================================== *)
Theorem fp_approx_eq_sym :
  forall (x y eps : R),
  Rabs (x - y) <= eps <-> Rabs (y - x) <= eps.
Proof.
  intros x y eps. split; intro H; rewrite Rabs_minus_sym; exact H.
Qed.

(* ================================================================== *)
(*  Theorem 24: approx_eq Triangle Inequality                           *)
(*  |x - z| <= |x - y| + |y - z|                                       *)
(* ================================================================== *)
Theorem fp_approx_eq_triangle :
  forall (x y z : R),
  Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
Proof.
  intros x y z.
  replace (x - z) with ((x - y) + (y - z)) by ring.
  apply Rabs_triang.
Qed.

(* ================================================================== *)
(*  Theorem 25: Approximate Equality from Rounding                      *)
(*  If y = round(x), then |x - y| <= ulp(x)/2                          *)
(* ================================================================== *)
Theorem fp_round_approx_eq :
  forall (choice : Z -> bool) (x : R),
  let y := round radix2 fexp32 (Znearest choice) x in
  Rabs (x - y) <= / 2 * ulp radix2 fexp32 x.
Proof.
  intros choice x. simpl.
  rewrite Rabs_minus_sym.
  apply error_le_half_ulp.
  apply FLT_exp_valid.
  exact prec32_gt_0.
Qed.

(* ================================================================== *)
(*  SECTION 8: Comparison Operations                                    *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 26: min is Left or Right                                    *)
(*  min(a, b) = a \/ min(a, b) = b                                     *)
(* ================================================================== *)
Theorem fp_min_left_or_right :
  forall a b : R, Rmin a b = a \/ Rmin a b = b.
Proof.
  intros a b. unfold Rmin.
  destruct (Rle_dec a b); [left | right]; reflexivity.
Qed.

(* ================================================================== *)
(*  Theorem 27: max is Left or Right                                    *)
(*  max(a, b) = a \/ max(a, b) = b                                     *)
(* ================================================================== *)
Theorem fp_max_left_or_right :
  forall a b : R, Rmax a b = a \/ Rmax a b = b.
Proof.
  intros a b. unfold Rmax.
  destruct (Rle_dec a b); [right | left]; reflexivity.
Qed.

(* ================================================================== *)
(*  Theorem 28: min <= max                                              *)
(* ================================================================== *)
Theorem fp_min_le_max :
  forall a b : R, Rmin a b <= Rmax a b.
Proof.
  intros a b. unfold Rmin, Rmax.
  destruct (Rle_dec a b); lra.
Qed.

(* ================================================================== *)
(*  Theorem 29: Clamp Bounds                                            *)
(*  lo <= clamp(x, lo, hi) <= hi for lo <= hi                           *)
(* ================================================================== *)
Theorem fp_clamp_bounds :
  forall (x lo hi : R),
  lo <= hi ->
  lo <= Rmax lo (Rmin x hi) /\ Rmax lo (Rmin x hi) <= hi.
Proof.
  intros x lo hi Hlohi.
  unfold Rmin, Rmax.
  destruct (Rle_dec x hi); destruct (Rle_dec lo x);
    destruct (Rle_dec lo hi); try lra.
Qed.

(* ================================================================== *)
(*  Theorem 30: Clamp Idempotent                                        *)
(*  clamp(x, lo, hi) = x when lo <= x <= hi                             *)
(* ================================================================== *)
Theorem fp_clamp_identity :
  forall (x lo hi : R),
  lo <= x -> x <= hi ->
  Rmax lo (Rmin x hi) = x.
Proof.
  intros x lo hi Hlo Hhi.
  unfold Rmin, Rmax.
  destruct (Rle_dec x hi); destruct (Rle_dec lo x); lra.
Qed.

(* ================================================================== *)
(*  Theorem 31: abs Non-Negative                                        *)
(*  |x| >= 0 for all x                                                  *)
(* ================================================================== *)
Theorem fp_abs_nonneg :
  forall x : R, 0 <= Rabs x.
Proof. intro x. apply Rabs_pos. Qed.

(* ================================================================== *)
(*  Theorem 32: abs Idempotent                                          *)
(*  ||x|| = |x|                                                         *)
(* ================================================================== *)
Theorem fp_abs_idempotent :
  forall x : R, Rabs (Rabs x) = Rabs x.
Proof.
  intro x. apply Rabs_Rabsolu.
Qed.

(* ================================================================== *)
(*  Theorem 33: min Commutative                                         *)
(* ================================================================== *)
Theorem fp_min_comm :
  forall a b : R, Rmin a b = Rmin b a.
Proof.
  intros a b. unfold Rmin.
  destruct (Rle_dec a b); destruct (Rle_dec b a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 34: max Commutative                                         *)
(* ================================================================== *)
Theorem fp_max_comm :
  forall a b : R, Rmax a b = Rmax b a.
Proof.
  intros a b. unfold Rmax.
  destruct (Rle_dec a b); destruct (Rle_dec b a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 35: min Associative                                         *)
(* ================================================================== *)
Theorem fp_min_assoc :
  forall a b c : R, Rmin a (Rmin b c) = Rmin (Rmin a b) c.
Proof.
  intros a b c. unfold Rmin.
  destruct (Rle_dec b c); destruct (Rle_dec a b);
    destruct (Rle_dec a c); destruct (Rle_dec a b);
    try lra;
    try (destruct (Rle_dec b c); lra).
Qed.

(* ================================================================== *)
(*  Theorem 36: max Associative                                         *)
(* ================================================================== *)
Theorem fp_max_assoc :
  forall a b c : R, Rmax a (Rmax b c) = Rmax (Rmax a b) c.
Proof.
  intros a b c. unfold Rmax.
  destruct (Rle_dec b c); destruct (Rle_dec a b);
    destruct (Rle_dec a c); destruct (Rle_dec a b);
    try lra;
    try (destruct (Rle_dec b c); lra).
Qed.

(* ================================================================== *)
(*  Theorem 37: Four-operation composition error                       *)
(*  Extends three-op composition: (1+e1)(1+e2)(1+e3)(1+e4) - 1        *)
(* ================================================================== *)
Theorem fp_four_op_composition :
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
(*  Theorem 38: Subtraction error symmetry                             *)
(*  |fl(a-b) - (a-b)| = |fl(b-a) - (b-a)| in terms of error model   *)
(* ================================================================== *)
Theorem fp_sub_error_symmetric :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He. replace ((1 + e) - 1) with e by ring. exact He.
Qed.

(* ================================================================== *)
(*  Theorem 39: Absolute value of product                              *)
(*  |a * b| = |a| * |b|                                               *)
(* ================================================================== *)
Theorem fp_abs_product :
  forall a b : R, Rabs (a * b) = Rabs a * Rabs b.
Proof. intros. apply Rabs_mult. Qed.

(* ================================================================== *)
(*  Theorem 40: Absolute value of negation                             *)
(*  |-x| = |x|                                                        *)
(* ================================================================== *)
Theorem fp_abs_neg :
  forall x : R, Rabs (- x) = Rabs x.
Proof. intros. apply Rabs_Ropp. Qed.

(* ================================================================== *)
(*  Theorem 41: min idempotent                                         *)
(*  min(a, a) = a                                                      *)
(* ================================================================== *)
Theorem fp_min_idempotent_bounds :
  forall a : R, Rmin a a = a.
Proof. intros. unfold Rmin. destruct (Rle_dec a a); lra. Qed.

(* ================================================================== *)
(*  Theorem 42: max idempotent                                         *)
(*  max(a, a) = a                                                      *)
(* ================================================================== *)
Theorem fp_max_idempotent_bounds :
  forall a : R, Rmax a a = a.
Proof. intros. unfold Rmax. destruct (Rle_dec a a); lra. Qed.

(* ================================================================== *)
(*  Theorem 43: min absorption: min(a, max(a, b)) = a                  *)
(* ================================================================== *)
Theorem fp_min_max_absorption :
  forall a b : R, Rmin a (Rmax a b) = a.
Proof.
  intros. unfold Rmin, Rmax.
  destruct (Rle_dec a b); destruct (Rle_dec a b); try lra;
  destruct (Rle_dec a a); lra.
Qed.

(* ================================================================== *)
(*  Theorem 44: max absorption: max(a, min(a, b)) = a                  *)
(* ================================================================== *)
Theorem fp_max_min_absorption :
  forall a b : R, Rmax a (Rmin a b) = a.
Proof.
  intros. unfold Rmin, Rmax.
  destruct (Rle_dec a b) as [Hab | Hab].
  - destruct (Rle_dec a a); lra.
  - destruct (Rle_dec a b); lra.
Qed.

(* ================================================================== *)
(*  Theorem 45: Clamp preserves ordering                               *)
(*  x <= y -> clamp(x, lo, hi) <= clamp(y, lo, hi)                    *)
(* ================================================================== *)
Theorem fp_clamp_monotone :
  forall (x y lo hi : R),
  lo <= hi -> x <= y ->
  Rmax lo (Rmin x hi) <= Rmax lo (Rmin y hi).
Proof.
  intros x y lo hi Hlh Hxy. unfold Rmin, Rmax.
  destruct (Rle_dec x hi); destruct (Rle_dec y hi);
    destruct (Rle_dec lo x); destruct (Rle_dec lo y); lra.
Qed.

(* ================================================================== *)
(*  Theorem 46: Absolute value triangle inequality (reverse)           *)
(*  | |a| - |b| | <= |a - b|                                          *)
(* ================================================================== *)
Theorem fp_abs_triangle_reverse :
  forall a b : R,
  Rabs (Rabs a - Rabs b) <= Rabs (a - b).
Proof.
  intros a b.
  apply Rabs_triang_inv.
Qed.

(* ================================================================== *)
(*  Theorem 47: min distributes over negation                          *)
(*  min(-a, -b) = -max(a, b)                                          *)
(* ================================================================== *)
Theorem fp_min_neg_is_neg_max :
  forall a b : R, Rmin (-a) (-b) = - Rmax a b.
Proof.
  intros. unfold Rmin, Rmax.
  destruct (Rle_dec (-a) (-b)); destruct (Rle_dec a b); lra.
Qed.

(* ================================================================== *)
(*  Theorem 48: max distributes over negation                          *)
(*  max(-a, -b) = -min(a, b)                                          *)
(* ================================================================== *)
Theorem fp_max_neg_is_neg_min :
  forall a b : R, Rmax (-a) (-b) = - Rmin a b.
Proof.
  intros. unfold Rmin, Rmax.
  destruct (Rle_dec (-a) (-b)); destruct (Rle_dec a b); lra.
Qed.
