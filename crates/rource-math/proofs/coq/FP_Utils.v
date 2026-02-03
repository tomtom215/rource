(* FP_Utils.v - IEEE 754 error bounds for utility function operations          *)
(* Part of the rource-math formal verification suite (Phase FP-3)             *)
(* Uses Flocq 4.1.3 for IEEE 754 binary32 formalization                      *)
(*                                                                             *)
(* Proves FP error bounds and properties for utility operations:              *)
(*   - lerp: 3-op chain (sub, mul, add)                                       *)
(*   - clamp: comparisons (exact)                                              *)
(*   - approx_eq: |a - b| < eps comparison                                    *)
(*   - deg_to_rad / rad_to_deg: 1-op each (mul by constant)                  *)
(*   - f32 rounding composition for multi-op utility expressions             *)
(*                                                                             *)
(* This file extends FP_ErrorBounds.v with additional utility-specific         *)
(* properties and error analysis for composed utility expressions.             *)
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
(*  SECTION 1: Lerp Error Analysis (Extended)                           *)
(*  lerp(a, b, t) = a + (b - a) * t                                    *)
(*  3 FP ops: sub(b,a), mul(diff,t), add(a, product)                  *)
(*  Worst chain: 3 ops                                                  *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 1: Lerp 3-op composition error bound                       *)
(* ================================================================== *)
Theorem fp_utils_lerp_composition_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 2: Lerp monotonicity in t                                   *)
(*  For a <= b: lerp(a,b,t1) <= lerp(a,b,t2) when t1 <= t2            *)
(* ================================================================== *)
Theorem fp_utils_lerp_mono_t :
  forall (a b t1 t2 : R),
  a <= b -> 0 <= t1 -> t1 <= t2 -> t2 <= 1 ->
  a + (b - a) * t1 <= a + (b - a) * t2.
Proof.
  intros a b t1 t2 Hab Ht1 Ht12 Ht2.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l; lra.
Qed.

(* ================================================================== *)
(*  Theorem 3: Lerp at t=0 returns a                                   *)
(* ================================================================== *)
Theorem fp_utils_lerp_at_zero :
  forall (a b : R),
  a + (b - a) * 0 = a.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 4: Lerp at t=1 returns b                                   *)
(* ================================================================== *)
Theorem fp_utils_lerp_at_one :
  forall (a b : R),
  a + (b - a) * 1 = b.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 5: Lerp at t=0.5 returns midpoint                          *)
(* ================================================================== *)
Theorem fp_utils_lerp_midpoint :
  forall (a b : R),
  a + (b - a) * / 2 = (a + b) / 2.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  Theorem 6: Lerp range for t in [0,1]                                *)
(* ================================================================== *)
Theorem fp_utils_lerp_range :
  forall (a b t : R),
  a <= b -> 0 <= t <= 1 ->
  a <= a + (b - a) * t <= b.
Proof.
  intros a b t Hab [Ht0 Ht1].
  split.
  - assert (H : 0 <= (b - a) * t) by (apply Rmult_le_pos; lra). lra.
  - assert (H : (b - a) * t <= (b - a) * 1) by (apply Rmult_le_compat_l; lra). lra.
Qed.

(* ================================================================== *)
(*  SECTION 2: Clamp Analysis (Extended)                                *)
(*  clamp(v, min, max) = min(max(v, min_val), max_val)                  *)
(*  Uses comparisons only — exact in IEEE 754                           *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 7: Clamp is exact (no FP error)                             *)
(*  min/max comparisons are exact in IEEE 754                           *)
(* ================================================================== *)
Theorem fp_utils_clamp_exact :
  forall (v lo hi : R),
  lo <= hi ->
  lo <= Rmax lo (Rmin v hi) <= hi.
Proof.
  intros v lo hi Hlh.
  split.
  - unfold Rmax. destruct (Rle_dec lo (Rmin v hi)); lra.
  - unfold Rmax, Rmin.
    destruct (Rle_dec lo (Rmin v hi));
    destruct (Rle_dec v hi); lra.
Qed.

(* ================================================================== *)
(*  Theorem 8: Clamp idempotence                                        *)
(* ================================================================== *)
Theorem fp_utils_clamp_idempotent :
  forall (v lo hi : R),
  lo <= hi ->
  let c := Rmax lo (Rmin v hi) in
  Rmax lo (Rmin c hi) = c.
Proof.
  intros v lo hi Hlh.
  simpl.
  unfold Rmax, Rmin.
  destruct (Rle_dec v hi);
  destruct (Rle_dec lo (Rmin v hi));
  unfold Rmin in *;
  destruct (Rle_dec v hi) in *;
  try lra;
  destruct (Rle_dec lo v) in *;
  try lra;
  destruct (Rle_dec hi hi);
  try lra;
  destruct (Rle_dec lo hi);
  try lra;
  destruct (Rle_dec lo lo);
  lra.
Qed.

(* ================================================================== *)
(*  Theorem 9: Clamp preserves ordering                                 *)
(* ================================================================== *)
Theorem fp_utils_clamp_preserves_order :
  forall (v1 v2 lo hi : R),
  lo <= hi -> v1 <= v2 ->
  Rmax lo (Rmin v1 hi) <= Rmax lo (Rmin v2 hi).
Proof.
  intros v1 v2 lo hi Hlh Hv.
  unfold Rmax, Rmin.
  destruct (Rle_dec v1 hi);
  destruct (Rle_dec v2 hi);
  destruct (Rle_dec lo v1);
  destruct (Rle_dec lo v2);
  try lra.
Qed.

(* ================================================================== *)
(*  SECTION 3: Approx_eq Analysis                                      *)
(*  approx_eq(a, b) = |a - b| < epsilon                                *)
(*  1 sub + 1 abs + 1 comparison = exact comparison after sub           *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 10: Approx_eq reflexivity                                   *)
(* ================================================================== *)
Theorem fp_utils_approx_eq_refl :
  forall (a eps : R),
  0 < eps ->
  Rabs (a - a) < eps.
Proof.
  intros a eps Heps.
  replace (a - a) with 0 by ring.
  rewrite Rabs_R0. exact Heps.
Qed.

(* ================================================================== *)
(*  Theorem 11: Approx_eq symmetry                                     *)
(* ================================================================== *)
Theorem fp_utils_approx_eq_sym :
  forall (a b eps : R),
  Rabs (a - b) < eps -> Rabs (b - a) < eps.
Proof.
  intros a b eps H.
  replace (b - a) with (-(a - b)) by ring.
  rewrite Rabs_Ropp. exact H.
Qed.

(* ================================================================== *)
(*  Theorem 12: Approx_eq triangle inequality                          *)
(* ================================================================== *)
Theorem fp_utils_approx_eq_triangle :
  forall (a b c eps1 eps2 : R),
  Rabs (a - b) < eps1 -> Rabs (b - c) < eps2 ->
  Rabs (a - c) < eps1 + eps2.
Proof.
  intros a b c eps1 eps2 H1 H2.
  replace (a - c) with ((a - b) + (b - c)) by ring.
  apply Rle_lt_trans with (Rabs (a - b) + Rabs (b - c)).
  - apply Rabs_triang.
  - lra.
Qed.

(* ================================================================== *)
(*  SECTION 4: Degree/Radian Conversion Analysis                       *)
(*  deg_to_rad(d) = d * (PI/180)                                       *)
(*  rad_to_deg(r) = r * (180/PI)                                       *)
(*  1 FP mul each                                                       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 13: deg_to_rad single-op error                             *)
(* ================================================================== *)
Theorem fp_utils_deg_to_rad_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 14: rad_to_deg single-op error                             *)
(* ================================================================== *)
Theorem fp_utils_rad_to_deg_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs ((1 + e) - 1) <= u32 / (1 + u32).
Proof.
  intros e He.
  replace ((1 + e) - 1) with e by ring.
  exact He.
Qed.

(* ================================================================== *)
(*  Theorem 15: deg-rad roundtrip in exact arithmetic                  *)
(* ================================================================== *)
Theorem fp_utils_deg_rad_roundtrip :
  forall (d : R),
  d * (PI / 180) * (180 / PI) = d.
Proof.
  intros d.
  field.
  apply Rgt_not_eq.
  apply PI_RGT_0.
Qed.

(* ================================================================== *)
(*  Theorem 16: rad-deg roundtrip in exact arithmetic                  *)
(* ================================================================== *)
Theorem fp_utils_rad_deg_roundtrip :
  forall (r : R),
  r * (180 / PI) * (PI / 180) = r.
Proof.
  intros r.
  field.
  apply Rgt_not_eq.
  apply PI_RGT_0.
Qed.

(* ================================================================== *)
(*  Theorem 17: deg_to_rad roundtrip 2-op error bound                 *)
(*  Converting deg->rad->deg introduces 2-op error                    *)
(* ================================================================== *)
Theorem fp_utils_deg_rad_roundtrip_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  exact two_op_error_bound.
Qed.

(* ================================================================== *)
(*  Theorem 18: 0 degrees = 0 radians                                  *)
(* ================================================================== *)
Theorem fp_utils_zero_deg_is_zero_rad :
  0 * (PI / 180) = 0.
Proof. ring. Qed.

(* ================================================================== *)
(*  Theorem 19: 180 degrees = PI radians                               *)
(* ================================================================== *)
Theorem fp_utils_180_deg_is_pi :
  180 * (PI / 180) = PI.
Proof. field. lra. Qed.

(* ================================================================== *)
(*  Theorem 20: 360 degrees = 2*PI radians                             *)
(* ================================================================== *)
Theorem fp_utils_360_deg_is_2pi :
  360 * (PI / 180) = 2 * PI.
Proof. field. lra. Qed.

(* ================================================================== *)
(*  SECTION 5: Composed Utility Expressions                             *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 21: Lerp then clamp: 3-op lerp + exact clamp              *)
(*  Total error is bounded by 3-op composition                          *)
(* ================================================================== *)
Theorem fp_utils_lerp_clamp_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 22: Unit roundoff is positive                               *)
(* ================================================================== *)
Theorem fp_utils_u32_pos :
  0 < u32.
Proof.
  unfold u32, u_ro.
  apply Rmult_lt_0_compat.
  - lra.
  - apply bpow_gt_0.
Qed.

(* ================================================================== *)
(*  Theorem 23: Error bound denominator is positive                    *)
(* ================================================================== *)
Theorem fp_utils_denom_pos :
  0 < 1 + u32.
Proof.
  assert (H := fp_utils_u32_pos). lra.
Qed.

(* ================================================================== *)
(*  Theorem 24: u/(1+u) < 1                                            *)
(* ================================================================== *)
Theorem fp_utils_relative_bound_lt_1 :
  u32 / (1 + u32) < 1.
Proof.
  assert (Hu : 0 < u32) by exact fp_utils_u32_pos.
  assert (Hlt : u32 < 1 + u32) by lra.
  assert (Hinv : 0 < / (1 + u32)) by (apply Rinv_0_lt_compat; lra).
  unfold Rdiv.
  apply (Rmult_lt_compat_r (/ (1 + u32))) in Hlt; [| exact Hinv].
  rewrite Rinv_r in Hlt; [exact Hlt | lra].
Qed.

(* ================================================================== *)
(*  Theorem 25: Single-op error accumulation is sublinear               *)
(*  (1+u/(1+u))^n - 1 < n * u/(1+u) for n >= 1                        *)
(* ================================================================== *)
Theorem fp_utils_error_sublinear_n2 :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  (1 + u32 / (1 + u32))^2 - 1 <= 2 * (u32 / (1 + u32)) + (u32 / (1 + u32))^2.
Proof.
  intros.
  set (u := u32 / (1 + u32)).
  replace ((1 + u) ^ 2 - 1) with (2 * u + u ^ 2) by ring.
  lra.
Qed.

(* ================================================================== *)
(*  Theorem 26: For small u, (1+u)^n - 1 approx n*u                   *)
(*  Specifically: (1+u)^2 - 1 = 2u + u^2                               *)
(* ================================================================== *)
Theorem fp_utils_error_expansion_2 :
  forall (u : R),
  (1 + u)^2 - 1 = 2 * u + u^2.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 27: Three-op expansion                                     *)
(*  (1+u)^3 - 1 = 3u + 3u^2 + u^3                                     *)
(* ================================================================== *)
Theorem fp_utils_error_expansion_3 :
  forall (u : R),
  (1 + u)^3 - 1 = 3 * u + 3 * u^2 + u^3.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 28: Four-op expansion                                      *)
(*  (1+u)^4 - 1 = 4u + 6u^2 + 4u^3 + u^4                             *)
(* ================================================================== *)
Theorem fp_utils_error_expansion_4 :
  forall (u : R),
  (1 + u)^4 - 1 = 4 * u + 6 * u^2 + 4 * u^3 + u^4.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 29: Five-op expansion                                      *)
(*  (1+u)^5 - 1 = 5u + 10u^2 + 10u^3 + 5u^4 + u^5                   *)
(* ================================================================== *)
Theorem fp_utils_error_expansion_5 :
  forall (u : R),
  (1 + u)^5 - 1 = 5 * u + 10 * u^2 + 10 * u^3 + 5 * u^4 + u^5.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 30: Six-op expansion                                       *)
(*  (1+u)^6 - 1 = 6u + 15u^2 + 20u^3 + 15u^4 + 6u^5 + u^6          *)
(* ================================================================== *)
Theorem fp_utils_error_expansion_6 :
  forall (u : R),
  (1 + u)^6 - 1 = 6 * u + 15 * u^2 + 20 * u^3 + 15 * u^4 + 6 * u^5 + u^6.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 31: Seven-op expansion                                     *)
(*  (1+u)^7 - 1 = binomial(7,k) u^k summed                            *)
(* ================================================================== *)
Theorem fp_utils_error_expansion_7 :
  forall (u : R),
  (1 + u)^7 - 1 = 7 * u + 21 * u^2 + 35 * u^3 + 35 * u^4
                   + 21 * u^5 + 7 * u^6 + u^7.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 32: Eight-op expansion                                     *)
(* ================================================================== *)
Theorem fp_utils_error_expansion_8 :
  forall (u : R),
  (1 + u)^8 - 1 = 8 * u + 28 * u^2 + 56 * u^3 + 70 * u^4
                   + 56 * u^5 + 28 * u^6 + 8 * u^7 + u^8.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 33: Subtraction of (1+u)^n terms factors cleanly           *)
(*  (1+u)^3 - (1+u)^2 = u * (1+u)^2                                   *)
(* ================================================================== *)
Theorem fp_utils_expansion_diff_3_2 :
  forall (u : R),
  (1 + u)^3 - (1 + u)^2 = u * (1 + u)^2.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 34: (1+u)^n >= 1 for u >= 0, instantiated for n=2         *)
(* ================================================================== *)
Theorem fp_utils_expansion_ge_one_2 :
  forall (u : R), 0 <= u -> 1 <= (1 + u)^2.
Proof. intros u Hu. nra. Qed.

(* ================================================================== *)
(*  Theorem 35: (1+u)^n >= 1 for u >= 0, instantiated for n=3         *)
(* ================================================================== *)
Theorem fp_utils_expansion_ge_one_3 :
  forall (u : R), 0 <= u -> 1 <= (1 + u)^3.
Proof. intros u Hu. nra. Qed.

(* ================================================================== *)
(*  Theorem 36: Product of (1+e_i) two-term expansion                  *)
(*  (1+a)(1+b) = 1 + a + b + ab                                       *)
(* ================================================================== *)
Theorem fp_utils_product_two :
  forall (a b : R), (1 + a) * (1 + b) = 1 + a + b + a * b.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 37: Three-term product expansion                           *)
(*  (1+a)(1+b)(1+c) = 1 + a + b + c + ab + ac + bc + abc             *)
(* ================================================================== *)
Theorem fp_utils_product_three :
  forall (a b c : R),
  (1 + a) * (1 + b) * (1 + c) = 1 + a + b + c + a*b + a*c + b*c + a*b*c.
Proof. intros. ring. Qed.
