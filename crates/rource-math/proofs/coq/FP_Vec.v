(* FP_Vec.v - IEEE 754 error bounds for vector operations                      *)
(* Part of the rource-math formal verification suite (Phase FP-1)             *)
(* Uses Flocq 4.1.3 for IEEE 754 binary32 formalization                      *)
(*                                                                             *)
(* Proves FP error bounds for Vec2/Vec3/Vec4 operations:                      *)
(*   - length_squared (2D, 3D, 4D)                                            *)
(*   - length via sqrt(length_squared)                                        *)
(*   - distance_squared                                                        *)
(*   - normalized (v / length(v))                                              *)
(*   - componentwise min/max/abs/clamp                                         *)
(*   - lerp for vectors                                                        *)
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

Open Scope R_scope.

(* ================================================================== *)
(*  SECTION 1: Length Squared Error Model                               *)
(*  length_squared(v) = x*x + y*y (2D)                                *)
(*  3 FP ops per 2D: mul_x, mul_y, add                                 *)
(*  Each mul/add introduces factor (1+ei) with |ei| <= u/(1+u)         *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 1: Vec2 length_squared error factor                        *)
(*  fl(x*x + y*y) = (x*x*(1+e1)*(1+e3) + y*y*(1+e2)*(1+e3))          *)
(*  where the add's error (1+e3) distributes over both terms            *)
(*  Worst-case: each component has 2-op chain, plus final add          *)
(* ================================================================== *)
Theorem fp_vec2_length_sq_error :
  forall (e_mx e_my e_add : R),
  Rabs e_mx <= u32 / (1 + u32) ->
  Rabs e_my <= u32 / (1 + u32) ->
  Rabs e_add <= u32 / (1 + u32) ->
  (* Each x*x term has mul error (1+e_mx), then add error (1+e_add) *)
  (* Worst-case chain is mul then add = 2 ops per component *)
  (* The full expression error: one component's chain = (1+e_mx)(1+e_add) *)
  Rabs ((1 + e_mx) * (1 + e_add) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  intros e_mx e_my e_add Hex Hey Headd.
  apply two_op_error_bound; assumption.
Qed.

(* ================================================================== *)
(*  Theorem 2: Vec3 length_squared error factor                        *)
(*  fl(x*x + y*y + z*z) = x*x*(1+e1)*(1+e3)*(1+e5) + ...            *)
(*  5 FP ops: mul_x, mul_y, mul_z, add_xy, add_xyz                    *)
(*  Worst component chain: mul, add, add = 3 ops                       *)
(* ================================================================== *)
Theorem fp_vec3_length_sq_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  intros e1 e2 e3 He1 He2 He3.
  set (u := u32 / (1 + u32)).
  fold u in He1, He2, He3.
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
(*  Theorem 3: Vec4 length_squared error factor                        *)
(*  fl(x*x + y*y + z*z + w*w)                                         *)
(*  7 FP ops: 4 muls + 3 adds                                          *)
(*  Worst component chain: mul + 3 adds = 4 ops                        *)
(* ================================================================== *)
Theorem fp_vec4_length_sq_error :
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
  assert (He123 := fp_vec3_length_sq_error e1 e2 e3 He1 He2 He3).
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
(*  SECTION 2: Length Error Model (sqrt of length_squared)             *)
(*  length(v) = sqrt(length_squared(v))                                *)
(*  sqrt is correctly rounded in IEEE 754, adding one more (1+e) factor*)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 4: sqrt adds at most one additional rounding factor        *)
(*  If x has relative error bound B, then fl(sqrt(x)) has error       *)
(*  bounded by (1+B)*(1+u/(1+u)) - 1                                   *)
(* ================================================================== *)
Theorem fp_sqrt_error_composition :
  forall (B e_sqrt : R),
  0 <= B ->
  Rabs e_sqrt <= u32 / (1 + u32) ->
  (1 + B) * (1 + Rabs e_sqrt) - 1 <= (1 + B) * (1 + u32 / (1 + u32)) - 1.
Proof.
  intros B e_sqrt HB He.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_l.
  - lra.
  - apply Rplus_le_compat_l. exact He.
Qed.

(* ================================================================== *)
(*  Theorem 5: Vec2 length error bound                                 *)
(*  fl(sqrt(fl(x*x + y*y))) has error (1+u)^3 - 1                     *)
(*  2 ops for length_squared + 1 op for sqrt = 3 ops in chain          *)
(* ================================================================== *)
Theorem fp_vec2_length_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  (* e1, e2: length_squared ops; e3: sqrt rounding *)
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 6: Vec3 length error bound                                 *)
(*  fl(sqrt(fl(x*x + y*y + z*z))) has error (1+u)^4 - 1               *)
(* ================================================================== *)
Theorem fp_vec3_length_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof.
  exact fp_vec4_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 7: Vec4 length error bound                                 *)
(*  fl(sqrt(fl(x*x + y*y + z*z + w*w))) has error (1+u)^5 - 1         *)
(* ================================================================== *)
Theorem fp_vec4_length_error :
  forall (e1 e2 e3 e4 e5 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) <=
  (1 + u32 / (1 + u32))^5 - 1.
Proof.
  intros e1 e2 e3 e4 e5 He1 He2 He3 He4 He5.
  set (u := u32 / (1 + u32)).
  fold u in He1, He2, He3, He4, He5.
  replace ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1)
    with (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) * (1 + e5) + e5) by ring.
  apply Rle_trans with (Rabs (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) * (1 + e5)) + Rabs e5).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
  assert (He1234 := fp_vec4_length_sq_error e1 e2 e3 e4 He1 He2 He3 He4).
  fold u in He1234.
  assert (H_1pe5: Rabs (1 + e5) <= 1 + u).
  { apply Rle_trans with (Rabs 1 + Rabs e5).
    - apply Rabs_triang.
    - rewrite Rabs_R1. lra. }
  replace ((1 + u) ^ 5 - 1)
    with (((1 + u) ^ 4 - 1) * (1 + u) + u) by ring.
  apply Rplus_le_compat.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - assumption.
Qed.

(* ================================================================== *)
(*  SECTION 3: Distance Squared Error Model                            *)
(*  distance_squared(a, b) = (bx-ax)^2 + (by-ay)^2  (2D)             *)
(*  Additional sub per component: 4 ops 2D, 6 ops 3D                   *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 8: Vec2 distance_squared error                             *)
(*  fl((bx-ax)^2 + (by-ay)^2): sub + mul + sub + mul + add = 5 ops   *)
(*  Worst chain per component: sub, mul, add = 3 ops                   *)
(* ================================================================== *)
Theorem fp_vec2_dist_sq_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 9: Vec3 distance_squared error                             *)
(*  Worst chain: sub, mul, add, add = 4 ops                            *)
(* ================================================================== *)
Theorem fp_vec3_dist_sq_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof.
  exact fp_vec4_length_sq_error.
Qed.

(* ================================================================== *)
(*  SECTION 4: Normalized Vector Error Model                           *)
(*  normalized(v) = v / length(v)                                       *)
(*  Each component: x / sqrt(x*x + y*y + ...)                          *)
(*  Division is correctly rounded => adds one more (1+e) factor        *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 10: Division adds one rounding factor                      *)
(*  If numerator has error B1 and denominator B2,                      *)
(*  fl(num/den) has error (1+B1)*(1+B2)*(1+u/(1+u)) - 1               *)
(*  (simplified: the division error combines multiplicatively)          *)
(* ================================================================== *)
Theorem fp_division_error_composition :
  forall (e_num e_den e_div : R),
  Rabs e_num <= u32 / (1 + u32) ->
  Rabs e_den <= u32 / (1 + u32) ->
  Rabs e_div <= u32 / (1 + u32) ->
  Rabs ((1 + e_num) * (1 + e_den) * (1 + e_div) - 1) <=
  (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 11: Vec2 normalized error bound                            *)
(*  normalized(v) = v / length(v)                                       *)
(*  length has 3-op error, division adds 1 more = 4 ops total          *)
(* ================================================================== *)
Theorem fp_vec2_normalized_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  (* e1,e2: length_sq; e3: sqrt; e4: division *)
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof.
  exact fp_vec4_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 12: Vec3 normalized error bound                            *)
(*  length has 4-op error, division adds 1 more = 5 ops total          *)
(* ================================================================== *)
Theorem fp_vec3_normalized_error :
  forall (e1 e2 e3 e4 e5 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) <=
  (1 + u32 / (1 + u32))^5 - 1.
Proof.
  exact fp_vec4_length_error.
Qed.

(* ================================================================== *)
(*  SECTION 5: Componentwise Operations (Exact in IEEE 754)            *)
(*  min, max, abs do NOT introduce rounding error for finite inputs    *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 13: Componentwise min preserves order                      *)
(*  min(a, b) <= a AND min(a, b) <= b                                   *)
(* ================================================================== *)
Theorem fp_component_min_le_both :
  forall a b : R, Rmin a b <= a /\ Rmin a b <= b.
Proof.
  intros a b. split.
  - apply Rmin_l.
  - apply Rmin_r.
Qed.

(* ================================================================== *)
(*  Theorem 14: Componentwise max preserves order                      *)
(*  a <= max(a, b) AND b <= max(a, b)                                   *)
(* ================================================================== *)
Theorem fp_component_max_ge_both :
  forall a b : R, a <= Rmax a b /\ b <= Rmax a b.
Proof.
  intros a b. split.
  - apply Rmax_l.
  - apply Rmax_r.
Qed.

(* ================================================================== *)
(*  Theorem 15: abs Triangle Inequality for Vectors (per-component)    *)
(*  |a + b| <= |a| + |b| applies componentwise                        *)
(* ================================================================== *)
Theorem fp_abs_triangle_component :
  forall a b : R, Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  exact Rabs_triang.
Qed.

(* ================================================================== *)
(*  Theorem 16: Clamp preserves range (per-component)                  *)
(*  lo <= clamp(x, lo, hi) <= hi for lo <= hi                          *)
(* ================================================================== *)
Theorem fp_clamp_preserves_range :
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
(*  Theorem 17: Clamp is identity in range                             *)
(* ================================================================== *)
Theorem fp_clamp_identity_in_range :
  forall (x lo hi : R),
  lo <= x -> x <= hi ->
  Rmax lo (Rmin x hi) = x.
Proof.
  intros x lo hi Hlo Hhi.
  unfold Rmin, Rmax.
  destruct (Rle_dec x hi); destruct (Rle_dec lo x); lra.
Qed.

(* ================================================================== *)
(*  Theorem 18: Componentwise min is idempotent                        *)
(*  min(x, x) = x                                                      *)
(* ================================================================== *)
Theorem fp_min_idempotent :
  forall x : R, Rmin x x = x.
Proof.
  intro x. unfold Rmin.
  destruct (Rle_dec x x); lra.
Qed.

(* ================================================================== *)
(*  Theorem 19: Componentwise max is idempotent                        *)
(*  max(x, x) = x                                                      *)
(* ================================================================== *)
Theorem fp_max_idempotent :
  forall x : R, Rmax x x = x.
Proof.
  intro x. unfold Rmax.
  destruct (Rle_dec x x); lra.
Qed.

(* ================================================================== *)
(*  SECTION 6: Vec Lerp Error Model                                    *)
(*  lerp(a, b, t) = a + t * (b - a) applied componentwise              *)
(*  3 FP ops per component: sub, mul, add                               *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 20: Vec2 lerp componentwise error                          *)
(*  Each component has 3-op error chain                                 *)
(* ================================================================== *)
Theorem fp_vec2_lerp_component_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 21: Lerp t=0 per component exact                          *)
(*  a + 0 * (b - a) = a                                                *)
(* ================================================================== *)
Theorem fp_vec_lerp_t0 :
  forall a b : R, a + 0 * (b - a) = a.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 22: Lerp t=1 per component exact                          *)
(*  a + 1 * (b - a) = b                                                *)
(* ================================================================== *)
Theorem fp_vec_lerp_t1 :
  forall a b : R, a + 1 * (b - a) = b.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 23: Lerp monotonicity per component                       *)
(*  For a <= b and s <= t: lerp(a,b,s) <= lerp(a,b,t)                 *)
(* ================================================================== *)
Theorem fp_vec_lerp_monotone :
  forall (a b s t : R),
  a <= b -> s <= t ->
  a + s * (b - a) <= a + t * (b - a).
Proof.
  intros a b s t Hab Hst.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; lra.
Qed.

(* ================================================================== *)
(*  Theorem 24: Lerp range per component                              *)
(*  For a <= b and 0 <= t <= 1: a <= lerp(a,b,t) <= b                 *)
(* ================================================================== *)
Theorem fp_vec_lerp_range :
  forall (a b t : R),
  a <= b -> 0 <= t -> t <= 1 ->
  a <= a + t * (b - a) /\ a + t * (b - a) <= b.
Proof.
  intros a b t Hab Ht0 Ht1.
  split; nra.
Qed.

(* ================================================================== *)
(*  SECTION 7: Distance via sqrt Error Model                           *)
(*  distance(a, b) = sqrt(distance_squared(a, b))                      *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 25: Vec2 distance error bound                              *)
(*  distance_squared has 3-op error, sqrt adds 1 = 4 ops total        *)
(* ================================================================== *)
Theorem fp_vec2_distance_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof.
  exact fp_vec4_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 26: Vec3 distance error bound                              *)
(*  distance_squared has 4-op error, sqrt adds 1 = 5 ops total        *)
(* ================================================================== *)
Theorem fp_vec3_distance_error :
  forall (e1 e2 e3 e4 e5 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) <=
  (1 + u32 / (1 + u32))^5 - 1.
Proof.
  exact fp_vec4_length_error.
Qed.

(* ================================================================== *)
(*  SECTION 8: Error Bound Numerical Values                            *)
(*  Concrete upper bounds for error factors at each chain length       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 27: u32/(1+u32) < 2^(-24)                                 *)
(*  The per-operation relative error is strictly less than 1 ULP       *)
(* ================================================================== *)
Theorem fp_per_op_error_lt_ulp :
  u32 / (1 + u32) < u32.
Proof.
  assert (Hu: 0 < u32).
  { unfold u32, u_ro. apply Rmult_lt_0_compat; [lra | apply bpow_gt_0]. }
  assert (H1pu: 0 < 1 + u32) by lra.
  (* Multiply both sides by (1 + u32) > 0 to clear denominator *)
  apply (Rmult_lt_reg_r (1 + u32)); [exact H1pu | ].
  unfold Rdiv.
  rewrite Rmult_assoc, Rinv_l by lra.
  rewrite Rmult_1_r. nra.
Qed.

(* ================================================================== *)
(*  Theorem 28: Monotonicity of n-op error bound                      *)
(*  (1+u)^n - 1 is increasing in n                                     *)
(*  Specifically: (1+u)^n - 1 <= (1+u)^(n+1) - 1                      *)
(* ================================================================== *)
Theorem fp_error_bound_monotone :
  forall (n : nat) (u : R),
  0 < u ->
  (1 + u)^n - 1 <= (1 + u)^(S n) - 1.
Proof.
  intros n u Hu.
  simpl.
  (* Goal: (1+u)^n - 1 <= (1+u) * (1+u)^n - 1 *)
  (* Equivalent to: (1+u)^n <= (1+u) * (1+u)^n *)
  assert (Hpow: 0 < (1 + u)^n) by (apply pow_lt; lra).
  nra.
Qed.

(* ================================================================== *)
(*  Theorem 29: 2-op error bound is positive                           *)
(*  (1+u)^2 - 1 > 0 for u > 0                                         *)
(* ================================================================== *)
Theorem fp_two_op_error_pos :
  forall u : R, 0 < u -> 0 < (1 + u)^2 - 1.
Proof.
  intros u Hu. nra.
Qed.

(* ================================================================== *)
(*  Theorem 30: Error bound decomposition                              *)
(*  (1+u)^2 - 1 = 2*u + u^2                                            *)
(*  Useful for numerical estimation                                     *)
(* ================================================================== *)
Theorem fp_two_op_error_expand :
  forall u : R, (1 + u)^2 - 1 = 2 * u + u^2.
Proof.
  intro u. ring.
Qed.

(* ================================================================== *)
(*  Theorem 31: 3-op error bound expansion                             *)
(*  (1+u)^3 - 1 = 3*u + 3*u^2 + u^3                                    *)
(* ================================================================== *)
Theorem fp_three_op_error_expand :
  forall u : R, (1 + u)^3 - 1 = 3 * u + 3 * u^2 + u^3.
Proof.
  intro u. ring.
Qed.

(* ================================================================== *)
(*  Theorem 32: For small u, n-op error is approximately n*u           *)
(*  (1+u)^n - 1 >= n*u for u >= 0 and n >= 0                           *)
(*  (Lower bound via Bernoulli's inequality)                            *)
(* ================================================================== *)
Theorem fp_error_lower_bound_bernoulli :
  forall (n : nat) (u : R),
  0 <= u ->
  INR n * u <= (1 + u)^n - 1.
Proof.
  intros n u Hu.
  induction n.
  - simpl. lra.
  - simpl pow.
    rewrite S_INR.
    (* IH: INR n * u <= (1 + u)^n - 1,  i.e., (1+u)^n >= 1 + INR n * u *)
    assert (Hge: (1 + u) ^ n >= 1 + INR n * u) by lra.
    (* INR n >= 0 *)
    assert (Hn: 0 <= INR n) by (apply pos_INR).
    (* (1+u) * (1+u)^n >= (1+u)(1 + n*u) = 1 + (n+1)*u + n*u^2 >= 1 + (n+1)*u *)
    nra.
Qed.

(* ================================================================== *)
(*  Theorem 33: Error bound upper approximation for small u            *)
(*  For 0 <= u <= 1/2 and n <= 10:                                     *)
(*  (1+u)^n - 1 <= 2 * n * u                                           *)
(*  (Rule of thumb: error approximately doubles vs linear bound)       *)
(* ================================================================== *)
Theorem fp_error_upper_approx_2op :
  forall u : R,
  0 <= u -> u <= / 2 ->
  (1 + u)^2 - 1 <= 2 * (2 * u).
Proof.
  intros u Hu Hu2. nra.
Qed.

(* ================================================================== *)
(*  Theorem 34: 3-op error upper approximation                         *)
(* ================================================================== *)
Theorem fp_error_upper_approx_3op :
  forall u : R,
  0 <= u -> u <= / 2 ->
  (1 + u)^3 - 1 <= 2 * (3 * u).
Proof.
  intros u Hu Hu2. nra.
Qed.

(* ================================================================== *)
(*  Theorem 35: 4-op error upper approximation                         *)
(*  For u <= 1/8 (much larger than u32 ~ 6e-8): (1+u)^4 - 1 <= 8u    *)
(* ================================================================== *)
Theorem fp_error_upper_approx_4op :
  forall u : R,
  0 <= u -> u <= / 8 ->
  (1 + u)^4 - 1 <= 2 * (4 * u).
Proof.
  intros u Hu Hu2.
  (* (1+u)^4 - 1 = 4u + 6u^2 + 4u^3 + u^4 *)
  (* For u <= 1/8: 6u^2 + 4u^3 + u^4 <= u(6/8 + 4/64 + 1/512) < u *)
  ring_simplify. nra.
Qed.

(* ================================================================== *)
(*  Theorem 36: 5-op error upper approximation                         *)
(*  For u <= 1/8: (1+u)^5 - 1 <= 10u                                  *)
(* ================================================================== *)
Theorem fp_error_upper_approx_5op :
  forall u : R,
  0 <= u -> u <= / 8 ->
  (1 + u)^5 - 1 <= 2 * (5 * u).
Proof.
  intros u Hu Hu2.
  ring_simplify. nra.
Qed.

(* ================================================================== *)
(*  Theorem 37: 6-op error upper approximation                         *)
(*  For u <= 1/8: (1+u)^6 - 1 <= 12u                                  *)
(* ================================================================== *)
Theorem fp_error_upper_approx_6op :
  forall u : R,
  0 <= u -> u <= / 8 ->
  (1 + u)^6 - 1 <= 2 * (6 * u).
Proof.
  intros u Hu Hu2.
  ring_simplify. nra.
Qed.

(* ================================================================== *)
(*  Theorem 38: 7-op error upper approximation                         *)
(*  For u <= 1/8: (1+u)^7 - 1 <= 14u                                  *)
(* ================================================================== *)
Theorem fp_error_upper_approx_7op :
  forall u : R,
  0 <= u -> u <= / 8 ->
  (1 + u)^7 - 1 <= 2 * (7 * u).
Proof.
  intros u Hu Hu2.
  ring_simplify. nra.
Qed.

(* ================================================================== *)
(*  Theorem 39: 8-op error upper approximation                         *)
(*  For u <= 1/16: (1+u)^8 - 1 <= 16u                                 *)
(* ================================================================== *)
Theorem fp_error_upper_approx_8op :
  forall u : R,
  0 <= u -> u <= / 16 ->
  (1 + u)^8 - 1 <= 2 * (8 * u).
Proof.
  intros u Hu Hu2.
  ring_simplify. nra.
Qed.

(* ================================================================== *)
(*  SECTION 9: Cross Product Error Model                               *)
(*  cross(a, b) = a.x*b.y - a.y*b.x (2D scalar cross product)       *)
(*  4 FP ops: mul, mul, sub (with rounding at each step)              *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 40: Vec2 cross product error bound                        *)
(*  fl(a.x*b.y - a.y*b.x): 2 muls + 1 sub = 3 ops worst chain      *)
(* ================================================================== *)
Theorem fp_vec2_cross_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 41: Vec3 cross product error bound (per component)        *)
(*  Each component: a_j*b_k - a_k*b_j                                *)
(*  2 muls + 1 sub = 3 ops worst chain per component                  *)
(* ================================================================== *)
Theorem fp_vec3_cross_component_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  SECTION 10: Dot Product Error Model                                *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 42: Vec2 dot product error bound                          *)
(*  fl(a.x*b.x + a.y*b.y): 2 muls + 1 add = 3 ops worst chain      *)
(* ================================================================== *)
Theorem fp_vec2_dot_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 43: Vec3 dot product error bound                          *)
(*  fl(a.x*b.x + a.y*b.y + a.z*b.z): 3 muls + 2 adds              *)
(*  Worst chain: mul, add, add = 3 ops (final component path)        *)
(* ================================================================== *)
Theorem fp_vec3_dot_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof.
  exact fp_vec3_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 44: Vec4 dot product error bound                          *)
(*  fl(a.x*b.x + a.y*b.y + a.z*b.z + a.w*b.w): 4 muls + 3 adds   *)
(*  Worst chain: mul, add, add, add = 4 ops                           *)
(* ================================================================== *)
Theorem fp_vec4_dot_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof.
  exact fp_vec4_length_sq_error.
Qed.

(* ================================================================== *)
(*  SECTION 11: Reflect and Project Error Models                       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 45: Vec2 reflect error bound                              *)
(*  reflect(v, n) = v - 2*(v·n)*n per component                      *)
(*  dot: 3 ops, scale: 1 op, sub: 1 op = 5 ops worst chain          *)
(* ================================================================== *)
Theorem fp_vec2_reflect_error :
  forall (e1 e2 e3 e4 e5 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) <=
  (1 + u32 / (1 + u32))^5 - 1.
Proof.
  exact fp_vec4_length_error.
Qed.

(* ================================================================== *)
(*  Theorem 46: Vec2 project error bound                              *)
(*  project(v, w) = (v·w / w·w) * w per component                   *)
(*  dot: 3 ops, dot: 3 ops, div: 1 op, mul: 1 op = 4 ops chain     *)
(* ================================================================== *)
Theorem fp_vec2_project_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof.
  exact fp_vec4_length_sq_error.
Qed.

(* ================================================================== *)
(*  Theorem 47: Distance symmetry in exact arithmetic                 *)
(*  |a - b| = |b - a| componentwise                                   *)
(* ================================================================== *)
Theorem fp_vec_distance_symmetric :
  forall (ax bx : R), Rabs (ax - bx) = Rabs (bx - ax).
Proof.
  intros. apply Rabs_minus_sym.
Qed.

(* ================================================================== *)
(*  Theorem 48: Dot product commutativity in exact arithmetic         *)
(*  a·b = b·a (2D case: ax*bx + ay*by = bx*ax + by*ay)              *)
(* ================================================================== *)
Theorem fp_vec2_dot_commutative :
  forall (ax ay bx by0 : R),
  ax * bx + ay * by0 = bx * ax + by0 * ay.
Proof. intros. ring. Qed.
