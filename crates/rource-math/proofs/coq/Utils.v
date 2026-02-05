(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Utils.v - Abstract Utility Function Specifications (R-based)
 *
 * Foundational mathematical operations from rource-math/src/lib.rs:
 * lerp, clamp, approx_eq, deg_to_rad, rad_to_deg.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import Reals.
Require Import Lra.
Require Import Lia.
Require Import ZArith.
Require Import R_Ifp.
Open Scope R_scope.

(** * Definitions *)

(** Linear interpolation: lerp(a, b, t) = a + (b - a) * t *)
Definition rlerp (a b t : R) : R := a + (b - a) * t.

(** Clamp value to [lo, hi] *)
Definition rclamp (v lo hi : R) : R :=
  if Rlt_dec v lo then lo
  else if Rlt_dec hi v then hi
  else v.

(** Approximate equality within epsilon *)
Definition rapprox_eq (a b eps : R) : Prop :=
  Rabs (a - b) < eps.

(** * Scalar Floor/Ceiling/Round Operations *)

(** Scalar floor: greatest integer ≤ x.
    Uses Int_part from R_Ifp: Int_part(x) = up(x) - 1
    where up(x) is the smallest integer strictly greater than x. *)
Definition Rfloor (x : R) : R := IZR (Int_part x).

(** Scalar ceiling: least integer ≥ x.
    Defined as ceil(x) = -floor(-x). *)
Definition Rceil (x : R) : R := - Rfloor (- x).

(** Scalar round: round half away from zero (matches Rust f32::round).
    For x ≥ 0: round(x) = floor(x + 0.5)
    For x < 0: round(x) = ceil(x - 0.5) *)
Definition Rround (x : R) : R :=
  if Rle_dec 0 x then Rfloor (x + / 2)
  else Rceil (x - / 2).

(** * Degree/Radian Conversion *)

(** Convert degrees to radians: d × π / 180 *)
Definition rdeg_to_rad (d : R) : R := d * PI / 180.

(** Convert radians to degrees: r × 180 / π *)
Definition rrad_to_deg (r : R) : R := r * 180 / PI.

(** * Lerp Properties *)

Theorem rlerp_zero : forall (a b : R),
  rlerp a b 0 = a.
Proof.
  intros. unfold rlerp. lra.
Qed.

Theorem rlerp_one : forall (a b : R),
  rlerp a b 1 = b.
Proof.
  intros. unfold rlerp. lra.
Qed.

Theorem rlerp_same : forall (a t : R),
  rlerp a a t = a.
Proof.
  intros. unfold rlerp. lra.
Qed.

Theorem rlerp_midpoint : forall (a b : R),
  rlerp a b (1/2) = (a + b) / 2.
Proof.
  intros. unfold rlerp. lra.
Qed.

Theorem rlerp_linear : forall (a b s t : R),
  rlerp a b s + (rlerp a b t - rlerp a b s) = rlerp a b t.
Proof.
  intros. unfold rlerp. lra.
Qed.

(** * Clamp Properties *)

Theorem rclamp_in_range : forall (v lo hi : R),
  lo <= hi ->
  let result := rclamp v lo hi in
  lo <= result /\ result <= hi.
Proof.
  intros v lo hi Hle. unfold rclamp.
  destruct (Rlt_dec v lo); destruct (Rlt_dec hi v); lra.
Qed.

Theorem rclamp_identity : forall (v lo hi : R),
  lo <= v -> v <= hi ->
  rclamp v lo hi = v.
Proof.
  intros v lo hi Hlo Hhi. unfold rclamp.
  destruct (Rlt_dec v lo); destruct (Rlt_dec hi v); lra.
Qed.

Theorem rclamp_lower : forall (v lo hi : R),
  v < lo -> lo <= hi ->
  rclamp v lo hi = lo.
Proof.
  intros v lo hi Hv Hle. unfold rclamp.
  destruct (Rlt_dec v lo); try lra.
Qed.

Theorem rclamp_upper : forall (v lo hi : R),
  v > hi -> lo <= hi ->
  rclamp v lo hi = hi.
Proof.
  intros v lo hi Hv Hle. unfold rclamp.
  destruct (Rlt_dec v lo); destruct (Rlt_dec hi v); lra.
Qed.

Theorem rclamp_idempotent : forall (v lo hi : R),
  lo <= hi ->
  rclamp (rclamp v lo hi) lo hi = rclamp v lo hi.
Proof.
  intros v lo hi Hle.
  assert (H := rclamp_in_range v lo hi Hle).
  destruct H as [Hlo Hhi].
  apply rclamp_identity; assumption.
Qed.

(** * Additional Lerp Properties *)

(** Theorem 11: lerp is affine: lerp(a,b,t) = (1-t)*a + t*b. *)
Theorem rlerp_affine : forall (a b t : R),
  rlerp a b t = (1 - t) * a + t * b.
Proof.
  intros. unfold rlerp. lra.
Qed.

(** Theorem 12: lerp commutes under symmetry: lerp(a,b,t) = lerp(b,a,1-t). *)
Theorem rlerp_symmetric : forall (a b t : R),
  rlerp a b t = rlerp b a (1 - t).
Proof.
  intros. unfold rlerp. lra.
Qed.

(** Theorem 13: lerp is monotone in t when a <= b. *)
Theorem rlerp_monotone : forall (a b s t : R),
  a <= b -> s <= t -> rlerp a b s <= rlerp a b t.
Proof.
  intros. unfold rlerp. nra.
Qed.

(** Theorem 14: lerp at quarter. *)
Theorem rlerp_quarter : forall (a b : R),
  rlerp a b (1/4) = (3 * a + b) / 4.
Proof.
  intros. unfold rlerp. lra.
Qed.

(** Theorem 15: lerp at three-quarters. *)
Theorem rlerp_three_quarter : forall (a b : R),
  rlerp a b (3/4) = (a + 3 * b) / 4.
Proof.
  intros. unfold rlerp. lra.
Qed.

(** Theorem 16: lerp difference: lerp(a,b,t) - lerp(a,b,s) = (b-a)*(t-s). *)
Theorem rlerp_diff : forall (a b s t : R),
  rlerp a b t - rlerp a b s = (b - a) * (t - s).
Proof.
  intros. unfold rlerp. lra.
Qed.

(** Theorem 17: lerp distributes addition: lerp(a+c, b+c, t) = lerp(a,b,t) + c. *)
Theorem rlerp_add_const : forall (a b c t : R),
  rlerp (a + c) (b + c) t = rlerp a b t + c.
Proof.
  intros. unfold rlerp. lra.
Qed.

(** Theorem 18: lerp scales: lerp(s*a, s*b, t) = s * lerp(a, b, t). *)
Theorem rlerp_scale : forall (a b s t : R),
  rlerp (s * a) (s * b) t = s * rlerp a b t.
Proof.
  intros. unfold rlerp. ring.
Qed.

(** * Additional Clamp Properties *)

(** Theorem 19: clamp monotone: if u <= v, clamp(u) <= clamp(v). *)
Theorem rclamp_monotone : forall (u v lo hi : R),
  lo <= hi -> u <= v ->
  rclamp u lo hi <= rclamp v lo hi.
Proof.
  intros u v lo hi Hle Huv.
  unfold rclamp.
  destruct (Rlt_dec u lo); destruct (Rlt_dec hi u);
  destruct (Rlt_dec v lo); destruct (Rlt_dec hi v); lra.
Qed.

(** Theorem 20: clamp of lo is lo. *)
Theorem rclamp_at_lo : forall (lo hi : R),
  lo <= hi -> rclamp lo lo hi = lo.
Proof.
  intros lo hi Hle. apply rclamp_identity; lra.
Qed.

(** Theorem 21: clamp of hi is hi. *)
Theorem rclamp_at_hi : forall (lo hi : R),
  lo <= hi -> rclamp hi lo hi = hi.
Proof.
  intros lo hi Hle. apply rclamp_identity; lra.
Qed.

(** * Approximate Equality Properties *)

(** Theorem 22: approx_eq is reflexive for positive eps. *)
Theorem rapprox_eq_refl : forall (a eps : R),
  eps > 0 -> rapprox_eq a a eps.
Proof.
  intros a eps Heps.
  unfold rapprox_eq.
  replace (a - a) with 0 by lra.
  rewrite Rabs_R0. lra.
Qed.

(** Theorem 23: approx_eq is symmetric. *)
Theorem rapprox_eq_sym : forall (a b eps : R),
  rapprox_eq a b eps -> rapprox_eq b a eps.
Proof.
  intros a b eps H.
  unfold rapprox_eq in *.
  rewrite Rabs_minus_sym. exact H.
Qed.

(** Theorem 24: triangle inequality for approx_eq.
    If |a - b| < eps1 and |b - c| < eps2 then |a - c| < eps1 + eps2. *)
Theorem rapprox_eq_triangle : forall (a b c eps1 eps2 : R),
  rapprox_eq a b eps1 -> rapprox_eq b c eps2 ->
  rapprox_eq a c (eps1 + eps2).
Proof.
  intros a b c eps1 eps2 Hab Hbc.
  unfold rapprox_eq in *.
  assert (Hac : a - c = (a - b) + (b - c)) by lra.
  rewrite Hac.
  eapply Rle_lt_trans. apply Rabs_triang.
  lra.
Qed.

(** Theorem 25: approx_eq is monotone in epsilon. *)
Theorem rapprox_eq_monotone_eps : forall (a b eps1 eps2 : R),
  eps1 <= eps2 -> rapprox_eq a b eps1 -> rapprox_eq a b eps2.
Proof.
  intros a b eps1 eps2 Hle Hab.
  unfold rapprox_eq in *. lra.
Qed.

(** Theorem 26: lerp is bounded between endpoints when 0 <= t <= 1 and a <= b. *)
Theorem rlerp_bounded : forall (a b t : R),
  a <= b -> 0 <= t -> t <= 1 ->
  a <= rlerp a b t /\ rlerp a b t <= b.
Proof.
  intros a b t Hab Ht0 Ht1. unfold rlerp. nra.
Qed.

(** Theorem 27: lerp nesting: lerp(a, b, lerp(0, 1, t)) = lerp(a, b, t). *)
Theorem rlerp_nesting_unit : forall (a b t : R),
  rlerp a b (rlerp 0 1 t) = rlerp a b t.
Proof.
  intros. unfold rlerp. lra.
Qed.

(** Theorem 28: clamp distance from center bounded by half-width. *)
Theorem rclamp_center_distance : forall (v lo hi : R),
  lo <= hi ->
  Rabs (rclamp v lo hi - (lo + hi) / 2) <= (hi - lo) / 2.
Proof.
  intros v lo hi Hle. unfold rclamp.
  destruct (Rlt_dec v lo); [|destruct (Rlt_dec hi v)];
  (apply Rabs_le; lra).
Qed.

(** Theorem 29: clamp preserves ordering within range. *)
Theorem rclamp_preserves_le : forall (u v lo hi : R),
  lo <= hi -> u <= v ->
  rclamp u lo hi <= rclamp v lo hi.
Proof.
  intros u v lo hi Hle Huv. unfold rclamp.
  destruct (Rlt_dec u lo); destruct (Rlt_dec hi u);
  destruct (Rlt_dec v lo); destruct (Rlt_dec hi v); lra.
Qed.

(** Theorem 30: lerp composition: lerp(a, lerp(a, b, s), t) = lerp(a, b, s*t). *)
Theorem rlerp_compose : forall (a b s t : R),
  rlerp a (rlerp a b s) t = rlerp a b (s * t).
Proof.
  intros. unfold rlerp. ring.
Qed.

(** * Non-Transitivity and Advanced Properties *)

(** Theorem 31: approx_eq is NOT transitive — fundamental counterexample.
    This is mathematically important: floating-point approximate equality
    lacks transitivity, unlike exact equality. This theorem provides
    a concrete witness demonstrating the failure of transitivity. *)
Theorem rapprox_eq_not_transitive :
  exists a b c eps : R,
    eps > 0 /\ rapprox_eq a b eps /\ rapprox_eq b c eps /\ ~ rapprox_eq a c eps.
Proof.
  exists 0, (3/4), (3/2), 1.
  unfold rapprox_eq.
  repeat split.
  - lra.
  - apply Rabs_def1; lra.
  - apply Rabs_def1; lra.
  - intro H. apply Rabs_def2 in H. lra.
Qed.

(** Theorem 32: lerp chaining — lerp from an intermediate result to b.
    lerp(lerp(a,b,s), b, t) = lerp(a, b, s + (1-s)*t). *)
Theorem rlerp_chain : forall (a b s t : R),
  rlerp (rlerp a b s) b t = rlerp a b (s + (1 - s) * t).
Proof.
  intros. unfold rlerp. ring.
Qed.

(** Theorem 33: lerp is injective in t when a ≠ b. *)
Theorem rlerp_injective_in_t : forall (a b t1 t2 : R),
  a <> b -> rlerp a b t1 = rlerp a b t2 -> t1 = t2.
Proof.
  intros a b t1 t2 Hab Heq.
  unfold rlerp in Heq.
  assert (Hne: b - a <> 0) by lra.
  assert (Hmul: (b - a) * t1 = (b - a) * t2) by lra.
  exact (Rmult_eq_reg_l (b - a) t1 t2 Hmul Hne).
Qed.

(** Theorem 34: approx_eq is translation-invariant.
    Adding a constant to both arguments preserves approximate equality. *)
Theorem rapprox_eq_add_const : forall (a b c eps : R),
  rapprox_eq a b eps <-> rapprox_eq (a + c) (b + c) eps.
Proof.
  intros. unfold rapprox_eq.
  replace (a + c - (b + c)) with (a - b) by ring.
  tauto.
Qed.

(** Theorem 35: approx_eq is negation-invariant.
    Negating both arguments preserves approximate equality. *)
Theorem rapprox_eq_neg_iff : forall (a b eps : R),
  rapprox_eq a b eps <-> rapprox_eq (-a) (-b) eps.
Proof.
  intros. unfold rapprox_eq.
  replace (-a - -b) with (-(a - b)) by ring.
  rewrite Rabs_Ropp. tauto.
Qed.

(** Theorem 36: lerp subtraction — difference of two lerps at the same t.
    lerp(a,b,t) - lerp(c,d,t) = lerp(a-c, b-d, t). *)
Theorem rlerp_sub : forall (a b c d t : R),
  rlerp a b t - rlerp c d t = rlerp (a - c) (b - d) t.
Proof.
  intros. unfold rlerp. ring.
Qed.

(** Theorem 37: lerp absolute difference formula.
    |lerp(a,b,t) - lerp(a,b,s)| = |b-a| * |t-s|. *)
Theorem rlerp_abs_diff : forall (a b s t : R),
  Rabs (rlerp a b t - rlerp a b s) = Rabs (b - a) * Rabs (t - s).
Proof.
  intros. unfold rlerp.
  replace (a + (b - a) * t - (a + (b - a) * s)) with ((b - a) * (t - s)) by ring.
  apply Rabs_mult.
Qed.

(** * Scalar Floor/Ceiling/Round Properties *)

(** Helper: Int_part of an integer equals the integer itself.
    Key proof technique: use tech_up to establish up(IZR z) = z+1,
    then Int_part = up - 1 = z. *)
Lemma Int_part_IZR : forall z : Z, Int_part (IZR z) = z.
Proof.
  intros z. unfold Int_part.
  assert (Hup : up (IZR z) = (z + 1)%Z).
  { symmetry. apply tech_up.
    - rewrite plus_IZR. simpl. lra.
    - rewrite plus_IZR. simpl. lra. }
  rewrite Hup. lia.
Qed.

(** Theorem 38: floor(x) ≤ x *)
Theorem Rfloor_le : forall x : R, Rfloor x <= x.
Proof.
  intros x. unfold Rfloor.
  destruct (base_Int_part x) as [H _]. exact H.
Qed.

(** Theorem 39: x < floor(x) + 1 *)
Theorem Rfloor_lt_succ : forall x : R, x < Rfloor x + 1.
Proof.
  intros x. unfold Rfloor.
  destruct (base_Int_part x) as [_ H]. lra.
Qed.

(** Theorem 40: x ≤ ceil(x) *)
Theorem Rceil_ge : forall x : R, x <= Rceil x.
Proof.
  intros x. unfold Rceil, Rfloor.
  destruct (base_Int_part (-x)) as [H _]. lra.
Qed.

(** Theorem 41: ceil(x) < x + 1 *)
Theorem Rceil_lt_succ : forall x : R, Rceil x < x + 1.
Proof.
  intros x. unfold Rceil, Rfloor.
  destruct (base_Int_part (-x)) as [_ H]. lra.
Qed.

(** Theorem 42: floor(0) = 0 *)
Theorem Rfloor_zero : Rfloor 0 = 0.
Proof.
  unfold Rfloor. rewrite Int_part_IZR. reflexivity.
Qed.

(** Theorem 43: ceil(0) = 0 *)
Theorem Rceil_zero : Rceil 0 = 0.
Proof.
  unfold Rceil. replace (- 0) with 0 by ring.
  rewrite Rfloor_zero. ring.
Qed.

(** Theorem 44: floor(-x) = -ceil(x) *)
Theorem Rfloor_neg : forall x : R, Rfloor (- x) = - Rceil x.
Proof.
  intros x. unfold Rceil. ring.
Qed.

(** Theorem 45: ceil(-x) = -floor(x) *)
Theorem Rceil_neg : forall x : R, Rceil (- x) = - Rfloor x.
Proof.
  intros x. unfold Rceil, Rfloor.
  replace (- - x) with x by ring. ring.
Qed.

(** Theorem 46: floor(x) ≤ ceil(x) *)
Theorem Rfloor_le_Rceil : forall x : R, Rfloor x <= Rceil x.
Proof.
  intros x.
  apply Rle_trans with x.
  - apply Rfloor_le.
  - apply Rceil_ge.
Qed.

(** Theorem 47: floor of an integer is that integer *)
Theorem Rfloor_integer : forall z : Z, Rfloor (IZR z) = IZR z.
Proof.
  intros z. unfold Rfloor. f_equal. apply Int_part_IZR.
Qed.

(** Theorem 48: ceil of an integer is that integer *)
Theorem Rceil_integer : forall z : Z, Rceil (IZR z) = IZR z.
Proof.
  intros z. unfold Rceil.
  rewrite <- opp_IZR. rewrite Rfloor_integer.
  rewrite opp_IZR. ring.
Qed.

(** * Degree/Radian Conversion Properties *)

(** Theorem 49: deg_to_rad(0) = 0 *)
Theorem rdeg_to_rad_zero : rdeg_to_rad 0 = 0.
Proof.
  unfold rdeg_to_rad. field.
Qed.

(** Theorem 50: rad_to_deg(0) = 0 *)
Theorem rrad_to_deg_zero : PI <> 0 -> rrad_to_deg 0 = 0.
Proof.
  intros Hpi. unfold rrad_to_deg. field. exact Hpi.
Qed.

(** Theorem 51: deg → rad → deg round-trip is identity *)
Theorem rdeg_rad_roundtrip : forall d : R,
  PI <> 0 -> rrad_to_deg (rdeg_to_rad d) = d.
Proof.
  intros d Hpi. unfold rrad_to_deg, rdeg_to_rad. field.
  exact Hpi.
Qed.

(** Theorem 52: rad → deg → rad round-trip is identity *)
Theorem rrad_deg_roundtrip : forall r : R,
  PI <> 0 -> rdeg_to_rad (rrad_to_deg r) = r.
Proof.
  intros r Hpi. unfold rdeg_to_rad, rrad_to_deg. field.
  exact Hpi.
Qed.

(** Theorem 53: deg_to_rad(180) = PI *)
Theorem rdeg_to_rad_180 : rdeg_to_rad 180 = PI.
Proof.
  unfold rdeg_to_rad. field.
Qed.

(** Theorem 54: deg_to_rad(90) = PI / 2 *)
Theorem rdeg_to_rad_90 : rdeg_to_rad 90 = PI / 2.
Proof.
  unfold rdeg_to_rad. field.
Qed.

(** Theorem 55: deg_to_rad(360) = 2 * PI *)
Theorem rdeg_to_rad_360 : rdeg_to_rad 360 = 2 * PI.
Proof.
  unfold rdeg_to_rad. field.
Qed.

(** Theorem 56: deg_to_rad is linear: deg_to_rad(a+b) = deg_to_rad(a) + deg_to_rad(b) *)
Theorem rdeg_to_rad_linear : forall a b : R,
  rdeg_to_rad (a + b) = rdeg_to_rad a + rdeg_to_rad b.
Proof.
  intros a b. unfold rdeg_to_rad. field.
Qed.

(** * Additional Floor/Ceil Properties *)

(** Theorem 57: Combined floor spec: floor(x) ≤ x < floor(x) + 1 *)
Theorem Rfloor_spec : forall x : R,
  Rfloor x <= x /\ x < Rfloor x + 1.
Proof.
  intros x. split.
  - apply Rfloor_le.
  - apply Rfloor_lt_succ.
Qed.

(** Theorem 58: floor of x in [0, 1) is 0 *)
Theorem Rfloor_eq : forall x : R,
  0 <= x -> x < 1 -> Rfloor x = 0.
Proof.
  intros x Hlo Hhi.
  unfold Rfloor.
  assert (H: 0%Z = Int_part x).
  { apply Int_part_spec. simpl. lra. }
  rewrite <- H. reflexivity.
Qed.
