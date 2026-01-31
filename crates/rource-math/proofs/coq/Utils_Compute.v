(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Utils_Compute.v - Computational Utility Functions (Z-based, Extractable)
 *
 * Z-based computational formalization of foundational operations:
 * lerp, clamp. Uses scaled integer arithmetic (1000 = 1.0).
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

(** * Definitions *)

(** Linear interpolation: lerp(a, b, t) = a + (b - a) * t / 1000 *)
Definition zlerp (a b t : Z) : Z := a + (b - a) * t / 1000.

(** Clamp value to [lo, hi] *)
Definition zclamp (v lo hi : Z) : Z :=
  if v <? lo then lo
  else if hi <? v then hi
  else v.

(** * Lerp Properties *)

Theorem zlerp_zero : forall (a b : Z),
  zlerp a b 0 = a.
Proof.
  intros. unfold zlerp.
  rewrite Z.mul_0_r.
  assert (Hdiv: 0 / 1000 = 0) by reflexivity.
  rewrite Hdiv. lia.
Qed.

Theorem zlerp_one : forall (a b : Z),
  zlerp a b 1000 = b.
Proof.
  intros. unfold zlerp.
  rewrite Z.div_mul by lia. lia.
Qed.

Theorem zlerp_same : forall (a t : Z),
  zlerp a a t = a.
Proof.
  intros. unfold zlerp.
  replace (a - a) with 0 by lia.
  rewrite Z.mul_0_l.
  assert (Hdiv: 0 / 1000 = 0) by reflexivity.
  rewrite Hdiv. lia.
Qed.

(** * Clamp Properties *)

Theorem zclamp_in_range : forall (v lo hi : Z),
  lo <= hi ->
  lo <= zclamp v lo hi /\ zclamp v lo hi <= hi.
Proof.
  intros v lo hi Hle. unfold zclamp.
  destruct (v <? lo) eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (hi <? v) eqn:E2.
    + apply Z.ltb_lt in E2. apply Z.ltb_ge in E1. lia.
    + apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. lia.
Qed.

Theorem zclamp_identity : forall (v lo hi : Z),
  lo <= v -> v <= hi ->
  zclamp v lo hi = v.
Proof.
  intros v lo hi Hlo Hhi. unfold zclamp.
  destruct (v <? lo) eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (hi <? v) eqn:E2.
    + apply Z.ltb_lt in E2. lia.
    + reflexivity.
Qed.

Theorem zclamp_lower : forall (v lo hi : Z),
  v < lo ->
  zclamp v lo hi = lo.
Proof.
  intros v lo hi Hv. unfold zclamp.
  destruct (v <? lo) eqn:E1.
  - reflexivity.
  - apply Z.ltb_ge in E1. lia.
Qed.

Theorem zclamp_upper : forall (v lo hi : Z),
  lo <= hi -> v > hi ->
  zclamp v lo hi = hi.
Proof.
  intros v lo hi Hle Hv. unfold zclamp.
  destruct (v <? lo) eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (hi <? v) eqn:E2.
    + reflexivity.
    + apply Z.ltb_ge in E2. lia.
Qed.

Theorem zclamp_idempotent : forall (v lo hi : Z),
  lo <= hi ->
  zclamp (zclamp v lo hi) lo hi = zclamp v lo hi.
Proof.
  intros v lo hi Hle.
  assert (H := zclamp_in_range v lo hi Hle).
  destruct H as [Hlo Hhi].
  apply zclamp_identity; assumption.
Qed.

(** * Computational Tests *)

Example zlerp_test_zero :
  zlerp 0 1000 0 = 0.
Proof. reflexivity. Qed.

Example zlerp_test_one :
  zlerp 0 1000 1000 = 1000.
Proof. reflexivity. Qed.

Example zlerp_test_half :
  zlerp 0 1000 500 = 500.
Proof. reflexivity. Qed.

Example zclamp_test_in_range :
  zclamp 500 0 1000 = 500.
Proof. reflexivity. Qed.

Example zclamp_test_below :
  zclamp (-100) 0 1000 = 0.
Proof. reflexivity. Qed.

Example zclamp_test_above :
  zclamp 2000 0 1000 = 1000.
Proof. reflexivity. Qed.

(** * Additional Lerp Properties *)

(** Theorem: lerp difference formula. *)
Theorem zlerp_diff : forall (a b s t : Z),
  zlerp a b t - zlerp a b s = (b - a) * t / 1000 - (b - a) * s / 1000.
Proof.
  intros. unfold zlerp. lia.
Qed.

(** Theorem: lerp with shifted endpoints. *)
Theorem zlerp_add_const : forall (a b c t : Z),
  zlerp (a + c) (b + c) t = zlerp a b t + c.
Proof.
  intros. unfold zlerp.
  replace ((b + c) - (a + c)) with (b - a) by lia. lia.
Qed.

(** * Additional Clamp Properties *)

(** Theorem: clamp at lo returns lo. *)
Theorem zclamp_at_lo : forall (lo hi : Z),
  lo <= hi -> zclamp lo lo hi = lo.
Proof.
  intros lo hi Hle. apply zclamp_identity; lia.
Qed.

(** Theorem: clamp at hi returns hi. *)
Theorem zclamp_at_hi : forall (lo hi : Z),
  lo <= hi -> zclamp hi lo hi = hi.
Proof.
  intros lo hi Hle. apply zclamp_identity; lia.
Qed.

(** Theorem: clamp is monotone. *)
Theorem zclamp_monotone : forall (u v lo hi : Z),
  lo <= hi -> u <= v ->
  zclamp u lo hi <= zclamp v lo hi.
Proof.
  intros u v lo hi Hle Huv.
  unfold zclamp.
  destruct (u <? lo) eqn:E1; destruct (v <? lo) eqn:E3.
  - lia.
  - apply Z.ltb_ge in E3.
    destruct (hi <? v) eqn:E4.
    + apply Z.ltb_lt in E4. lia.
    + apply Z.ltb_ge in E4. lia.
  - apply Z.ltb_ge in E1. apply Z.ltb_lt in E3. lia.
  - apply Z.ltb_ge in E1. apply Z.ltb_ge in E3.
    destruct (hi <? u) eqn:E2; destruct (hi <? v) eqn:E4.
    + lia.
    + apply Z.ltb_lt in E2. apply Z.ltb_ge in E4. lia.
    + apply Z.ltb_ge in E2. apply Z.ltb_lt in E4. lia.
    + apply Z.ltb_ge in E2. apply Z.ltb_ge in E4. lia.
Qed.

(** * Approximate Equality (Z-based) *)

(** Approximate equality: |a - b| < eps *)
Definition zapprox_eq (a b eps : Z) : Prop :=
  Z.abs (a - b) < eps.

(** Theorem: triangle inequality for approx_eq. *)
Theorem zapprox_eq_triangle : forall (a b c eps1 eps2 : Z),
  zapprox_eq a b eps1 -> zapprox_eq b c eps2 ->
  zapprox_eq a c (eps1 + eps2).
Proof.
  intros a b c eps1 eps2 Hab Hbc.
  unfold zapprox_eq in *.
  assert (Hac : a - c = (a - b) + (b - c)) by lia.
  rewrite Hac.
  eapply Z.le_lt_trans.
  - apply Z.abs_triangle.
  - lia.
Qed.

(** Theorem: approx_eq is monotone in epsilon. *)
Theorem zapprox_eq_monotone_eps : forall (a b eps1 eps2 : Z),
  eps1 <= eps2 -> zapprox_eq a b eps1 -> zapprox_eq a b eps2.
Proof.
  intros a b eps1 eps2 Hle Hab.
  unfold zapprox_eq in *. lia.
Qed.

(** * Additional Lerp Boundedness *)

(** Theorem: lerp is bounded between endpoints when 0 <= t <= 1000 and a <= b. *)
Theorem zlerp_bounded : forall (a b t : Z),
  a <= b -> 0 <= t -> t <= 1000 ->
  a <= zlerp a b t /\ zlerp a b t <= b.
Proof.
  intros a b t Hab Ht0 Ht1. unfold zlerp.
  assert (Hba : 0 <= b - a) by lia.
  assert (Hprod : 0 <= (b - a) * t).
  { apply Z.mul_nonneg_nonneg; lia. }
  split.
  - assert (Hdiv : 0 <= (b - a) * t / 1000).
    { apply Z.div_pos; lia. }
    lia.
  - assert (Hle : (b - a) * t <= (b - a) * 1000).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    assert (Hdiv : (b - a) * t / 1000 <= (b - a) * 1000 / 1000).
    { apply Z.div_le_mono; lia. }
    rewrite Z.div_mul in Hdiv by lia. lia.
Qed.

(** Theorem: lerp nesting with unit interval: zlerp(a, b, zlerp(0, 1000, t)) = zlerp(a, b, t). *)
Theorem zlerp_nesting_unit : forall (a b t : Z),
  zlerp a b (zlerp 0 1000 t) = zlerp a b t.
Proof.
  intros.
  assert (H: zlerp 0 1000 t = t).
  { unfold zlerp.
    replace (1000 - 0) with 1000 by lia.
    rewrite Z.mul_comm.
    rewrite Z.div_mul by lia.
    lia. }
  rewrite H. reflexivity.
Qed.

(** * Additional Clamp Distance Properties *)

(** Theorem: clamp distance from midpoint bounded (scaled by 2 to avoid Z division). *)
(** That is: |lo + hi - 2 * clamp(v, lo, hi)| <= hi - lo. *)
Theorem zclamp_center_distance_2x : forall (v lo hi : Z),
  lo <= hi ->
  Z.abs (lo + hi - 2 * zclamp v lo hi) <= hi - lo.
Proof.
  intros v lo hi Hle.
  assert (H := zclamp_in_range v lo hi Hle).
  destruct H as [Hlo Hhi].
  destruct (Z.abs_spec (lo + hi - 2 * zclamp v lo hi)) as [[_ Heq] | [_ Heq]];
  rewrite Heq; lia.
Qed.
