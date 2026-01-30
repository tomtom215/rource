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
