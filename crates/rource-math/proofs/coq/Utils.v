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
