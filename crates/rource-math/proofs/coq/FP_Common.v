(* FP_Common.v - Common definitions for IEEE 754 floating-point verification *)
(* Part of the rource-math formal verification suite                         *)
(* Uses Flocq 4.1.3 for IEEE 754 formalization                              *)
(*                                                                            *)
(* This file defines the binary32 (f32) format parameters, rounding mode,    *)
(* overflow preconditions, and helper lemmas used throughout the FP proofs.   *)
(* All proofs are machine-checked with zero admits.                           *)

Require Import Reals.
Require Import ZArith.
Require Import Lia.
Require Import Lra.
Require Import Flocq.Core.Core.
Require Import Flocq.Core.FLT.
Require Import Flocq.Core.Ulp.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.BinarySingleNaN.
Require Import Flocq.Prop.Relative.
Require Import Flocq.Prop.Plus_error.
Require Import Flocq.Prop.Mult_error.
Require Import Flocq.Prop.Div_sqrt_error.

Open Scope R_scope.

(* ================================================================== *)
(*  IEEE 754 Binary32 (f32) Format Parameters                          *)
(* ================================================================== *)

(* Precision: 24 significand bits (23 stored + 1 implicit) *)
Definition prec32 : Z := 24%Z.

(* Maximum exponent: 128 (emax) *)
Definition emax32 : Z := 128%Z.

(* Minimum exponent: 3 - 128 - 24 = -149 *)
Definition emin32 : Z := (3 - emax32 - prec32)%Z.

(* The FLT exponent function for binary32 *)
Definition fexp32 := FLT_exp emin32 prec32.

(* Proof that precision > 0 *)
Lemma prec32_gt_0 : Prec_gt_0 prec32.
Proof. unfold Prec_gt_0, prec32. lia. Qed.

(* Proof that precision < emax *)
Lemma prec32_lt_emax : Prec_lt_emax prec32 emax32.
Proof. unfold Prec_lt_emax, prec32, emax32. lia. Qed.

(* ================================================================== *)
(*  Rounding Mode                                                       *)
(* ================================================================== *)

(* We use round-to-nearest-even (the default IEEE 754 rounding mode) *)
Definition rnd32 := mode_NE.

(* ================================================================== *)
(*  Unit Roundoff                                                       *)
(* ================================================================== *)

(* The unit roundoff for binary32: u = 2^(-24) *)
(* This is the relative rounding error bound for a single operation *)
Definition u32 := u_ro radix2 prec32.

(* Machine epsilon for binary32: eps = 2^(-23) *)
(* Note: eps = 2*u *)
Definition eps32 := bpow radix2 (-prec32 + 1)%Z.

(* ================================================================== *)
(*  Key Flocq Lemmas Instantiated for Binary32                         *)
(* ================================================================== *)

(* Relative error bound for round-to-nearest in FLT format:
   For |x| >= 2^(emin + prec - 1), we have:
   |round(x) - x| <= eps/2 * |x|                                      *)
Lemma relative_error_binary32 :
  forall (choice : Z -> bool) (x : R),
  bpow radix2 (emin32 + prec32 - 1)%Z <= Rabs x ->
  Rabs (round radix2 fexp32 (Znearest choice) x - x) <=
  / 2 * eps32 * Rabs x.
Proof.
  intros choice x Hx.
  apply relative_error_N_FLT.
  - exact prec32_gt_0.
  - exact Hx.
Qed.

(* The eps/2 form: for normalized numbers, relative error <= u/(1+u) *)
Lemma relative_error_binary32_u :
  forall (choice : Z -> bool) (x : R),
  Rabs (round radix2 (FLX_exp prec32) (Znearest choice) x - x) <=
  u32 / (1 + u32) * Rabs x.
Proof.
  intros choice x.
  apply relative_error_N_FLX'.
  exact prec32_gt_0.
Qed.

(* Standard model: round(x) = x * (1 + eps) + eta
   where |eps| <= u/(1+u) and |eta| <= 1/2 * bpow(emin)
   and eps * eta = 0 (one of them is zero)                             *)
Lemma standard_model_binary32 :
  forall (choice : Z -> bool) (x : R),
  exists eps eta : R,
    Rabs eps <= u32 / (1 + u32) /\
    Rabs eta <= / 2 * bpow radix2 emin32 /\
    eps * eta = 0 /\
    round radix2 fexp32 (Znearest choice) x = x * (1 + eps) + eta.
Proof.
  intros choice x.
  apply relative_error_N_FLT'_ex.
  exact prec32_gt_0.
Qed.

(* ================================================================== *)
(*  Error Composition Helpers                                           *)
(* ================================================================== *)

(* When composing two operations each with relative error u/(1+u),
   the total relative error is bounded by (1+u/(1+u))^2 - 1           *)
Lemma two_op_error_bound :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof.
  intros e1 e2 He1 He2.
  replace ((1 + e1) * (1 + e2) - 1) with (e1 + e2 + e1 * e2) by ring.
  apply Rle_trans with (Rabs e1 + Rabs e2 + Rabs (e1 * e2)).
  - apply Rle_trans with (Rabs (e1 + e2) + Rabs (e1 * e2)).
    + apply Rabs_triang.
    + apply Rplus_le_compat_r. apply Rabs_triang.
  - rewrite Rabs_mult.
    replace ((1 + u32 / (1 + u32)) ^ 2 - 1)
      with (u32 / (1 + u32) + u32 / (1 + u32) + u32 / (1 + u32) * (u32 / (1 + u32))).
    + apply Rplus_le_compat.
      * apply Rplus_le_compat; assumption.
      * apply Rmult_le_compat; try apply Rabs_pos; assumption.
    + ring.
Qed.

(* ================================================================== *)
(*  No-Overflow Predicates                                              *)
(* ================================================================== *)

(* A real value is representable in binary32 (does not overflow) *)
Definition no_overflow32 (x : R) : Prop :=
  Rabs x < bpow radix2 emax32.

(* The normal number threshold for binary32 *)
Definition normal_threshold32 : R := bpow radix2 (emin32 + prec32 - 1)%Z.

(* Value is in the normal range (not subnormal) *)
Definition is_normal32 (x : R) : Prop :=
  normal_threshold32 <= Rabs x.

(* ================================================================== *)
(*  Useful Constants                                                    *)
(* ================================================================== *)

(* Maximum finite f32 value: approximately 3.4028235e+38 *)
Definition max_f32 : R := bpow radix2 (emax32 - 1)%Z * (2 - bpow radix2 (1 - prec32)%Z).

(* Minimum positive normal f32: approximately 1.175494e-38 *)
Definition min_normal_f32 : R := bpow radix2 (emin32 + prec32 - 1)%Z.

(* Minimum positive subnormal f32: approximately 1.401298e-45 *)
Definition min_subnormal_f32 : R := bpow radix2 emin32.
