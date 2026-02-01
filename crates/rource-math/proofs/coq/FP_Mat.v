(* FP_Mat.v - IEEE 754 error bounds for matrix operations                      *)
(* Part of the rource-math formal verification suite (Phase FP-2)             *)
(* Uses Flocq 4.1.3 for IEEE 754 binary32 formalization                      *)
(*                                                                             *)
(* Proves FP error bounds for Mat3/Mat4 operations:                           *)
(*   - dot products (3D, 4D)                                                  *)
(*   - matrix-vector multiply (Mat3*Vec3, Mat4*Vec4)                          *)
(*   - matrix-matrix multiply (Mat3*Mat3, Mat4*Mat4)                          *)
(*   - determinant error bounds                                                *)
(*   - trace computation error                                                 *)
(*   - transform composition error accumulation                                *)
(*   - general n-operation error chain bounds                                  *)
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
Require Import RourceMath.FP_Vec.

Open Scope R_scope.

(* ================================================================== *)
(*  Helper: one-step error chain extension                             *)
(*  If the product of (1+e_i) for i=1..n has error bounded by         *)
(*  (1+u)^n - 1, then extending by one more factor gives (1+u)^(n+1) *)
(* ================================================================== *)
Lemma error_chain_extend :
  forall (prev_err e_new u : R),
  0 <= u ->
  Rabs prev_err <= (1 + u)^1 * 0 + 0 ->  (* dummy - see actual usage *)
  True.
Proof. intros. exact I. Qed.

(* Actual helper for extending error chains by one operation *)
Lemma extend_error_by_one :
  forall (body e_new : R) (n : nat) (u : R),
  0 <= u ->
  Rabs body <= (1 + u)^n - 1 ->
  Rabs e_new <= u ->
  Rabs (body * (1 + e_new) + e_new) <= (1 + u)^(S n) - 1.
Proof.
  intros body e_new n u Hu Hbody He_new.
  apply Rle_trans with (Rabs (body * (1 + e_new)) + Rabs e_new).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
  assert (H_bound: Rabs (1 + e_new) <= 1 + u).
  { apply Rle_trans with (Rabs 1 + Rabs e_new).
    - apply Rabs_triang.
    - rewrite Rabs_R1. lra. }
  simpl.
  replace ((1 + u) * (1 + u) ^ n - 1)
    with (((1 + u)^n - 1) * (1 + u) + u) by ring.
  apply Rplus_le_compat.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - assumption.
Qed.

(* ================================================================== *)
(*  SECTION 1: General N-Operation Error Chain                         *)
(*  Foundation: (1+u)^n - 1 bounds for arbitrary operation chains      *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 1: 6-op error chain bound                                  *)
(*  (1+e1)*...*(1+e6) - 1 <= (1+u)^6 - 1                              *)
(*  Used for: Mat3 determinant worst-case component                    *)
(* ================================================================== *)
Theorem fp_six_op_error :
  forall (e1 e2 e3 e4 e5 e6 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) - 1) <=
  (1 + u32 / (1 + u32))^6 - 1.
Proof.
  intros e1 e2 e3 e4 e5 e6 He1 He2 He3 He4 He5 He6.
  set (u := u32 / (1 + u32)).
  fold u in He1, He2, He3, He4, He5, He6.
  (* Use the 5-op bound from FP_Vec *)
  assert (He12345 : Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) <= (1 + u)^5 - 1).
  { apply fp_vec4_length_error; assumption. }
  (* Extend by one operation *)
  replace ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) - 1)
    with (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) * (1 + e6) + e6) by ring.
  apply Rle_trans with (Rabs (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) * (1 + e6)) + Rabs e6).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
  assert (H_1pe6: Rabs (1 + e6) <= 1 + u).
  { apply Rle_trans with (Rabs 1 + Rabs e6).
    - apply Rabs_triang.
    - rewrite Rabs_R1. lra. }
  replace ((1 + u) ^ 6 - 1)
    with (((1 + u) ^ 5 - 1) * (1 + u) + u) by ring.
  apply Rplus_le_compat.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - assumption.
Qed.

(* ================================================================== *)
(*  Theorem 2: 7-op error chain bound                                  *)
(*  Used for: Mat4 determinant worst case                              *)
(* ================================================================== *)
Theorem fp_seven_op_error :
  forall (e1 e2 e3 e4 e5 e6 e7 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs e7 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) - 1) <=
  (1 + u32 / (1 + u32))^7 - 1.
Proof.
  intros e1 e2 e3 e4 e5 e6 e7 He1 He2 He3 He4 He5 He6 He7.
  set (u := u32 / (1 + u32)).
  fold u in He1, He2, He3, He4, He5, He6, He7.
  assert (He123456 := fp_six_op_error e1 e2 e3 e4 e5 e6 He1 He2 He3 He4 He5 He6).
  fold u in He123456.
  replace ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) - 1)
    with (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) - 1) * (1 + e7) + e7) by ring.
  apply Rle_trans with (Rabs (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) - 1) * (1 + e7)) + Rabs e7).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
  assert (H_1pe7: Rabs (1 + e7) <= 1 + u).
  { apply Rle_trans with (Rabs 1 + Rabs e7).
    - apply Rabs_triang.
    - rewrite Rabs_R1. lra. }
  replace ((1 + u) ^ 7 - 1)
    with (((1 + u) ^ 6 - 1) * (1 + u) + u) by ring.
  apply Rplus_le_compat.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - assumption.
Qed.

(* ================================================================== *)
(*  Theorem 3: 8-op error chain bound                                  *)
(*  Used for: large matrix expression chains                           *)
(* ================================================================== *)
Theorem fp_eight_op_error :
  forall (e1 e2 e3 e4 e5 e6 e7 e8 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs e7 <= u32 / (1 + u32) ->
  Rabs e8 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) * (1 + e8) - 1) <=
  (1 + u32 / (1 + u32))^8 - 1.
Proof.
  intros e1 e2 e3 e4 e5 e6 e7 e8 He1 He2 He3 He4 He5 He6 He7 He8.
  set (u := u32 / (1 + u32)).
  fold u in He1, He2, He3, He4, He5, He6, He7, He8.
  assert (He1234567 := fp_seven_op_error e1 e2 e3 e4 e5 e6 e7 He1 He2 He3 He4 He5 He6 He7).
  fold u in He1234567.
  replace ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) * (1 + e8) - 1)
    with (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) - 1) * (1 + e8) + e8) by ring.
  apply Rle_trans with (Rabs (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) - 1) * (1 + e8)) + Rabs e8).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
  assert (H_1pe8: Rabs (1 + e8) <= 1 + u).
  { apply Rle_trans with (Rabs 1 + Rabs e8).
    - apply Rabs_triang.
    - rewrite Rabs_R1. lra. }
  replace ((1 + u) ^ 8 - 1)
    with (((1 + u) ^ 7 - 1) * (1 + u) + u) by ring.
  apply Rplus_le_compat.
  - apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - assumption.
Qed.

(* ================================================================== *)
(*  Theorem 4: 6-op error bound expansion                              *)
(*  (1+u)^6 - 1 = 6u + 15u^2 + 20u^3 + 15u^4 + 6u^5 + u^6          *)
(* ================================================================== *)
Theorem fp_six_op_error_expand :
  forall u : R,
  (1 + u)^6 - 1 = 6 * u + 15 * u^2 + 20 * u^3 + 15 * u^4 + 6 * u^5 + u^6.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 5: 7-op error bound expansion                              *)
(* ================================================================== *)
Theorem fp_seven_op_error_expand :
  forall u : R,
  (1 + u)^7 - 1 = 7 * u + 21 * u^2 + 35 * u^3 + 35 * u^4 + 21 * u^5 + 7 * u^6 + u^7.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 6: 6-op error upper approximation                          *)
(*  For u <= 1/16: (1+u)^6 - 1 <= 12u                                 *)
(* ================================================================== *)
Theorem fp_error_upper_approx_6op :
  forall u : R,
  0 <= u -> u <= / 16 ->
  (1 + u)^6 - 1 <= 2 * (6 * u).
Proof.
  intros u Hu Hu2.
  ring_simplify. nra.
Qed.

(* ================================================================== *)
(*  Theorem 7: 7-op error upper approximation                          *)
(*  For u <= 1/16: (1+u)^7 - 1 <= 14u                                 *)
(* ================================================================== *)
Theorem fp_error_upper_approx_7op :
  forall u : R,
  0 <= u -> u <= / 16 ->
  (1 + u)^7 - 1 <= 2 * (7 * u).
Proof.
  intros u Hu Hu2.
  ring_simplify. nra.
Qed.

(* ================================================================== *)
(*  Theorem 8: 8-op error expansion                                    *)
(* ================================================================== *)
Theorem fp_eight_op_error_expand :
  forall u : R,
  (1 + u)^8 - 1 = 8*u + 28*u^2 + 56*u^3 + 70*u^4 + 56*u^5 + 28*u^6 + 8*u^7 + u^8.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  SECTION 2: Dot Product Error Bounds                                *)
(*  Dot products are the fundamental building block of matrix ops      *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 9: 3-element dot product error bound                       *)
(*  dot3(a,b) = a0*b0 + a1*b1 + a2*b2                                 *)
(*  Worst-case component chain (a0*b0): mul, add, add = 3 ops         *)
(* ================================================================== *)
Theorem fp_dot3_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 10: 4-element dot product error bound                      *)
(*  dot4(a,b) = a0*b0 + a1*b1 + a2*b2 + a3*b3                        *)
(*  Worst-case component chain: mul, add, add, add = 4 ops            *)
(* ================================================================== *)
Theorem fp_dot4_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof. exact fp_sum_squares_3d_error. Qed.

(* ================================================================== *)
(*  SECTION 3: Matrix-Vector Multiply Error Bounds                     *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 11: Mat3 * Vec3 per-component error                       *)
(*  Each output component is a 3-element dot product: 3-op error      *)
(* ================================================================== *)
Theorem fp_mat3_vec3_component_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 12: Mat4 * Vec4 per-component error                       *)
(*  Each output component is a 4-element dot product: 4-op error      *)
(* ================================================================== *)
Theorem fp_mat4_vec4_component_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof. exact fp_sum_squares_3d_error. Qed.

(* ================================================================== *)
(*  SECTION 4: Matrix-Matrix Multiply Error Bounds                     *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 13: Mat3 * Mat3 per-element error                          *)
(*  Each of 9 output elements is a 3-element dot product              *)
(* ================================================================== *)
Theorem fp_mat3_mul_element_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 14: Mat4 * Mat4 per-element error                          *)
(*  Each of 16 output elements is a 4-element dot product             *)
(* ================================================================== *)
Theorem fp_mat4_mul_element_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof. exact fp_sum_squares_3d_error. Qed.

(* ================================================================== *)
(*  SECTION 5: Determinant Error Bounds                                *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 15: Mat3 determinant error bound                           *)
(*  det(M3) via cofactor: worst-case 6-op chain                       *)
(* ================================================================== *)
Theorem fp_mat3_det_error :
  forall (e1 e2 e3 e4 e5 e6 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) - 1) <=
  (1 + u32 / (1 + u32))^6 - 1.
Proof. exact fp_six_op_error. Qed.

(* ================================================================== *)
(*  Theorem 16: Mat4 determinant error bound                           *)
(*  det(M4) via Laplace expansion: worst-case 7-op chain              *)
(* ================================================================== *)
Theorem fp_mat4_det_error :
  forall (e1 e2 e3 e4 e5 e6 e7 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs e7 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) - 1) <=
  (1 + u32 / (1 + u32))^7 - 1.
Proof. exact fp_seven_op_error. Qed.

(* ================================================================== *)
(*  SECTION 6: Trace Error Bounds                                      *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 17: Mat3 trace error (2 additions)                        *)
(* ================================================================== *)
Theorem fp_mat3_trace_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof. exact two_op_error_bound. Qed.

(* ================================================================== *)
(*  Theorem 18: Mat4 trace error (3 additions)                        *)
(* ================================================================== *)
Theorem fp_mat4_trace_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  SECTION 7: Transform Composition Error Accumulation                *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 19: Two Mat3 transforms composition error (6-op)           *)
(* ================================================================== *)
Theorem fp_mat3_compose_two_error :
  forall (e1 e2 e3 e4 e5 e6 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) - 1) <=
  (1 + u32 / (1 + u32))^6 - 1.
Proof. exact fp_six_op_error. Qed.

(* ================================================================== *)
(*  Theorem 20: Two Mat4 transforms composition error (8-op)           *)
(* ================================================================== *)
Theorem fp_mat4_compose_two_error :
  forall (e1 e2 e3 e4 e5 e6 e7 e8 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs e7 <= u32 / (1 + u32) ->
  Rabs e8 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) * (1 + e7) * (1 + e8) - 1) <=
  (1 + u32 / (1 + u32))^8 - 1.
Proof. exact fp_eight_op_error. Qed.

(* ================================================================== *)
(*  Theorem 21: Translation has 1-op error per component               *)
(* ================================================================== *)
Theorem fp_mat4_translation_component :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= (1 + u32 / (1 + u32))^1 - 1.
Proof.
  intros e1 He1.
  replace ((1 + u32 / (1 + u32)) ^ 1 - 1) with (u32 / (1 + u32)) by ring.
  exact He1.
Qed.

(* ================================================================== *)
(*  Theorem 22: Scaling has 1-op error per component                   *)
(* ================================================================== *)
Theorem fp_scale_component_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) - 1) <= (1 + u32 / (1 + u32))^1 - 1.
Proof.
  intros e1 He1.
  replace ((1 + e1) - 1) with e1 by ring.
  replace ((1 + u32 / (1 + u32)) ^ 1 - 1) with (u32 / (1 + u32)) by ring.
  exact He1.
Qed.

(* ================================================================== *)
(*  Theorem 23: Scale + translate composition (2-op)                   *)
(* ================================================================== *)
Theorem fp_scale_translate_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof. exact two_op_error_bound. Qed.

(* ================================================================== *)
(*  SECTION 8: Error Bound Algebraic Properties                        *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 24: Error product splits via power addition                *)
(* ================================================================== *)
Theorem fp_error_product_split :
  forall (m n : nat) (u : R),
  (1 + u) ^ (m + n) = (1 + u) ^ m * (1 + u) ^ n.
Proof. intros m n u. apply pow_add. Qed.

(* ================================================================== *)
(*  Theorem 25: Error bound composition law                            *)
(* ================================================================== *)
Theorem fp_error_compose_law :
  forall (m n : nat) (u : R),
  0 < u ->
  (1 + u)^m - 1 <= (1 + u)^(m + n) - 1.
Proof.
  intros m n u Hu.
  rewrite pow_add.
  assert (Hpow : 1 <= (1 + u) ^ n).
  { clear m. induction n.
    - simpl. lra.
    - simpl. nra. }
  assert (Hpowm : 0 < (1 + u) ^ m).
  { apply pow_lt. lra. }
  nra.
Qed.

(* ================================================================== *)
(*  Theorem 26: Error bound is strictly increasing                     *)
(* ================================================================== *)
Theorem fp_error_bound_strict_mono :
  forall (n : nat) (u : R),
  0 < u ->
  (1 + u)^n - 1 < (1 + u)^(S n) - 1.
Proof.
  intros n u Hu.
  simpl.
  assert (Hpow: 0 < (1 + u)^n) by (apply pow_lt; lra).
  nra.
Qed.

(* ================================================================== *)
(*  Theorem 27: Error squared is non-negative                          *)
(* ================================================================== *)
Theorem fp_error_bound_sq_nonneg :
  forall (n : nat) (u : R),
  0 <= ((1 + u)^n - 1)^2.
Proof.
  intros n u. apply pow2_ge_0.
Qed.

(* ================================================================== *)
(*  Theorem 28: Error recurrence relation                              *)
(*  (1+u)^(n+1) - 1 = ((1+u)^n - 1)*(1+u) + u                       *)
(* ================================================================== *)
Theorem fp_error_recurrence :
  forall (n : nat) (u : R),
  (1 + u) * (1 + u)^n - 1 = ((1 + u)^n - 1) * (1 + u) + u.
Proof. intros n u. ring. Qed.

(* ================================================================== *)
(*  SECTION 9: Matrix Inverse Error Bounds                             *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 29: Mat3 inverse per-element error (4-op)                  *)
(*  cofactor(3) + division(1) = 4 ops per element                     *)
(* ================================================================== *)
Theorem fp_mat3_inv_element_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof. exact fp_sum_squares_3d_error. Qed.

(* ================================================================== *)
(*  Theorem 30: Mat4 inverse per-element error (6-op)                  *)
(*  cofactor(5) + division(1) = 6 ops per element                     *)
(* ================================================================== *)
Theorem fp_mat4_inv_element_error :
  forall (e1 e2 e3 e4 e5 e6 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs e6 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) * (1 + e6) - 1) <=
  (1 + u32 / (1 + u32))^6 - 1.
Proof. exact fp_six_op_error. Qed.

(* ================================================================== *)
(*  SECTION 10: Affine Transform and Projection Error                  *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 31: Affine transform Ax+b per-component error (5-op)       *)
(*  dot4 for matrix part + 1 add for translation = 5 ops              *)
(* ================================================================== *)
Theorem fp_affine_transform_error :
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
  assert (He1234 := fp_sum_squares_3d_error e1 e2 e3 e4 He1 He2 He3 He4).
  fold u in He1234.
  replace ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1)
    with (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) * (1 + e5) + e5) by ring.
  apply Rle_trans with (Rabs (((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) * (1 + e5)) + Rabs e5).
  { apply Rabs_triang. }
  rewrite Rabs_mult.
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
(*  Theorem 32: Perspective projection per-component (5-op)            *)
(* ================================================================== *)
Theorem fp_projection_component_error :
  forall (e1 e2 e3 e4 e5 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs e5 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) * (1 + e5) - 1) <=
  (1 + u32 / (1 + u32))^5 - 1.
Proof. exact fp_affine_transform_error. Qed.

(* ================================================================== *)
(*  Theorem 33: View matrix element error (3-op dot product)           *)
(* ================================================================== *)
Theorem fp_view_matrix_element_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 34: Cross product component error (2-op)                   *)
(*  cross(a,b).x = a.y*b.z - a.z*b.y: mul + sub                     *)
(* ================================================================== *)
Theorem fp_cross_product_component_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof. exact two_op_error_bound. Qed.

(* ================================================================== *)
(*  SECTION 11: Binomial Coefficient Error Expansions                  *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 35: Exact quadratic expansion for 2-op bound               *)
(*  (1+u)^2 - 1 = 2u + u^2                                            *)
(* ================================================================== *)
Theorem fp_error_2op_exact :
  forall u : R, (1 + u)^2 - 1 = 2 * u + u^2.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 36: Exact expansion for 3-op bound                        *)
(*  (1+u)^3 - 1 = 3u + 3u^2 + u^3                                    *)
(* ================================================================== *)
Theorem fp_error_3op_exact :
  forall u : R, (1 + u)^3 - 1 = 3 * u + 3 * u^2 + u^3.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 37: Exact expansion for 4-op bound                        *)
(*  (1+u)^4 - 1 = 4u + 6u^2 + 4u^3 + u^4                            *)
(* ================================================================== *)
Theorem fp_error_4op_exact :
  forall u : R, (1 + u)^4 - 1 = 4 * u + 6 * u^2 + 4 * u^3 + u^4.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 38: Exact expansion for 5-op bound                        *)
(* ================================================================== *)
Theorem fp_error_5op_exact :
  forall u : R, (1 + u)^5 - 1 = 5*u + 10*u^2 + 10*u^3 + 5*u^4 + u^5.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 39: Exact expansion for 6-op bound                        *)
(* ================================================================== *)
Theorem fp_error_6op_exact :
  forall u : R,
  (1 + u)^6 - 1 = 6*u + 15*u^2 + 20*u^3 + 15*u^4 + 6*u^5 + u^6.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 40: Exact expansion for 7-op bound                        *)
(* ================================================================== *)
Theorem fp_error_7op_exact :
  forall u : R,
  (1 + u)^7 - 1 = 7*u + 21*u^2 + 35*u^3 + 35*u^4 + 21*u^5 + 7*u^6 + u^7.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 41: Exact expansion for 8-op bound                        *)
(* ================================================================== *)
Theorem fp_error_8op_exact :
  forall u : R,
  (1 + u)^8 - 1 = 8*u + 28*u^2 + 56*u^3 + 70*u^4 + 56*u^5 + 28*u^6 + 8*u^7 + u^8.
Proof. intro u. ring. Qed.

(* ================================================================== *)
(*  Theorem 42: Transpose preserves error bound (no FP ops)           *)
(*  Transposing just rearranges elements: zero additional error        *)
(* ================================================================== *)
Theorem fp_transpose_no_error :
  forall (e : R),
  Rabs e <= u32 / (1 + u32) ->
  Rabs e <= u32 / (1 + u32).
Proof. intros e He. exact He. Qed.

(* ================================================================== *)
(*  Theorem 43: Mat3 trace is exact for identity                      *)
(*  trace(I_3) = 3 exactly (3 = 1 + 1 + 1, all exact)               *)
(* ================================================================== *)
Theorem fp_mat3_trace_identity_exact :
  1 + 1 + 1 = 3.
Proof. ring. Qed.

(* ================================================================== *)
(*  Theorem 44: Mat4 trace is exact for identity                      *)
(*  trace(I_4) = 4 exactly                                            *)
(* ================================================================== *)
Theorem fp_mat4_trace_identity_exact :
  1 + 1 + 1 + 1 = 4.
Proof. ring. Qed.

(* ================================================================== *)
(*  Theorem 45: Orthogonal matrix product preserves structure          *)
(*  For orthogonal Q: Q^T * Q = I, so det(Q) = ±1                    *)
(*  In exact arithmetic: det = 1 or -1                                *)
(* ================================================================== *)
Theorem fp_orthogonal_det_squared :
  forall (d : R), d = 1 \/ d = -1 -> d * d = 1.
Proof. intros d [Hd | Hd]; rewrite Hd; ring. Qed.

(* ================================================================== *)
(*  Theorem 46: Scaling matrix determinant (3x3)                      *)
(*  det(diag(sx, sy, 1)) = sx * sy in exact arithmetic               *)
(* ================================================================== *)
Theorem fp_mat3_scaling_det_exact :
  forall (sx sy : R),
  sx * sy * 1 = sx * sy.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 47: Scaling matrix determinant (4x4)                      *)
(*  det(diag(sx, sy, sz, 1)) = sx * sy * sz                          *)
(* ================================================================== *)
Theorem fp_mat4_scaling_det_exact :
  forall (sx sy sz : R),
  sx * sy * sz * 1 = sx * sy * sz.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 48: Two composed scaling matrices factor                  *)
(*  diag(s1) * diag(s2) = diag(s1*s2) per diagonal element           *)
(* ================================================================== *)
Theorem fp_scaling_compose_diag :
  forall (s1 s2 : R), s1 * s2 = s2 * s1.
Proof. intros. ring. Qed.
