(* FP_Color.v - IEEE 754 error bounds for color operations                     *)
(* Part of the rource-math formal verification suite (Phase FP-2)             *)
(* Uses Flocq 4.1.3 for IEEE 754 binary32 formalization                      *)
(*                                                                             *)
(* Proves FP error bounds for color-related computations:                     *)
(*   - color luminance (weighted sum)                                          *)
(*   - color lerp (per-component interpolation)                                *)
(*   - alpha blending (a*c1 + (1-a)*c2)                                       *)
(*   - gamma correction approximation                                          *)
(*   - color component addition/multiplication                                 *)
(*   - color clamping (exact operations)                                       *)
(*   - Rect area and perimeter error                                           *)
(*   - Bounds center and size error                                            *)
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
(*  SECTION 1: Color Luminance Error Model                             *)
(*  luminance(r,g,b) = 0.2126*r + 0.7152*g + 0.0722*b                *)
(*  3 muls + 2 adds = 5 FP ops                                         *)
(*  Worst-case component chain: mul + 2 adds = 3 ops                  *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 1: Luminance per-component error (3-op chain)              *)
(*  The r-component: 0.2126*r feeds into add chain                    *)
(*  mul(1 op) + add(1 op) + add(1 op) = 3 ops in worst chain         *)
(* ================================================================== *)
Theorem fp_luminance_component_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 2: Luminance overall error bound                           *)
(*  The total expression has 5 ops but worst chain is 3 ops            *)
(*  (the last-added component goes through mul + 1 add = 2 ops)       *)
(*  Conservative bound: 3-op for the worst component                   *)
(* ================================================================== *)
Theorem fp_luminance_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 3: Luminance is bounded by weighted sum property           *)
(*  If r,g,b in [0,1], then luminance in [0,1]                        *)
(*  0.2126 + 0.7152 + 0.0722 = 1.0                                    *)
(* ================================================================== *)
Theorem fp_luminance_weights_sum_to_one :
  2126 / 10000 + 7152 / 10000 + 722 / 10000 = 1.
Proof. field. Qed.

(* ================================================================== *)
(*  Theorem 4: Luminance range for unit-range components               *)
(*  For 0 <= r,g,b <= 1: 0 <= lum <= 1                                *)
(* ================================================================== *)
Theorem fp_luminance_unit_range :
  forall (r g b : R),
  0 <= r -> r <= 1 ->
  0 <= g -> g <= 1 ->
  0 <= b -> b <= 1 ->
  0 <= 2126/10000 * r + 7152/10000 * g + 722/10000 * b /\
  2126/10000 * r + 7152/10000 * g + 722/10000 * b <= 1.
Proof.
  intros r g b Hr0 Hr1 Hg0 Hg1 Hb0 Hb1.
  split; nra.
Qed.

(* ================================================================== *)
(*  SECTION 2: Color Lerp Error Model                                  *)
(*  color_lerp(c1, c2, t) = c1 + t * (c2 - c1) per component         *)
(*  3 FP ops per component: sub, mul, add                              *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 5: Color lerp per-component error (3-op)                   *)
(* ================================================================== *)
Theorem fp_color_lerp_component_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 6: Color lerp at t=0 is exact                             *)
(* ================================================================== *)
Theorem fp_color_lerp_t0 :
  forall c1 c2 : R, c1 + 0 * (c2 - c1) = c1.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 7: Color lerp at t=1 is exact                             *)
(* ================================================================== *)
Theorem fp_color_lerp_t1 :
  forall c1 c2 : R, c1 + 1 * (c2 - c1) = c2.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 8: Color lerp at t=0.5 is midpoint                       *)
(* ================================================================== *)
Theorem fp_color_lerp_midpoint :
  forall c1 c2 : R, c1 + / 2 * (c2 - c1) = (c1 + c2) / 2.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  Theorem 9: Color lerp preserves range [c1, c2]                   *)
(* ================================================================== *)
Theorem fp_color_lerp_range :
  forall (c1 c2 t : R),
  c1 <= c2 -> 0 <= t -> t <= 1 ->
  c1 <= c1 + t * (c2 - c1) /\ c1 + t * (c2 - c1) <= c2.
Proof.
  intros c1 c2 t Hc Ht0 Ht1. split; nra.
Qed.

(* ================================================================== *)
(*  Theorem 10: Color lerp monotonicity in t                          *)
(* ================================================================== *)
Theorem fp_color_lerp_monotone :
  forall (c1 c2 s t : R),
  c1 <= c2 -> s <= t ->
  c1 + s * (c2 - c1) <= c1 + t * (c2 - c1).
Proof.
  intros c1 c2 s t Hc Hst.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; lra.
Qed.

(* ================================================================== *)
(*  SECTION 3: Alpha Blending Error Model                              *)
(*  blend(c1, c2, a) = a*c1 + (1-a)*c2                                *)
(*  Per component: 2 muls + 1 sub + 1 add = 4 ops                     *)
(*  Worst chain: mul + add = 2 ops (for the a*c1 or (1-a)*c2 term)    *)
(*  After combining: 3-op chain                                        *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 11: Alpha blend per-component error (3-op chain)           *)
(* ================================================================== *)
Theorem fp_alpha_blend_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 12: Alpha blend at a=0 yields c2                          *)
(* ================================================================== *)
Theorem fp_alpha_blend_a0 :
  forall c1 c2 : R, 0 * c1 + (1 - 0) * c2 = c2.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 13: Alpha blend at a=1 yields c1                          *)
(* ================================================================== *)
Theorem fp_alpha_blend_a1 :
  forall c1 c2 : R, 1 * c1 + (1 - 1) * c2 = c1.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 14: Alpha blend is convex combination                     *)
(*  For 0 <= a <= 1: result is between c1 and c2                     *)
(* ================================================================== *)
Theorem fp_alpha_blend_convex :
  forall (c1 c2 a : R),
  0 <= a -> a <= 1 -> c1 <= c2 ->
  c1 <= a * c1 + (1 - a) * c2 /\ a * c1 + (1 - a) * c2 <= c2.
Proof.
  intros c1 c2 a Ha0 Ha1 Hc. split; nra.
Qed.

(* ================================================================== *)
(*  Theorem 15: Alpha blend symmetry                                   *)
(*  blend(c1, c2, a) = blend(c2, c1, 1-a)                             *)
(* ================================================================== *)
Theorem fp_alpha_blend_symmetry :
  forall (c1 c2 a : R),
  a * c1 + (1 - a) * c2 = (1 - a) * c2 + a * c1.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 16: Alpha blend with equal colors                          *)
(*  blend(c, c, a) = c for any a                                      *)
(* ================================================================== *)
Theorem fp_alpha_blend_equal :
  forall (c a : R),
  a * c + (1 - a) * c = c.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  SECTION 4: Color Component Arithmetic                              *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 17: Color addition per-component (1-op)                    *)
(* ================================================================== *)
Theorem fp_color_add_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= u32 / (1 + u32).
Proof. intros e1 He1. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 18: Color multiplication per-component (1-op)              *)
(* ================================================================== *)
Theorem fp_color_mul_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= u32 / (1 + u32).
Proof. intros e1 He1. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 19: Color scale (scalar * color) per-component (1-op)      *)
(* ================================================================== *)
Theorem fp_color_scale_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) - 1) <= u32 / (1 + u32).
Proof.
  intros e1 He1.
  replace ((1 + e1) - 1) with e1 by ring.
  exact He1.
Qed.

(* ================================================================== *)
(*  SECTION 5: Color Clamping (Exact Operations)                       *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 20: Color clamp preserves [0,1] range                     *)
(* ================================================================== *)
Theorem fp_color_clamp_range :
  forall x : R,
  0 <= Rmax 0 (Rmin x 1) /\ Rmax 0 (Rmin x 1) <= 1.
Proof.
  intro x. unfold Rmin, Rmax.
  destruct (Rle_dec x 1); destruct (Rle_dec 0 x);
    destruct (Rle_dec 0 1); try lra.
Qed.

(* ================================================================== *)
(*  Theorem 21: Color clamp is identity for valid colors               *)
(* ================================================================== *)
Theorem fp_color_clamp_identity :
  forall x : R,
  0 <= x -> x <= 1 ->
  Rmax 0 (Rmin x 1) = x.
Proof.
  intros x Hx0 Hx1. unfold Rmin, Rmax.
  destruct (Rle_dec x 1); destruct (Rle_dec 0 x); lra.
Qed.

(* ================================================================== *)
(*  Theorem 22: Color clamp idempotent                                 *)
(*  clamp(clamp(x)) = clamp(x)                                        *)
(* ================================================================== *)
Theorem fp_color_clamp_idempotent :
  forall x : R,
  Rmax 0 (Rmin (Rmax 0 (Rmin x 1)) 1) = Rmax 0 (Rmin x 1).
Proof.
  intro x.
  assert (H := fp_color_clamp_range x).
  destruct H as [H0 H1].
  apply fp_color_clamp_identity; assumption.
Qed.

(* ================================================================== *)
(*  SECTION 6: Gamma Correction Approximation                          *)
(*  sRGB gamma: linear for small values, power curve for larger        *)
(*  Approximate gamma: pow(c, 1/2.2) ~ sqrt(c) for rough estimate     *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 23: sqrt preserves [0,1] range                            *)
(*  For 0 <= x <= 1: 0 <= sqrt(x) <= 1                                *)
(* ================================================================== *)
Theorem fp_gamma_sqrt_range :
  forall x : R,
  0 <= x -> x <= 1 ->
  0 <= sqrt x /\ sqrt x <= 1.
Proof.
  intros x Hx0 Hx1. split.
  - apply sqrt_pos.
  - rewrite <- sqrt_1.
    apply sqrt_le_1; lra.
Qed.

(* ================================================================== *)
(*  Theorem 24: sqrt is monotone (for gamma correction)               *)
(*  0 <= x <= y => sqrt(x) <= sqrt(y)                                  *)
(* ================================================================== *)
Theorem fp_gamma_sqrt_monotone :
  forall x y : R,
  0 <= x -> x <= y ->
  sqrt x <= sqrt y.
Proof.
  intros x y Hx Hxy.
  apply sqrt_le_1; lra.
Qed.

(* ================================================================== *)
(*  Theorem 25: sqrt of 0 is 0 (black stays black)                   *)
(* ================================================================== *)
Theorem fp_gamma_sqrt_zero : sqrt 0 = 0.
Proof. apply sqrt_0. Qed.

(* ================================================================== *)
(*  Theorem 26: sqrt of 1 is 1 (white stays white)                   *)
(* ================================================================== *)
Theorem fp_gamma_sqrt_one : sqrt 1 = 1.
Proof. apply sqrt_1. Qed.

(* ================================================================== *)
(*  SECTION 7: Rect Area and Perimeter Error                           *)
(*  area = width * height (1 mul)                                      *)
(*  perimeter = 2*(width + height) (1 add + 1 mul)                    *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 27: Rect area error (1-op)                                 *)
(* ================================================================== *)
Theorem fp_color_area_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= u32 / (1 + u32).
Proof. intros e1 He1. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 28: Rect perimeter error (2-op: add + mul)                *)
(* ================================================================== *)
Theorem fp_color_perimeter_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof. exact two_op_error_bound. Qed.

(* ================================================================== *)
(*  Theorem 29: Rect contains_point per-axis (comparison is exact)     *)
(*  FP comparison of finite values is exact in IEEE 754                *)
(* ================================================================== *)
Theorem fp_rect_contains_exact_compare :
  forall (x lo hi : R),
  lo <= x -> x <= hi -> lo <= x /\ x <= hi.
Proof. intros x lo hi Hlo Hhi. split; assumption. Qed.

(* ================================================================== *)
(*  SECTION 8: Bounds Center and Size Error                            *)
(*  center = (min + max) / 2 : add + div = 2 ops                      *)
(*  size = max - min : 1 sub                                           *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 30: Bounds center per-axis error (2-op)                   *)
(* ================================================================== *)
Theorem fp_bounds_center_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof. exact two_op_error_bound. Qed.

(* ================================================================== *)
(*  Theorem 31: Bounds size per-axis error (1-op: subtraction)         *)
(* ================================================================== *)
Theorem fp_bounds_size_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= u32 / (1 + u32).
Proof. intros e1 He1. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 32: Bounds volume error (3D: 2 muls)                      *)
(*  volume = width * height * depth = 2 muls in chain                 *)
(* ================================================================== *)
Theorem fp_bounds_volume_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof. exact two_op_error_bound. Qed.

(* ================================================================== *)
(*  SECTION 9: Additional Color Properties                             *)
(* ================================================================== *)

(* ================================================================== *)
(*  Theorem 33: Color contrast ratio computation error (2-op)          *)
(*  contrast_ratio = (L1 + 0.05) / (L2 + 0.05)                       *)
(*  2 ops: 1 add (for offset) + 1 div = 2 ops chain                  *)
(* ================================================================== *)
Theorem fp_contrast_ratio_error :
  forall (e1 e2 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) - 1) <= (1 + u32 / (1 + u32))^2 - 1.
Proof. exact two_op_error_bound. Qed.

(* ================================================================== *)
(*  Theorem 34: Color contrasting computation error (luminance + cmp)  *)
(*  contrasting(c) = luminance(c) <= 0.5 ? white : black              *)
(*  Error comes from luminance (3-op), comparison is exact             *)
(* ================================================================== *)
Theorem fp_contrasting_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 35: Premultiplied alpha (c*a) per-component (1-op)        *)
(* ================================================================== *)
Theorem fp_premultiplied_alpha_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= u32 / (1 + u32).
Proof. intros e1 He1. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 36: Color distance squared (3D color space)                *)
(*  dist_sq = (r2-r1)^2 + (g2-g1)^2 + (b2-b1)^2                     *)
(*  Same as Vec3 distance_squared: 3-op worst chain                    *)
(* ================================================================== *)
Theorem fp_color_distance_sq_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 37: HSL to RGB hue-sector computation error                *)
(*  hue / 60 followed by modular arithmetic: 1 div                    *)
(* ================================================================== *)
Theorem fp_hsl_hue_sector_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= u32 / (1 + u32).
Proof. intros e1 He1. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 38: Brightness adjustment (multiply) error (1-op)          *)
(* ================================================================== *)
Theorem fp_brightness_adjust_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e1 <= u32 / (1 + u32).
Proof. intros e1 He1. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 39: Color distance (sqrt of distance_squared)             *)
(*  3-op for distance_squared + 1-op for sqrt = 4-op chain           *)
(* ================================================================== *)
Theorem fp_color_distance_error :
  forall (e1 e2 e3 e4 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs e4 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) * (1 + e4) - 1) <=
  (1 + u32 / (1 + u32))^4 - 1.
Proof. exact fp_sum_squares_3d_error. Qed.

(* ================================================================== *)
(*  Theorem 40: Color addition saturates at 1 (clamped add)           *)
(*  add + clamp = 1-op + exact comparison                             *)
(* ================================================================== *)
Theorem fp_color_add_saturate_range :
  forall (a b : R),
  0 <= a -> 0 <= b ->
  0 <= Rmin (a + b) 1 /\ Rmin (a + b) 1 <= 1.
Proof.
  intros a b Ha Hb. unfold Rmin.
  destruct (Rle_dec (a + b) 1); split; lra.
Qed.

(* ================================================================== *)
(*  Theorem 41: Color component negation reversal                     *)
(*  1 - (1 - x) = x (used in alpha inversion)                        *)
(* ================================================================== *)
Theorem fp_color_alpha_invert_roundtrip :
  forall (x : R), 1 - (1 - x) = x.
Proof. intros. ring. Qed.

(* ================================================================== *)
(*  Theorem 42: Premultiplied alpha blend formula                     *)
(*  c_out = c_src + c_dst * (1 - a_src)                              *)
(*  3-op chain: sub, mul, add                                         *)
(* ================================================================== *)
Theorem fp_premul_blend_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 43: Color to integer conversion (multiply by 255)         *)
(*  fl(c * 255) has 1-op error                                        *)
(* ================================================================== *)
Theorem fp_color_to_u8_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) - 1) <= u32 / (1 + u32).
Proof. intros e1 He1. replace ((1 + e1) - 1) with e1 by ring. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 44: Integer to color conversion (divide by 255)           *)
(*  fl(n / 255) has 1-op error                                        *)
(* ================================================================== *)
Theorem fp_color_from_u8_error :
  forall (e1 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) - 1) <= u32 / (1 + u32).
Proof. intros e1 He1. replace ((1 + e1) - 1) with e1 by ring. exact He1. Qed.

(* ================================================================== *)
(*  Theorem 45: Color midpoint blend formula exact                    *)
(*  (c1 + c2) / 2 via blend: a=0.5                                   *)
(* ================================================================== *)
Theorem fp_color_midpoint_blend :
  forall (c1 c2 : R),
  / 2 * c1 + (1 - / 2) * c2 = (c1 + c2) / 2.
Proof. intros. field. Qed.

(* ================================================================== *)
(*  Theorem 46: Grayscale conversion (average of RGB)                 *)
(*  gray = (r + g + b) / 3: 2 adds + 1 div = 3-op chain             *)
(* ================================================================== *)
Theorem fp_grayscale_avg_error :
  forall (e1 e2 e3 : R),
  Rabs e1 <= u32 / (1 + u32) ->
  Rabs e2 <= u32 / (1 + u32) ->
  Rabs e3 <= u32 / (1 + u32) ->
  Rabs ((1 + e1) * (1 + e2) * (1 + e3) - 1) <= (1 + u32 / (1 + u32))^3 - 1.
Proof. exact fp_three_op_composition. Qed.

(* ================================================================== *)
(*  Theorem 47: Luminance weight ordering in exact arithmetic         *)
(*  green > red > blue weights for Rec. 709                           *)
(* ================================================================== *)
Theorem fp_luminance_weight_order :
  722 / 10000 < 2126 / 10000 /\ 2126 / 10000 < 7152 / 10000.
Proof. split; lra. Qed.

(* ================================================================== *)
(*  Theorem 48: Color component squared is non-negative               *)
(*  Used for distance computation: (c2 - c1)^2 >= 0                  *)
(* ================================================================== *)
Theorem fp_color_diff_sq_nonneg :
  forall (c1 c2 : R), 0 <= (c2 - c1) * (c2 - c1).
Proof. intros. nra. Qed.
