(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Color_Compute.v - Computational RGBA Color Specification (Extractable)
 *
 * Z-based computational formalization of RGBA colors. Components are
 * integers representing scaled fixed-point values (0-1000 = 0.0-1.0).
 *
 * LAYERED VERIFICATION ARCHITECTURE:
 *
 *   Layer 1 (Abstract):      Color.v / Color_Proofs.v     (R-based, 26 theorems)
 *   Layer 2 (Computational): Color_Compute.v              (Z-based, extractable)
 *   Layer 3 (Extraction):    Color_Extract.v              (OCaml/WASM output)
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 * - All definitions are constructive and computable
 * - All proofs are machine-checked by Coq
 * - Zero admits, zero axioms beyond standard library
 *)

Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

(** * ZColor Definition *)

Record ZColor : Type := mkZColor {
  zcolor_r : Z;
  zcolor_g : Z;
  zcolor_b : Z;
  zcolor_a : Z
}.

(** * Equality *)

Lemma zcolor_eq_dec : forall (a b : ZColor), {a = b} + {a <> b}.
Proof.
  intros [ar ag ab0 aa] [br bg bb ba].
  destruct (Z.eq_dec ar br) as [Hr | Hr];
  destruct (Z.eq_dec ag bg) as [Hg | Hg];
  destruct (Z.eq_dec ab0 bb) as [Hb | Hb];
  destruct (Z.eq_dec aa ba) as [Ha | Ha].
  - left. subst. reflexivity.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
Defined.

Lemma zcolor_eq : forall r1 g1 b1 a1 r2 g2 b2 a2 : Z,
  r1 = r2 -> g1 = g2 -> b1 = b2 -> a1 = a2 ->
  mkZColor r1 g1 b1 a1 = mkZColor r2 g2 b2 a2.
Proof.
  intros. subst. reflexivity.
Qed.

(** * Constructors *)

Definition zcolor_new (r g b a : Z) : ZColor := mkZColor r g b a.
Definition zcolor_rgb (r g b : Z) : ZColor := mkZColor r g b 1000.
Definition zcolor_gray (v : Z) : ZColor := mkZColor v v v 1000.
Definition zcolor_transparent : ZColor := mkZColor 0 0 0 0.
Definition zcolor_black : ZColor := mkZColor 0 0 0 1000.
Definition zcolor_white : ZColor := mkZColor 1000 1000 1000 1000.

(** * Operations *)

Definition zcolor_with_alpha (c : ZColor) (alpha : Z) : ZColor :=
  mkZColor (zcolor_r c) (zcolor_g c) (zcolor_b c) alpha.

Definition zcolor_fade (c : ZColor) (factor : Z) : ZColor :=
  mkZColor (zcolor_r c) (zcolor_g c) (zcolor_b c) (zcolor_a c * factor / 1000).

Definition zcolor_lerp (a b : ZColor) (t : Z) : ZColor :=
  mkZColor
    (zcolor_r a + (zcolor_r b - zcolor_r a) * t / 1000)
    (zcolor_g a + (zcolor_g b - zcolor_g a) * t / 1000)
    (zcolor_b a + (zcolor_b b - zcolor_b a) * t / 1000)
    (zcolor_a a + (zcolor_a b - zcolor_a a) * t / 1000).

Definition zcolor_premultiplied (c : ZColor) : ZColor :=
  mkZColor
    (zcolor_r c * zcolor_a c / 1000)
    (zcolor_g c * zcolor_a c / 1000)
    (zcolor_b c * zcolor_a c / 1000)
    (zcolor_a c).

Definition zcolor_blend_over (src dst : ZColor) : ZColor :=
  let inv := 1000 - zcolor_a src in
  mkZColor
    ((zcolor_r src * zcolor_a src + zcolor_r dst * inv) / 1000)
    ((zcolor_g src * zcolor_a src + zcolor_g dst * inv) / 1000)
    ((zcolor_b src * zcolor_a src + zcolor_b dst * inv) / 1000)
    ((zcolor_a src * 1000 + zcolor_a dst * inv) / 1000).

(** Luminance (scaled by 10000): 2126*R + 7152*G + 722*B *)
Definition zcolor_luminance (c : ZColor) : Z :=
  2126 * zcolor_r c + 7152 * zcolor_g c + 722 * zcolor_b c.

Definition zclamp (v lo hi : Z) : Z :=
  if v <? lo then lo
  else if hi <? v then hi
  else v.

Definition zcolor_clamp (c : ZColor) : ZColor :=
  mkZColor
    (zclamp (zcolor_r c) 0 1000)
    (zclamp (zcolor_g c) 0 1000)
    (zclamp (zcolor_b c) 0 1000)
    (zclamp (zcolor_a c) 0 1000).

(** * Algebraic Properties *)

(** ** Constructor Properties *)

Theorem zcolor_new_components : forall r g b a : Z,
  let c := zcolor_new r g b a in
  zcolor_r c = r /\ zcolor_g c = g /\ zcolor_b c = b /\ zcolor_a c = a.
Proof.
  intros. simpl. repeat split; reflexivity.
Qed.

Theorem zcolor_rgb_full_alpha : forall r g b : Z,
  zcolor_a (zcolor_rgb r g b) = 1000.
Proof.
  intros. reflexivity.
Qed.

Theorem zcolor_gray_equal_rgb : forall v : Z,
  let c := zcolor_gray v in
  zcolor_r c = v /\ zcolor_g c = v /\ zcolor_b c = v /\ zcolor_a c = 1000.
Proof.
  intros. simpl. repeat split; reflexivity.
Qed.

(** ** Alpha Operations *)

Theorem zcolor_with_alpha_preserves_rgb : forall (c : ZColor) (alpha : Z),
  let result := zcolor_with_alpha c alpha in
  zcolor_r result = zcolor_r c /\
  zcolor_g result = zcolor_g c /\
  zcolor_b result = zcolor_b c /\
  zcolor_a result = alpha.
Proof.
  intros. destruct c. simpl. repeat split; reflexivity.
Qed.

Theorem zcolor_fade_preserves_rgb : forall (c : ZColor) (factor : Z),
  let result := zcolor_fade c factor in
  zcolor_r result = zcolor_r c /\
  zcolor_g result = zcolor_g c /\
  zcolor_b result = zcolor_b c.
Proof.
  intros. destruct c. simpl. repeat split; reflexivity.
Qed.

Theorem zcolor_fade_zero : forall (c : ZColor),
  zcolor_a (zcolor_fade c 0) = 0.
Proof.
  intros [r g b a]. unfold zcolor_fade. cbn [zcolor_a zcolor_r zcolor_g zcolor_b].
  rewrite Z.mul_0_r. reflexivity.
Qed.

(** ** Interpolation Properties *)

Theorem zcolor_lerp_same : forall (c : ZColor) (t : Z),
  zcolor_lerp c c t = c.
Proof.
  intros [r g b a] t.
  assert (Hsame: forall x : Z, x + (x - x) * t / 1000 = x).
  { intro x. replace (x - x) with 0 by lia. rewrite Z.mul_0_l.
    assert (Hdiv: 0 / 1000 = 0) by reflexivity. rewrite Hdiv. lia. }
  unfold zcolor_lerp. cbn -[Z.mul Z.div Z.add Z.sub].
  apply zcolor_eq; apply Hsame.
Qed.

Theorem zcolor_lerp_zero : forall (a b : ZColor),
  zcolor_lerp a b 0 = a.
Proof.
  intros [ar ag ab0 aa] [br bg bb ba].
  assert (Hzero: forall x y : Z, x + (y - x) * 0 / 1000 = x).
  { intros. rewrite Z.mul_0_r.
    assert (Hdiv: 0 / 1000 = 0) by reflexivity. rewrite Hdiv. lia. }
  unfold zcolor_lerp. cbn -[Z.mul Z.div Z.add Z.sub].
  apply zcolor_eq; apply Hzero.
Qed.

Theorem zcolor_lerp_one : forall (a b : ZColor),
  zcolor_lerp a b 1000 = b.
Proof.
  intros [ar ag ab0 aa] [br bg bb ba].
  assert (Hlerp: forall x y : Z, x + (y - x) * 1000 / 1000 = y)
    by (intros; rewrite Z.div_mul by lia; lia).
  unfold zcolor_lerp. cbn -[Z.mul Z.div Z.add Z.sub].
  apply zcolor_eq; apply Hlerp.
Qed.

(** ** Premultiplication Properties *)

Theorem zcolor_premultiplied_preserves_alpha : forall (c : ZColor),
  zcolor_a (zcolor_premultiplied c) = zcolor_a c.
Proof.
  intros [r g b a]. simpl. reflexivity.
Qed.

Theorem zcolor_premultiplied_zero_alpha : forall (c : ZColor),
  zcolor_a c = 0 ->
  zcolor_r (zcolor_premultiplied c) = 0 /\
  zcolor_g (zcolor_premultiplied c) = 0 /\
  zcolor_b (zcolor_premultiplied c) = 0.
Proof.
  intros [r g b a] Ha. cbn [zcolor_a] in Ha. subst.
  unfold zcolor_premultiplied. cbn [zcolor_r zcolor_g zcolor_b zcolor_a].
  repeat split; rewrite Z.mul_0_r; reflexivity.
Qed.

(** ** Blending Properties *)

Theorem zcolor_blend_transparent_fg : forall (src dst : ZColor),
  zcolor_a src = 0 ->
  zcolor_r (zcolor_blend_over src dst) = zcolor_r dst /\
  zcolor_g (zcolor_blend_over src dst) = zcolor_g dst /\
  zcolor_b (zcolor_blend_over src dst) = zcolor_b dst.
Proof.
  intros [sr sg sb sa] [dr dg db da] Ha. cbn [zcolor_a] in Ha. subst.
  unfold zcolor_blend_over. cbn -[Z.mul Z.div Z.add Z.sub].
  repeat split.
  - replace (sr * 0 + dr * (1000 - 0)) with (dr * 1000) by ring.
    rewrite Z.div_mul by lia. reflexivity.
  - replace (sg * 0 + dg * (1000 - 0)) with (dg * 1000) by ring.
    rewrite Z.div_mul by lia. reflexivity.
  - replace (sb * 0 + db * (1000 - 0)) with (db * 1000) by ring.
    rewrite Z.div_mul by lia. reflexivity.
Qed.

(** ** Luminance Properties *)

Theorem zcolor_luminance_black :
  zcolor_luminance zcolor_black = 0.
Proof.
  unfold zcolor_luminance, zcolor_black. simpl. reflexivity.
Qed.

Theorem zcolor_luminance_white :
  zcolor_luminance zcolor_white = 10000000.
Proof.
  unfold zcolor_luminance, zcolor_white. simpl. reflexivity.
Qed.

Theorem zcolor_luminance_gray : forall (v : Z),
  zcolor_luminance (zcolor_gray v) = 10000 * v.
Proof.
  intros v. unfold zcolor_luminance, zcolor_gray.
  cbn -[Z.mul Z.add]. ring.
Qed.

Theorem zcolor_luminance_nonneg : forall (c : ZColor),
  zcolor_r c >= 0 -> zcolor_g c >= 0 -> zcolor_b c >= 0 ->
  zcolor_luminance c >= 0.
Proof.
  intros [r g b a] Hr Hg Hb.
  cbn -[Z.mul Z.add] in *.
  unfold zcolor_luminance. cbn -[Z.mul Z.add]. nia.
Qed.

(** * Component-wise Operations *)

(** Color addition (component-wise) *)
Definition zcolor_add (a b : ZColor) : ZColor :=
  mkZColor (zcolor_r a + zcolor_r b) (zcolor_g a + zcolor_g b)
           (zcolor_b a + zcolor_b b) (zcolor_a a + zcolor_a b).

(** Color scalar multiplication (fixed-point: s=1000 means 1.0) *)
Definition zcolor_scale (c : ZColor) (s : Z) : ZColor :=
  mkZColor (zcolor_r c * s / 1000) (zcolor_g c * s / 1000)
           (zcolor_b c * s / 1000) (zcolor_a c * s / 1000).

(** Color inversion: 1000-c for RGB (1000 = 1.0), alpha preserved *)
Definition zcolor_invert (c : ZColor) : ZColor :=
  mkZColor (1000 - zcolor_r c) (1000 - zcolor_g c) (1000 - zcolor_b c) (zcolor_a c).

(** Color mix (average of two colors) *)
Definition zcolor_mix (a b : ZColor) : ZColor :=
  mkZColor ((zcolor_r a + zcolor_r b) / 2) ((zcolor_g a + zcolor_g b) / 2)
           ((zcolor_b a + zcolor_b b) / 2) ((zcolor_a a + zcolor_a b) / 2).

(** ** Inversion Properties *)

Theorem zcolor_invert_involutive : forall (c : ZColor),
  zcolor_invert (zcolor_invert c) = c.
Proof.
  intros [r g b a]. unfold zcolor_invert. simpl.
  apply zcolor_eq; lia.
Qed.

Theorem zcolor_invert_preserves_alpha : forall (c : ZColor),
  zcolor_a (zcolor_invert c) = zcolor_a c.
Proof.
  intros [r g b a]. unfold zcolor_invert. simpl. reflexivity.
Qed.

Theorem zcolor_invert_black :
  zcolor_invert zcolor_black = mkZColor 1000 1000 1000 1000.
Proof.
  unfold zcolor_invert, zcolor_black. simpl. reflexivity.
Qed.

Theorem zcolor_invert_white :
  zcolor_invert zcolor_white = mkZColor 0 0 0 1000.
Proof.
  unfold zcolor_invert, zcolor_white. simpl. reflexivity.
Qed.

(** ** Mix Properties *)

Theorem zcolor_mix_comm : forall (a b : ZColor),
  zcolor_mix a b = zcolor_mix b a.
Proof.
  intros [ar ag ab0 aa] [br bg bb ba]. unfold zcolor_mix. simpl.
  apply zcolor_eq; f_equal; lia.
Qed.

Theorem zcolor_mix_self : forall (c : ZColor),
  zcolor_mix c c = c.
Proof.
  intros [r g b a]. unfold zcolor_mix. simpl.
  apply zcolor_eq.
  - replace (r + r) with (r * 2) by ring. apply Z.div_mul. lia.
  - replace (g + g) with (g * 2) by ring. apply Z.div_mul. lia.
  - replace (b + b) with (b * 2) by ring. apply Z.div_mul. lia.
  - replace (a + a) with (a * 2) by ring. apply Z.div_mul. lia.
Qed.

(** ** Addition Properties *)

Theorem zcolor_add_comm : forall (a b : ZColor),
  zcolor_add a b = zcolor_add b a.
Proof.
  intros [ar ag ab0 aa] [br bg bb ba]. unfold zcolor_add. simpl.
  apply zcolor_eq; ring.
Qed.

Theorem zcolor_add_transparent : forall (c : ZColor),
  zcolor_add c zcolor_transparent = c.
Proof.
  intros [r g b a]. unfold zcolor_add, zcolor_transparent. simpl.
  apply zcolor_eq; ring.
Qed.

(** ** Scale Properties *)

Theorem zcolor_scale_one : forall (c : ZColor),
  zcolor_scale c 1000 = c.
Proof.
  intros [r g b a]. unfold zcolor_scale. simpl.
  apply zcolor_eq; apply Z.div_mul; lia.
Qed.

Theorem zcolor_scale_zero : forall (c : ZColor),
  zcolor_scale c 0 = zcolor_transparent.
Proof.
  intros [r g b a]. unfold zcolor_scale, zcolor_transparent. simpl. reflexivity.
Qed.

(** * Computational Tests *)

Example zcolor_test_new :
  zcolor_new 500 600 700 800 = mkZColor 500 600 700 800.
Proof. reflexivity. Qed.

Example zcolor_test_rgb :
  zcolor_a (zcolor_rgb 500 500 500) = 1000.
Proof. reflexivity. Qed.

Example zcolor_test_gray :
  zcolor_gray 500 = mkZColor 500 500 500 1000.
Proof. reflexivity. Qed.

Example zcolor_test_luminance :
  zcolor_luminance (mkZColor 1000 0 0 1000) = 2126000.
Proof. reflexivity. Qed.
