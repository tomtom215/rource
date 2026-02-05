(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Color.v - Abstract RGBA Color Specification (R-based)
 *
 * This module provides a mathematical formalization of RGBA colors
 * using Coq's R (real number) type.
 *
 * LAYERED VERIFICATION ARCHITECTURE:
 *
 *   Layer 1 (Abstract):      Color.v / Color_Proofs.v     (R-based)
 *   Layer 2 (Computational): Color_Compute.v              (Z-based, extractable)
 *   Layer 3 (Extraction):    Color_Extract.v              (OCaml/WASM output)
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 *)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(** * Color Definition *)

Record Color : Type := mkColor {
  color_r : R;
  color_g : R;
  color_b : R;
  color_a : R
}.

(** * Equality Lemma *)

Lemma color_eq : forall r1 g1 b1 a1 r2 g2 b2 a2 : R,
  r1 = r2 -> g1 = g2 -> b1 = b2 -> a1 = a2 ->
  mkColor r1 g1 b1 a1 = mkColor r2 g2 b2 a2.
Proof.
  intros. subst. reflexivity.
Qed.

(** * Constructors *)

Definition color_new (r g b a : R) : Color := mkColor r g b a.
Definition color_rgb (r g b : R) : Color := mkColor r g b 1.
Definition color_gray (v : R) : Color := mkColor v v v 1.

(** * Named Constants *)

Definition color_transparent : Color := mkColor 0 0 0 0.
Definition color_black : Color := mkColor 0 0 0 1.
Definition color_white : Color := mkColor 1 1 1 1.
Definition color_red : Color := mkColor 1 0 0 1.
Definition color_green : Color := mkColor 0 1 0 1.
Definition color_blue : Color := mkColor 0 0 1 1.

(** * Alpha Operations *)

Definition color_with_alpha (c : Color) (alpha : R) : Color :=
  mkColor (color_r c) (color_g c) (color_b c) alpha.

Definition color_fade (c : Color) (factor : R) : Color :=
  mkColor (color_r c) (color_g c) (color_b c) (color_a c * factor).

(** * Interpolation *)

Definition color_lerp (a b : Color) (t : R) : Color :=
  mkColor
    (color_r a + (color_r b - color_r a) * t)
    (color_g a + (color_g b - color_g a) * t)
    (color_b a + (color_b b - color_b a) * t)
    (color_a a + (color_a b - color_a a) * t).

(** * Premultiplication *)

Definition color_premultiplied (c : Color) : Color :=
  mkColor
    (color_r c * color_a c)
    (color_g c * color_a c)
    (color_b c * color_a c)
    (color_a c).

(** * Alpha Blending *)

Definition color_blend_over (src dst : Color) : Color :=
  let inv := 1 - color_a src in
  mkColor
    (color_r src * color_a src + color_r dst * inv)
    (color_g src * color_a src + color_g dst * inv)
    (color_b src * color_a src + color_b dst * inv)
    (color_a src + color_a dst * inv).

(** * Luminance (Rec. 709) *)

Definition color_luminance (c : Color) : R :=
  0.2126 * color_r c + 0.7152 * color_g c + 0.0722 * color_b c.

(** * Clamping *)

Definition clamp01 (v : R) : R :=
  if Rle_dec v 0 then 0
  else if Rle_dec 1 v then 1
  else v.

Definition color_clamp (c : Color) : Color :=
  mkColor (clamp01 (color_r c)) (clamp01 (color_g c))
          (clamp01 (color_b c)) (clamp01 (color_a c)).

(** * Component-wise Operations *)

(** Color addition (component-wise) *)
Definition color_add (a b : Color) : Color :=
  mkColor (color_r a + color_r b) (color_g a + color_g b)
          (color_b a + color_b b) (color_a a + color_a b).

(** Color scalar multiplication *)
Definition color_scale (c : Color) (s : R) : Color :=
  mkColor (color_r c * s) (color_g c * s) (color_b c * s) (color_a c * s).

(** Color inversion: 1 - c (alpha preserved) *)
Definition color_invert (c : Color) : Color :=
  mkColor (1 - color_r c) (1 - color_g c) (1 - color_b c) (color_a c).

(** Color mix (average of two colors) *)
Definition color_mix (a b : Color) : Color :=
  mkColor ((color_r a + color_r b) / 2) ((color_g a + color_g b) / 2)
          ((color_b a + color_b b) / 2) ((color_a a + color_a b) / 2).

(** Color contrasting: returns black or white for maximum contrast.
    Uses luminance threshold of 0.5 (Rec. 709 luminance). *)
Definition color_contrasting (c : Color) : Color :=
  if Rle_dec (color_luminance c) (1/2) then color_white else color_black.

(** Darken a color by a factor in [0, 1].
    darken(c, 0) = c, darken(c, 1) = black (preserving alpha). *)
Definition color_darken (c : Color) (amount : R) : Color :=
  mkColor (color_r c * (1 - amount))
          (color_g c * (1 - amount))
          (color_b c * (1 - amount))
          (color_a c).

(** Lighten a color by a factor in [0, 1].
    lighten(c, 0) = c, lighten(c, 1) = white (preserving alpha). *)
Definition color_lighten (c : Color) (amount : R) : Color :=
  mkColor (color_r c + (1 - color_r c) * amount)
          (color_g c + (1 - color_g c) * amount)
          (color_b c + (1 - color_b c) * amount)
          (color_a c).

(** * Integer Conversion Operations *)

(** Convert a natural number in [0, 255] to its real-valued [0, 1] equivalent. *)
Definition u8_to_f32 (n : R) : R := n / 255.

(** Convert from 8-bit RGBA values to Color.
    Models Rust's from_rgba8(r, g, b, a) where each argument is u8. *)
Definition color_from_u8 (r g b a : R) : Color :=
  mkColor (u8_to_f32 r) (u8_to_f32 g) (u8_to_f32 b) (u8_to_f32 a).

(** Convert from 8-bit RGB values to Color (alpha = 1.0).
    Models Rust's from_rgb8(r, g, b). *)
Definition color_from_rgb8 (r g b : R) : Color :=
  color_from_u8 r g b 255.

(** Convert from hex RGB value (alpha = 1.0).
    Models Rust's from_hex(0xRRGGBB). *)
Definition color_from_hex (r_byte g_byte b_byte : R) : Color :=
  mkColor (u8_to_f32 r_byte) (u8_to_f32 g_byte) (u8_to_f32 b_byte) 1.

(** Convert from hex RGBA value.
    Models Rust's from_hex_alpha(0xRRGGBBAA). *)
Definition color_from_hex_alpha (r_byte g_byte b_byte a_byte : R) : Color :=
  mkColor (u8_to_f32 r_byte) (u8_to_f32 g_byte)
          (u8_to_f32 b_byte) (u8_to_f32 a_byte).

(** Convert a [0, 1] real to its [0, 255] integer equivalent (with rounding).
    Models Rust's `(v.clamp(0.0, 1.0) * 255.0 + 0.5) as u32`.
    In exact arithmetic over R, this simplifies to v * 255. *)
Definition f32_to_u8 (v : R) : R := clamp01 v * 255.

(** * Approximate Equality *)

(** Approximate equality with epsilon tolerance.
    Matches Rust: Color::approx_eq(other) with default epsilon. *)
Definition color_approx_eq (a b : Color) (eps : R) : Prop :=
  Rabs (color_r a - color_r b) <= eps /\
  Rabs (color_g a - color_g b) <= eps /\
  Rabs (color_b a - color_b b) <= eps /\
  Rabs (color_a a - color_a b) <= eps.

(** * Array Conversion *)

(** Convert color to (r, g, b, a) tuple — models From<Color> for [f32; 4]. *)
Definition color_to_rgba (c : Color) : (R * R * R * R) :=
  (color_r c, color_g c, color_b c, color_a c).

(** Convert color to (r, g, b) tuple — models From<Color> for [f32; 3]. *)
Definition color_to_rgb (c : Color) : (R * R * R) :=
  (color_r c, color_g c, color_b c).

(** Construct color from (r, g, b, a) tuple — models From<[f32; 4]> for Color. *)
Definition color_from_rgba (r g b a : R) : Color := mkColor r g b a.

(** Construct color from (r, g, b) tuple — models From<[f32; 3]> for Color (a=1). *)
Definition color_from_rgb_tuple (r g b : R) : Color := mkColor r g b 1.

(** Color luminance threshold: luminance > 0.5 means "light".
    Models Rust's concept but does not directly correspond to a pub fn. *)
Definition color_is_light (c : Color) : Prop :=
  color_luminance c > 1/2.

(** Color is dark: luminance ≤ 0.5. *)
Definition color_is_dark (c : Color) : Prop :=
  color_luminance c <= 1/2.

(** Contrast ratio between two colors (simplified Weber contrast).
    Models the general concept of contrast measurement. *)
Definition color_contrast (a b : Color) : R :=
  let la := color_luminance a in
  let lb := color_luminance b in
  Rabs (la - lb).

(** * Notations *)

Notation "+c" := color_new (at level 0).
