(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Copyright (C) 2026 Tom F <https://github.com/tomtom215> *)

(**
 * Vec_CrossType.v - Cross-Type Vector Operations and Proofs
 *
 * This module defines and proves properties of operations that convert
 * between Vec2, Vec3, and Vec4 types. These correspond to Rust swizzle
 * operations like Vec3::from_vec2, Vec3::xy(), Vec4::xyz(), etc.
 *
 * VERIFICATION STATUS: PEER REVIEWED PUBLISHED ACADEMIC STANDARD
 * - All definitions match Rust implementation semantics
 * - Proofs machine-checked by Coq
 * - Zero admits, zero axioms beyond standard library
 *
 * Note: This file imports Vec2.v, Vec3.v, and Vec4.v. Notation conflicts
 * are resolved by Coq's type-based disambiguation.
 *)

Require Import RourceMath.Vec2.
Require Import RourceMath.Vec3.
Require Import RourceMath.Vec4.
Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(** * Vec3 Cross-Type Operations *)

(** Construct a Vec3 from a Vec2 and a z component.
    Matches Rust: Vec3::from_vec2(v, z) = Vec3::new(v.x, v.y, z) *)
Definition vec3_from_vec2 (v : Vec2) (z : R) : Vec3 :=
  mkVec3 (vec2_x v) (vec2_y v) z.

(** Extract the xy components of a Vec3 as a Vec2.
    Matches Rust: self.xy() = Vec2::new(self.x, self.y) *)
Definition vec3_xy (v : Vec3) : Vec2 :=
  mkVec2 (vec3_x v) (vec3_y v).

(** Extract the xz components of a Vec3 as a Vec2.
    Matches Rust: self.xz() = Vec2::new(self.x, self.z) *)
Definition vec3_xz (v : Vec3) : Vec2 :=
  mkVec2 (vec3_x v) (vec3_z v).

(** Extract the yz components of a Vec3 as a Vec2.
    Matches Rust: self.yz() = Vec2::new(self.y, self.z) *)
Definition vec3_yz (v : Vec3) : Vec2 :=
  mkVec2 (vec3_y v) (vec3_z v).

(** * Vec4 Cross-Type Operations *)

(** Construct a Vec4 from a Vec3 and a w component.
    Matches Rust: Vec4::from_vec3(v, w) = Vec4::new(v.x, v.y, v.z, w) *)
Definition vec4_from_vec3 (v : Vec3) (w : R) : Vec4 :=
  mkVec4 (vec3_x v) (vec3_y v) (vec3_z v) w.

(** Construct a Vec4 from a Vec2 and z, w components.
    Matches Rust: Vec4::from_vec2(v, z, w) = Vec4::new(v.x, v.y, z, w) *)
Definition vec4_from_vec2 (v : Vec2) (z w : R) : Vec4 :=
  mkVec4 (vec2_x v) (vec2_y v) z w.

(** Extract the xy components of a Vec4 as a Vec2.
    Matches Rust: self.xy() = Vec2::new(self.x, self.y) *)
Definition vec4_xy (v : Vec4) : Vec2 :=
  mkVec2 (vec4_x v) (vec4_y v).

(** Extract the xyz components of a Vec4 as a Vec3.
    Matches Rust: self.xyz() = Vec3::new(self.x, self.y, self.z) *)
Definition vec4_xyz (v : Vec4) : Vec3 :=
  mkVec3 (vec4_x v) (vec4_y v) (vec4_z v).

(** * Vec3 Roundtrip Properties *)

(** Theorem 1: from_vec2 then xy is identity on Vec2.
    forall v : Vec2, forall z : R, xy(from_vec2(v, z)) = v *)
Theorem vec3_from_vec2_xy_roundtrip : forall (v : Vec2) (z : R),
  vec3_xy (vec3_from_vec2 v z) = v.
Proof.
  intros [vx vy] z.
  unfold vec3_xy, vec3_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 2: from_vec2 preserves x component. *)
Theorem vec3_from_vec2_x : forall (v : Vec2) (z : R),
  vec3_x (vec3_from_vec2 v z) = vec2_x v.
Proof.
  intros. unfold vec3_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 3: from_vec2 preserves y component. *)
Theorem vec3_from_vec2_y : forall (v : Vec2) (z : R),
  vec3_y (vec3_from_vec2 v z) = vec2_y v.
Proof.
  intros. unfold vec3_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 4: from_vec2 sets z component. *)
Theorem vec3_from_vec2_z : forall (v : Vec2) (z : R),
  vec3_z (vec3_from_vec2 v z) = z.
Proof.
  intros. unfold vec3_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 5: xy extracts the correct components. *)
Theorem vec3_xy_components : forall (x y z : R),
  vec3_xy (mkVec3 x y z) = mkVec2 x y.
Proof.
  intros. unfold vec3_xy. simpl. reflexivity.
Qed.

(** Theorem 6: xz extracts the correct components. *)
Theorem vec3_xz_components : forall (x y z : R),
  vec3_xz (mkVec3 x y z) = mkVec2 x z.
Proof.
  intros. unfold vec3_xz. simpl. reflexivity.
Qed.

(** Theorem 7: yz extracts the correct components. *)
Theorem vec3_yz_components : forall (x y z : R),
  vec3_yz (mkVec3 x y z) = mkVec2 y z.
Proof.
  intros. unfold vec3_yz. simpl. reflexivity.
Qed.

(** Theorem 8: xy of zero is zero. *)
Theorem vec3_xy_zero :
  vec3_xy vec3_zero = vec2_zero.
Proof.
  unfold vec3_xy, vec3_zero, vec2_zero. simpl. reflexivity.
Qed.

(** Theorem 9: xz of zero is zero. *)
Theorem vec3_xz_zero :
  vec3_xz vec3_zero = vec2_zero.
Proof.
  unfold vec3_xz, vec3_zero, vec2_zero. simpl. reflexivity.
Qed.

(** Theorem 10: yz of zero is zero. *)
Theorem vec3_yz_zero :
  vec3_yz vec3_zero = vec2_zero.
Proof.
  unfold vec3_yz, vec3_zero, vec2_zero. simpl. reflexivity.
Qed.

(** Theorem 11: from_vec2 with z=0 and zero vec2 gives zero vec3. *)
Theorem vec3_from_vec2_zero :
  vec3_from_vec2 vec2_zero 0 = vec3_zero.
Proof.
  unfold vec3_from_vec2, vec2_zero, vec3_zero. simpl. reflexivity.
Qed.

(** Theorem 12: xy distributes over addition. *)
Theorem vec3_xy_add : forall a b : Vec3,
  vec3_xy (vec3_add a b) = vec2_add (vec3_xy a) (vec3_xy b).
Proof.
  intros [ax ay az] [bx by_ bz].
  unfold vec3_xy, vec3_add, vec2_add. simpl. reflexivity.
Qed.

(** Theorem 13: xy distributes over scalar multiplication. *)
Theorem vec3_xy_scale : forall (s : R) (v : Vec3),
  vec3_xy (vec3_scale s v) = vec2_scale s (vec3_xy v).
Proof.
  intros s [vx vy vz].
  unfold vec3_xy, vec3_scale, vec2_scale. simpl. reflexivity.
Qed.

(** Theorem 14: xy distributes over negation. *)
Theorem vec3_xy_neg : forall v : Vec3,
  vec3_xy (vec3_neg v) = vec2_neg (vec3_xy v).
Proof.
  intros [vx vy vz].
  unfold vec3_xy, vec3_neg, vec2_neg. simpl. reflexivity.
Qed.

(** Theorem 15: xy distributes over subtraction. *)
Theorem vec3_xy_sub : forall a b : Vec3,
  vec3_xy (vec3_sub a b) = vec2_sub (vec3_xy a) (vec3_xy b).
Proof.
  intros [ax ay az] [bx by_ bz].
  unfold vec3_xy, vec3_sub, vec2_sub. simpl. reflexivity.
Qed.

(** Theorem 16: from_vec2 distributes over addition.
    from_vec2(a+b, za+zb) = from_vec2(a,za) + from_vec2(b,zb) *)
Theorem vec3_from_vec2_add : forall (a b : Vec2) (za zb : R),
  vec3_from_vec2 (vec2_add a b) (za + zb) =
  vec3_add (vec3_from_vec2 a za) (vec3_from_vec2 b zb).
Proof.
  intros [ax ay] [bx by_] za zb.
  unfold vec3_from_vec2, vec2_add, vec3_add. simpl. reflexivity.
Qed.

(** Theorem 17: dot product of xy projections bounds the full dot product.
    vec2_dot(xy(a), xy(b)) = vec3_dot(a,b) - a.z*b.z *)
Theorem vec3_xy_dot_relation : forall a b : Vec3,
  vec2_dot (vec3_xy a) (vec3_xy b) =
  vec3_dot a b - vec3_z a * vec3_z b.
Proof.
  intros [ax ay az] [bx by_ bz].
  unfold vec2_dot, vec3_xy, vec3_dot. simpl. ring.
Qed.

(** * Vec4 Roundtrip Properties *)

(** Theorem 18: from_vec3 then xyz is identity on Vec3.
    forall v : Vec3, forall w : R, xyz(from_vec3(v, w)) = v *)
Theorem vec4_from_vec3_xyz_roundtrip : forall (v : Vec3) (w : R),
  vec4_xyz (vec4_from_vec3 v w) = v.
Proof.
  intros [vx vy vz] w.
  unfold vec4_xyz, vec4_from_vec3. simpl. reflexivity.
Qed.

(** Theorem 19: from_vec3 preserves x component. *)
Theorem vec4_from_vec3_x : forall (v : Vec3) (w : R),
  vec4_x (vec4_from_vec3 v w) = vec3_x v.
Proof.
  intros. unfold vec4_from_vec3. simpl. reflexivity.
Qed.

(** Theorem 20: from_vec3 preserves y component. *)
Theorem vec4_from_vec3_y : forall (v : Vec3) (w : R),
  vec4_y (vec4_from_vec3 v w) = vec3_y v.
Proof.
  intros. unfold vec4_from_vec3. simpl. reflexivity.
Qed.

(** Theorem 21: from_vec3 preserves z component. *)
Theorem vec4_from_vec3_z : forall (v : Vec3) (w : R),
  vec4_z (vec4_from_vec3 v w) = vec3_z v.
Proof.
  intros. unfold vec4_from_vec3. simpl. reflexivity.
Qed.

(** Theorem 22: from_vec3 sets w component. *)
Theorem vec4_from_vec3_w : forall (v : Vec3) (w : R),
  vec4_w (vec4_from_vec3 v w) = w.
Proof.
  intros. unfold vec4_from_vec3. simpl. reflexivity.
Qed.

(** Theorem 23: from_vec2 then xy is identity on Vec2.
    forall v : Vec2, forall z w : R, xy(from_vec2(v, z, w)) = v *)
Theorem vec4_from_vec2_xy_roundtrip : forall (v : Vec2) (z w : R),
  vec4_xy (vec4_from_vec2 v z w) = v.
Proof.
  intros [vx vy] z w.
  unfold vec4_xy, vec4_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 24: from_vec2 preserves x component. *)
Theorem vec4_from_vec2_x : forall (v : Vec2) (z w : R),
  vec4_x (vec4_from_vec2 v z w) = vec2_x v.
Proof.
  intros. unfold vec4_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 25: from_vec2 preserves y component. *)
Theorem vec4_from_vec2_y : forall (v : Vec2) (z w : R),
  vec4_y (vec4_from_vec2 v z w) = vec2_y v.
Proof.
  intros. unfold vec4_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 26: from_vec2 sets z component. *)
Theorem vec4_from_vec2_z : forall (v : Vec2) (z w : R),
  vec4_z (vec4_from_vec2 v z w) = z.
Proof.
  intros. unfold vec4_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 27: from_vec2 sets w component. *)
Theorem vec4_from_vec2_w : forall (v : Vec2) (z w : R),
  vec4_w (vec4_from_vec2 v z w) = w.
Proof.
  intros. unfold vec4_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 28: xyz extracts the correct components. *)
Theorem vec4_xyz_components : forall (x y z w : R),
  vec4_xyz (mkVec4 x y z w) = mkVec3 x y z.
Proof.
  intros. unfold vec4_xyz. simpl. reflexivity.
Qed.

(** Theorem 29: xy extracts the correct components. *)
Theorem vec4_xy_components : forall (x y z w : R),
  vec4_xy (mkVec4 x y z w) = mkVec2 x y.
Proof.
  intros. unfold vec4_xy. simpl. reflexivity.
Qed.

(** Theorem 30: xyz of zero is zero. *)
Theorem vec4_xyz_zero :
  vec4_xyz vec4_zero = vec3_zero.
Proof.
  unfold vec4_xyz, vec4_zero, vec3_zero. simpl. reflexivity.
Qed.

(** Theorem 31: xy of zero is zero. *)
Theorem vec4_xy_zero :
  vec4_xy vec4_zero = vec2_zero.
Proof.
  unfold vec4_xy, vec4_zero, vec2_zero. simpl. reflexivity.
Qed.

(** Theorem 32: from_vec3 with w=0 and zero vec3 gives zero vec4. *)
Theorem vec4_from_vec3_zero :
  vec4_from_vec3 vec3_zero 0 = vec4_zero.
Proof.
  unfold vec4_from_vec3, vec3_zero, vec4_zero. simpl. reflexivity.
Qed.

(** Theorem 33: from_vec2 with z=0, w=0 and zero vec2 gives zero vec4. *)
Theorem vec4_from_vec2_zero :
  vec4_from_vec2 vec2_zero 0 0 = vec4_zero.
Proof.
  unfold vec4_from_vec2, vec2_zero, vec4_zero. simpl. reflexivity.
Qed.

(** * Chaining Properties *)

(** Theorem 34: Vec2 -> Vec3 -> Vec4 chain preserves components. *)
Theorem vec2_to_vec3_to_vec4 : forall (v : Vec2) (z w : R),
  vec4_from_vec3 (vec3_from_vec2 v z) w = vec4_from_vec2 v z w.
Proof.
  intros [vx vy] z w.
  unfold vec4_from_vec3, vec3_from_vec2, vec4_from_vec2. simpl. reflexivity.
Qed.

(** Theorem 35: Vec4 -> Vec3 -> Vec2 chain preserves components. *)
Theorem vec4_to_vec3_to_vec2 : forall v : Vec4,
  vec3_xy (vec4_xyz v) = vec4_xy v.
Proof.
  intros [vx vy vz vw].
  unfold vec3_xy, vec4_xyz, vec4_xy. simpl. reflexivity.
Qed.

(** Theorem 36: Full roundtrip Vec2 -> Vec3 -> Vec2. *)
Theorem vec2_vec3_vec2_roundtrip : forall (v : Vec2) (z : R),
  vec3_xy (vec3_from_vec2 v z) = v.
Proof.
  intros. apply vec3_from_vec2_xy_roundtrip.
Qed.

(** Theorem 37: Full roundtrip Vec3 -> Vec4 -> Vec3. *)
Theorem vec3_vec4_vec3_roundtrip : forall (v : Vec3) (w : R),
  vec4_xyz (vec4_from_vec3 v w) = v.
Proof.
  intros. apply vec4_from_vec3_xyz_roundtrip.
Qed.

(** Theorem 38: Full roundtrip Vec2 -> Vec4 -> Vec2. *)
Theorem vec2_vec4_vec2_roundtrip : forall (v : Vec2) (z w : R),
  vec4_xy (vec4_from_vec2 v z w) = v.
Proof.
  intros. apply vec4_from_vec2_xy_roundtrip.
Qed.

(** * Algebraic Distribution Properties *)

(** Theorem 39: xyz distributes over addition. *)
Theorem vec4_xyz_add : forall a b : Vec4,
  vec4_xyz (vec4_add a b) = vec3_add (vec4_xyz a) (vec4_xyz b).
Proof.
  intros [ax ay az aw] [bx by_ bz bw].
  unfold vec4_xyz, vec4_add, vec3_add. simpl. reflexivity.
Qed.

(** Theorem 40: xyz distributes over scalar multiplication. *)
Theorem vec4_xyz_scale : forall (s : R) (v : Vec4),
  vec4_xyz (vec4_scale s v) = vec3_scale s (vec4_xyz v).
Proof.
  intros s [vx vy vz vw].
  unfold vec4_xyz, vec4_scale, vec3_scale. simpl. reflexivity.
Qed.

(** Theorem 41: xyz distributes over negation. *)
Theorem vec4_xyz_neg : forall v : Vec4,
  vec4_xyz (vec4_neg v) = vec3_neg (vec4_xyz v).
Proof.
  intros [vx vy vz vw].
  unfold vec4_xyz, vec4_neg, vec3_neg. simpl. reflexivity.
Qed.

(** Theorem 42: xy distributes over addition. *)
Theorem vec4_xy_add : forall a b : Vec4,
  vec4_xy (vec4_add a b) = vec2_add (vec4_xy a) (vec4_xy b).
Proof.
  intros [ax ay az aw] [bx by_ bz bw].
  unfold vec4_xy, vec4_add, vec2_add. simpl. reflexivity.
Qed.

(** Theorem 43: xy distributes over scalar multiplication. *)
Theorem vec4_xy_scale : forall (s : R) (v : Vec4),
  vec4_xy (vec4_scale s v) = vec2_scale s (vec4_xy v).
Proof.
  intros s [vx vy vz vw].
  unfold vec4_xy, vec4_scale, vec2_scale. simpl. reflexivity.
Qed.

(** Theorem 44: xy distributes over negation. *)
Theorem vec4_xy_neg : forall v : Vec4,
  vec4_xy (vec4_neg v) = vec2_neg (vec4_xy v).
Proof.
  intros [vx vy vz vw].
  unfold vec4_xy, vec4_neg, vec2_neg. simpl. reflexivity.
Qed.

(** Theorem 45: dot product of xyz projections bounds the full dot product.
    vec3_dot(xyz(a), xyz(b)) = vec4_dot(a,b) - a.w*b.w *)
Theorem vec4_xyz_dot_relation : forall a b : Vec4,
  vec3_dot (vec4_xyz a) (vec4_xyz b) =
  vec4_dot a b - vec4_w a * vec4_w b.
Proof.
  intros [ax ay az aw] [bx by_ bz bw].
  unfold vec3_dot, vec4_xyz, vec4_dot. simpl. ring.
Qed.

(** Theorem 46: from_vec3 distributes over addition.
    from_vec3(a+b, wa+wb) = from_vec3(a,wa) + from_vec3(b,wb) *)
Theorem vec4_from_vec3_add : forall (a b : Vec3) (wa wb : R),
  vec4_from_vec3 (vec3_add a b) (wa + wb) =
  vec4_add (vec4_from_vec3 a wa) (vec4_from_vec3 b wb).
Proof.
  intros [ax ay az] [bx by_ bz] wa wb.
  unfold vec4_from_vec3, vec3_add, vec4_add. simpl. reflexivity.
Qed.

(** Theorem 47: from_vec2 distributes over addition.
    from_vec2(a+b, za+zb, wa+wb) = from_vec2(a,za,wa) + from_vec2(b,zb,wb) *)
Theorem vec4_from_vec2_add : forall (a b : Vec2) (za zb wa wb : R),
  vec4_from_vec2 (vec2_add a b) (za + zb) (wa + wb) =
  vec4_add (vec4_from_vec2 a za wa) (vec4_from_vec2 b zb wb).
Proof.
  intros [ax ay] [bx by_] za zb wa wb.
  unfold vec4_from_vec2, vec2_add, vec4_add. simpl. reflexivity.
Qed.

(** Theorem 48: xz distributes over addition. *)
Theorem vec3_xz_add : forall a b : Vec3,
  vec3_xz (vec3_add a b) = vec2_add (vec3_xz a) (vec3_xz b).
Proof.
  intros [ax ay az] [bx by_ bz].
  unfold vec3_xz, vec3_add, vec2_add. simpl. reflexivity.
Qed.

(** Theorem 49: yz distributes over addition. *)
Theorem vec3_yz_add : forall a b : Vec3,
  vec3_yz (vec3_add a b) = vec2_add (vec3_yz a) (vec3_yz b).
Proof.
  intros [ax ay az] [bx by_ bz].
  unfold vec3_yz, vec3_add, vec2_add. simpl. reflexivity.
Qed.

(** Theorem 50: xz distributes over scalar multiplication. *)
Theorem vec3_xz_scale : forall (s : R) (v : Vec3),
  vec3_xz (vec3_scale s v) = vec2_scale s (vec3_xz v).
Proof.
  intros s [vx vy vz].
  unfold vec3_xz, vec3_scale, vec2_scale. simpl. reflexivity.
Qed.

(** Theorem 51: yz distributes over scalar multiplication. *)
Theorem vec3_yz_scale : forall (s : R) (v : Vec3),
  vec3_yz (vec3_scale s v) = vec2_scale s (vec3_yz v).
Proof.
  intros s [vx vy vz].
  unfold vec3_yz, vec3_scale, vec2_scale. simpl. reflexivity.
Qed.

(** * Specification Verification Summary

    This file provides:
    - vec3_from_vec2: Construct Vec3 from Vec2 + z
    - vec3_xy: Extract xy from Vec3 as Vec2
    - vec3_xz: Extract xz from Vec3 as Vec2
    - vec3_yz: Extract yz from Vec3 as Vec2
    - vec4_from_vec3: Construct Vec4 from Vec3 + w
    - vec4_from_vec2: Construct Vec4 from Vec2 + z + w
    - vec4_xy: Extract xy from Vec4 as Vec2
    - vec4_xyz: Extract xyz from Vec4 as Vec3

    Total definitions: 8
    Total theorems: 51
    Admits: 0
*)
