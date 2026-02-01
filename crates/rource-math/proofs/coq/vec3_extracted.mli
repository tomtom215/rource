
module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val eq_dec : int -> int -> bool
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val eq_dec : int -> int -> bool
 end

type zVec3 = { zvec3_x : int; zvec3_y : int; zvec3_z : int }

val zvec3_x : zVec3 -> int

val zvec3_y : zVec3 -> int

val zvec3_z : zVec3 -> int

val zvec3_eq_dec : zVec3 -> zVec3 -> bool

val zvec3_new : int -> int -> int -> zVec3

val zvec3_zero : zVec3

val zvec3_splat : int -> zVec3

val zvec3_unit_x : zVec3

val zvec3_unit_y : zVec3

val zvec3_unit_z : zVec3

val zvec3_add : zVec3 -> zVec3 -> zVec3

val zvec3_sub : zVec3 -> zVec3 -> zVec3

val zvec3_neg : zVec3 -> zVec3

val zvec3_scale : int -> zVec3 -> zVec3

val zvec3_mul : zVec3 -> zVec3 -> zVec3

val zvec3_dot : zVec3 -> zVec3 -> int

val zvec3_cross : zVec3 -> zVec3 -> zVec3

val zvec3_length_squared : zVec3 -> int

val zvec3_lerp : int -> zVec3 -> zVec3 -> zVec3

val zvec3_scalar_triple : zVec3 -> zVec3 -> zVec3 -> int
