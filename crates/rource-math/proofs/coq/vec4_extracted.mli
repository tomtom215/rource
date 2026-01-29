
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

type zVec4 = { zvec4_x : int; zvec4_y : int; zvec4_z : int; zvec4_w : int }

val zvec4_x : zVec4 -> int

val zvec4_y : zVec4 -> int

val zvec4_z : zVec4 -> int

val zvec4_w : zVec4 -> int

val zvec4_eq_dec : zVec4 -> zVec4 -> bool

val zvec4_new : int -> int -> int -> int -> zVec4

val zvec4_zero : zVec4

val zvec4_one : zVec4

val zvec4_splat : int -> zVec4

val zvec4_unit_x : zVec4

val zvec4_unit_y : zVec4

val zvec4_unit_z : zVec4

val zvec4_unit_w : zVec4

val zvec4_add : zVec4 -> zVec4 -> zVec4

val zvec4_sub : zVec4 -> zVec4 -> zVec4

val zvec4_neg : zVec4 -> zVec4

val zvec4_scale : int -> zVec4 -> zVec4

val zvec4_mul : zVec4 -> zVec4 -> zVec4

val zvec4_dot : zVec4 -> zVec4 -> int

val zvec4_length_squared : zVec4 -> int
