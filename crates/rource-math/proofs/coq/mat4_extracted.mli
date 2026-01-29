
module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val mul : int -> int -> int
 end

type zMat4 = { zm4_0 : int; zm4_1 : int; zm4_2 : int; zm4_3 : int;
               zm4_4 : int; zm4_5 : int; zm4_6 : int; zm4_7 : int;
               zm4_8 : int; zm4_9 : int; zm4_10 : int; zm4_11 : int;
               zm4_12 : int; zm4_13 : int; zm4_14 : int; zm4_15 : int }

val zm4_0 : zMat4 -> int

val zm4_1 : zMat4 -> int

val zm4_2 : zMat4 -> int

val zm4_3 : zMat4 -> int

val zm4_4 : zMat4 -> int

val zm4_5 : zMat4 -> int

val zm4_6 : zMat4 -> int

val zm4_7 : zMat4 -> int

val zm4_8 : zMat4 -> int

val zm4_9 : zMat4 -> int

val zm4_10 : zMat4 -> int

val zm4_11 : zMat4 -> int

val zm4_12 : zMat4 -> int

val zm4_13 : zMat4 -> int

val zm4_14 : zMat4 -> int

val zm4_15 : zMat4 -> int

val zmat4_zero : zMat4

val zmat4_identity : zMat4

val zmat4_add : zMat4 -> zMat4 -> zMat4

val zmat4_neg : zMat4 -> zMat4

val zmat4_sub : zMat4 -> zMat4 -> zMat4

val zmat4_scale : int -> zMat4 -> zMat4

val zmat4_transpose : zMat4 -> zMat4

val zmat4_mul : zMat4 -> zMat4 -> zMat4

val zmat4_trace : zMat4 -> int
