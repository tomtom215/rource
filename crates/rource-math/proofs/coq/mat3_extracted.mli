
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

  val sub : int -> int -> int

  val mul : int -> int -> int
 end

type zMat3 = { zm3_0 : int; zm3_1 : int; zm3_2 : int; zm3_3 : int;
               zm3_4 : int; zm3_5 : int; zm3_6 : int; zm3_7 : int; zm3_8 : 
               int }

val zm3_0 : zMat3 -> int

val zm3_1 : zMat3 -> int

val zm3_2 : zMat3 -> int

val zm3_3 : zMat3 -> int

val zm3_4 : zMat3 -> int

val zm3_5 : zMat3 -> int

val zm3_6 : zMat3 -> int

val zm3_7 : zMat3 -> int

val zm3_8 : zMat3 -> int

val zmat3_zero : zMat3

val zmat3_identity : zMat3

val zmat3_add : zMat3 -> zMat3 -> zMat3

val zmat3_neg : zMat3 -> zMat3

val zmat3_sub : zMat3 -> zMat3 -> zMat3

val zmat3_scale : int -> zMat3 -> zMat3

val zmat3_transpose : zMat3 -> zMat3

val zmat3_mul : zMat3 -> zMat3 -> zMat3

val zmat3_determinant : zMat3 -> int

val zmat3_trace : zMat3 -> int
