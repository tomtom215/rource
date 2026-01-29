
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

type zVec2 = { zvec2_x : int; zvec2_y : int }

val zvec2_x : zVec2 -> int

val zvec2_y : zVec2 -> int

val zvec2_eq_dec : zVec2 -> zVec2 -> bool

val zvec2_new : int -> int -> zVec2

val zvec2_zero : zVec2

val zvec2_splat : int -> zVec2

val zvec2_unit_x : zVec2

val zvec2_unit_y : zVec2

val zvec2_add : zVec2 -> zVec2 -> zVec2

val zvec2_sub : zVec2 -> zVec2 -> zVec2

val zvec2_neg : zVec2 -> zVec2

val zvec2_scale : int -> zVec2 -> zVec2

val zvec2_mul : zVec2 -> zVec2 -> zVec2

val zvec2_dot : zVec2 -> zVec2 -> int

val zvec2_cross : zVec2 -> zVec2 -> int

val zvec2_perp : zVec2 -> zVec2

val zvec2_length_squared : zVec2 -> int

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

val zvec3_scalar_triple : zVec3 -> zVec3 -> zVec3 -> int

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
