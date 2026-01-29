
module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec p p0)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec p p0)
        y)
      x
 end

type zVec2 = { zvec2_x : int; zvec2_y : int }

(** val zvec2_x : zVec2 -> int **)

let zvec2_x z0 =
  z0.zvec2_x

(** val zvec2_y : zVec2 -> int **)

let zvec2_y z0 =
  z0.zvec2_y

(** val zvec2_eq_dec : zVec2 -> zVec2 -> bool **)

let zvec2_eq_dec a b =
  let { zvec2_x = zvec2_x0; zvec2_y = zvec2_y0 } = a in
  let { zvec2_x = zvec2_x1; zvec2_y = zvec2_y1 } = b in
  let s = Z.eq_dec zvec2_x0 zvec2_x1 in
  if s then Z.eq_dec zvec2_y0 zvec2_y1 else false

(** val zvec2_new : int -> int -> zVec2 **)

let zvec2_new x y =
  { zvec2_x = x; zvec2_y = y }

(** val zvec2_zero : zVec2 **)

let zvec2_zero =
  { zvec2_x = 0; zvec2_y = 0 }

(** val zvec2_splat : int -> zVec2 **)

let zvec2_splat v =
  { zvec2_x = v; zvec2_y = v }

(** val zvec2_unit_x : zVec2 **)

let zvec2_unit_x =
  { zvec2_x = 1; zvec2_y = 0 }

(** val zvec2_unit_y : zVec2 **)

let zvec2_unit_y =
  { zvec2_x = 0; zvec2_y = 1 }

(** val zvec2_add : zVec2 -> zVec2 -> zVec2 **)

let zvec2_add a b =
  { zvec2_x = (Z.add a.zvec2_x b.zvec2_x); zvec2_y =
    (Z.add a.zvec2_y b.zvec2_y) }

(** val zvec2_sub : zVec2 -> zVec2 -> zVec2 **)

let zvec2_sub a b =
  { zvec2_x = (Z.sub a.zvec2_x b.zvec2_x); zvec2_y =
    (Z.sub a.zvec2_y b.zvec2_y) }

(** val zvec2_neg : zVec2 -> zVec2 **)

let zvec2_neg v =
  { zvec2_x = (Z.opp v.zvec2_x); zvec2_y = (Z.opp v.zvec2_y) }

(** val zvec2_scale : int -> zVec2 -> zVec2 **)

let zvec2_scale s v =
  { zvec2_x = (Z.mul s v.zvec2_x); zvec2_y = (Z.mul s v.zvec2_y) }

(** val zvec2_mul : zVec2 -> zVec2 -> zVec2 **)

let zvec2_mul a b =
  { zvec2_x = (Z.mul a.zvec2_x b.zvec2_x); zvec2_y =
    (Z.mul a.zvec2_y b.zvec2_y) }

(** val zvec2_dot : zVec2 -> zVec2 -> int **)

let zvec2_dot a b =
  Z.add (Z.mul a.zvec2_x b.zvec2_x) (Z.mul a.zvec2_y b.zvec2_y)

(** val zvec2_cross : zVec2 -> zVec2 -> int **)

let zvec2_cross a b =
  Z.sub (Z.mul a.zvec2_x b.zvec2_y) (Z.mul a.zvec2_y b.zvec2_x)

(** val zvec2_perp : zVec2 -> zVec2 **)

let zvec2_perp v =
  { zvec2_x = (Z.opp v.zvec2_y); zvec2_y = v.zvec2_x }

(** val zvec2_length_squared : zVec2 -> int **)

let zvec2_length_squared v =
  zvec2_dot v v

type zVec3 = { zvec3_x : int; zvec3_y : int; zvec3_z : int }

(** val zvec3_x : zVec3 -> int **)

let zvec3_x z0 =
  z0.zvec3_x

(** val zvec3_y : zVec3 -> int **)

let zvec3_y z0 =
  z0.zvec3_y

(** val zvec3_z : zVec3 -> int **)

let zvec3_z z0 =
  z0.zvec3_z

(** val zvec3_eq_dec : zVec3 -> zVec3 -> bool **)

let zvec3_eq_dec a b =
  let { zvec3_x = zvec3_x0; zvec3_y = zvec3_y0; zvec3_z = zvec3_z0 } = a in
  let { zvec3_x = zvec3_x1; zvec3_y = zvec3_y1; zvec3_z = zvec3_z1 } = b in
  let s = Z.eq_dec zvec3_x0 zvec3_x1 in
  if s
  then let s0 = Z.eq_dec zvec3_y0 zvec3_y1 in
       if s0 then Z.eq_dec zvec3_z0 zvec3_z1 else false
  else false

(** val zvec3_new : int -> int -> int -> zVec3 **)

let zvec3_new x y z0 =
  { zvec3_x = x; zvec3_y = y; zvec3_z = z0 }

(** val zvec3_zero : zVec3 **)

let zvec3_zero =
  { zvec3_x = 0; zvec3_y = 0; zvec3_z = 0 }

(** val zvec3_splat : int -> zVec3 **)

let zvec3_splat v =
  { zvec3_x = v; zvec3_y = v; zvec3_z = v }

(** val zvec3_unit_x : zVec3 **)

let zvec3_unit_x =
  { zvec3_x = 1; zvec3_y = 0; zvec3_z = 0 }

(** val zvec3_unit_y : zVec3 **)

let zvec3_unit_y =
  { zvec3_x = 0; zvec3_y = 1; zvec3_z = 0 }

(** val zvec3_unit_z : zVec3 **)

let zvec3_unit_z =
  { zvec3_x = 0; zvec3_y = 0; zvec3_z = 1 }

(** val zvec3_add : zVec3 -> zVec3 -> zVec3 **)

let zvec3_add a b =
  { zvec3_x = (Z.add a.zvec3_x b.zvec3_x); zvec3_y =
    (Z.add a.zvec3_y b.zvec3_y); zvec3_z = (Z.add a.zvec3_z b.zvec3_z) }

(** val zvec3_sub : zVec3 -> zVec3 -> zVec3 **)

let zvec3_sub a b =
  { zvec3_x = (Z.sub a.zvec3_x b.zvec3_x); zvec3_y =
    (Z.sub a.zvec3_y b.zvec3_y); zvec3_z = (Z.sub a.zvec3_z b.zvec3_z) }

(** val zvec3_neg : zVec3 -> zVec3 **)

let zvec3_neg v =
  { zvec3_x = (Z.opp v.zvec3_x); zvec3_y = (Z.opp v.zvec3_y); zvec3_z =
    (Z.opp v.zvec3_z) }

(** val zvec3_scale : int -> zVec3 -> zVec3 **)

let zvec3_scale s v =
  { zvec3_x = (Z.mul s v.zvec3_x); zvec3_y = (Z.mul s v.zvec3_y); zvec3_z =
    (Z.mul s v.zvec3_z) }

(** val zvec3_mul : zVec3 -> zVec3 -> zVec3 **)

let zvec3_mul a b =
  { zvec3_x = (Z.mul a.zvec3_x b.zvec3_x); zvec3_y =
    (Z.mul a.zvec3_y b.zvec3_y); zvec3_z = (Z.mul a.zvec3_z b.zvec3_z) }

(** val zvec3_dot : zVec3 -> zVec3 -> int **)

let zvec3_dot a b =
  Z.add (Z.add (Z.mul a.zvec3_x b.zvec3_x) (Z.mul a.zvec3_y b.zvec3_y))
    (Z.mul a.zvec3_z b.zvec3_z)

(** val zvec3_cross : zVec3 -> zVec3 -> zVec3 **)

let zvec3_cross a b =
  { zvec3_x =
    (Z.sub (Z.mul a.zvec3_y b.zvec3_z) (Z.mul a.zvec3_z b.zvec3_y));
    zvec3_y =
    (Z.sub (Z.mul a.zvec3_z b.zvec3_x) (Z.mul a.zvec3_x b.zvec3_z));
    zvec3_z =
    (Z.sub (Z.mul a.zvec3_x b.zvec3_y) (Z.mul a.zvec3_y b.zvec3_x)) }

(** val zvec3_length_squared : zVec3 -> int **)

let zvec3_length_squared v =
  zvec3_dot v v

(** val zvec3_scalar_triple : zVec3 -> zVec3 -> zVec3 -> int **)

let zvec3_scalar_triple a b c =
  zvec3_dot a (zvec3_cross b c)

type zVec4 = { zvec4_x : int; zvec4_y : int; zvec4_z : int; zvec4_w : int }

(** val zvec4_x : zVec4 -> int **)

let zvec4_x z0 =
  z0.zvec4_x

(** val zvec4_y : zVec4 -> int **)

let zvec4_y z0 =
  z0.zvec4_y

(** val zvec4_z : zVec4 -> int **)

let zvec4_z z0 =
  z0.zvec4_z

(** val zvec4_w : zVec4 -> int **)

let zvec4_w z0 =
  z0.zvec4_w

(** val zvec4_eq_dec : zVec4 -> zVec4 -> bool **)

let zvec4_eq_dec a b =
  let { zvec4_x = zvec4_x0; zvec4_y = zvec4_y0; zvec4_z = zvec4_z0; zvec4_w =
    zvec4_w0 } = a
  in
  let { zvec4_x = zvec4_x1; zvec4_y = zvec4_y1; zvec4_z = zvec4_z1; zvec4_w =
    zvec4_w1 } = b
  in
  let s = Z.eq_dec zvec4_x0 zvec4_x1 in
  if s
  then let s0 = Z.eq_dec zvec4_y0 zvec4_y1 in
       if s0
       then let s1 = Z.eq_dec zvec4_z0 zvec4_z1 in
            if s1 then Z.eq_dec zvec4_w0 zvec4_w1 else false
       else false
  else false

(** val zvec4_new : int -> int -> int -> int -> zVec4 **)

let zvec4_new x y z0 w =
  { zvec4_x = x; zvec4_y = y; zvec4_z = z0; zvec4_w = w }

(** val zvec4_zero : zVec4 **)

let zvec4_zero =
  { zvec4_x = 0; zvec4_y = 0; zvec4_z = 0; zvec4_w = 0 }

(** val zvec4_one : zVec4 **)

let zvec4_one =
  { zvec4_x = 1; zvec4_y = 1; zvec4_z = 1; zvec4_w = 1 }

(** val zvec4_splat : int -> zVec4 **)

let zvec4_splat v =
  { zvec4_x = v; zvec4_y = v; zvec4_z = v; zvec4_w = v }

(** val zvec4_unit_x : zVec4 **)

let zvec4_unit_x =
  { zvec4_x = 1; zvec4_y = 0; zvec4_z = 0; zvec4_w = 0 }

(** val zvec4_unit_y : zVec4 **)

let zvec4_unit_y =
  { zvec4_x = 0; zvec4_y = 1; zvec4_z = 0; zvec4_w = 0 }

(** val zvec4_unit_z : zVec4 **)

let zvec4_unit_z =
  { zvec4_x = 0; zvec4_y = 0; zvec4_z = 1; zvec4_w = 0 }

(** val zvec4_unit_w : zVec4 **)

let zvec4_unit_w =
  { zvec4_x = 0; zvec4_y = 0; zvec4_z = 0; zvec4_w = 1 }

(** val zvec4_add : zVec4 -> zVec4 -> zVec4 **)

let zvec4_add a b =
  { zvec4_x = (Z.add a.zvec4_x b.zvec4_x); zvec4_y =
    (Z.add a.zvec4_y b.zvec4_y); zvec4_z = (Z.add a.zvec4_z b.zvec4_z);
    zvec4_w = (Z.add a.zvec4_w b.zvec4_w) }

(** val zvec4_sub : zVec4 -> zVec4 -> zVec4 **)

let zvec4_sub a b =
  { zvec4_x = (Z.sub a.zvec4_x b.zvec4_x); zvec4_y =
    (Z.sub a.zvec4_y b.zvec4_y); zvec4_z = (Z.sub a.zvec4_z b.zvec4_z);
    zvec4_w = (Z.sub a.zvec4_w b.zvec4_w) }

(** val zvec4_neg : zVec4 -> zVec4 **)

let zvec4_neg v =
  { zvec4_x = (Z.opp v.zvec4_x); zvec4_y = (Z.opp v.zvec4_y); zvec4_z =
    (Z.opp v.zvec4_z); zvec4_w = (Z.opp v.zvec4_w) }

(** val zvec4_scale : int -> zVec4 -> zVec4 **)

let zvec4_scale s v =
  { zvec4_x = (Z.mul s v.zvec4_x); zvec4_y = (Z.mul s v.zvec4_y); zvec4_z =
    (Z.mul s v.zvec4_z); zvec4_w = (Z.mul s v.zvec4_w) }

(** val zvec4_mul : zVec4 -> zVec4 -> zVec4 **)

let zvec4_mul a b =
  { zvec4_x = (Z.mul a.zvec4_x b.zvec4_x); zvec4_y =
    (Z.mul a.zvec4_y b.zvec4_y); zvec4_z = (Z.mul a.zvec4_z b.zvec4_z);
    zvec4_w = (Z.mul a.zvec4_w b.zvec4_w) }

(** val zvec4_dot : zVec4 -> zVec4 -> int **)

let zvec4_dot a b =
  Z.add
    (Z.add (Z.add (Z.mul a.zvec4_x b.zvec4_x) (Z.mul a.zvec4_y b.zvec4_y))
      (Z.mul a.zvec4_z b.zvec4_z)) (Z.mul a.zvec4_w b.zvec4_w)

(** val zvec4_length_squared : zVec4 -> int **)

let zvec4_length_squared v =
  zvec4_dot v v

type zMat3 = { zm3_0 : int; zm3_1 : int; zm3_2 : int; zm3_3 : int;
               zm3_4 : int; zm3_5 : int; zm3_6 : int; zm3_7 : int; zm3_8 : 
               int }

(** val zm3_0 : zMat3 -> int **)

let zm3_0 z0 =
  z0.zm3_0

(** val zm3_1 : zMat3 -> int **)

let zm3_1 z0 =
  z0.zm3_1

(** val zm3_2 : zMat3 -> int **)

let zm3_2 z0 =
  z0.zm3_2

(** val zm3_3 : zMat3 -> int **)

let zm3_3 z0 =
  z0.zm3_3

(** val zm3_4 : zMat3 -> int **)

let zm3_4 z0 =
  z0.zm3_4

(** val zm3_5 : zMat3 -> int **)

let zm3_5 z0 =
  z0.zm3_5

(** val zm3_6 : zMat3 -> int **)

let zm3_6 z0 =
  z0.zm3_6

(** val zm3_7 : zMat3 -> int **)

let zm3_7 z0 =
  z0.zm3_7

(** val zm3_8 : zMat3 -> int **)

let zm3_8 z0 =
  z0.zm3_8

(** val zmat3_zero : zMat3 **)

let zmat3_zero =
  { zm3_0 = 0; zm3_1 = 0; zm3_2 = 0; zm3_3 = 0; zm3_4 = 0; zm3_5 = 0; zm3_6 =
    0; zm3_7 = 0; zm3_8 = 0 }

(** val zmat3_identity : zMat3 **)

let zmat3_identity =
  { zm3_0 = 1; zm3_1 = 0; zm3_2 = 0; zm3_3 = 0; zm3_4 = 1; zm3_5 = 0; zm3_6 =
    0; zm3_7 = 0; zm3_8 = 1 }

(** val zmat3_add : zMat3 -> zMat3 -> zMat3 **)

let zmat3_add a b =
  { zm3_0 = (Z.add a.zm3_0 b.zm3_0); zm3_1 = (Z.add a.zm3_1 b.zm3_1); zm3_2 =
    (Z.add a.zm3_2 b.zm3_2); zm3_3 = (Z.add a.zm3_3 b.zm3_3); zm3_4 =
    (Z.add a.zm3_4 b.zm3_4); zm3_5 = (Z.add a.zm3_5 b.zm3_5); zm3_6 =
    (Z.add a.zm3_6 b.zm3_6); zm3_7 = (Z.add a.zm3_7 b.zm3_7); zm3_8 =
    (Z.add a.zm3_8 b.zm3_8) }

(** val zmat3_neg : zMat3 -> zMat3 **)

let zmat3_neg a =
  { zm3_0 = (Z.opp a.zm3_0); zm3_1 = (Z.opp a.zm3_1); zm3_2 =
    (Z.opp a.zm3_2); zm3_3 = (Z.opp a.zm3_3); zm3_4 = (Z.opp a.zm3_4);
    zm3_5 = (Z.opp a.zm3_5); zm3_6 = (Z.opp a.zm3_6); zm3_7 =
    (Z.opp a.zm3_7); zm3_8 = (Z.opp a.zm3_8) }

(** val zmat3_sub : zMat3 -> zMat3 -> zMat3 **)

let zmat3_sub a b =
  zmat3_add a (zmat3_neg b)

(** val zmat3_scale : int -> zMat3 -> zMat3 **)

let zmat3_scale s a =
  { zm3_0 = (Z.mul s a.zm3_0); zm3_1 = (Z.mul s a.zm3_1); zm3_2 =
    (Z.mul s a.zm3_2); zm3_3 = (Z.mul s a.zm3_3); zm3_4 = (Z.mul s a.zm3_4);
    zm3_5 = (Z.mul s a.zm3_5); zm3_6 = (Z.mul s a.zm3_6); zm3_7 =
    (Z.mul s a.zm3_7); zm3_8 = (Z.mul s a.zm3_8) }

(** val zmat3_transpose : zMat3 -> zMat3 **)

let zmat3_transpose a =
  { zm3_0 = a.zm3_0; zm3_1 = a.zm3_3; zm3_2 = a.zm3_6; zm3_3 = a.zm3_1;
    zm3_4 = a.zm3_4; zm3_5 = a.zm3_7; zm3_6 = a.zm3_2; zm3_7 = a.zm3_5;
    zm3_8 = a.zm3_8 }

(** val zmat3_mul : zMat3 -> zMat3 -> zMat3 **)

let zmat3_mul a b =
  { zm3_0 =
    (Z.add (Z.add (Z.mul a.zm3_0 b.zm3_0) (Z.mul a.zm3_3 b.zm3_1))
      (Z.mul a.zm3_6 b.zm3_2)); zm3_1 =
    (Z.add (Z.add (Z.mul a.zm3_1 b.zm3_0) (Z.mul a.zm3_4 b.zm3_1))
      (Z.mul a.zm3_7 b.zm3_2)); zm3_2 =
    (Z.add (Z.add (Z.mul a.zm3_2 b.zm3_0) (Z.mul a.zm3_5 b.zm3_1))
      (Z.mul a.zm3_8 b.zm3_2)); zm3_3 =
    (Z.add (Z.add (Z.mul a.zm3_0 b.zm3_3) (Z.mul a.zm3_3 b.zm3_4))
      (Z.mul a.zm3_6 b.zm3_5)); zm3_4 =
    (Z.add (Z.add (Z.mul a.zm3_1 b.zm3_3) (Z.mul a.zm3_4 b.zm3_4))
      (Z.mul a.zm3_7 b.zm3_5)); zm3_5 =
    (Z.add (Z.add (Z.mul a.zm3_2 b.zm3_3) (Z.mul a.zm3_5 b.zm3_4))
      (Z.mul a.zm3_8 b.zm3_5)); zm3_6 =
    (Z.add (Z.add (Z.mul a.zm3_0 b.zm3_6) (Z.mul a.zm3_3 b.zm3_7))
      (Z.mul a.zm3_6 b.zm3_8)); zm3_7 =
    (Z.add (Z.add (Z.mul a.zm3_1 b.zm3_6) (Z.mul a.zm3_4 b.zm3_7))
      (Z.mul a.zm3_7 b.zm3_8)); zm3_8 =
    (Z.add (Z.add (Z.mul a.zm3_2 b.zm3_6) (Z.mul a.zm3_5 b.zm3_7))
      (Z.mul a.zm3_8 b.zm3_8)) }

(** val zmat3_determinant : zMat3 -> int **)

let zmat3_determinant a =
  Z.add
    (Z.sub
      (Z.mul a.zm3_0 (Z.sub (Z.mul a.zm3_4 a.zm3_8) (Z.mul a.zm3_7 a.zm3_5)))
      (Z.mul a.zm3_3 (Z.sub (Z.mul a.zm3_1 a.zm3_8) (Z.mul a.zm3_7 a.zm3_2))))
    (Z.mul a.zm3_6 (Z.sub (Z.mul a.zm3_1 a.zm3_5) (Z.mul a.zm3_4 a.zm3_2)))

(** val zmat3_trace : zMat3 -> int **)

let zmat3_trace a =
  Z.add (Z.add a.zm3_0 a.zm3_4) a.zm3_8

type zMat4 = { zm4_0 : int; zm4_1 : int; zm4_2 : int; zm4_3 : int;
               zm4_4 : int; zm4_5 : int; zm4_6 : int; zm4_7 : int;
               zm4_8 : int; zm4_9 : int; zm4_10 : int; zm4_11 : int;
               zm4_12 : int; zm4_13 : int; zm4_14 : int; zm4_15 : int }

(** val zm4_0 : zMat4 -> int **)

let zm4_0 z0 =
  z0.zm4_0

(** val zm4_1 : zMat4 -> int **)

let zm4_1 z0 =
  z0.zm4_1

(** val zm4_2 : zMat4 -> int **)

let zm4_2 z0 =
  z0.zm4_2

(** val zm4_3 : zMat4 -> int **)

let zm4_3 z0 =
  z0.zm4_3

(** val zm4_4 : zMat4 -> int **)

let zm4_4 z0 =
  z0.zm4_4

(** val zm4_5 : zMat4 -> int **)

let zm4_5 z0 =
  z0.zm4_5

(** val zm4_6 : zMat4 -> int **)

let zm4_6 z0 =
  z0.zm4_6

(** val zm4_7 : zMat4 -> int **)

let zm4_7 z0 =
  z0.zm4_7

(** val zm4_8 : zMat4 -> int **)

let zm4_8 z0 =
  z0.zm4_8

(** val zm4_9 : zMat4 -> int **)

let zm4_9 z0 =
  z0.zm4_9

(** val zm4_10 : zMat4 -> int **)

let zm4_10 z0 =
  z0.zm4_10

(** val zm4_11 : zMat4 -> int **)

let zm4_11 z0 =
  z0.zm4_11

(** val zm4_12 : zMat4 -> int **)

let zm4_12 z0 =
  z0.zm4_12

(** val zm4_13 : zMat4 -> int **)

let zm4_13 z0 =
  z0.zm4_13

(** val zm4_14 : zMat4 -> int **)

let zm4_14 z0 =
  z0.zm4_14

(** val zm4_15 : zMat4 -> int **)

let zm4_15 z0 =
  z0.zm4_15

(** val zmat4_zero : zMat4 **)

let zmat4_zero =
  { zm4_0 = 0; zm4_1 = 0; zm4_2 = 0; zm4_3 = 0; zm4_4 = 0; zm4_5 = 0; zm4_6 =
    0; zm4_7 = 0; zm4_8 = 0; zm4_9 = 0; zm4_10 = 0; zm4_11 = 0; zm4_12 = 0;
    zm4_13 = 0; zm4_14 = 0; zm4_15 = 0 }

(** val zmat4_identity : zMat4 **)

let zmat4_identity =
  { zm4_0 = 1; zm4_1 = 0; zm4_2 = 0; zm4_3 = 0; zm4_4 = 0; zm4_5 = 1; zm4_6 =
    0; zm4_7 = 0; zm4_8 = 0; zm4_9 = 0; zm4_10 = 1; zm4_11 = 0; zm4_12 = 0;
    zm4_13 = 0; zm4_14 = 0; zm4_15 = 1 }

(** val zmat4_add : zMat4 -> zMat4 -> zMat4 **)

let zmat4_add a b =
  { zm4_0 = (Z.add a.zm4_0 b.zm4_0); zm4_1 = (Z.add a.zm4_1 b.zm4_1); zm4_2 =
    (Z.add a.zm4_2 b.zm4_2); zm4_3 = (Z.add a.zm4_3 b.zm4_3); zm4_4 =
    (Z.add a.zm4_4 b.zm4_4); zm4_5 = (Z.add a.zm4_5 b.zm4_5); zm4_6 =
    (Z.add a.zm4_6 b.zm4_6); zm4_7 = (Z.add a.zm4_7 b.zm4_7); zm4_8 =
    (Z.add a.zm4_8 b.zm4_8); zm4_9 = (Z.add a.zm4_9 b.zm4_9); zm4_10 =
    (Z.add a.zm4_10 b.zm4_10); zm4_11 = (Z.add a.zm4_11 b.zm4_11); zm4_12 =
    (Z.add a.zm4_12 b.zm4_12); zm4_13 = (Z.add a.zm4_13 b.zm4_13); zm4_14 =
    (Z.add a.zm4_14 b.zm4_14); zm4_15 = (Z.add a.zm4_15 b.zm4_15) }

(** val zmat4_neg : zMat4 -> zMat4 **)

let zmat4_neg a =
  { zm4_0 = (Z.opp a.zm4_0); zm4_1 = (Z.opp a.zm4_1); zm4_2 =
    (Z.opp a.zm4_2); zm4_3 = (Z.opp a.zm4_3); zm4_4 = (Z.opp a.zm4_4);
    zm4_5 = (Z.opp a.zm4_5); zm4_6 = (Z.opp a.zm4_6); zm4_7 =
    (Z.opp a.zm4_7); zm4_8 = (Z.opp a.zm4_8); zm4_9 = (Z.opp a.zm4_9);
    zm4_10 = (Z.opp a.zm4_10); zm4_11 = (Z.opp a.zm4_11); zm4_12 =
    (Z.opp a.zm4_12); zm4_13 = (Z.opp a.zm4_13); zm4_14 = (Z.opp a.zm4_14);
    zm4_15 = (Z.opp a.zm4_15) }

(** val zmat4_sub : zMat4 -> zMat4 -> zMat4 **)

let zmat4_sub a b =
  zmat4_add a (zmat4_neg b)

(** val zmat4_scale : int -> zMat4 -> zMat4 **)

let zmat4_scale s a =
  { zm4_0 = (Z.mul s a.zm4_0); zm4_1 = (Z.mul s a.zm4_1); zm4_2 =
    (Z.mul s a.zm4_2); zm4_3 = (Z.mul s a.zm4_3); zm4_4 = (Z.mul s a.zm4_4);
    zm4_5 = (Z.mul s a.zm4_5); zm4_6 = (Z.mul s a.zm4_6); zm4_7 =
    (Z.mul s a.zm4_7); zm4_8 = (Z.mul s a.zm4_8); zm4_9 = (Z.mul s a.zm4_9);
    zm4_10 = (Z.mul s a.zm4_10); zm4_11 = (Z.mul s a.zm4_11); zm4_12 =
    (Z.mul s a.zm4_12); zm4_13 = (Z.mul s a.zm4_13); zm4_14 =
    (Z.mul s a.zm4_14); zm4_15 = (Z.mul s a.zm4_15) }

(** val zmat4_transpose : zMat4 -> zMat4 **)

let zmat4_transpose a =
  { zm4_0 = a.zm4_0; zm4_1 = a.zm4_4; zm4_2 = a.zm4_8; zm4_3 = a.zm4_12;
    zm4_4 = a.zm4_1; zm4_5 = a.zm4_5; zm4_6 = a.zm4_9; zm4_7 = a.zm4_13;
    zm4_8 = a.zm4_2; zm4_9 = a.zm4_6; zm4_10 = a.zm4_10; zm4_11 = a.zm4_14;
    zm4_12 = a.zm4_3; zm4_13 = a.zm4_7; zm4_14 = a.zm4_11; zm4_15 = a.zm4_15 }

(** val zmat4_mul : zMat4 -> zMat4 -> zMat4 **)

let zmat4_mul a b =
  { zm4_0 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_0 b.zm4_0) (Z.mul a.zm4_4 b.zm4_1))
        (Z.mul a.zm4_8 b.zm4_2)) (Z.mul a.zm4_12 b.zm4_3)); zm4_1 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_1 b.zm4_0) (Z.mul a.zm4_5 b.zm4_1))
        (Z.mul a.zm4_9 b.zm4_2)) (Z.mul a.zm4_13 b.zm4_3)); zm4_2 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_2 b.zm4_0) (Z.mul a.zm4_6 b.zm4_1))
        (Z.mul a.zm4_10 b.zm4_2)) (Z.mul a.zm4_14 b.zm4_3)); zm4_3 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_3 b.zm4_0) (Z.mul a.zm4_7 b.zm4_1))
        (Z.mul a.zm4_11 b.zm4_2)) (Z.mul a.zm4_15 b.zm4_3)); zm4_4 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_0 b.zm4_4) (Z.mul a.zm4_4 b.zm4_5))
        (Z.mul a.zm4_8 b.zm4_6)) (Z.mul a.zm4_12 b.zm4_7)); zm4_5 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_1 b.zm4_4) (Z.mul a.zm4_5 b.zm4_5))
        (Z.mul a.zm4_9 b.zm4_6)) (Z.mul a.zm4_13 b.zm4_7)); zm4_6 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_2 b.zm4_4) (Z.mul a.zm4_6 b.zm4_5))
        (Z.mul a.zm4_10 b.zm4_6)) (Z.mul a.zm4_14 b.zm4_7)); zm4_7 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_3 b.zm4_4) (Z.mul a.zm4_7 b.zm4_5))
        (Z.mul a.zm4_11 b.zm4_6)) (Z.mul a.zm4_15 b.zm4_7)); zm4_8 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_0 b.zm4_8) (Z.mul a.zm4_4 b.zm4_9))
        (Z.mul a.zm4_8 b.zm4_10)) (Z.mul a.zm4_12 b.zm4_11)); zm4_9 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_1 b.zm4_8) (Z.mul a.zm4_5 b.zm4_9))
        (Z.mul a.zm4_9 b.zm4_10)) (Z.mul a.zm4_13 b.zm4_11)); zm4_10 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_2 b.zm4_8) (Z.mul a.zm4_6 b.zm4_9))
        (Z.mul a.zm4_10 b.zm4_10)) (Z.mul a.zm4_14 b.zm4_11)); zm4_11 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_3 b.zm4_8) (Z.mul a.zm4_7 b.zm4_9))
        (Z.mul a.zm4_11 b.zm4_10)) (Z.mul a.zm4_15 b.zm4_11)); zm4_12 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_0 b.zm4_12) (Z.mul a.zm4_4 b.zm4_13))
        (Z.mul a.zm4_8 b.zm4_14)) (Z.mul a.zm4_12 b.zm4_15)); zm4_13 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_1 b.zm4_12) (Z.mul a.zm4_5 b.zm4_13))
        (Z.mul a.zm4_9 b.zm4_14)) (Z.mul a.zm4_13 b.zm4_15)); zm4_14 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_2 b.zm4_12) (Z.mul a.zm4_6 b.zm4_13))
        (Z.mul a.zm4_10 b.zm4_14)) (Z.mul a.zm4_14 b.zm4_15)); zm4_15 =
    (Z.add
      (Z.add (Z.add (Z.mul a.zm4_3 b.zm4_12) (Z.mul a.zm4_7 b.zm4_13))
        (Z.mul a.zm4_11 b.zm4_14)) (Z.mul a.zm4_15 b.zm4_15)) }

(** val zmat4_trace : zMat4 -> int **)

let zmat4_trace a =
  Z.add (Z.add (Z.add a.zm4_0 a.zm4_5) a.zm4_10) a.zm4_15
