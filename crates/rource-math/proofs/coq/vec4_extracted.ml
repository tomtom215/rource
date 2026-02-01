
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

(** val zvec4_lerp : int -> zVec4 -> zVec4 -> zVec4 **)

let zvec4_lerp t a b =
  zvec4_add a (zvec4_scale t (zvec4_sub b a))
