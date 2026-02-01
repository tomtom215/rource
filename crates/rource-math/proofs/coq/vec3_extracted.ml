
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

(** val zvec3_lerp : int -> zVec3 -> zVec3 -> zVec3 **)

let zvec3_lerp t a b =
  zvec3_add a (zvec3_scale t (zvec3_sub b a))

(** val zvec3_scalar_triple : zVec3 -> zVec3 -> zVec3 -> int **)

let zvec3_scalar_triple a b c =
  zvec3_dot a (zvec3_cross b c)
