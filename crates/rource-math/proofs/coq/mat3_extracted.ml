
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
 end

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
