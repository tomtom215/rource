
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

  (** val mul : int -> int -> int **)

  let mul = ( * )
 end

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
