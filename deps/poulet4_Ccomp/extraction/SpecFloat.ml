open BinInt
open BinNums
open BinPos
open Datatypes

(** val digits2_pos : positive -> positive **)

let rec digits2_pos = function
| Coq_xI p -> Pos.succ (digits2_pos p)
| Coq_xO p -> Pos.succ (digits2_pos p)
| Coq_xH -> Coq_xH

(** val coq_Zdigits2 : coq_Z -> coq_Z **)

let coq_Zdigits2 n = match n with
| Z0 -> n
| Zpos p -> Zpos (digits2_pos p)
| Zneg p -> Zpos (digits2_pos p)

(** val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  match n with
  | Coq_xI n' -> iter_pos f n' (iter_pos f n' (f x))
  | Coq_xO n' -> iter_pos f n' (iter_pos f n' x)
  | Coq_xH -> f x

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

(** val cond_Zopp : bool -> coq_Z -> coq_Z **)

let cond_Zopp b m =
  if b then Z.opp m else m
