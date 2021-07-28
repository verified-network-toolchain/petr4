open BinInt
open BinNums
open Datatypes
open SpecFloat

(** val cond_incr : bool -> coq_Z -> coq_Z **)

let cond_incr b m =
  if b then Z.add m (Zpos Coq_xH) else m

(** val round_sign_DN : bool -> location -> bool **)

let round_sign_DN s = function
| Coq_loc_Exact -> false
| Coq_loc_Inexact _ -> s

(** val round_sign_UP : bool -> location -> bool **)

let round_sign_UP s = function
| Coq_loc_Exact -> false
| Coq_loc_Inexact _ -> negb s

(** val round_N : bool -> location -> bool **)

let round_N p = function
| Coq_loc_Exact -> false
| Coq_loc_Inexact c -> (match c with
                        | Eq -> p
                        | Lt -> false
                        | Gt -> true)
