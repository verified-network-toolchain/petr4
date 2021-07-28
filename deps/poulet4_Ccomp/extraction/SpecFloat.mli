open BinInt
open BinNums
open BinPos
open Datatypes

val digits2_pos : positive -> positive

val coq_Zdigits2 : coq_Z -> coq_Z

val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

val cond_Zopp : bool -> coq_Z -> coq_Z
