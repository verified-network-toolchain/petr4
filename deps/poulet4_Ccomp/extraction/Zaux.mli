open BinInt
open BinNums
open BinPos
open Datatypes

type radix =
  coq_Z
  (* singleton inductive, whose constructor was Build_radix *)

val radix_val : radix -> coq_Z

val radix2 : radix

val coq_Zpos_div_eucl_aux1 : positive -> positive -> coq_Z * coq_Z

val coq_Zpos_div_eucl_aux : positive -> positive -> coq_Z * coq_Z

val coq_Zfast_div_eucl : coq_Z -> coq_Z -> coq_Z * coq_Z

val iter_nat : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1
