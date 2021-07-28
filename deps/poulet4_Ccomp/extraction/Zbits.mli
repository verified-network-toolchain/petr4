open BinInt
open BinNums
open BinPos
open Coqlib
open Datatypes

val coq_P_mod_two_p : positive -> nat -> coq_Z

val coq_Zshiftin : bool -> coq_Z -> coq_Z

val coq_Zzero_ext : coq_Z -> coq_Z -> coq_Z

val coq_Zsign_ext : coq_Z -> coq_Z -> coq_Z

val coq_Z_one_bits : nat -> coq_Z -> coq_Z -> coq_Z list

val coq_P_is_power2 : positive -> bool

val coq_Z_is_power2 : coq_Z -> coq_Z option

val coq_Zsize : coq_Z -> coq_Z
