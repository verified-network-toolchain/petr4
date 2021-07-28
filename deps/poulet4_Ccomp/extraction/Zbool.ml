open BinInt
open BinNums
open Datatypes

(** val coq_Zeq_bool : coq_Z -> coq_Z -> bool **)

let coq_Zeq_bool x y =
  match Z.compare x y with
  | Eq -> true
  | _ -> false
