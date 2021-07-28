open EquivDec
open String0

type string = char list

(** val coq_StringEqDec : string coq_EqDec **)

let coq_StringEqDec =
  string_dec
