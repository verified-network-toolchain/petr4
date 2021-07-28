open BinInt
open BinNums

(** val coq_FLT_exp : coq_Z -> coq_Z -> coq_Z -> coq_Z **)

let coq_FLT_exp emin prec e =
  Z.max (Z.sub e prec) emin
