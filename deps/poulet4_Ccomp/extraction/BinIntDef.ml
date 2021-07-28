open BinNums
open BinPos
open Datatypes

module Z =
 struct
  (** val of_nat : nat -> coq_Z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)
 end
