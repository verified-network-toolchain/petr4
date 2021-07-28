open BinNums

module Pos :
 sig
  val succ : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end
