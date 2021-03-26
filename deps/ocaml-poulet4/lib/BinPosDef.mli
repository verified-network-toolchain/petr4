
module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of Bigint.t
  | IsNeg
 end
