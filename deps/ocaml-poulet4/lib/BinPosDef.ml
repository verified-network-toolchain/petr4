
module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of Bigint.t
  | IsNeg
 end
