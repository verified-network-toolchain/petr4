include Poulet4.Typed

let eq_dir d1 d2 =
  match d1, d2 with
  | In, In
  | Out, Out
  | InOut, InOut
  | Directionless, Directionless -> true
  | _ -> false

type 'a info = 'a Types.info 

module Annotation = Types.Annotation
