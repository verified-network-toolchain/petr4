open Sexplib.Conv

type 'a pre_t = 'a Poulet4.P4String.t

type t = P4info.t pre_t

let eq x y =
  x.str = y.str

let neq x y =
  not (eq x y)
