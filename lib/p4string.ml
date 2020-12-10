open Sexplib.Conv

type 'a pre_t =
  [%import:'a Poulet4.P4String.t
    [@with Poulet4.String0.t := string]]
  [@@deriving sexp,show,yojson]

type t = Info.t pre_t
  [@@deriving sexp,show,yojson]

let eq x y =
  x.str = y.str

let neq x y =
  not (eq x y)
