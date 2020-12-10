open Sexplib.Conv

type 'a pre_t =
  [%import:'a Poulet4.P4Int.t
    [@with Bigint.t := Util.bigint]]
  [@@deriving sexp,show,yojson]

type t = Info.t pre_t
  [@@deriving sexp,show,yojson]
