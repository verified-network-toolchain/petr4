open Sexplib.Conv
open Util

type 'a pre_t =
  [%import:'a Poulet4.P4Int.t
    [@with Bigint.t := bigint]]
  [@@deriving sexp,show,yojson]

type t = P4info.t pre_t
  [@@deriving sexp,show,yojson]
