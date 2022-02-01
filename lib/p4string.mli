type 'a pre_t =
  [%import:'a Poulet4.P4String.t
    [@with Poulet4.String0.t := string]]
  [@@deriving sexp,show,yojson]

type t = P4info.t pre_t
  [@@deriving sexp,show,yojson]

val eq: 'a pre_t -> 'a pre_t -> bool
val neq: 'a pre_t -> 'a pre_t -> bool
