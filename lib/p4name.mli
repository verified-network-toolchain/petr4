type 'a pre_t =
  [%import:'a Poulet4.Typed.name
    [@with Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]

type t = Info.t pre_t
  [@@deriving sexp,show,yojson]

val to_bare : t -> t
val name_info: t -> Info.t
val name_eq : t -> t -> bool
val name_only : t -> string
