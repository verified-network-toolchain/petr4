(* This disables an "unused open P4string" warning. The open is unused
   in the file, but it signals to dune that this file depends on the
   p4string module. The use of P4string is inside a macro and it seems
   Dune does not parse macros. *)
[@@@warning "-33"]
open P4string

type 'a pre_t =
  [%import:'a Poulet4.Typed.name
    [@with Poulet4.P4String.t := P4string.pre_t]]
  [@@deriving sexp,show,yojson]

type t = P4info.t pre_t
  [@@deriving sexp,show,yojson]

val to_bare : t -> t
val name_info: t -> P4info.t
val name_eq : t -> t -> bool
val name_only : t -> string
