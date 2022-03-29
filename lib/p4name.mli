type 'a pre_t = 'a Poulet4.Typed.name

type t = P4info.t pre_t

val to_bare : t -> t
val name_info: t -> P4info.t
val name_eq : t -> t -> bool
val name_only : t -> string
