type 'a pre_t = 'a Poulet4.Typed.name

type t = P4info.t pre_t

val to_bare : t -> t
val name_tags : t -> P4info.t
val name_eq : t -> t -> bool
val p4string_name_only : t -> P4string.t
val name_only : t -> string
