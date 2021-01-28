type t
val create : unit -> t
val seen_name : t -> string -> bool
val observe_name : t -> string -> unit
val freshen_name : t -> string -> string
val freshen_p4string : t -> P4string.t -> P4string.t
