type 'a pre_t = 'a Poulet4.P4String.t

type t = P4info.t pre_t

val eq: 'a pre_t -> 'a pre_t -> bool
val neq: 'a pre_t -> 'a pre_t -> bool
