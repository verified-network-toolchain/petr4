(* val packet_in: switch -> port -> Cstruct.t -> unit *)

val start: string -> handlers:(Petr4.Runtime.message -> unit) -> unit -> unit Lwt.t
