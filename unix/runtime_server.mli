(* val packet_in: switch -> port -> Cstruct.t -> unit *)

val start: string -> handlers:(Petr4.Runtime.ctrl_msg -> unit) -> unit -> unit Lwt.t

val post_packet: string -> int -> string -> unit Lwt.t
         
