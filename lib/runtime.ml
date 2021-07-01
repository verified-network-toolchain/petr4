type ctrl_packet = {
  switch : string;
  in_port : int;
  packet : string;
}
[@@deriving yojson]

(* name convention: "message FROM the controller" *)
type ctrl_msg =
  | Insert of { table : string; 
                matches : (string * string) list;
                action : string; 
                action_data : (string * string) list }
  | PacketOut of ctrl_packet
  | CounterRequest of { name : string; index: int }
[@@deriving yojson]

(* again, "message FROM the switch" *)
type switch_msg =
  | Hello of { switch : string;
               ports : int; }
  | Event of { switch : string; }
  | PacketIn of ctrl_packet
  | CounterResponse of { switch: string; name : string; index: int; count : int }
[@@deriving yojson]
