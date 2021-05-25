type ctrl_packet = {
  switch : string;
  in_port : int;
  packet : string;
}
[@@deriving yojson]

type ctrl_msg = 
  | Insert of { table : string; 
                matches : (string * string) list; 
                action : string; 
                action_data : (string * string) list }
  | PacketOut of ctrl_packet
[@@deriving yojson]

type switch_msg =
  | Hello of { switch: string; 
               ports: int }
  | Event of { switch : string }
  | PacketIn of ctrl_packet
[@@deriving yojson]
	    
