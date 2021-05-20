type ctrl_pkt = {
  switch : string;
  in_port : int;
  pkt : string;
}
[@@deriving yojson]

type ctrl_msg = 
  | Insert of { table : string; 
                matches : (string * string) list; 
                action : string; 
                action_data : (string * string) list }
  | PktOut of ctrl_pkt
[@@deriving yojson]

type switch_msg =
  | Hello of { switch: string; 
               ports: int }
  | Event of { switch : string }
  | PktIn of ctrl_pkt
[@@deriving yojson]
	    