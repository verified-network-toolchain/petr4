
(* name convention: "message FROM the controller" *)
type ctrl_msg =
  | Insert of { table : string; 
                matches : (string * string) list;
                action : string; 
                action_data : (string * string) list }
  | PktOut of { pkt : string; }
[@@deriving yojson]

(* again, "message FROM the switch" *)
type switch_msg =
  | Hello of { switch : string;
               ports : int; }
  | Event of { switch : string }
  | PktIn of { pkt : string; }
[@@deriving yojson]
