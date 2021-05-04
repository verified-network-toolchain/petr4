type message = 
  | Insert of { table : string; 
                matches : (string * string) list; 
                action : string; 
                action_data : (string * string) list }
   [@@deriving yojson]
