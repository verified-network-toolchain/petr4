type message = 
  | Hello of { switch: string; 
               ports: int }
  | Insert of { table : string; 
                matches : (string * string) list; 
                action : string; 
                action_data : (string * string) list }
   [@@deriving yojson]
