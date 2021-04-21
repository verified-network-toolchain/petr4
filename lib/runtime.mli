type message = 
  | Insert of { table : string; 
                pattern : string; 
                action : string; 
                action_data : string list }
   [@@deriving yojson]
