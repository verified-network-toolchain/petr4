open Pp
open Pp.O

let semi = text ";"
   
let format_ctyp t =
  match t with
  | Cimpl.CTVoid -> text "void"
  | Cimpl.CTInt -> text "int"

let format_cvar x =
  text x

let format_cexp e =
  match e with
  | Cimpl.CEVar x ->
     format_cvar x
  | Cimpl.CEInt n ->
     Int.to_string n |> text
                
let format_stmt s =
  match s with
  | Cimpl.CSSkip -> 
     semi
  | Cimpl.CSAssign(x,e) -> box(format_cvar x ++
                               space ++
                               text "=" ++
                               space ++
                               format_cexp e ++
                               semi)
           
let format_cblk b =
  match b with
  | Cimpl.CBlock ss ->
     box (text "{" ++
          space ++
          Pretty.(format_list_nl) format_stmt ss ++
          text "}")
           
let format_cdecl d =
  match d with
  | Cimpl.CDFunction(typ,name,body) ->
     box (format_ctyp typ ++
          space ++
          text name ++
          space ++ 
          text "()" ++
          space ++
          format_cblk body)
        
let format_program p =
  match p with
  | Cimpl.CProgram(ds) ->
     box (Pretty.(format_list_nl) format_cdecl ds) ++ (text "\n")
                                                 
