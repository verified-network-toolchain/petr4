open Pp
open Pp.O

let format_ctyp t =
  match t with
  | Cimpl.CVoid -> text "void"
  | Cimpl.CInt -> text "int"

let format_stmt s =
  match s with
  | Cimpl.CSkip -> text ";"
           
let format_cblk b =
  match b with
  | Cimpl.CBlock ss ->
     box (text "{" ++
          space ++
          Pretty.(format_list_nl) format_stmt ss ++
          text "}")
           
let format_cdecl d =
  match d with
  | Cimpl.CFunction(typ,name,body) ->
     box (format_ctyp typ ++
          space ++
          text name ++
          space ++ 
          format_cblk body)
        
let format_program p =
  match p with
  | Cimpl.CProgram(ds) ->
     box (Pretty.(format_list_nl) format_cdecl ds) ++ (text "\n")
                                                 
