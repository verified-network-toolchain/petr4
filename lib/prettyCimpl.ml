open Pp
open Pp.O

let semi = text ";"
   
let format_ctyp t =
  match t with
  | Cimpl.CTVoid -> text "void"
  | Cimpl.CTInt -> text "int"

let format_cvar x =
  text x

let format_bop (x : Cimpl.bop) =
  match x with 
  | Cimpl.CBEq -> text "="
  | Cimpl.CBNe -> text "!="
  | Cimpl.CBLt -> text "<"
  | Cimpl.CBGt -> text ">"
  | Cimpl.CBGte -> text ">="
  | Cimpl.CBLte -> text "<="
  | Cimpl.CBAnd -> text "&&"
  | Cimpl.CBOr -> text "||"
  | Cimpl.CBAdd -> text "+"
  | Cimpl.CBSub -> text "-"
  | Cimpl.CBMul -> text "*"
  | Cimpl.CBDiv -> text "/"
  | Cimpl.CBMod -> text "%"
  
let format_uop (x : Cimpl.uop) = 
  match x with 
  | Cimpl.CUNeg -> text "-"

let rec format_cexp e =
  match e with
  | Cimpl.CEVar x ->
     format_cvar x
  | Cimpl.CEInt n ->
     Int.to_string n |> text
  | Cimpl.CECompExpr (b, c1, c2) -> 
    format_cexp c1  ++ space ++ format_bop b ++ space ++ format_cexp c2 ++ semi
  | Cimpl.CEUniExpr (u, c) -> 
    format_uop u ++ space++ format_cexp c ++ semi

let rec format_list s = 
  List.fold_left (fun acc stmt -> acc ++ format_stmt stmt) (text "") s
  
and format_stmt s =
  match s with
  | Cimpl.CSSkip -> 
     semi
  | Cimpl.CSAssign(x,e) -> box(format_cvar x ++
                               space ++
                               text "=" ++
                               space ++
                               format_cexp e ++
                               semi)
  | Cimpl.CSIf (c1, cs1, cs2) -> 
    box~indent:4 (text "if" ++
      space ++ format_cexp c1 ++ space ++ text "{" ++ newline ++ text "    "
      ++ format_list cs1 ++ newline ++ text "}" ++ space ++ text "else" ++ 
      space ++ text "{" ++ newline ++ text "    " ++ format_list cs2 ++
      newline ++ text "}"++ semi)
           
let format_cblk b =
  match b with
  | Cimpl.CKBlock ss ->
     text "{" ++
     newline ++
     text "    " ++  
     box ~indent:4 (Pretty.(format_list_nl) format_stmt ss) ++
     newline ++
     text "}"
           
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
                                                 
