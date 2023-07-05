open Pp
open Pp.O
open Core
   
open Poulet4.GCL

let format_bop bop =
  match bop with
  | BitVec.BVPlus _ ->
     text "+"
  | BitVec.BVMinus _ ->
     text "-"
  | BitVec.BVTimes _ ->
     text "*"
  | BitVec.BVConcat ->
     text "@"
  | BitVec.BVShl _ ->
     text "<<"
  | BitVec.BVShr _ ->
     text ">>"
  | BitVec.BVAnd ->
     text "&"
  | BitVec.BVOr ->
     text "|"
  | BitVec.BVXor ->
     text "^"

let format_uop uop =
  match uop with
  | BitVec.BVNeg ->
     text "~"
  | BitVec.BVCast(i) ->
     text "(" ++
     text "bits" ++
     text "<" ++
     (Int.to_string i |> text) ++
     text ">" ++
     text ")"
  | BitVec.BVSlice(hi,lo) ->
     text "[" ++
     (Int.to_string hi |> text) ++
     text ":" ++
     (Int.to_string hi |> text) ++
     text "]"

let rec format_bitvec bv = match bv with
  | BitVec.BitVec (n, Some w) ->
     (Int.to_string w |> text) ++
     text "w" ++
     (Int.to_string n |> text)
  | BitVec.BitVec (n, None) ->
     (Int.to_string n |> text)
  | BitVec.Int (n, Some w) ->
     (Int.to_string w |> text) ++
     text "w" ++
     (Bigint.to_string n |> text)
  | BitVec.Int (n, None) ->
     (Bigint.to_string n |> text)
  | BitVec.BVVar(x,n) ->
     text x ++
     text "_" ++
     (Int.to_string n |> text)
  | BitVec.BinOp (bop, u, v) ->
     box (text "(" ++
          format_bitvec u ++
          space ++
          format_bop bop ++  
          space ++
          format_bitvec v ++
          text ")")
  | BitVec.UnOp(uop, u) ->
     box (text "(" ++
          format_uop uop ++  
          space ++
          format_bitvec u ++
          text ")")

let format_lbop lbop =
  match lbop with
  | Form.LOr ->
     text "||"
  | Form.LAnd ->
     text "&&"
  | Form.LImp ->
     text "=>"
  | Form.LIff ->
     text "<=>"

let format_lcomp lcomp =
  match lcomp with
  | Form.LEq ->
     text "="
  | Form.LLe _ ->
     text "<="
  | Form.LLt _ ->
     text "<"
  | Form.LGe _ ->
     text ">="
  | Form.LGt _ ->
     text ">"
  | Form.LNeq ->
     text "!="

let rec format_form form =
  match form with
  | Form.LBool (b) ->
    Bool.to_string b |> text
  | Form.LBop(lbop, p, q) ->
     box (text "(" ++
          format_form p ++
          space ++
          format_lbop lbop ++
          space ++
          format_form q)
  | Form.LNot(p) ->
     box (text "!" ++
          format_form p)
  | Form.LVar(x) ->
     text x
  | Form.LComp(lcomp, u, v) ->
     box (text "(" ++
          format_bitvec u ++
          space ++
          format_lcomp lcomp ++  
          space ++
          format_bitvec v ++
          text ")")

let rec format_gcl (gcl:Poulet4.ToGCL.target) =
  match gcl with
  | GCL.GSkip ->
     text "skip"
  | GCL.GAssign(typ,lhs, rhs) ->
     box(text lhs ++
         space ++
         text ":=" ++
         space ++
         format_bitvec rhs) 
  | GCL.GSeq(g1,g2) ->
     box(format_gcl g1 ++
         text ";" ++
         text "\n" ++
         format_gcl g2)
  | GCL.GChoice(g1,g2) ->
     box(text "(" ++
         space ++
         space ++
         space ++
         format_gcl g1 ++
         text "\n" ++
         text "[]" ++
         space ++  
         format_gcl g2 ++
         text ")")
  | GCL.GAssume(p) ->
     box(text "assume" ++
         space ++
         format_form p)
  | GCL.GAssert(p) ->
     box(text "assert" ++
         space ++
         format_form p)
  | GCL.GExternVoid(f,args) ->
     box(text f ++
         text "(" ++
         (Pretty.format_list_sep
            (fun arg -> text "<yo>")
            "~" args) ++
         text ")")
  | GCL.GExternAssn(x,f,args) ->
     box(text x ++
         space ++
         text ":=" ++ 
         space ++
         text f ++
         text "(" ++
         (Pretty.format_list_sep
            (fun arg -> text "<yo>")
            "~" args) ++
         text ")")
  | GCL.GTable(t,keys,acts) ->
     box (text "<table" ++ space ++ text t ++ text ">")

let pp_to_string pp = Format.asprintf "%a" Pp.to_fmt pp
    
let to_string gcl =
  let (prsr,pipe) = gcl in
  pp_to_string (format_gcl prsr) ^
  "----------\n" ^
  pp_to_string (format_gcl pipe)
                 
