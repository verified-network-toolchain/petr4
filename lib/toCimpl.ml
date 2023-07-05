open Core
open Poulet4
open GCL
   
let compile_program (prsr,pipe) =
  let dummy = [] in
  let rec compile g = 
    match pipe with
    | GCL.GSkip -> []
    | GCL.GAssign(typ,lhs,rhs) -> dummy
    | GCL.GSeq(g1,g2) ->
       compile g1 @
       compile g2
    | GCL.GChoice(g1,g2) -> dummy
    | GCL.GAssume(phi) -> dummy
    | GCL.GAssert(phi) -> dummy
    | GCL.GExternVoid(e,args) -> dummy
    | GCL.GExternAssn(x,e,args) -> dummy
    | GCL.GTable(tbl,keys,actions) -> dummy in
  Ok (compile pipe)
