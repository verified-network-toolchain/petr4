open Core
open Poulet4
open GCL
   
let compile_program (prsr,pipe) =
  let dummy = [] in
  let compile g = 
    match pipe with
    | GCL.GSkip ->
       []
    | GCL.GAssign(typ,lhs,rhs) ->
       dummy
    | GCL.GSeq(g1,g2) ->
       dummy
    | GCL.GChoice(g1,g2) ->
       dummy
    | GCL.GAssume(phi) ->
       dummy
    | GCL.GAssert(phi) ->
       dummy
    | GCL.GExternVoid(e,args) ->
       dummy
    | GCL.GExternAssn(x,e,args) ->
       dummy
    | GCL.GTable(tbl,keys,actions) ->
       dummy in
  let open Cimpl in 
  let stmts = compile pipe in
  let cdecl = CFunction(CVoid, "main", CBlock stmts) in
  Ok (CProgram [cdecl])
