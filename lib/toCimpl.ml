open Core
open Poulet4
open GCL
   
let compile_program (prsr,pipe) =
  let dummy = [] in
  (* TODO: not tail recursive *)
  let rec compile g = 
    match g with
    | GCL.GSkip ->
       [Cimpl.CSkip]
    | GCL.GAssign(typ,lhs,rhs) ->
       dummy
    | GCL.GSeq(g1,g2) ->
       let c2 = compile g2 in
       let c1 = compile g1 in
       c1 @ c2
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
  let cdecl = CFunction(CInt, "main", CBlock stmts) in
  Ok (CProgram [cdecl])
