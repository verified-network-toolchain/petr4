open Core
open Poulet4
open GCL

let compile_lhs l : Cimpl.cvar =
  failwith "unimplemented"

let compile_rhs r : Cimpl.cexpr =
  failwith "unimplemented"

let compile_typ t : Cimpl.ctyp =
  failwith "unimplemented"
     
let rec compile_gcl g : Cimpl.cstmt list =
  let dummy = [] in
  match g with
  | GCL.GSkip ->
     [Cimpl.CSkip]
  | GCL.GAssign(typ,lhs,rhs) ->
     let _ = compile_typ typ in
     let cvar = compile_lhs lhs in
     let cexpr = compile_rhs rhs in
     [CAssign(cvar,cexpr)]
  | GCL.GSeq(g1,g2) ->
     let c1 = compile_gcl g1 in
     let c2 = compile_gcl g2 in
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
     dummy

let compile_program (prsr,pipe) =
  let stmts = compile_gcl pipe in
  let cdecl = Cimpl.(CFunction(CInt, "main", CBlock stmts))in
  Ok (Cimpl.CProgram [cdecl])
