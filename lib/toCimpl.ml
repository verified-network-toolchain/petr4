open Core
open Poulet4
open GCL
open Cimpl
open Form

let compile_lhs (l:string) : Cimpl.cvar =
  l

let compile_rhs (r:BitVec.t) : Cimpl.cexpr =
  match r with
  | BitVec(n,w) ->
     CEInt n
  | _ -> 
     failwith "unimplemented"

(*takes in a formula and returns a cexpr*)
let rec compile_form (f : Form.t) : cexpr = 
   match f with 
   | LBool b -> 
      (* since C doesnt have booleans so we are using Int 1 and 0 for it*)
      begin 
         match b with 
         | true -> CEInt 1 
         | false -> CEInt 0
      end 
   | LBop ( lbop, t1 , t2 ) -> 
      let c1 = compile_form t1 in
      let c2 = compile_form t2 in 
      begin 
         match lbop with 
         | LOr -> CECompExpr (CBOr, c1, c2)
         | LAnd -> CECompExpr (CBAnd, c1, c2)
         | LImp -> failwith "unimplemented"
         | LIff -> failwith "unimplemented"
      end 
   | LNot t -> failwith "unimplemented"
   | LVar cvar -> failwith "unimplemented"
   | LComp (lcomp, t1, t2) -> failwith "unimplemented"

let compile_typ t : Cimpl.ctyp =
  failwith "unimplemented"

(* checks if two formulaes are equal*)
let form_eq phi1 phi2 = true 
     
let rec compile_gcl g : Cimpl.cstmt list =
  let dummy = [] in
  match g with
  | GCL.GSkip ->
     []
  | GCL.GAssign(typ,lhs,rhs) ->
     let cvar = compile_lhs lhs in
     let cexpr = compile_rhs rhs in
     [CSAssign(cvar,cexpr)]
  | GCL.GSeq(g1,g2) -> 
         (* something like x := 5 *)
         let c1 = compile_gcl g1 in
         let c2 = compile_gcl g2 in
         c1 @ c2
         (*GCL.GChoice(GSeq(GAssume phi1, g1), GSeq(GAssume(LNot(phi2), g2)) when form_eq phi1 phi2*)
  | GCL.GChoice(GSeq(GAssume phi1, g1), GSeq(GAssume(Form.LNot(phi2)), g2)) when form_eq phi1 phi2 ->
      let c1 = compile_gcl g1 in
      let c2 = compile_gcl g2 in
      let b = compile_form phi1 in 
      [CSIf (b, c1, c2)]
  | GCL.GChoice (_,_) -> failwith "unsupported choice"
  | GCL.GAssume(phi) -> 
   (*GAssume is basically precondition boolean expression*)
   let c = compile_form phi  in [CSIf (c, [CSSkip], [CSSkip])]
  | GCL.GAssert(phi) ->
   let c = compile_form phi  in [CSIf (c, [CSSkip], [CSSkip])]
   (*handling GAssume and GAssert in the same way -> 
         assume is precondition and assert is postcondition*)
  | GCL.GExternVoid(e,args) ->
     dummy
  | GCL.GExternAssn(x,e,args) ->
     dummy
  | GCL.GTable(tbl,keys,actions) ->
     dummy

let compile_program (prsr,pipe) =
  let stmts = compile_gcl pipe in
  let cdecl = Cimpl.(CDFunction(CTInt, "main", CKBlock stmts))in
  Ok (Cimpl.CProgram [cdecl])
