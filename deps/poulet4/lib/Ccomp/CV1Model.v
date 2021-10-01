(* This file should provide the main function of a v1model
The current implementation is only a subset of v1model
Meaning it doesn't provide features such as register or hashing. *)
From compcert Require Import Clight Ctypes Integers Cop Clightdefs.
Require Import Poulet4.Ccomp.CCompEnv.
Require Import Poulet4.Ccomp.Petr4Runtime.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4sel.P4sel.
Require Import String.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.
Section v1model.
Open Scope string_scope.
Context (tags_t: Type).
Context (bit_vec: type).
Definition packet_in := 
    (Tstruct $"packet_in" noattr).
Definition packet_out :=
    (Tstruct $"packet_in" noattr).
Definition empty_main := 
  Clight.mkfunction Ctypes.Tvoid 
  (AST.mkcallconv None true true)
  [] [] [] Sskip.

(* The order is 
Parser -> VerifyChecksum -> Ingress -> Egress -> ComputeChecksum -> Deparser *)
Definition main_fn (env: ClightEnv tags_t ) (cargs: P4sel.Expr.constructor_args tags_t): Clight.function
:= 
(* this is sketchy because I'm not sure how many instantiations will there be
and I'm not sure if the name works as I thought they would*)
let p := Field.get "p" cargs in
let vr := Field.get "vr" cargs in
let ig := Field.get "ig" cargs in
let eg := Field.get "eg" cargs in
let ck := Field.get "ck" cargs in
let dep := Field.get "dep" cargs in
match p, vr, ig, eg, ck , dep with
| Some (P4sel.Expr.CAName p), 
  Some (P4sel.Expr.CAName vr), 
  Some (P4sel.Expr.CAName ig), 
  Some (P4sel.Expr.CAName eg), 
  Some (P4sel.Expr.CAName ck), 
  Some (P4sel.Expr.CAName dep) => 

  match lookup_function tags_t env p, lookup_function tags_t env vr, lookup_function tags_t env ig, lookup_function tags_t env eg, lookup_function tags_t env ck, lookup_function tags_t env dep with
    | Some(pf,pid), Some(vrf,vrid), Some(igf,igid), Some(egf,egid), Some(ckf,ckid), Some(depf,depid) =>
      match pf.(fn_params) with
      | (_,_)::(_, (Tpointer Ht _))::(_, Tpointer Mt _)::(_, Tpointer STDt _)::_ => 
        let '(Hname, Mname, STDname, PKT_INname, PKT_OUTname) := ("_V1Header", "_V1Metadata", "_V1StandardMeta", "_V1PacketIn", "_V1PacketOut") in
        let envH := add_var tags_t env Hname Ht in 
        let envM := add_var tags_t envH Mname Mt in
        let envSTD := add_var tags_t envM STDname STDt in
        let envPKTIn := add_var tags_t envSTD PKT_INname packet_in in 
        let envPKTOut := add_var tags_t envPKTIn PKT_OUTname packet_out in 
        match find_ident tags_t envPKTOut Hname,find_ident tags_t envPKTOut Mname,find_ident tags_t envPKTOut STDname,find_ident tags_t envPKTOut PKT_INname,find_ident tags_t envPKTOut PKT_OUTname with
        | Some Hid,Some Mid,Some STDid,Some PKTINid,Some PKTOutid => 
          let '(H,M,STD,PKT_IN,PKT_OUT) := (Evar Hid Ht,Evar Mid Mt,Evar STDid STDt,Evar PKTINid packet_in, Evar PKTOutid packet_out) in
          let '(Href,Mref,STDref,PKT_Inref,PKT_OUTref) := (Eaddrof H (Tpointer Ht noattr),Eaddrof M (Tpointer Mt noattr),Eaddrof STD (Tpointer STDt noattr),Eaddrof PKT_IN (Tpointer packet_in noattr),Eaddrof PKT_OUT (Tpointer packet_out noattr))in
          (*declared all the variables*)
          let ParserCall := Scall None (Evar pid (Clight.type_of_function pf)) [PKT_IN;Href;Mref;STDref] in
          let VerifyChecksumCall := Scall None (Evar vrid (Clight.type_of_function vrf)) [Href;Mref] in
          let IngressCall := Scall None (Evar igid (Clight.type_of_function igf)) [Href;Mref;STDref] in
          let EgressCall := Scall None (Evar egid (Clight.type_of_function egf)) [Href;Mref;STDref] in
          let ComputeChecksumCall := Scall None (Evar ckid (Clight.type_of_function ckf)) [Href;Mref] in
          let DeparserCall := Scall None (Evar depid (Clight.type_of_function depf)) [PKT_OUT; H] in
          let body:= Ssequence ParserCall (Ssequence VerifyChecksumCall (Ssequence IngressCall (Ssequence EgressCall (Ssequence ComputeChecksumCall DeparserCall)))) in
          Clight.mkfunction Ctypes.type_int32s 
          (AST.mkcallconv None true true)
          [] (get_vars tags_t envPKTOut) (get_temps tags_t envPKTOut) body

        | _,_,_,_,_ => empty_main
        end


      | _ => empty_main
      end

    | _,_,_,_,_,_ => empty_main
    end
| _, _, _, _, _, _ => empty_main
end .



End v1model.




