(* This file should provide the main function of a v1model
The current implementation is only a subset of v1model
Meaning it doesn't provide features such as register or hashing. *)
From compcert Require Import Clight Ctypes Integers Cop.
Require Import Poulet4.Ccomp.CCompEnv.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import String.
Section v1model.
Open Scope string_scope.
Context (tags_t: Type).
Definition empty_main := 
  Clight.mkfunction Ctypes.Tvoid 
  (AST.mkcallconv None true true)
  [] [] [] Sskip.
(* The order is 
Parser -> VerifyChecksum -> Ingress -> Egress -> ComputeChecksum -> Deparser *)
Definition main_fn (env: ClightEnv) (cargs: P4cub.Expr.constructor_args tags_t): Clight.function
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
| Some (P4cub.Expr.CAName p), 
  Some (P4cub.Expr.CAName vr), 
  Some (P4cub.Expr.CAName ig), 
  Some (P4cub.Expr.CAName eg), 
  Some (P4cub.Expr.CAName ck), 
  Some (P4cub.Expr.CAName dep) => 

  match lookup_function env p, lookup_function env vr, lookup_function env ig, lookup_function env eg, lookup_function env ck, lookup_function env dep with
  | Some(pf,pid), Some(vrf,vrid), Some(igf,igid), Some(egf,egid), Some(ckf,ckid), Some(depf,depid) =>
  match pf.(fn_params) with
  | (_,_)::(_, Ht)::(_, Mt)::_ => empty_main
  | _ => empty_main
  end

  | _,_,_,_,_,_ => empty_main
  end
| _, _, _, _, _, _ => empty_main
end .



End v1model.




