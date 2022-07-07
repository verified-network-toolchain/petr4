(* This file should provide the main function of a v1model
The current implementation is only a subset of v1model
Meaning it doesn't provide features such as register or hashing. *)
From compcert Require Import Clight Ctypes Integers Cop Clightdefs.
Require Import Poulet4.Ccomp.CCompEnv.
Require Import Poulet4.Ccomp.Petr4Runtime.
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import String.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.
Section v1model.
Open Scope string_scope.
Context (bit_vec: type).
Definition packet_in := 
    (Tstruct $"packet_in" noattr).
Definition packet_out :=
    (Tstruct $"packet_out" noattr).
Definition ptr_pkt_in := Tpointer packet_in noattr.
Definition ptr_pkt_out := Tpointer packet_out noattr.
Definition empty_main := 
  Clight.mkfunction Ctypes.Tvoid 
  (AST.mkcallconv None true true)
  [] [] [] Sskip.
(* 
Definition typelist_extract_bool := Ctypes.Tcons ptr_pkt_in
(Ctypes.Tcons (Tpointer type_bool noattr) Ctypes.Tnil).
Definition typelist_extract_bitvec := Ctypes.Tcons ptr_pkt_in 
(Ctypes.Tcons TpointerBitVec 
(Ctypes.Tcons TpointerBitVec
(Ctypes.Tcons TpointerBitVec Ctypes.Tnil))). *)
(* Definition extract := Evar $"extract" (Tfunction typelist_bop_bool tvoid cc_default). *)

(** The order is 
    Parser -> VerifyChecksum -> Ingress -> Egress -> ComputeChecksum -> Deparser *)
Definition main_fn (env: ClightEnv) (cargs: TopDecl.constructor_args): Clight.function
:= 
(* TODO: this is sketchy because I'm not sure how many instantiations will there be
   and I'm not sure if the name works as I thought they would*)
match cargs (*p, vr, ig, eg, ck , dep*) with
| [ TopDecl.CAName p; TopDecl.CAName vr; TopDecl.CAName ig;
    TopDecl.CAName eg; TopDecl.CAName ck; TopDecl.CAName dep] =>
    match
      env.(expected_instances)
      lookup_function env p,
      lookup_function env vr,
      lookup_function env ig,
      lookup_function env eg,
      lookup_function env ck,
      lookup_function env dep with
    | inl (pf,pid),
      inl (vrf,vrid),
      inl (igf,igid),
      inl (egf,egid),
      inl (ckf,ckid),
      inl (depf,depid) =>
        match pf.(fn_params) with
        | [_; Tpointer Ht _; Tpointer Mt _; Tpointer STDt _; _] => 
            let '(Hname, Mname, STDname, PKT_INname, PKT_OUTname)
              := ("_V1Header",
                   "_V1Metadata",
                   "_V1StandardMeta",
                   "_V1PacketIn",
                   "_V1PacketOut") in
        let envH := add_var  env Hname Ht in 
        let envM := add_var  envH Mname Mt in
        let envSTD := add_var  envM STDname STDt in
        let envPKTIn := add_var  envSTD PKT_INname packet_in in 
        let envPKTOut := add_var  envPKTIn PKT_OUTname packet_out in 
        match
          find_ident envPKTOut Hname,
          find_ident envPKTOut Mname,
          find_ident envPKTOut STDname,
          find_ident  envPKTOut PKT_INname,
          find_ident  envPKTOut PKT_OUTname with
        | inl Hid,inl Mid,inl STDid,inl PKTINid,inl PKTOutid => 
            let '(H,M,STD,PKT_IN,PKT_OUT) :=
              (Evar Hid Ht,Evar Mid Mt,
                Evar STDid STDt,Evar PKTINid packet_in,
                Evar PKTOutid packet_out) in
            let '(Href,Mref,STDref,PKT_Inref,PKT_OUTref) :=
              (Eaddrof H (Tpointer Ht noattr),
                Eaddrof M (Tpointer Mt noattr),
                Eaddrof STD (Tpointer STDt noattr),
                Eaddrof PKT_IN (Tpointer packet_in noattr),
                Eaddrof PKT_OUT (Tpointer packet_out noattr)) in
          (*declared all the variables*)
            let ParserCall :=
              Scall
                None
                (Evar pid (Clight.type_of_function pf))
                [PKT_IN;Href;Mref;STDref] in
            let VerifyChecksumCall :=
              Scall
                None
                (Evar vrid (Clight.type_of_function vrf))
                [Href;Mref] in
            let IngressCall :=
              Scall
                None
                (Evar igid (Clight.type_of_function igf))
                [Href;Mref;STDref] in
            let EgressCall :=
              Scall
                None
                (Evar egid (Clight.type_of_function egf))
                [Href;Mref;STDref] in
            let ComputeChecksumCall :=
              Scall
                None
                (Evar ckid (Clight.type_of_function ckf))
                [Href;Mref] in
            let DeparserCall :=
              Scall
                None
                (Evar depid (Clight.type_of_function depf))
                [PKT_OUT; H] in
            let body :=
              Ssequence
                ParserCall
                (Ssequence
                   VerifyChecksumCall
                   (Ssequence
                      IngressCall
                      (Ssequence
                         EgressCall
                         (Ssequence ComputeChecksumCall DeparserCall)))) in
            Clight.mkfunction
              Ctypes.type_int32s 
              (AST.mkcallconv None true true)
              [] (get_vars  envPKTOut) (get_temps  envPKTOut) body
        | _,_,_,_,_ => empty_main
        end


      | _ => empty_main
      end

    | _,_,_,_,_,_ => empty_main
    end
| _ => empty_main
end .



End v1model.
