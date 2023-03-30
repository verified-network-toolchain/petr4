(* This file should provide the main function of a v1model
The current implementation is only a subset of v1model
Meaning it doesn't provide features such as register or hashing. *)
From compcert Require Import Clight Ctypes Integers Cop Clightdefs.
From Poulet4 Require Import Ccomp.CCompEnv Ccomp.Petr4Runtime
  P4cub.Syntax.Syntax Utils.Envn.
Require Import String.
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
Definition main_fn (env: ClightEnv)
  (cargs: Top.constructor_args) : Clight.function
:= 
(* TODO: this is sketchy because I'm not sure how many instantiations will there be
   and I'm not sure if the name works as I thought they would*)
match cargs (*p, vr, ig, eg, ck , dep*) with
| [p; vr; ig; eg; ck; dep] =>
    match
      lookup_function p env,
      lookup_function vr env,
      lookup_function ig env,
      lookup_function eg env,
      lookup_function ck env,
      lookup_function dep env with
    | Result.Ok (pid,pf),
      Result.Ok (vrid,vrf),
      Result.Ok (igid,igf),
      Result.Ok (egid,egf),
      Result.Ok (ckid,ckf),
      Result.Ok (depid,depf) =>
        (* TODO: make sure expression constructor params
           are included in clight functions for constructors *)
        match pf.(fn_params) with
        | [(PKTINid, _);
           (PKTOutid, _);
           (Hid, Tpointer Ht _);
           (Mid, Tpointer Mt _);
           (STDid, Tpointer STDt _)] =>
            let '(PKT_INname, PKT_OUTname) := ("_V1PacketIn", "_V1PacketOut") in
            (*let envSTD := add_var env STDt in
            let envM := add_var envSTD Mt in
            let envH := add_var envM Ht in
            let envPKTIn := add_instance_var PKT_INname packet_in envH in
            let envPKTOut := add_instance_var PKT_OUTname packet_out envPKTIn in
            match
              find_var 0 envPKTOut,
              find_var 1 envPKTOut,
              find_var 2 envPKTOut,
              Env.find PKT_INname envPKTOut.(instanceMap),
              Env.find PKT_OUTname envPKTOut.(instanceMap) with
              | Result.Ok _ Hid, Result.Ok _ Mid, Result.Ok _ STDid,
              Some PKTINid, Some PKTOutid => *)
            let env' :=
              {{ env with vars := (Hid, Ht) :: (Mid, Mt) :: (STDid, STDt) :: env.(vars)
               ; varMap := Hid :: Mid :: STDid :: env.(varMap) }} in
            let envPKTOut :=
              {{ env' with vars := (PKTOutid, packet_out) :: (PKTINid, packet_in) :: env'.(vars)
               ; instanceMap :=
                   Env.bind
                     PKT_OUTname PKTOutid
                     (Env.bind PKT_INname PKTINid env'.(instanceMap)) }} in
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
        (*| _,_,_,_,_ => empty_main
        end *)


      | _ => empty_main
      end

    | _,_,_,_,_,_ => empty_main
    end
| _ => empty_main
end .



End v1model.
