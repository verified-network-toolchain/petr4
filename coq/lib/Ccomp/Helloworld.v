Require Import Poulet4.P4cub.Syntax.Syntax
        String Poulet4.P4cub.Syntax.CubNotations.
Open Scope string_scope.
Open Scope list_scope.
Notation t := (Typ.t).
Notation it := (InstTyp.t).
Notation e := (Exp.t).
Notation s := (Stm.t).
Notation par_e := (Trns.t).
Notation ct_d := (Ctrl.t).
Notation tpdecl := (Top.t).

Require Import Coq.PArith.BinPosDef.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Definition metadata : t := 
  Typ.Struct false [(*meta:*) Typ.Int $ Pos.of_nat 32].
Definition hdrs : t := Typ.Struct false [(*hd:*) Typ.Bool].
Definition pkt_in := InstTyp.Extern "packet_in".
Definition pkt_out := InstTyp.Extern "packet_out".
Definition std_meta := Typ.Struct false [(*stdmeta:*) Typ.Bool].
Definition oneplusone := 
  let width := N.of_nat 32 in  
  let one := Z.of_nat 1 in
  Exp.Bop (Typ.Bit width) `+%bin (width `W one)%exp (width `W one)%exp.
Definition parser_start_state : s :=
  Stm.Trans (Trns.Direct Lbl.Accept).
Definition parsr_cparams : Top.constructor_params := [].
Definition parsr_params : Typ.params :=
  [ ("hdr",PAOut hdrs)
    ; ("meta",PAInOut metadata)
    ; ("standard_meta",PAInOut std_meta)].
Definition myparser : tpdecl :=
  Top.Parser
    "MyParser"
    parsr_cparams []
    [("b","packet_in")] parsr_params
    parser_start_state [].
Definition instance_myparser : tpdecl :=
  Top.Instantiate "MyParser" "my_parser" [] [] [].

Definition gress_cparams : Top.constructor_params := [].
Definition gress_params : Typ.params :=
  [ ("hdr",PAInOut hdrs)
    ; ("meta",PAInOut metadata)
    ; ("standard_meta",PAInOut std_meta)].
Definition ingress_decl : ct_d := 
  Ctrl.Action "test_ingress" [] [] Stm.Skip.
Definition ingress : tpdecl :=
  Top.Control
    "MyIngress" gress_cparams [] [] gress_params
    [ingress_decl] Stm.Skip.
Definition instance_myingress : tpdecl :=
  Top.Instantiate "MyIngress" "my_ingress" [] [] [].

Definition egress_decl : ct_d := 
  Ctrl.Action "test_egress" [] [] Stm.Skip.
Definition egress : tpdecl := 
  Top.Control
    "MyEgress" gress_cparams [] [] gress_params
    [egress_decl] Stm.Skip.
Definition instance_myegress : tpdecl :=
  Top.Instantiate "MyEgress" "my_egress" [] [] [].

Definition deparser_cparams : Top.constructor_params := [].
Definition deparser_params : Typ.params := [ ("hdr",PAIn hdrs)].
Definition mydeparser_decl : ct_d :=
  Ctrl.Action
    "test_deparser" [] [] (`let "x" := inr oneplusone `in Stm.Skip)%stm.

Definition mydeparser : tpdecl := 
  Top.Control
    "MyDeparser"
    deparser_cparams []
    [("b","packet_out")] deparser_params
    [mydeparser_decl] Stm.Skip.
Definition instance_mydeparser : tpdecl :=
  Top.Instantiate "MyDeparser" "my_deparser" [] [] [].

Definition checksum_cparams : Top.constructor_params := [].
Definition checksum_params : Typ.params :=
  [("hdr",PAInOut hdrs); ("meta",PAInOut metadata)].
Definition verify_decl : ct_d :=
  Ctrl.Action "test_verifyChecksum" [] [] Stm.Skip.
Definition verify : tpdecl :=
  Top.Control
    "MyVerifyChecksum"
    checksum_cparams [] [] checksum_params
    [verify_decl] Stm.Skip.
Definition instance_myverify : tpdecl :=
  Top.Instantiate "MyVerifyChecksum" "my_verify" [] [] [].

Definition compute_decl : ct_d :=
  Ctrl.Action "test_computeChecksum" [] [] Stm.Skip.
Definition compute : tpdecl :=
  Top.Control
      "MyComputeChecksum"
      checksum_cparams [] [] checksum_params
      [compute_decl] Stm.Skip.
Definition instance_mycompute : tpdecl :=
  Top.Instantiate "MyComputeChecksum" "my_compute" [] [] [].

Definition instance_args : Top.constructor_args :=
  [ (*p:=*) "my_parser";
    (*vr:=*) "my_verify";
    (*ig:=*) "my_ingress";
    (*eg:=*) "my_egress";
    (*ck:=*) "my_compute";
    (*dep:=*) "my_deparser" ].
Definition instance : tpdecl :=
  Top.Instantiate "V1Switch" "main" [] instance_args [].

Definition instances : list tpdecl := 
  [ instance_myparser
    ; instance_myingress
    ; instance_myegress
    ; instance_mydeparser
    ; instance_myverify
    ; instance_mycompute
    ; instance ].

Definition helloworld_program : list tpdecl := 
  [ myparser
    ; verify
    ; ingress
    ; egress
    ; compute
    ; mydeparser ] ++ instances.
