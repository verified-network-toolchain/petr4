Require Import Poulet4.P4cub.Syntax.Syntax
        String Poulet4.P4cub.Syntax.CubNotations.
Open Scope string_scope.
Open Scope list_scope.
Notation t := (Expr.t).
Notation it := (TopDecl.it).
Notation e := (Expr.e).
Notation s := (Stmt.s).
Notation par_e := (Parser.e).
Notation ct_d := (Control.d).
Notation tpdecl := (TopDecl.d).

Import AllCubNotations.

Require Import Coq.PArith.BinPosDef.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Definition metadata : t := 
  Expr.TStruct [(*meta:*) Expr.TInt $ Pos.of_nat 32] false.
Definition hdrs : t := Expr.TStruct [(*hd:*) Expr.TBool] false.
Definition pkt_in := TopDecl.ExternInstType "packet_in".
Definition pkt_out := TopDecl.ExternInstType "packet_out".
Definition std_meta := Expr.TStruct [(*stdmeta:*) Expr.TBool] false.
Definition oneplusone := 
  let width := N.of_nat 32 in  
  let one := Z.of_nat 1 in
  Expr.Bop (Expr.TBit width) `+%bop (width `W one)%expr (width `W one)%expr.
Definition parser_start_state : s :=
  Stmt.Transition (Parser.Goto Parser.Accept).
Definition parsr_cparams : TopDecl.constructor_params := [].
Definition parsr_params : Expr.params :=
  [ (*hdr:*) PAOut hdrs
    ; (*meta:*) PAInOut metadata
    ; (*standard_meta:*) PAInOut std_meta].
Definition myparser : tpdecl :=
  TopDecl.Parser
    "MyParser"
    parsr_cparams
    [(*b:*) "packet_in"] parsr_params
    parser_start_state [].
Definition instance_myparser : tpdecl :=
  TopDecl.Instantiate "MyParser" [] [].

Definition gress_cparams : TopDecl.constructor_params := [].
Definition gress_params : Expr.params :=
  [ (*hdr*) PAInOut hdrs
    ; (*meta*) PAInOut metadata
    ; (*standard_meta*) PAInOut std_meta].
Definition ingress_decl : ct_d := 
  Control.Action "test_ingress" [] [] Stmt.Skip.
Definition ingress : tpdecl :=
  TopDecl.Control
    "MyIngress" gress_cparams [] gress_params
    [ingress_decl] Stmt.Skip.
Definition instance_myingress : tpdecl :=
  TopDecl.Instantiate "MyIngress" [] [].

Definition egress_decl : ct_d := 
  Control.Action "test_egress" [] [] Stmt.Skip.
Definition egress : tpdecl := 
  TopDecl.Control
    "MyEgress" gress_cparams [] gress_params
    [egress_decl] Stmt.Skip.
Definition instance_myegress : tpdecl :=
  TopDecl.Instantiate "MyEgress" [] [].

Definition deparser_cparams : TopDecl.constructor_params := [].
Definition deparser_params : Expr.params := [ (*hdr:*) PAIn hdrs].
Definition mydeparser_decl : ct_d :=
  Control.Action
    "test_deparser" [] [] (Stmt.Var (inr oneplusone) Stmt.Skip).

Definition mydeparser : tpdecl := 
  TopDecl.Control
    "MyDeparser"
    deparser_cparams
    [(*b:*) "packet_out"] deparser_params
    [mydeparser_decl] Stmt.Skip.
Definition instance_mydeparser : tpdecl :=
  TopDecl.Instantiate "MyDeparser" [] [].

Definition checksum_cparams : TopDecl.constructor_params := [].
Definition checksum_params : Expr.params :=
  [(*hdr:*) PAInOut hdrs; (*meta*) PAInOut metadata].
Definition verify_decl : ct_d :=
  Control.Action "test_verifyChecksum" [] [] Stmt.Skip.
Definition verify : tpdecl :=
  TopDecl.Control
    "MyVerifyChecksum"
    checksum_cparams [] checksum_params
    [verify_decl] Stmt.Skip.
Definition instance_myverify : tpdecl :=
  TopDecl.Instantiate "MyVerifyChecksum" [] [].

Definition compute_decl : ct_d :=
  Control.Action "test_computeChecksum" [] [] Stmt.Skip.
Definition compute : tpdecl :=
  TopDecl.Control
      "MyComputeChecksum"
      checksum_cparams [] checksum_params
      [compute_decl] Stmt.Skip.
Definition instance_mycompute : tpdecl :=
  TopDecl.Instantiate "MyComputeChecksum" [] [].

Definition instance_args : TopDecl.constructor_args :=
  [ (*p:=*) TopDecl.CAName 5 (*my_parser*)
    ; (*vr:=*) TopDecl.CAName 1 (*my_verify*)
    ; (*ig:=*) TopDecl.CAName 4 (*my_ingress*)
    ; (*eg:=*) TopDecl.CAName 3 (*my_egress*)
    ; (*ck:=*) TopDecl.CAName 0 (*my_compute*)
    ; (*dep:=*) TopDecl.CAName 2 (*my_deparser*) ].
Definition instance : tpdecl :=
  TopDecl.Instantiate "V1Switch" [] instance_args.

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
