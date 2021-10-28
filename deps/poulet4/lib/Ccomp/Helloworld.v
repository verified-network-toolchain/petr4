Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import String.
Require Import Poulet4.P4cub.Syntax.Equality
        Poulet4.P4cub.Syntax.CubNotations.
Open Scope string_scope.
Open Scope list_scope.
Notation t := (Expr.t).
Notation ct := (Expr.ct).
Notation e := (Expr.e nat).
Notation s := (Stmt.s nat).
Notation par_e := (Parser.e nat).
Notation par_st_blk := (Parser.state_block nat).
Notation ct_table := (Control.table nat).
Notation ct_d := (Control.d nat).
Notation tpdecl := (TopDecl.d nat).

Import AllCubNotations.

Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinIntDef.
Definition metadata : t := 
  let width := Pos.of_nat 32 in    
  {{struct {[("meta", {{int <width>}})]} }}.
Definition hdrs : t := 
  {{struct {[("hd", {{Bool}})]} }}.
Definition pkt_in := Expr.CTExtern "packet_in".
Definition pkt_out := Expr.CTExtern "packet_out".
Definition std_meta := {{struct {[("stdmeta", {{Bool}})]} }}.
Definition oneplusone := 
  let width := Pos.of_nat 32 in  
  let one := Z.of_nat 1 in
  -{init "x" := BOP width S one @ 0 + width S one @ 0 : bit<width> @ 0 @ 0}-.
Definition parser_start_state : par_st_blk :=
   &{state { skip @ 0 } transition goto accept @ 0 }&.
Definition parsr_cparams : Expr.constructor_params := [].
Definition parsr_params : Expr.params :=
  [("hdr", PAOut hdrs); ("meta", PAInOut metadata); ("standard_meta", PAInOut std_meta)].
Definition myparser : tpdecl := 
  %{parser "MyParser" ( parsr_cparams ) ([("b", "packet_in")]) ( parsr_params )
           start := parser_start_state { [("start",parser_start_state)] } @ 0 }%.
Definition instance_myparser : tpdecl := 
%{Instance "my_parser" of "MyParser" < [] > ( [] ) @ 0}%.

Definition gress_cparams : Expr.constructor_params := [].
Definition gress_params : Expr.params :=
  [("hdr", PAInOut hdrs); ("meta", PAInOut metadata); ("standard_meta", PAInOut std_meta)].
Definition ingress_decl : ct_d := 
  c{action "test_ingress" ([]) { skip @ 0 } @ 0}c.
Definition ingress : tpdecl := 
  %{control "MyIngress" ( gress_cparams ) ([]) ( gress_params )
            apply { skip @ 0 } where { ingress_decl } @ 0}%.
Definition instance_myingress : tpdecl := 
  %{Instance "my_ingress" of "MyIngress" < [] > ( [] ) @ 0}%.

Definition egress_decl : ct_d := 
  c{action "test_egress" ([]) { skip @ 0 } @ 0}c.
Definition egress : tpdecl := 
  %{control "MyEgress" ( gress_cparams ) ([]) ( gress_params )
            apply { skip @ 0 } where { egress_decl } @ 0}%.
Definition instance_myegress : tpdecl := 
  %{Instance "my_egress" of "MyEgress" < [] > ( [] ) @ 0}%.

Definition deparser_cparams : Expr.constructor_params := [].
Definition deparser_params : Expr.params := [ ("hdr", PAIn hdrs)].
Definition mydeparser_decl : ct_d :=
  c{action "test_deparser" ( [] ) {  oneplusone } @ 0}c.

Definition mydeparser : tpdecl := 
  %{control
      "MyDeparser"
      ( deparser_cparams )
      ([("b", "packet_out")]) ( deparser_params )
      apply { skip @ 0 } where { mydeparser_decl } @ 0}%.
Definition instance_mydeparser : tpdecl := 
  %{Instance "my_deparser" of "MyDeparser" < [] > ( [] ) @ 0}%.

Definition checksum_cparams : Expr.constructor_params := [].
Definition checksum_params : Expr.params := [("hdr", PAInOut hdrs); ("meta", PAInOut metadata)].
Definition verify_decl : ct_d := 
  c{action "test_verifyChecksum" ([]) { skip @ 0 } @ 0}c.
Definition verify : tpdecl := 
  %{control
      "MyVerifyChecksum"
      (checksum_cparams) ([]) (checksum_params)
      apply { skip @ 0 } where { verify_decl } @ 0}%.
Definition instance_myverify : tpdecl := 
  %{Instance "my_verify" of "MyVerifyChecksum" < [] > ( [] ) @ 0}%.

  Definition compute_decl : ct_d := 
    c{action "test_computeChecksum" ([]) { skip @ 0 } @ 0}c.
Definition compute : tpdecl := 
  %{control
      "MyComputeChecksum"
      (checksum_cparams) ([]) (checksum_params)
      apply { skip @ 0 } where { compute_decl } @ 0}%.
Definition instance_mycompute : tpdecl := 
  %{Instance "my_compute" of "MyComputeChecksum" < [] > ( [] ) @ 0}%.

Definition instance_args : Expr.constructor_args nat :=
  [("p",Expr.CAName "my_parser");("vr",Expr.CAName "my_verify");
  ("ig",Expr.CAName "my_ingress");("eg",Expr.CAName "my_egress");
  ("ck",Expr.CAName "my_compute");("dep",Expr.CAName "my_deparser")].
Definition instance : tpdecl :=
  %{Instance "main" of "V1Switch" < [] > ( instance_args ) @ 0}%.

Definition instances : tpdecl := 
  %{instance_myparser
      ;%; instance_myingress
      ;%; instance_myegress
      ;%; instance_mydeparser
      ;%; instance_myverify
      ;%; instance_mycompute
      ;%; instance @ 0 @ 0 @ 0 @ 0 @ 0 @ 0}%.

Definition helloworld_program : tpdecl := 
  %{ myparser
       ;%; verify
       ;%; ingress
       ;%; egress
       ;%; compute
       ;%; mydeparser
       ;%; instances @ 0 @ 0 @ 0 @ 0 @ 0 @ 0}%.
