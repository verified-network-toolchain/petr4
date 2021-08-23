Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import String.
Require Import Poulet4.P4cub.Syntax.Equality.
Open Scope string_scope.
Open Scope list_scope.
Module P := P4cub.
Module F := P.F.
Module E := P.Expr.
Module ST := P.Stmt.
Module PA := P.Parser.
Module CT := P.Control.
Module TD := P.TopDecl.
Notation t := (E.t).
Notation ct := (E.ct).
Notation e := (E.e nat).
Notation s := (ST.s nat).
Notation par_e := (PA.e nat).
Notation par_st_blk := (PA.state_block nat).
Notation ct_table := (CT.ControlDecl.table nat).
Notation ct_d := (CT.ControlDecl.d nat).
Notation tpdecl := (TD.d nat).

Import P4cub.P4cubNotations.

Require Import Coq.PArith.BinPosDef.
Definition metadata : t := {{struct {[("meta", {{Bool}})]} }}.
Definition hdrs : t := 
  {{struct {[("hd", {{Bool}})]} }}.
Definition pkt_in := E.CTExtern "packet_in".
Definition pkt_out := E.CTExtern "packet_out".
Definition std_meta := {{struct {[("stdmeta", {{Bool}})]} }}.


Definition parser_start_state : par_st_blk :=
   &{state { -{skip @ 0}- } transition p{ goto ={ accept }= @ 0 }p}&.
Definition parsr_cparams : E.constructor_params := [("packet", pkt_in)].
Definition parsr_params : E.params := [("hdr", P.PAOut hdrs); ("meta", P.PAInOut metadata); ("standard_meta", P.PAInOut std_meta)].
Definition myparser : tpdecl := 
  %{parser "MyParser" ( parsr_cparams ) ( parsr_params ) start := parser_start_state { [("start",parser_start_state)] } @ 0 }%.

Definition gress_cparams : E.constructor_params := [].
Definition gress_params : E.params := [("hdr", P.PAInOut hdrs); ("meta", P.PAInOut metadata); ("standard_meta", P.PAInOut std_meta)].
Definition ingress_decl : ct_d := 
  c{action "test_ingress" ([]) { -{skip @ 0}- } @ 0}c.
Definition ingress : tpdecl := 
  %{control "MyIngress" ( gress_cparams ) ( gress_params ) apply { -{skip @ 0}- } where { ingress_decl } @ 0}%.

Definition egress_decl : ct_d := 
  c{action "test_egress" ([]) { -{skip @ 0}- } @ 0}c.
Definition egress : tpdecl := 
  %{control "MyEgress" ( gress_cparams ) ( gress_params ) apply { -{skip @ 0}- } where { egress_decl } @ 0}%.

Definition deparser_cparams : E.constructor_params := [("packet",pkt_out)].
Definition deparser_params : E.params := [("hdr", P.PAIn hdrs)].
Definition mydeparser_decl : ct_d :=
  c{action "test_deparser" ( deparser_params ) { -{skip @ 0}- } @ 0}c.

Definition mydeparser : tpdecl := 
  %{control "MyDeparser" ( deparser_cparams ) ( deparser_params ) apply { -{skip @ 0}- } where { mydeparser_decl } @ 0}%.


Definition checksum_cparams : E.constructor_params := [].
Definition checksum_params : E.params := [("hdr", P.PAInOut hdrs); ("meta", P.PAInOut metadata)].
Definition verify_decl : ct_d := 
  c{action "test_verifyChecksum" ([]) { -{skip @ 0}- } @ 0}c.
Definition verify : tpdecl := 
  %{control "MyVerifyChecksum" ( checksum_cparams ) ( checksum_params ) apply { -{skip @ 0}- } where { verify_decl } @ 0}%.
Definition compute_decl : ct_d := 
  c{action "test_computeChecksum" ([]) { -{skip @ 0}- } @ 0}c.
Definition compute : tpdecl := 
  %{control "MyComputeChecksum" ( checksum_cparams ) ( checksum_params ) apply { -{skip @ 0}- } where { compute_decl } @ 0}%.


Definition instance_args : E.constructor_args nat := [("p",E.CAName "MyParser");("vr",E.CAName "MyVerifyChecksum");("ig",E.CAName "MyIngress");("eg",E.CAName "MyEgress");("ck",E.CAName "MyComputeChecksum");("dep",E.CAName "MyDeparser")].
Definition instance : tpdecl :=
  %{Instance "main" of "V1Switch" ( instance_args ) @ 0}%.

Definition helloworld_program : tpdecl := 
  %{ myparser ;%; (%{ verify ;%; (%{ ingress ;%; (%{ egress ;%; (%{ compute ;%; (%{mydeparser ;%; instance @ 0}%) @ 0}%) @ 0}%) @ 0}%) @ 0}%) @ 0}%.




