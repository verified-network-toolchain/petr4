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
Notation e := (E.e string).
Notation s := (ST.s string).
Notation par_e := (PA.e string).
Notation par_st_blk := (PA.state_block string).
Notation ct_table := (CT.ControlDecl.table string).
Notation ct_d := (CT.ControlDecl.d string).
Notation tpdecl := (TD.d string).

Import P4cub.P4cubNotations.
Definition metadata : t := {{struct {[]} }}.
Definition hdrs : t := {{struct {[]} }}.
Definition parser_start_state : par_st_blk :=
   &{state { -{skip @ ""}- } transition p{ goto ={ accept }= @ "" }p}&.
Definition parsr_cparams : E.constructor_params := [].
Definition parsr_params : E.params := [("hdr", P.PAOut hdrs); ("meta", P.PAInOut metadata)].
Definition myparser : tpdecl := 
  %{parser "MyParser" ( parsr_cparams ) ( parsr_params ) start := parser_start_state { [("start",parser_start_state)] } @ "" }%.

Definition control_cparams : E.constructor_params := [].
Definition control_params : E.params := [("hdr", P.PAInOut hdrs); ("meta", P.PAInOut metadata); ("process", P.PAInOut {{ Bool }})].
Definition mycontrol_decl : ct_d := 
  c{action "test_control" ( control_params ) { -{skip @ ""}- } @ ""}c.
Definition mycontrol : tpdecl := 
  %{control "MyControl" ( control_cparams ) ( control_params ) apply { -{skip @ ""}- } where { mycontrol_decl } @ ""}%.
  
Definition deparser_cparams : E.constructor_params := [].
Definition deparser_params : E.params := [("hdr", P.PAIn hdrs); ("meta", P.PAIn metadata); ("process", P.PAIn {{ Bool }})].
Definition mydeparser_decl : ct_d :=
  c{action "test_deparser" ( deparser_params ) { -{skip @ ""}- } @ ""}c.

Definition mydeparser : tpdecl := 
  %{control "MyDeparser" ( deparser_cparams ) ( deparser_params ) apply { -{skip @ ""}- } where { mydeparser_decl } @ ""}%.

Definition helloworld_program : tpdecl := 
  %{ myparser ;%; (%{ mycontrol ;%; mydeparser @ ""}%) @ ""}%.




