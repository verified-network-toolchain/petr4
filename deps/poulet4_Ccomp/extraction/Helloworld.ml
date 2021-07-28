open AST0
open BinNums
open Datatypes
open EquivDec
open EquivUtil

module P = P4cub
module Coq__1 = P

module E = P.Expr

module PA = P.Parser

module CT = P.Control

module TD = P.TopDecl

(** val metadata : E.t **)

let metadata =
  P4cub.Expr.TStruct []

(** val hdrs : E.t **)

let hdrs =
  P4cub.Expr.TStruct []

(** val parser_start_state : nat PA.state_block **)

let parser_start_state =
  P4cub.Parser.State ((P4cub.Stmt.SSkip O), (P4cub.Parser.PGoto
    (P4cub.Parser.STAccept, O)))

(** val parsr_cparams : E.constructor_params **)

let parsr_cparams =
  []

(** val parsr_params : E.params **)

let parsr_params =
  (('h'::('d'::('r'::[]))), (P.PAOut
    hdrs)) :: ((('m'::('e'::('t'::('a'::[])))), (P.PAInOut metadata)) :: [])

(** val myparser : nat TD.d **)

let myparser =
  P4cub.TopDecl.TPParser
    (('M'::('y'::('P'::('a'::('r'::('s'::('e'::('r'::[])))))))),
    parsr_cparams, parsr_params, parser_start_state,
    ((('s'::('t'::('a'::('r'::('t'::[]))))), parser_start_state) :: []), O)

(** val control_cparams : E.constructor_params **)

let control_cparams =
  []

(** val control_params : E.params **)

let control_params =
  (('h'::('d'::('r'::[]))), (P.PAInOut
    hdrs)) :: ((('m'::('e'::('t'::('a'::[])))), (P.PAInOut
    metadata)) :: ((('p'::('r'::('o'::('c'::('e'::('s'::('s'::[]))))))),
    (P.PAInOut P4cub.Expr.TBool)) :: []))

(** val mycontrol_decl : nat CT.ControlDecl.d **)

let mycontrol_decl =
  P4cub.Control.ControlDecl.CDAction
    (('t'::('e'::('s'::('t'::('_'::('c'::('o'::('n'::('t'::('r'::('o'::('l'::[])))))))))))),
    control_params, (P4cub.Stmt.SSkip O), O)

(** val mycontrol : nat TD.d **)

let mycontrol =
  P4cub.TopDecl.TPControl
    (('M'::('y'::('C'::('o'::('n'::('t'::('r'::('o'::('l'::[]))))))))),
    control_cparams, control_params, mycontrol_decl, (P4cub.Stmt.SSkip O), O)

(** val deparser_cparams : E.constructor_params **)

let deparser_cparams =
  []

(** val deparser_params : E.params **)

let deparser_params =
  (('h'::('d'::('r'::[]))), (P.PAIn
    hdrs)) :: ((('m'::('e'::('t'::('a'::[])))), (P.PAIn
    metadata)) :: ((('p'::('r'::('o'::('c'::('e'::('s'::('s'::[]))))))),
    (P.PAIn P4cub.Expr.TBool)) :: []))

(** val mydeparser_decl : nat CT.ControlDecl.d **)

let mydeparser_decl =
  P4cub.Control.ControlDecl.CDAction
    (('t'::('e'::('s'::('t'::('_'::('d'::('e'::('p'::('a'::('r'::('s'::('e'::('r'::[]))))))))))))),
    deparser_params, (P4cub.Stmt.SSkip O), O)

(** val mydeparser : nat TD.d **)

let mydeparser =
  P4cub.TopDecl.TPControl
    (('M'::('y'::('D'::('e'::('p'::('a'::('r'::('s'::('e'::('r'::[])))))))))),
    deparser_cparams, deparser_params, mydeparser_decl, (P4cub.Stmt.SSkip O),
    O)

(** val helloworld_program : nat TD.d **)

let helloworld_program =
  P4cub.TopDecl.TPSeq (myparser, (P4cub.TopDecl.TPSeq (mycontrol, mydeparser,
    O)), O)
