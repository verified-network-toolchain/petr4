Require Import Syntax.
Require Import Eval.
Require Import Typed.
Require Import Strings.String.
Require String.
Require Import Coq.ZArith.BinIntDef.
Require Import Monads.State.

Require Import Step.
Require Import Unroll.

Open Scope string_scope.
Open Scope list_scope.

Require Import IntExampleWeakestPre.

(* 
  A simple loop example which iterates 5 times and then accepts

parser LoopExample (packet_in pkt, out int<2> output) {
  int iters;
  state start {
    iters = 5;
    transition loop;
  }
  state loop {
    iters = iters - 1;
    transition select(iters) {
      0 : accept;
      _ : loop;
    }
  }
}
*)

Definition tag_t := unit.
Definition tag := tt.
Definition int_typ : P4Type := TypInteger.


Definition iter_name : P4String tag_t := MkP4String tag_t tag "iters".
Definition iter_decl := DeclVariable tag_t tag int_typ iter_name None.

Definition scope : Env_EvalEnv := MkEnv_EvalEnv nil nil "dummy".

Definition pkt_param : P4Parameter := MkParameter true Directionless (TypExtern "packet_in") "pkt".
Definition pkt_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName "pkt")) (TypExtern "packet_in") Directionless.
Definition out_type : P4Type := TypInt 2.
Definition out_param : P4Parameter := MkParameter true Out out_type "output".
Definition locals : list (Declaration tag_t) := iter_decl :: nil.

Definition iter_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName "iters")) TypInteger Directionless.
Definition z_expr : Expression tag_t := MkExpression _ tt (ExpInt _ (MkP4Int _ tt 0 None)) TypInteger Directionless.
Definition one_expr : Expression tag_t := MkExpression _ tt (ExpInt _ (MkP4Int _ tt 1 None)) TypInteger Directionless.
Definition five_expr : Expression tag_t := MkExpression _ tt (ExpInt _ (MkP4Int _ tt 5 None)) TypInteger Directionless.
Definition minus_expr : Expression tag_t := MkExpression _ tt (ExpBinaryOp _ Minus (iter_expr, one_expr)) TypInteger Directionless.

Definition decrement : Statement tag_t := MkStatement _ tt (StatAssignment _ iter_expr minus_expr) StmUnit.
Definition initialize : Statement tag_t := MkStatement _ tt (StatAssignment _ iter_expr five_expr) StmUnit.

Definition start_body: list (Statement tag_t) := initialize :: nil.
Definition loop_body: list (Statement tag_t) := decrement :: nil.

Definition start_st : ParserState tag_t := MkParserState _ tt (MkP4String _ tt "start") start_body (ParserDirect _ tt (MkP4String _ tt "loop")).

Definition loop_transition : ParserTransition tag_t := 
  let loop_case := MkParserCase _ tt ((MkMatch _ tt (MatchExpression tag_t z_expr) TypInteger) :: nil) (MkP4String _ tt "loop") in
  let accept_case := MkParserCase _ tt ((MkMatch _ tt (MatchDontCare tag_t) TypInteger) :: nil) (MkP4String _ tt String.accept) in
    ParserSelect _ tt (iter_expr :: nil) (loop_case :: accept_case :: nil).

Definition loop_st : ParserState tag_t := MkParserState _ tt (MkP4String _ tt "loop") loop_body loop_transition.

Definition states : list (ParserState tag_t) := start_st :: loop_st :: nil.

Definition LoopParser : ValueObject tag_t := ValObjParser _ scope nil locals states.

(* Compute LoopParser. *)
(* Compute rename_loop tag_t tt LoopParser loop_st. *)
(* Compute unroll_loop tag_t tt LoopParser loop_st. *)

Definition unrolledLP := unroll_loop _ tt LoopParser loop_st.

Compute

(* 
  The loop example should unroll to the following:

parser LoopExample (packet_in pkt, out int<2> output) {
  int iters;
  state start {
    iters = 5;
    transition loop;
  }
  state loop {
    iters = iters - 1;
    transition select(iters) {
      0 : accept;
      _ : loop';
    }
  }
  state loop' {
    iters = iters - 1;
    transition select(iters) {
      0 : accept;
      _ : loop';
    }
  }
}
*)