Require Import Syntax.
Require Import Eval.
Require Import Typed.
Require Import Strings.String.
Require Import Coq.ZArith.BinIntDef.
Require Import Monads.State.

Require Import Step.
Require Import Unroll.

Open Scope string_scope.
Open Scope list_scope.

Require Import IntExample.

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

Notation P4String := (P4String.t tag_t).
Notation P4Int := (P4Int.t tag_t).

Definition MkP4String (s: string) : P4String := {| P4String.tags := tag; P4String.str := s |}.
Definition MkP4Int (n: Z) (width: option (nat * bool)) : P4Int := {| P4Int.tags := tag; P4Int.value := n; P4Int.width_signed := width |}.

Definition tag_t := unit.
Definition tag := tt.
Definition int_typ : @P4Type tag_t := TypInteger.


Definition iter_name : P4String := MkP4String "iters".
Definition iter_decl := DeclVariable tag int_typ iter_name None.

Definition scope : Env_EvalEnv := MkEnv_EvalEnv nil nil (MkP4String "dummy").

Definition pkt_param : P4Parameter := MkParameter true Directionless (TypExtern (MkP4String "packet_in")) None (MkP4String "pkt").
Definition pkt_expr : @Expression tag_t := MkExpression tag (ExpName (BareName (MkP4String "pkt"))) (TypExtern (MkP4String "packet_in")) Directionless.
Definition out_type : @P4Type tag_t := TypInt 2.
Definition out_param : @P4Parameter tag_t := MkParameter true Out out_type None (MkP4String "output").
Definition locals : list (@Declaration tag_t) := iter_decl :: nil.

Definition iter_expr : @Expression tag_t := MkExpression tag (ExpName (BareName (MkP4String "iters"))) TypInteger Directionless.
Definition z_expr : @Expression tag_t := MkExpression tag (ExpInt (MkP4Int 0 None)) TypInteger Directionless.
Definition one_expr : @Expression tag_t := MkExpression tag (ExpInt (MkP4Int 1 None)) TypInteger Directionless.
Definition five_expr : @Expression tag_t := MkExpression tag (ExpInt (MkP4Int 5 None)) TypInteger Directionless.
Definition minus_expr : @Expression tag_t := MkExpression tag (ExpBinaryOp Minus (iter_expr, one_expr)) TypInteger Directionless.

Definition decrement : @Statement tag_t := MkStatement tag (StatAssignment iter_expr minus_expr) StmUnit.
Definition initialize : @Statement tag_t := MkStatement tag (StatAssignment iter_expr five_expr) StmUnit.

Definition start_body: list (@Statement tag_t) := initialize :: nil.
Definition loop_body: list (@Statement tag_t) := decrement :: nil.

Definition start_st : @ParserState tag_t := MkParserState tag (MkP4String "start") start_body (ParserDirect tag (MkP4String "loop")).

Definition loop_transition : @ParserTransition tag_t :=
  let loop_case := MkParserCase tag ((MkMatch tag (MatchExpression z_expr) TypInteger) :: nil) (MkP4String "loop") in
  let accept_case := MkParserCase tag ((MkMatch tag (MatchDontCare) TypInteger) :: nil) (MkP4String StringConstants.accept) in
    ParserSelect tag (iter_expr :: nil) (loop_case :: accept_case :: nil).

Definition loop_st : @ParserState tag_t := MkParserState tag (MkP4String "loop") loop_body loop_transition.

Definition states : list (@ParserState tag_t) := start_st :: loop_st :: nil.

Definition LoopParser : @ValueObject tag_t := ValObjParser scope nil nil locals states.

(* Compute LoopParser. *)
(* Compute rename_loop tag_t tt LoopParser loop_st. *)
(* Compute unroll_loop tag_t tt LoopParser loop_st. *)

Definition unrolledLP := unroll_loop _ tt LoopParser loop_st.

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
