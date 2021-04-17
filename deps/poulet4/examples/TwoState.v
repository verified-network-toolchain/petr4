Require Import Poulet4.Syntax.
Require Import Poulet4.Eval.
Require Import Poulet4.Typed.
Require Import Poulet4.Monads.State.
Require Import Poulet4.Environment.Environment.
Require Import Poulet4.Step.

Require Import Poulet4.Examples.IntExample.

Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinIntDef.

Open Scope string_scope.
Open Scope list_scope.

Definition tag_t := unit.
Definition tag := tt.

(* OK, now consider the following two parsers: *)
(*
parser Tupled (packet_in pkt, out int x, out int y) {
  state start {
    pkt.extract(x);
    pkt.extract(y);
    transition accept;
  }
}

parser Curried (packet_in pkt, out int x, out int y) {
  state start {
    pkt.extract(x);
    transition middle;
  }
  state middle {
    pkt.extract(y);
    transition accept;
  }
}

An interesting property is that Tupled and Curried behave the same on all packets!
*)


Definition x_param : @P4Parameter tag_t := MkParameter true Out out_type None (MkP4String "x").
Definition y_param : @P4Parameter tag_t := MkParameter true Out out_type None (MkP4String "y").
Definition x_expr : @Expression tag_t := MkExpression tt (ExpName (BareName (MkP4String "x"))) out_type Directionless.
Definition y_expr : @Expression tag_t := MkExpression tt (ExpName (BareName (MkP4String "y"))) out_type Directionless.
Definition extract_x := build_extract_stmt out_type x_expr.
Definition extract_y := build_extract_stmt out_type y_expr.

Definition body_tupled := extract_x :: extract_y :: nil.
Definition body_1_curried := extract_x :: nil.
Definition body_2_curried := extract_y :: nil.

Definition start_st_tupled : @ParserState tag_t := MkParserState tt (MkP4String "start") body_tupled (ParserDirect tt (MkP4String StringConstants.accept)).
Definition start_st_curried : @ParserState tag_t := MkParserState tt (MkP4String "start") body_1_curried (ParserDirect tt (MkP4String "middle")).
Definition mid_st_curried : @ParserState tag_t := MkParserState tt (MkP4String "middle") body_2_curried (ParserDirect tt (MkP4String StringConstants.accept)).

Definition states_tupled : list (@ParserState tag_t) := start_st_tupled :: nil.
Definition states_curried : list (@ParserState tag_t) := start_st_curried :: nil.

Definition IntParserTupled : @ValueObject tag_t := ValObjParser scope nil nil nil states_tupled.
Definition IntParserCurried : @ValueObject tag_t := ValObjParser scope nil nil nil states_curried.


Definition build_env (bits: list bool) :=
  let heap := MNat.add 0 (ValObj (ValObjPacket bits)) (MNat.add 1 out_value (MNat.add 2 out_value (MNat.empty _))) in
  let scope := MStr.add "pkt" 0 (MStr.add "x" 1 (MStr.add "y" 2 (MStr.empty _))) in
  MkEnvironment tag_t 0 (MStr.empty _ :: nil) (MNat.empty _)
.
