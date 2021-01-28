Require Import Syntax.
Require Import Eval.
Require Import Typed.
Require Import Strings.String.
Require String.
Require Import Coq.ZArith.BinIntDef.
Require Import Monads.State.
Require Import IntExample.

Require Import Step.

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


Definition x_param : P4Parameter := MkParameter true Out out_type "x".
Definition y_param : P4Parameter := MkParameter true Out out_type "y".
Definition x_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName "x")) out_type Directionless.
Definition y_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName "y")) out_type Directionless.
Definition extract_x := build_extract_stmt out_type x_expr.
Definition extract_y := build_extract_stmt out_type y_expr.

Definition body_tupled := extract_x :: extract_y :: nil.
Definition body_1_curried := extract_x :: nil.
Definition body_2_curried := extract_y :: nil.

Definition start_st_tupled : ParserState tag_t := MkParserState _ tt (MkP4String _ tt "start") body_tupled (ParserDirect _ tt (MkP4String _ tt String.accept)).
Definition start_st_curried : ParserState tag_t := MkParserState _ tt (MkP4String _ tt "start") body_1_curried (ParserDirect _ tt (MkP4String _ tt "middle")).
Definition mid_st_curried : ParserState tag_t := MkParserState _ tt (MkP4String _ tt "middle") body_2_curried (ParserDirect _ tt (MkP4String _ tt String.accept)).

Definition states_tupled : list (ParserState tag_t) := start_st_tupled :: nil.
Definition states_curried : list (ParserState tag_t) := start_st_curried :: nil.

Definition IntParserTupled := ValObjParser _ scope nil nil states_tupled.
Definition IntParserCurried := ValObjParser _ scope nil nil states_curried.

Definition build_env (bits: list bool): Environment.environment tag_t :=
  Environment.extend_scope _ "pkt" (ValObj _ (ValObjPacket _ bits)) (
    Environment.extend_scope _ "x" out_value (
      Environment.extend_scope _ "y" out_value (
        Environment.MStr.empty _
      )
    )
  ) :: nil.
