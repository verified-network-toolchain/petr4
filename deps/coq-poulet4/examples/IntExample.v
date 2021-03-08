Require Import Syntax.
Require Import Eval.
Require Import Typed.
Require Import Strings.String.
Require Import Coq.ZArith.BinIntDef.
Require Import Monads.State.
Require Import Environment.Environment.

Require Import Step.

Open Scope string_scope.
Open Scope list_scope.

Definition tag_t := unit.
Definition tag := tt.

Notation P4String := (P4String.t tag_t).

Definition MkP4String (s: string) : P4String := {| P4String.tags := tag; P4String.str := s |}.


Definition constTyp : P4Type := @TypInteger tag_t.
Definition name : P4String := MkP4String "hello_world".
Definition value : ValueBase := @ValBaseInteger tag_t 42.

Definition parses (p: @ValueObject tag_t) (fuel: nat) (start_state: P4String) (start_env: Environment.environment tag_t): bool :=
  match run_with_state start_env (step_trans tag_t tag p fuel start_state) with
  | (inl _, _) => true
  | _ => false
  end.

Definition EmptyParser : @Declaration tag_t := DeclConstant tag constTyp name value.


(* Let's just parse an int... *)

(*
parser IntExample (packet_in pkt, out int<2> output) {
  state start {
    pkt.extract(output);
    transition accept;
  }
}
*)

Definition scope : @Env_EvalEnv tag_t := MkEnv_EvalEnv nil nil (MkP4String "dummy").

Definition pkt_param : @P4Parameter tag_t := MkParameter true Directionless (TypExtern (MkP4String "packet_in")) None (MkP4String "pkt").
Definition pkt_expr : @Expression tag_t := MkExpression tt (ExpName (BareName (MkP4String "pkt"))) (TypExtern (MkP4String "packet_in")) Directionless.
Definition out_type : @P4Type tag_t := TypInt 2.
Definition out_param : @P4Parameter tag_t := MkParameter true Out out_type None (MkP4String "output").
Definition locals : list (@Declaration tag_t) := nil.
Definition output_expr : @Expression tag_t := MkExpression tt (ExpName (BareName (MkP4String "output"))) out_type Directionless.
Definition pkt_extract_expr : @Expression tag_t := MkExpression tt (ExpName (BareName (MkP4String "pkt"))) (TypFunction (MkFunctionType nil ((MkParameter false Directionless out_type None (MkP4String "t"))::nil) FunBuiltin out_type)) Directionless.
Definition build_extract_stmt (into_type: @P4Type tag_t) (into_expr: @Expression tag_t) := MkStatement tt (StatMethodCall (MkExpression tt (ExpExpressionMember pkt_extract_expr (MkP4String StringConstants.extract)) TypVoid Directionless) (into_type :: nil) (Some into_expr :: nil)) StmVoid.
Definition extract_stmt : @Statement tag_t := build_extract_stmt out_type output_expr.


Definition body: list (@Statement tag_t) := extract_stmt :: nil.
Definition start_st : @ParserState tag_t := MkParserState tt (MkP4String "start") body (ParserDirect tt (MkP4String StringConstants.accept)).

Definition states : list (@ParserState tag_t) := start_st :: nil.

Definition IntParser : @ValueObject tag_t := ValObjParser scope nil nil nil states.

Definition pkt_value : @Value tag_t := ValObj (ValObjPacket (true :: true :: nil)).
Definition out_value : @Value tag_t := ValBase (ValBaseInteger 0).

Notation environment := (environment tag_t).

Definition good_env :=
  let heap := MNat.add 0 pkt_value (MNat.add 1 out_value (MNat.empty _)) in
  let scope := MStr.add "pkt" 0 (MStr.add "output" 1 (MStr.empty _)) in
  MkEnvironment tag_t 0 (MStr.empty _ :: nil) (MNat.empty _)
.

Definition inter_env :=
  let heap := MNat.add 0 (ValObj (ValObjPacket nil)) (MNat.add 1 out_value (MNat.empty _)) in
  let scope := MStr.add "pkt" 0 (MStr.add "output" 1 (MStr.empty _)) in
  MkEnvironment tag_t 0 (MStr.empty _ :: nil) (MNat.empty _)
.
