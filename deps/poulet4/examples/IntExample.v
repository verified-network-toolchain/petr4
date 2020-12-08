Require Import Syntax.
Require Import Eval.
Require Import Typed.
Require Import CamlString.
Require Import Strings.String.
Require Import Coq.ZArith.BinIntDef.
Require Import Monads.State.

Require Import Step.

Open Scope list_scope.

Definition tag_t := unit.
Definition tag := tt.
Definition constTyp : P4Type := TypInteger.
Definition name : P4String tag_t := MkP4String tag_t tag (caml_string_of_chars "hello_world").
Definition value : ValueBase tag_t := ValBaseInteger tag_t 42.

Definition parses (p: ValueObject tag_t) (fuel: nat) (start: caml_string): bool :=
  match run_with_state nil (step_trans tag_t tag p fuel start) with
  | (inl _, _) => true
  | _ => false
  end.

Definition EmptyParser : Declaration tag_t := DeclConstant tag_t tag constTyp name value.


(* Let's just parse an int... *)

(* 
parser IntExample (packet_in pkt, out int output) {
  state start {
    pkt.extract(output);
    transition accept;
  }
}
*)

(* TODO: I'm pretty sure this scope needs to be legit and needs definitions for pkt and output, so something like
  scope_pkt_3 := [pkt |-> Packet [1;1], output |-> 0]
*)
Definition scope : Env_EvalEnv := MkEnv_EvalEnv nil nil (caml_string_of_chars "dummy").

Definition pkt_param : P4Parameter := MkParameter true Directionless (TypExtern (caml_string_of_chars "packet_in")) (caml_string_of_chars "pkt").
Definition out_param : P4Parameter := MkParameter true Out TypInteger (caml_string_of_chars "output").
Definition locals : list (Declaration tag_t) := nil.
Definition accept_st : ParserState tag_t := MkParserState _ tt (MkP4String _ tt StrConstants.accept) nil (ParserDirect _ tt (MkP4String _ tt StrConstants.accept)).
Definition output_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName (caml_string_of_chars "output"))) TypInteger Directionless.
Definition pkt_extract_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName (caml_string_of_chars "pkt"))) (TypFunction (MkFunctionType nil ((MkParameter false Directionless TypInteger (caml_string_of_chars "x"))::nil) FunBuiltin TypInteger)) Directionless.
Definition extract_stmt : Statement tag_t := 
  MkStatement _ tt (StatMethodCall _ (MkExpression _ tt (ExpExpressionMember _ pkt_extract_expr (MkP4String _ tt StrConstants.extract)) TypVoid Directionless) nil nil) StmVoid.


Definition body: list (Statement tag_t) := extract_stmt :: nil.
Definition start_st : ParserState tag_t := MkParserState _ tt (MkP4String _ tt (caml_string_of_chars "start")) body (ParserDirect _ tt (MkP4String _ tt StrConstants.accept)).

Definition states : list (ParserState tag_t) := start_st :: nil.

Definition IntParser : ValueObject tag_t := ValObjParser _ scope nil nil states.

Lemma caml_string_true : forall s: string, caml_string_eqb (caml_string_of_chars s) (caml_string_of_chars s) = true.
Admitted.

Lemma int_parses_corr : parses IntParser 2 (caml_string_of_chars "start") = true.
Proof.
  unfold parses.
  unfold step_trans.
  unfold step. unfold run_with_state.
  unfold IntParser. auto. unfold lookup_state.
  unfold states. unfold start_st. auto.
  rewrite caml_string_true.
  unfold body. auto. 
  unfold eval_statement.
  unfold Monad.mbind. auto.
Admitted.
