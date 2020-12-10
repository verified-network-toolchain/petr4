Require Import Syntax.
Require Import Eval.
Require Import Typed.
Require Import Strings.String.
Require String.
Require Import Coq.ZArith.BinIntDef.
Require Import Monads.State.

Require Import Step.

Open Scope list_scope.
Open Scope string_scope.

Definition tag_t := unit.
Definition tag := tt.
Definition constTyp : P4Type := TypInteger.
Definition name : P4String tag_t := MkP4String tag_t tag "hello_world".
Definition value : ValueBase tag_t := ValBaseInteger tag_t 42.

Definition parses (p: ValueObject tag_t) (fuel: nat) (start_state: String.t) (start_env: Environment.environment tag_t): bool :=
  match run_with_state start_env (step_trans tag_t tag p fuel start_state) with
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

Definition scope : Env_EvalEnv := MkEnv_EvalEnv nil nil "dummy".
(* Definition good_scope : Env_EvalEnv := MkEnv_EvalEnv  *)

Definition pkt_param : P4Parameter := MkParameter true Directionless (TypExtern "packet_in") "pkt".
Definition out_type : P4Type := TypInt 2.
Definition out_param : P4Parameter := MkParameter true Out out_type "output".
Definition locals : list (Declaration tag_t) := nil.
Definition accept_st : ParserState tag_t := MkParserState _ tt (MkP4String _ tt String.accept) nil (ParserDirect _ tt (MkP4String _ tt String.accept)).
Definition output_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName "output")) out_type Directionless.
Definition pkt_extract_expr : Expression tag_t := MkExpression _ tt (ExpName _ (BareName "pkt")) (TypFunction (MkFunctionType nil ((MkParameter false Directionless out_type "x")::nil) FunBuiltin out_type)) Directionless.
Definition extract_stmt : Statement tag_t := 
  MkStatement _ tt (StatMethodCall _ (MkExpression _ tt (ExpExpressionMember _ pkt_extract_expr (MkP4String _ tt String.extract)) TypVoid Directionless) (out_type :: nil) (Some output_expr :: nil)) StmVoid.


Definition body: list (Statement tag_t) := extract_stmt :: nil.
Definition start_st : ParserState tag_t := MkParserState _ tt (MkP4String _ tt "start") body (ParserDirect _ tt (MkP4String _ tt String.accept)).

Definition states : list (ParserState tag_t) := start_st :: nil.

Definition IntParser : ValueObject tag_t := ValObjParser _ scope nil nil states.

Definition bad_env : Environment.environment tag_t := nil.

Lemma int_parses_fail : parses IntParser 2 "start" bad_env = false.
Proof.
  reflexivity.
Qed.

Definition pkt_value : Value tag_t := ValObj _ (ValObjPacket _ (true :: true :: nil)).
Definition out_value : Value tag_t := ValBase _ (ValBaseInteger _ 0).
Definition top_scope : Environment.scope tag_t := 
  Environment.extend_scope _ "pkt" pkt_value (
    Environment.extend_scope _ "output" out_value (
      Environment.MStr.empty _
    )
  ).

Definition inter_scope : Environment.scope tag_t := 
  Environment.MStr.add "pkt"
                              (ValObj tag_t (ValObjPacket tag_t nil))
                              top_scope.
Definition good_env: Environment.environment tag_t := top_scope :: nil.

Lemma top_find_pkt: Environment.MStr.find "pkt" top_scope = Some pkt_value.
Proof.
  unfold top_scope, Environment.extend_scope.
  apply Environment.MStr.find_1.
  now apply Environment.MStr.add_1.
Qed.
Lemma top_find_val : Environment.MStr.find "output" top_scope = Some out_value.
Proof.
  unfold top_scope, Environment.extend_scope.
  apply Environment.MStr.find_1.
  apply Environment.MStr.add_2;
    [congruence|].
  now apply Environment.MStr.add_1.
Qed.

Lemma top_find_val_inter : Environment.MStr.find "output" inter_scope = Some out_value.
Proof.
  unfold top_scope, Environment.extend_scope.
  apply Environment.MStr.find_1.
  apply Environment.MStr.add_2; [congruence|].
  apply Environment.MStr.add_2; [congruence|].
  now apply Environment.MStr.add_1.
Qed.

Hint Rewrite top_find_pkt top_find_val top_find_val_inter: int_example.

Lemma int_parses : parses IntParser 2 "start" good_env = true.
Proof.
  unfold parses.
  simpl.
  unfold IntParser.
  unfold states.
  unfold start_st.
  unfold parses.
  unfold step_trans. auto.
  unfold run_with_state.
  unfold good_env.
  unfold Monad.mbind.
  unfold state_monad_inst.
  unfold state_bind.

  unfold step.
  unfold lookup_state.
  simpl.
  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.
  unfold body. 

  unfold eval_statement.
  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.
  unfold Environment.map_env. unfold Environment.push_scope. unfold Environment.extend_scope.
  auto.
  unfold Monad.mret. unfold state_monad_inst. unfold state_return.

  unfold states_to_block. unfold List.fold_right.
  unfold extract_stmt.

  unfold eval_method_call.
  unfold eval_expression. unfold pkt_extract_expr.
  unfold Environment.find_environment. unfold Environment.lift_env_lookup_fn.
  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.
  unfold Environment.toss_value.
  unfold Environment.find_environment'.
  unfold Environment.str_of_name_warning_not_safe.
  auto.


  assert (H := top_find_pkt).
  unfold Environment.MStr.find. unfold Environment.MStr.Raw.find. auto.
  unfold Environment.MStr.this. 
  unfold Environment.MStr.empty. unfold Environment.MStr.Raw.empty.

  
  
  unfold Environment.MStr.find in H. unfold Environment.MStr.Raw.find in H. 

  unfold Environment.MStr.this in H.
  rewrite H.
  clear H.

  unfold Monad.mret. unfold state_monad_inst. unfold state_return.
  unfold pkt_value.
  unfold String.extract.

  simpl.
  unfold extract_value_func. unfold eval_builtin_func.

  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.
  unfold eval_arguments.
  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.
  unfold eval_expression. unfold output_expr.

  unfold Environment.find_environment. unfold Environment.lift_env_lookup_fn. unfold Environment.find_lvalue'.
  unfold Environment.find_environment'. unfold Environment.str_of_name_warning_not_safe.
  
  unfold Environment.MStr.find. unfold Environment.MStr.Raw.find. auto.

  unfold Environment.MStr.this.
  assert (H := top_find_val).

  unfold Environment.MStr.find in H. unfold Environment.MStr.Raw.find in H. auto.

  unfold Environment.MStr.this in H.
  rewrite H. clear H.

  unfold Monad.mret. unfold state_monad_inst. unfold state_return.

  unfold String.extract. 
  unfold String.isValid.
  unfold String.setValid.
  unfold String.setInvalid.
  unfold String.pop_front. simpl.
  unfold String.push_front. simpl.
  unfold is_packet_func.
  unfold String.extract. 

  unfold Environment.dummy_value.
  unfold eval_packet_func.
  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.
  unfold Environment.find_lvalue. unfold Environment.lift_env_lookup_fn. unfold Environment.find_lvalue'.
  unfold Environment.find_environment'. unfold Environment.str_of_name_warning_not_safe.
  unfold Environment.MStr.this.
  unfold Environment.MStr.find. unfold Environment.MStr.Raw.find. auto.

  unfold Environment.MStr.this.

  assert (H := top_find_pkt).
  unfold Environment.MStr.find in H. unfold Environment.MStr.Raw.find in H.
  unfold Environment.MStr.this in H.
  rewrite H. clear H.

  unfold Monad.mret. unfold state_monad_inst. unfold state_return.

  unfold pkt_value.
  unfold String.extract. simpl in *.
  unfold Packet.eval_packet_extract_fixed.
  unfold out_type.

  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.
  unfold Packet.read_first_bits.
  unfold Monad.mret. unfold state_monad_inst. unfold state_return.


  unfold Environment.update_lvalue. unfold Environment.lift_env_fn. unfold Environment.update_lvalue'.
  
  unfold Environment.update_environment'.
  unfold Environment.str_of_name_warning_not_safe.
  unfold Environment.MStr.find. unfold Environment.MStr.Raw.find. unfold Environment.MStr.this.


  unfold Monad.mbind. unfold state_monad_inst. unfold state_bind.

  assert (H := top_find_pkt).
  unfold Environment.MStr.find in H. unfold Environment.MStr.Raw.find in H.
  unfold Environment.MStr.this in H.
  rewrite H. clear H.
  unfold Option.option_monad_inst. unfold Option.option_bind.
  (* unfold Environment.update_scope. *)
  unfold Environment.insert_scope.

  unfold Monad.mbind. unfold Option.option_monad_inst. unfold Option.option_bind.

  rewrite top_find_pkt.

  unfold Monad.mret. unfold Option.option_ret. unfold state_return.

  unfold eval_lvalue.
  unfold Monad.mret. unfold state_monad_inst. unfold state_return.

  assert (H := top_find_val_inter).
  unfold Environment.MStr.find in H. unfold Environment.MStr.Raw.find in H. unfold Environment.MStr.this in H.
  unfold inter_scope in H.
  rewrite H. clear H.
  assert (H := top_find_val_inter).
  unfold inter_scope in H.
  rewrite H. clear H.

  unfold Environment.pop_scope.
  unfold eval_transition.
  unfold Monad.mret. unfold state_monad_inst. unfold state_return.
  unfold String.accept. 
  simpl.
  auto.
Qed.

