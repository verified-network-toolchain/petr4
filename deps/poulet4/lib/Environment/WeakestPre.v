Require Import Poulet4.Syntax.
Require Import Poulet4.Eval.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.
Require Import Poulet4.Step.
Require Import Poulet4.Typed.
Require Import Poulet4.Environment.Environment.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Import ListNotations.

Open Scope monad_scope.
Open Scope monad.

Section WeakestPre.

  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Definition environment := @Environment.environment tags_t.


  Definition pred {A: Type} := A -> Prop.

  Definition pred_true {A: Type} (a : A) := True.

  Definition pred_false {A: Type} (a : A) := False.

  Definition pred_env_pushed (p: @pred environment) (env: environment) : Prop :=
      match stack_push tags_t env with
      | (inr _, _) => False
      | (inl _, env') => p env'
      end
  .

  Definition pred_env_popped (p: @pred environment) (env: environment) : Prop :=
      match stack_pop tags_t env with
      | (inr _, _) => False
      | (inl _, env') => p env'
      end
  .

  Fixpoint weakest_precondition_expression
      (expr: @Expression tags_t)
      (post: @pred (environment * (@Value tags_t)))
      : @pred environment
  :=
      pred_false
  with weakest_precondition_expression_lvalue
      (expr: @Expression tags_t)
      (post: @pred (environment * (@ValueLvalue tags_t)))
      : @pred environment
  :=
      pred_false
  .

  Lemma weakest_precondition_expression_correct:
      forall env_pre expr post,
          weakest_precondition_expression expr post env_pre ->
              match eval_expression tags_t tags_dummy expr env_pre with
              | (inl val_post, env_post) => post (env_post, val_post)
              | _ => False
              end
  .
  Proof.
      intros.
      induction expr.
      simpl in H.
      contradiction.
  Qed.

  Lemma weakest_precondition_expression_lvalue_correct:
      forall expr env_pre post,
          weakest_precondition_expression_lvalue expr post env_pre ->
              match eval_lvalue tags_t expr env_pre with
              | (inl val_post, env_post) => post (env_post, val_post)
              | _ => False
              end
  .
  Proof.
      intros.
      induction expr.
      unfold pred_false in H.
      contradiction.
  Qed.

  Definition weakest_precondition_method_call
    (callee: @Expression tags_t)
    (type_args: list (@P4Type tags_t))
    (args: list (option (@Expression tags_t)))
    (post: @pred (environment * (@Value tags_t)))
    : @pred environment
  :=
    pred_false
  .

  Lemma weakest_precondition_method_call_correct:
    forall env_pre callee type_args args post,
      weakest_precondition_method_call callee type_args args post env_pre ->
        match eval_method_call tags_t tags_dummy
        (eval_expression tags_t tags_dummy) callee type_args args env_pre with
        | (inl val_post, env_post) => post (env_post, val_post)
        | _ => False
        end
  .
  Proof.
    intros.
    unfold weakest_precondition_method_call in H.
    unfold pred_false in H.
    contradiction H.
  Qed.

  Equations weakest_precondition_statement (stmt: @Statement tags_t) (post: @pred environment) : @pred environment :=
    weakest_precondition_statement (MkStatement _ stmt _) post :=
      weakest_precondition_statement_pre stmt post
  with weakest_precondition_statement_pre (stmt: @StatementPreT tags_t) (post: @pred environment) : @pred environment :=
    weakest_precondition_statement_pre (StatBlock block) post :=
      let inter := weakest_precondition_block block (pred_env_popped post) in
      pred_env_pushed inter;
    weakest_precondition_statement_pre (StatAssignment lhs rhs) post :=
      let inter' := fun '(env_inter', lval) =>
        let inter := fun '(env_inter, rval) =>
          match env_update _ lval rval env_inter with
          | (inl tt, env_post) => post env_post
          | _ => False
          end
        in weakest_precondition_expression rhs inter env_inter'
      in weakest_precondition_expression_lvalue lhs inter';
    weakest_precondition_statement_pre (StatMethodCall callee type_args args) post :=
      let post' := fun val_and_env => post (fst val_and_env) in
      weakest_precondition_method_call callee type_args args post';
    weakest_precondition_statement_pre StatEmpty post :=
      post;
    weakest_precondition_statement_pre _ _ :=
      pred_false
  with weakest_precondition_block (block: @Block tags_t) (post: @pred environment) : @pred environment :=
    weakest_precondition_block (BlockEmpty _) post :=
      post;
    weakest_precondition_block (BlockCons stmt rest) post :=
      let inter := weakest_precondition_block rest post in
      weakest_precondition_statement stmt inter
  .

  Definition weakest_precondition_block_correct
      (block: @Block tags_t)
  :=
      forall env_pre post,
          weakest_precondition_block block post env_pre ->
              match eval_block tags_t tags_dummy block env_pre with
              | (inl tt, env_post) => post env_post
              | _ => True
              end
  .

  Definition weakest_precondition_statement_pre_correct
      (stmt: @StatementPreT tags_t)
  :=
      forall env_pre post,
          weakest_precondition_statement_pre stmt post env_pre ->
              match eval_statement_pre tags_t tags_dummy stmt env_pre with
              | (inl tt, env_post) => post env_post
              | _ => True
              end
  .

  Definition weakest_precondition_statement_correct
      (stmt: @Statement tags_t)
  :=
      forall env_pre post,
          weakest_precondition_statement stmt post env_pre ->
              match eval_statement tags_t tags_dummy stmt env_pre with
              | (inl tt, env_post) => post env_post
              | _ => True
              end
  .

  Definition weakest_precondition_statement_maybe_correct
      (stmt_maybe: option (@Statement tags_t))
  :=
      match stmt_maybe with
      | None => True
      | Some stmt => weakest_precondition_statement_correct stmt
      end
  .

  Definition weakest_precondition_block_maybe_correct
      (block_maybe: option (@Block tags_t))
  :=
      match block_maybe with
      | None => True
      | Some block => weakest_precondition_block_correct block
      end
  .

  Lemma weakest_precondition_correctness:
      forall stmt, weakest_precondition_statement_correct stmt
  .
  Proof.
      intros.
      induction stmt
          using @statement_rec with
          (PStatementPreT := weakest_precondition_statement_pre_correct)
          (PStatementMaybe := weakest_precondition_statement_maybe_correct)
          (PBlock := weakest_precondition_block_correct)
          (PBlockMaybe := weakest_precondition_block_maybe_correct)
          (PStatementSwitchCase := fun _ => True)
          (PStatementSwitchCaseList := fun _ => True); try easy.
      - unfold weakest_precondition_statement_pre_correct; intros.
        unfold weakest_precondition_statement_pre in H.
        apply weakest_precondition_expression_lvalue_correct in H.
        rewrite eval_statement_pre_equation_2.
        simpl; unfold state_bind; simpl.
        destruct (eval_lvalue tags_t lhs env_pre).
        destruct s; try contradiction.
        apply weakest_precondition_expression_correct in H.
        destruct (eval_expression tags_t tags_dummy rhs e).
        destruct s; try contradiction.
        destruct (env_update tags_t v v0 e0).
        destruct s; try contradiction.
        exact H.
      - unfold weakest_precondition_statement_pre_correct; intros.
        rewrite weakest_precondition_statement_pre_equation_5 in H.
        simpl in H; unfold pred_env_pushed in H.
        apply IHstmt in H.
        rewrite eval_statement_pre_equation_5; simpl.
        unfold state_bind; simpl.
        destruct (eval_block tags_t tags_dummy block _).
        destruct s; try trivial; destruct u.
        unfold pred_env_popped in H.
        destruct (stack_pop tags_t e).
        destruct s; try trivial.
        destruct u; exact H.
      - unfold weakest_precondition_block_correct; intros.
        rewrite weakest_precondition_block_equation_2 in H.
        simpl in H; apply IHstmt in H.
        rewrite eval_block_equation_2.
        simpl; unfold state_bind; simpl.
        destruct (eval_statement tags_t tags_dummy stmt env_pre).
        destruct s; try trivial.
        destruct u.
        apply IHstmt0 in H.
        destruct (eval_block tags_t tags_dummy rest e).
        exact H.
  Qed.
End WeakestPre.
