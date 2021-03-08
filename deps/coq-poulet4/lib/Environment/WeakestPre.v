Require Import Syntax.
Require Import Eval.
Require Import Monads.Monad.
Require Import Monads.State.
Require Import Step.
Require Import Typed.
Require Import Environment.Environment.
Require Import Strings.String.
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

  Fixpoint weakest_precondition_arguments
      (params: list (@P4Parameter tags_t))
      (args: list (option (@Expression tags_t)))
      (post: @pred (environment * (list (option (@Value tags_t)))))
      : @pred environment
  :=
      fun env_pre =>
          match (args, params) with
          | (nil, nil) => post (env_pre, nil)
          | (Some arg :: args', param :: params') =>
            let inter := fun '(env_inter, val) =>
                let post' := fun '(env_post, vals) =>
                  post (env_post, (Some val) :: vals)
                in weakest_precondition_arguments params' args' post' env_inter
            in let '(MkParameter _ dir _ _ _) := param in
            match dir with
            | In => weakest_precondition_expression arg inter env_pre
            (* TODO: @Tobias, please check these out? *)
            (* | Out =>
              let inter' := fun '(env_inter, val) =>
                  inter (env_inter, ValLvalue val)
              in weakest_precondition_expression_lvalue arg inter' env_pre *)
            (* | _ => False *)
            end
          | (None :: args', param :: params') =>
            let post' := fun '(env_post, vals) =>
              post (env_post, None :: vals)
            in weakest_precondition_arguments params' args' post' env_pre
          | _ => False
          end
  .

  Lemma weakest_precondition_arguments_correct:
      forall params args env_pre post,
          weakest_precondition_arguments params args post env_pre ->
              match eval_arguments tags_t (eval_expression tags_t tags_dummy) params args env_pre with
              | (inl vals_post, env_post) => post (env_post, vals_post)
              | _ => False
              end
  .
  Proof.
      intro params.
      induction params; intro args; destruct args; intros.
      - simpl.
        exact H.
      - destruct o; simpl in H; contradiction.
      - simpl in H; contradiction.
      - destruct o as [expr|].
        * destruct a, direction; try contradiction.
          -- simpl in H.
            apply weakest_precondition_expression_correct in H.
            case_eq (eval_expression tags_t tags_dummy expr env_pre).
            intros s env_inter eval_expression_result.
            rewrite eval_expression_result in H.
            destruct s as [val_inter|]; try contradiction.
            apply IHparams in H.
            case_eq (eval_arguments tags_t (eval_expression tags_t tags_dummy) params args env_inter).
            intros s env_post eval_arguments_result.
            rewrite eval_arguments_result in H.
            destruct s as [vals_post|]; try contradiction.
            rewrite eval_arguments_equation_4.
            simpl; unfold state_bind.
            rewrite eval_expression_result.
            rewrite eval_arguments_result.
            simpl.
            exact H.
          -- simpl in H.
  Admitted.
          (* TODO: it looks like an lvalue refactoring broke this? *)
            (* apply weakest_precondition_expression_lvalue_correct in H.
            case_eq (eval_lvalue tags_t expr env_pre).
            intros s env_inter eval_lvalue_result.
            rewrite eval_lvalue_result in H.
            destruct s as [val_inter|]; try contradiction.
            apply IHparams in H.
            case_eq (eval_arguments tags_t (eval_expression tags_t tags_dummy) params args env_inter).
            intros vals env_post eval_arguments_result.
            rewrite eval_arguments_result in H.
            destruct vals; try contradiction.
            rewrite eval_arguments_equation_4.
            simpl; unfold state_bind.
            rewrite eval_lvalue_result; simpl.
            rewrite eval_arguments_result; simpl.
            exact H.
        * simpl in H.
          apply IHparams in H.
          case_eq (eval_arguments tags_t (eval_expression tags_t tags_dummy) params args env_pre).
          intros s env_post eval_arguments_result.
          rewrite eval_arguments_result in H.
          destruct s as [vals_post|]; try contradiction.
          rewrite eval_arguments_equation_5.
          simpl; unfold state_bind.
          rewrite eval_arguments_result.
          simpl.
          exact H.
  Qed. *)

  Definition weakest_precondition_method_call
    (callee: @Expression tags_t)
    (type_args: list (@P4Type tags_t))
    (args: list (option (@Expression tags_t)))
    (post: @pred (environment * (@Value tags_t)))
  :=
    let inter' := fun '(env_inter', func) =>
      match func with
      | ValObj (ValObjFun params impl) =>
        let inter := fun '(env_inter, arg_vals) =>
          match impl with
          | ValFuncImplBuiltin name obj =>
            match eval_builtin_func _ name obj type_args arg_vals env_inter with
            | (inl val, env_post) => post (env_post, val)
            | _ => False
            end
          | _ => False
          end
        in weakest_precondition_arguments params args inter env_inter'
      | _ => False
      end
    in weakest_precondition_expression callee inter'
  .

  Lemma weakest_precondition_method_call_correct:
    forall env_pre callee type_args args post,
      weakest_precondition_method_call callee type_args args post env_pre ->
        match eval_method_call tags_t (eval_expression tags_t tags_dummy) callee type_args args env_pre with
        | (inl val_post, env_post) => post (env_post, val_post)
        | _ => False
        end
  .
  Proof.
    intros.
    unfold eval_method_call, Unpack.unpack_func; simpl.
    unfold state_bind; simpl.
    apply weakest_precondition_expression_correct in H.
    destruct (eval_expression tags_t tags_dummy callee env_pre).
    destruct s; try contradiction.
    destruct v; try contradiction.
    destruct v; try contradiction.
    simpl; simpl in H.
    apply weakest_precondition_arguments_correct in H.
    destruct (eval_arguments tags_t (eval_expression tags_t tags_dummy) params args e).
    destruct s; try contradiction.
    destruct impl; try contradiction.
    destruct (eval_builtin_func tags_t name caller type_args l e0).
    destruct s; try contradiction.
    exact H.
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
        rewrite weakest_precondition_statement_pre_equation_1 in H; simpl in H.
        apply weakest_precondition_method_call_correct in H.
        rewrite eval_statement_pre_equation_1.
        unfold toss_value; simpl.
        destruct (eval_method_call tags_t (eval_expression tags_t tags_dummy) func type_args args).
        destruct s; try contradiction.
        exact H.
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