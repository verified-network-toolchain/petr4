Require Import Syntax.
Require Import Eval.
Require Import Monads.Monad.
Require Import Monads.State.
Require Import Step.
Require Import Typed.
Require Import Environment.
Require Import Strings.String.

Open Scope monad_scope.
Open Scope monad.

Require Import IntExample.

Definition pred {A: Type} := A -> Prop.

Definition pred_true {A: Type} (a : A) := True.

Definition pred_false {A: Type} (a : A) := False.

Definition pred_env_pushed (p: @pred environment) (env: environment) : Prop :=
    match stack_push tag_t env with
    | (inr _, _) => False
    | (inl _, env') => p env'
    end
.

Definition pred_env_popped (p: @pred environment) (env: environment) : Prop :=
    match stack_pop tag_t env with
    | (inr _, _) => False
    | (inl _, env') => p env'
    end
.

Fixpoint weakest_precondition_expression
    (expr: Expression tag_t)
    (post: @pred (environment * (Value tag_t)))
    : @pred environment
:=
    pred_false
with weakest_precondition_expression_lvalue
    (expr: Expression tag_t)
    (post: @pred (environment * (ValueLvalue tag_t)))
    : @pred environment
:=
    pred_false
.

Lemma weakest_precondition_expression_correct:
    forall env_pre expr post,
        weakest_precondition_expression expr post env_pre ->
            match eval_expression tag_t tag expr env_pre with
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
            match eval_lvalue tag_t expr env_pre with
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
    (params: list (P4Parameter tag_t))
    (args: list (option (Expression tag_t)))
    (post: @pred (environment * (list (option (Value tag_t)))))
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
          in let '(MkParameter _ _ dir _ _ _) := param in
          match dir with
          | In => weakest_precondition_expression arg inter env_pre
          | Out =>
            let inter' := fun '(env_inter, val) =>
                inter (env_inter, ValLvalue tag_t val)
            in weakest_precondition_expression_lvalue arg inter' env_pre
          | _ => False
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
            match eval_arguments tag_t tag params args env_pre with
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
           case_eq (eval_expression tag_t tag expr env_pre).
           intros s env_inter eval_expression_result.
           rewrite eval_expression_result in H.
           destruct s as [val_inter|]; try contradiction.
           apply IHparams in H.
           case_eq (eval_arguments tag_t tag params args env_inter).
           intros s env_post eval_arguments_result.
           rewrite eval_arguments_result in H.
           destruct s as [vals_post|]; try contradiction.
           simpl; unfold state_bind.
           rewrite eval_expression_result.
           rewrite eval_arguments_result.
           simpl.
           exact H.
        -- simpl in H.
           apply weakest_precondition_expression_lvalue_correct in H.
           case_eq (eval_lvalue tag_t expr env_pre).
           intros s env_inter eval_lvalue_result.
           rewrite eval_lvalue_result in H.
           destruct s as [val_inter|]; try contradiction.
           apply IHparams in H.
           case_eq (eval_arguments tag_t tag params args env_inter).
           intros vals env_post eval_arguments_result.
           rewrite eval_arguments_result in H.
           destruct vals; try contradiction.
           simpl; unfold state_bind.
           rewrite eval_lvalue_result; simpl.
           rewrite eval_arguments_result; simpl.
           exact H.
      * simpl in H.
        apply IHparams in H.
        case_eq (eval_arguments tag_t tag params args env_pre).
        intros s env_post eval_arguments_result.
        rewrite eval_arguments_result in H.
        destruct s as [vals_post|]; try contradiction.
        simpl; unfold state_bind.
        rewrite eval_arguments_result.
        simpl.
        exact H.
Qed.

Fixpoint weakest_precondition_statement
    (stmt: Statement tag_t)
    (post: @pred environment)
    : @pred environment
:=
    let '(MkStatement _ _ stmt _) := stmt in
    weakest_precondition_statement_pre stmt post
with weakest_precondition_statement_pre
    (stmt: StatementPreT tag_t)
    (post: @pred environment)
    : @pred environment
:=
    match stmt with
    | StatBlock _ block =>
      let inter := weakest_precondition_block block (pred_env_popped post) in
      pred_env_pushed inter
    | StatAssignment _ lhs rhs =>
      let inter' := fun '(env_inter', lval) =>
          let inter := fun '(env_inter, rval) =>
              match env_update tag_t tag lval rval env_inter with
              | (inl tt, env_post) => post env_post
              | _ => False
              end
          in weakest_precondition_expression rhs inter env_inter'
      in weakest_precondition_expression_lvalue lhs inter'
    | StatMethodCall _ callee type_args args =>
      let inter' := fun '(env_inter', func) =>
          match func with
          | ValObj _ (ValObjFun _ params impl) =>
            let inter := fun '(env_inter, arg_vals) =>
                match impl with
                | ValFuncImplBuiltin _ name obj =>
                  match eval_builtin_func tag_t tag name obj type_args arg_vals env_inter with
                  | (inl val, env_post) => post env_post
                  | _ => False
                  end
                | _ => False
                end
            in weakest_precondition_arguments params args inter env_inter'
          | _ => False
          end
      in weakest_precondition_expression callee inter'
    | StatEmpty _ => post
    | _ => pred_false
    end
with weakest_precondition_block
    (block: Block tag_t)
    (post: @pred environment)
    : @pred environment
:=
    match block with
    | BlockEmpty _ _ => post
    | BlockCons _ stmt block' =>
      let inter := weakest_precondition_block block' post in
      weakest_precondition_statement stmt inter
    end
.

Definition weakest_precondition_block_correct
    (block: Block tag_t)
:=
    forall env_pre post,
        weakest_precondition_block block post env_pre ->
            match eval_block tag_t tag block env_pre with
            | (inl tt, env_post) => post env_post
            | _ => False
            end
.

Definition weakest_precondition_statement_pre_correct
    (stmt: StatementPreT tag_t)
:=
    forall env_pre post,
        weakest_precondition_statement_pre stmt post env_pre ->
            match eval_statement_pre tag_t tag stmt env_pre with
            | (inl tt, env_post) => post env_post
            | _ => False
            end
.

Definition weakest_precondition_statement_correct
    (stmt: Statement tag_t)
:=
    forall env_pre post,
        weakest_precondition_statement stmt post env_pre ->
            match eval_statement tag_t tag stmt env_pre with
            | (inl tt, env_post) => post env_post
            | _ => False
            end
.

Lemma foo:
    forall block env env',
        env_stack tag_t env <> nil ->
        eval_block tag_t tag block env = (inl tt, env') ->
        env_stack tag_t env' <> nil
.
Admitted.

Lemma weakest_precondition_correctness:
    forall stmt, weakest_precondition_statement_correct stmt
.
Proof.
    intros.
    apply statement_mut with
        (tags_t := tag_t)
        (P0 := weakest_precondition_statement_pre_correct)
        (P1 := weakest_precondition_block_correct);
        unfold weakest_precondition_statement_pre_correct;
        intros;
        try (simpl in H; unfold pred_false in H; contradiction).
    - unfold weakest_precondition_statement_correct.
      intros.
      simpl in H0.
      specialize (H env_pre post H0).
      case_eq (eval_statement_pre tag_t tag stmt0 env_pre).
      intros s env_post eval_statement_pre_result.
      rewrite eval_statement_pre_result in H.
      destruct s; try contradiction; destruct u.
      unfold eval_statement.
      fold (eval_statement_pre tag_t tag stmt0 env_pre).
      rewrite eval_statement_pre_result.
      exact H.
    - simpl in H;
      apply weakest_precondition_expression_correct in H.
      case_eq (eval_expression tag_t tag func env_pre).
      intros s env_inter' eval_expression_result.
      rewrite eval_expression_result in H.
      destruct s; try contradiction.
      repeat (destruct v; try contradiction).
      apply weakest_precondition_arguments_correct in H.
      case_eq (eval_arguments tag_t tag params args env_inter').
      intros s env_inter eval_arguments_result.
      rewrite eval_arguments_result in H.
      destruct s; try contradiction.
      destruct impl; try contradiction.
      case_eq (eval_builtin_func tag_t tag name caller type_args l env_inter).
      intros s env_post eval_builtin_func_result.
      rewrite eval_builtin_func_result in H.
      destruct s; try contradiction.
      unfold eval_statement_pre.
      unfold toss_value.
      unfold eval_method_call.
      simpl; unfold state_bind.
      rewrite eval_expression_result.
      rewrite eval_arguments_result.
      rewrite eval_builtin_func_result.
      simpl.
      exact H.
    - unfold weakest_precondition_statement_pre in H.
      apply weakest_precondition_expression_lvalue_correct in H.
      case_eq (eval_lvalue tag_t lhs env_pre).
      intros s env_inter' eval_lvalue_result.
      rewrite eval_lvalue_result in H.
      destruct s as [lval|]; try contradiction.
      apply weakest_precondition_expression_correct in H.
      case_eq (eval_expression tag_t tag rhs env_inter').
      intros s env_inter eval_expression_result.
      rewrite eval_expression_result in H.
      destruct s as [rval|]; try contradiction.
      case_eq (env_update tag_t tag lval rval env_inter).
      intros s env_post env_update_result.
      rewrite env_update_result in H.
      destruct s; try contradiction; destruct u.
      unfold eval_statement_pre.
      simpl; unfold state_bind.
      rewrite eval_lvalue_result.
      rewrite eval_expression_result.
      rewrite env_update_result.
      exact H.
    - simpl in H0.
      unfold pred_env_pushed in H0.
      case_eq (stack_push tag_t env_pre); intros.
      rewrite H1 in H0.
      destruct s; try contradiction.
      specialize (H e (pred_env_popped post) H0).
      case_eq (eval_block tag_t tag block e).
      intros s env_post' eval_block_result.
      rewrite eval_block_result in H.
      destruct s; try contradiction; destruct u, u0.
      unfold eval_statement_pre.
      fold (eval_block tag_t tag block).
      simpl; unfold state_bind; simpl.
      unfold stack_push in H1.
      inversion H1.
      rewrite H3.
      rewrite eval_block_result.
      unfold pred_env_popped in H.
      case_eq (stack_pop tag_t env_post'); intros.
      rewrite H2 in H.
      destruct s; try contradiction.
      destruct u.
      exact H.
    - simpl in H.
      simpl.
      exact H.
    - unfold weakest_precondition_block_correct; intros; simpl.
      unfold weakest_precondition_block in H.
      exact H.
    - unfold weakest_precondition_block_correct; intros.
      simpl in H1.
      specialize (H env_pre (weakest_precondition_block rest post) H1).
      case_eq (eval_statement tag_t tag statement env_pre).
      intros s env_inter eval_statement_result.
      rewrite eval_statement_result in H.
      destruct s; try contradiction; destruct u.
      specialize (H0 env_inter post H).
      case_eq (eval_block tag_t tag rest env_inter).
      intros s env_post eval_block_result.
      rewrite eval_block_result in H0.
      destruct s; try contradiction; destruct u.
      unfold eval_block.
      fold (eval_statement tag_t tag statement).
      fold (eval_block tag_t tag rest).
      simpl; unfold state_bind.
      rewrite eval_statement_result.
      rewrite eval_block_result.
      exact H0.
Qed.
