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

Definition pred_env_pushed (p: pred) (env: environment tag_t) :=
    p (push_scope tag_t env)
.

Definition pred_env_popped (p: pred) (env: environment tag_t) :=
    match pop_scope tag_t env with
    | Some env' => p env'
    | None => False
    end
.

Fixpoint weakest_precondition_expression
    (expr: Expression tag_t)
    (post: @pred ((environment tag_t) * (Value tag_t)))
    : @pred (environment tag_t)
:=
    pred_false
with weakest_precondition_expression_lvalue
    (expr: Expression tag_t)
    (post: @pred ((environment tag_t) * ValueLvalue))
    : @pred (environment tag_t)
:=
    pred_false
.

Lemma weakest_precondition_expression_correct:
    forall env_pre expr post,
        weakest_precondition_expression expr post env_pre ->
            exists env_post val_post,
                post (env_post, val_post) /\
                eval_expression tag_t tag expr env_pre
                    = (inl val_post, env_post)
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
            exists env_post val_post,
                post (env_post, val_post) /\
                eval_lvalue tag_t expr env_pre = (inl val_post, env_post)
.
Proof.
    intros.
    induction expr.
    unfold pred_false in H.
    contradiction.
Qed.

Fixpoint weakest_precondition_arguments
    (params: list P4Parameter)
    (args: list (option (Expression tag_t)))
    (post: @pred ((environment tag_t) * (list (option (Value tag_t)))))
    : @pred (environment tag_t)
:=
    fun env_pre =>
        match (args, params) with
        | (nil, nil) => post (env_pre, nil)
        | (Some arg :: args', param :: params') =>
          let inter := fun '(env_inter, val) =>
              let post' := fun '(env_post, vals) =>
                post (env_post, (Some val) :: vals)
              in weakest_precondition_arguments params' args' post' env_inter
          in let '(MkParameter _ dir _ _) := param in
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
            exists env_post vals_post,
                post (env_post, vals_post) /\
                eval_arguments tag_t tag params args env_pre =
                    (inl vals_post, env_post)
.
Proof.
    intro params.
    induction params; intro args; destruct args; intros.
    - simpl in H.
      exists env_pre, nil.
      split; [exact H|].
      reflexivity.
    - destruct o; contradiction.
    - simpl in H; contradiction.
    - destruct o.
      * destruct a, direction; try contradiction.
        -- apply weakest_precondition_expression_correct in H.
           destruct H as [env_inter [val [H eval_expression_result]]].
           apply IHparams in H.
           destruct H as [env_post [vals [env_post_fits eval_arguments_result]]].
           exists env_post, (Some val :: vals).
           split; [exact env_post_fits|].
           simpl; unfold state_bind.
           rewrite eval_expression_result.
           rewrite eval_arguments_result.
           reflexivity.
        -- apply weakest_precondition_expression_lvalue_correct in H.
           destruct H as [env_inter [val [H eval_lvalue_result]]].
           apply IHparams in H.
           destruct H as [env_post [vals [env_post_fits eval_arguments_result]]].
           exists env_post, (Some (ValLvalue tag_t val) :: vals).
           split; [exact env_post_fits|].
           simpl; unfold state_bind.
           rewrite eval_lvalue_result; simpl.
           rewrite eval_arguments_result.
           reflexivity.
      * simpl in H.
        apply IHparams in H.
        destruct H as [env_post [vals [env_post_fits eval_arguments_result]]].
        exists env_post, (None :: vals).
        split; [exact env_post_fits|].
        simpl; unfold state_bind.
        rewrite eval_arguments_result.
        reflexivity.
Qed.

Fixpoint weakest_precondition_statement
    (stmt: Statement tag_t)
    (post: @pred (environment tag_t))
    : @pred (environment tag_t)
:=
    let '(MkStatement _ _ stmt _) := stmt in
    weakest_precondition_statement_pre stmt post
with weakest_precondition_statement_pre
    (stmt: StatementPreT tag_t)
    (post: @pred (environment tag_t))
    : @pred (environment tag_t)
:=
    match stmt with
    | StatBlock _ block =>
      let inter := weakest_precondition_block block (pred_env_popped post) in
      pred_env_pushed inter
    | StatAssignment _ lhs rhs =>
      let inter' := fun '(env_inter', lval) =>
          let inter := fun '(env_inter, rval) =>
              exists env_post,
                  (inl tt, env_post)
                    = update_lvalue tag_t tag lval rval env_inter /\
                  post env_post
          in weakest_precondition_expression rhs inter env_inter'
      in weakest_precondition_expression_lvalue lhs inter'
    | StatMethodCall _ callee type_args args =>
      let inter' := fun '(env_inter', func) =>
          match func with
          | ValObj _ (ValObjFun _ params impl) =>
            let inter := fun '(env_inter, arg_vals) =>
                match impl with
                | ValFuncImplBuiltin _ name obj =>
                  exists env_post val,
                    post env_post /\
                    (inl val, env_post)
                        = eval_builtin_func tag_t tag name obj
                                            type_args arg_vals env_inter
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
    (post: @pred (environment tag_t))
    : @pred (environment tag_t)
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
            exists env_post,
                post env_post /\
                eval_block tag_t tag block env_pre = (inl tt, env_post)
.

Definition weakest_precondition_statement_pre_correct
    (stmt: StatementPreT tag_t)
:=
    forall env_pre post,
        weakest_precondition_statement_pre stmt post env_pre ->
            exists env_post,
                post env_post /\
                eval_statement_pre tag_t tag stmt env_pre = (inl tt, env_post)
.

Definition weakest_precondition_statement_correct
    (stmt: Statement tag_t)
:=
    forall env_pre post,
        weakest_precondition_statement stmt post env_pre ->
            exists env_post,
                post env_post /\
                eval_statement tag_t tag stmt env_pre = (inl tt, env_post)
.

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
      destruct H as [env_post [env_post_fits eval_statement_result]].
      exists env_post.
      split; [exact env_post_fits|].
      rewrite <- eval_statement_result.
      reflexivity.
    - simpl in H.
      apply weakest_precondition_expression_correct in H.
      destruct H as [env_inter' [impl [H eval_expression_result]]].
      destruct impl; try contradiction.
      destruct v; try contradiction.
      apply weakest_precondition_arguments_correct in H.
      destruct H as [env_inter [vals [H eval_arguments_result]]].
      destruct impl; try contradiction.
      destruct H as [env_post [val [env_post_fits eval_builtin_func_result]]].
      exists env_post.
      split; [exact env_post_fits|].
      unfold eval_statement_pre; simpl.
      unfold toss_value.
      unfold eval_method_call; simpl.
      unfold state_bind.
      rewrite eval_expression_result.
      rewrite eval_arguments_result.
      rewrite <- eval_builtin_func_result.
      reflexivity.
    - unfold weakest_precondition_statement_pre in H.
      apply weakest_precondition_expression_lvalue_correct in H.
      destruct H as [env_inter' [lval [H eval_lvalue_result]]].
      apply weakest_precondition_expression_correct in H.
      destruct H as [env_inter [rval [env_inter_prop eval_expression_result]]].
      destruct env_inter_prop as [env_post [update_lvalue_result env_post_fits]].
      exists env_post.
      split; [exact env_post_fits|].
      unfold eval_statement_pre; simpl.
      unfold state_bind.
      rewrite eval_lvalue_result.
      rewrite eval_expression_result.
      rewrite update_lvalue_result.
      reflexivity.
    - simpl in H0.
      unfold pred_env_pushed in H0.
      unfold weakest_precondition_block_correct in H.
      specialize (H (push_scope tag_t env_pre) (pred_env_popped post) H0).
      destruct H as [env_post' [env_post_fits eval_block_result]].
      unfold pred_env_popped in env_post_fits.
      case_eq (pop_scope tag_t env_post');
        intros;
        rewrite H in env_post_fits;
        try contradiction.
      exists e.
      split; [exact env_post_fits|].
      unfold eval_statement_pre.
      fold (eval_block tag_t tag block).
      simpl; unfold state_bind.
      unfold map_env; simpl.
      rewrite eval_block_result.
      unfold lift_env_fn.
      rewrite H.
      reflexivity.
    - simpl in H.
      exists env_pre.
      split; [exact H|].
      reflexivity.
    - unfold weakest_precondition_block_correct; intros.
      unfold weakest_precondition_block in H.
      exists env_pre.
      split; [exact H|].
      reflexivity.
    - unfold weakest_precondition_block_correct.
      intros.
      simpl in H1.
      apply H in H1.
      destruct H1 as [env_inter [H1 eval_statement_result]].
      apply H0 in H1.
      destruct H1 as [env_post [env_post_fits eval_block_result]].
      exists env_post.
      split; [exact env_post_fits|].
      unfold eval_block.
      fold (eval_statement tag_t tag statement).
      fold (eval_block tag_t tag rest).
      simpl; unfold state_bind.
      rewrite eval_statement_result.
      exact eval_block_result.
Qed.
