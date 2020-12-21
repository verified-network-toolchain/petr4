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

Fixpoint weakest_precondition_expression (expr: Expression tag_t) (post_env: @pred (environment tag_t)) (post_val: @pred (Value tag_t)) : @pred (environment tag_t) :=
    pred_false
with weakest_precondition_expression_lvalue (expr: Expression tag_t) (post_env: @pred (environment tag_t)) (post_val: @pred ValueLvalue) : @pred (environment tag_t) :=
    pred_false
.

Lemma weakest_precondition_expression_correct:
    forall env_pre expr post post_val,
        weakest_precondition_expression expr post post_val env_pre ->
            exists env_post val_post,
                post env_post /\
                post_val val_post /\
                eval_expression tag_t tag expr env_pre = (inl val_post, env_post)
.
Proof.
    intros.
    induction expr.
    unfold pred_false in H.
    contradiction.
Qed.

Lemma weakest_precondition_expression_lvalue_correct:
    forall expr env_pre post post_val,
        weakest_precondition_expression_lvalue expr post post_val env_pre ->
            exists env_post val_post,
                post env_post /\
                post_val val_post /\
                eval_lvalue tag_t expr env_pre = (inl val_post, env_post)
.
Proof.
    intros.
    induction expr.
    unfold pred_false in H.
    contradiction.
Qed.

Fixpoint weakest_precondition (stmt: Statement tag_t) (post: @pred (environment tag_t)) : @pred (environment tag_t) :=
    match stmt with
    | MkStatement _ _ stmt' _ =>
      match stmt' with
      | StatBlock _ block =>
        let inter := weakest_precondition_block block (pred_env_popped post) in
        pred_env_pushed inter
      | StatAssignment _ lhs rhs =>
        let inter :=
            fun env_inter =>
            forall rval lval env_post,
                (inl tt, env_post) = update_lvalue tag_t tag lval rval env_inter /\
                post env_post
        in
        let inter' := weakest_precondition_expression rhs inter pred_true in
        weakest_precondition_expression_lvalue lhs inter' pred_true
      (* | StatMethodCall callee type_args args =>
        fun env_pre => *)
      | StatEmpty _ => post
      | _ => pred_false
      end
    end
with weakest_precondition_block (block: Block tag_t) (post: @pred (environment tag_t)) : @pred (environment tag_t) :=
    match block with
    | BlockEmpty _ _ => post
    | BlockCons _ stmt block' =>
      let inter := weakest_precondition_block block' post in
      weakest_precondition stmt inter
    end
.

Lemma weakest_precondition_block_correct:
    forall env_pre block post,
        weakest_precondition_block block post env_pre ->
            exists env_post,
                post env_post /\
                eval_block tag_t tag block env_pre = (inl tt, env_post)
.
Admitted.

Lemma weakest_precondition_correct:
    forall env_pre prog post,
        weakest_precondition prog post env_pre ->
            exists env_post,
                post env_post /\
                eval_statement tag_t tag prog env_pre = (inl tt, env_post)
.
Proof.
    intros.
    destruct prog.
    induction stmt; try (unfold pred_false in H; simpl in H; contradiction).
    - unfold weakest_precondition in H.
      apply weakest_precondition_expression_lvalue_correct in H.
      destruct H as [env_inter [val_rhs [H [_ eval_lvalue_result]]]].
      apply weakest_precondition_expression_correct in H.
      destruct H as [env_post [val_lhs [update_lvalue_result [_ eval_expression_result]]]].
      exists env_post.
      specialize (update_lvalue_result val_lhs val_rhs env_post).
      split.
      * intuition.
      * unfold eval_statement; simpl.
        unfold state_bind.
        rewrite eval_lvalue_result.
        rewrite eval_expression_result.
        easy.
    - simpl weakest_precondition in H.
      unfold pred_env_pushed in H.
      apply weakest_precondition_block_correct in H.
      destruct H as [env_post [env_post_fits eval_block_result]].
      unfold pred_env_popped in env_post_fits.
      case_eq (pop_scope tag_t env_post); intros.
      * rewrite H in env_post_fits.
        exists e.
        split; try easy.
        replace (eval_statement tag_t tag (MkStatement tag_t tags (StatBlock tag_t block) typ))
          with (map_env tag_t (push_scope tag_t);;
                eval_block tag_t tag block;;
                lift_env_fn tag_t (pop_scope tag_t));
          [|reflexivity].
        simpl.
        unfold state_bind.
        simpl.
        rewrite eval_block_result.
        unfold lift_env_fn.
        rewrite H.
        reflexivity.
      * rewrite H in env_post_fits.
        contradiction.
    - exists env_pre.
      simpl in H.
      split; try easy.
Qed.
