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
      replace (eval_statement_pre tag_t tag (StatBlock tag_t block))
         with (map_env tag_t (push_scope tag_t);;
               eval_block tag_t tag block;;
               lift_env_fn tag_t (pop_scope tag_t));
         [|reflexivity]; simpl.
      unfold state_bind; simpl.
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
      replace (eval_block tag_t tag (BlockCons tag_t statement rest))
         with (eval_statement tag_t tag statement;;
               eval_block tag_t tag rest);
         [|reflexivity]; simpl.
      unfold state_bind; simpl.
      rewrite eval_statement_result.
      exact eval_block_result.
Qed.
