Require Import Syntax.
Require Import Eval.
Require Import Monads.Monad.
Require Import Monads.State.
Require Import Step.
Require Import Typed.
Require Import Environment.
Open Scope monad_scope.
Open Scope monad.

Require Import IntExample.

Definition pred := environment tag_t -> Prop.

(* A predicate that is true for all environments that are the result of
   pushing an empty scope in an environment satisfying the parameter. *)
Definition pred_env_pushed (p: pred) (env: environment tag_t) :=
    exists env', env = push_scope tag_t env' /\ p env'
.

(* A predicate that is true for all environments that, when popped, yield
   a valid environment that satisfies the parameter. *)
Definition pred_env_popped (p: pred) (env: environment tag_t) :=
    exists env', pop_scope tag_t env = Some env' /\ p env' 
.

(* The predicate that holds for all environments. *)
Definition pred_trivial := fun env : environment tag_t => True.

(* A Hoare triple for statements, implementing total correctness: for all
   environments that satisfy the precondition, there exists an environment
   that is the result of the correct execution of the program, and this
   environment satisfies the postcondition. *)
Definition hoare_triple
    (pre: pred)
    (stmt: Statement tag_t)
    (post: pred)
:=
    forall env_pre,
        pre env_pre ->
        exists env_post,
            post env_post /\
            eval_statement tag_t tag stmt env_pre = (inl tt, env_post)
.

(* A Hoare triple for total correctness of a block of statements. *)
Definition hoare_triple_block
    (pre: pred)
    (block: Block tag_t)
    (post: pred)
:=
    forall env_pre,
        pre env_pre ->
        exists env_post,
            post env_post /\
            eval_block tag_t tag block env_pre = (inl tt, env_post)
.

(* If a statement is a block statement, then correctness of the block w.r.t.
   the pushed precondition and popped postcondition implies correctness of the
   statement itself. *)
Lemma hoare_lift_block
    (pre: pred)
    (block: Block tag_t)
    (post: pred)
:
    hoare_triple_block (pred_env_pushed pre) block (pred_env_popped post) ->
        hoare_triple pre (MkStatement tag_t tag (StatBlock tag_t block) StmUnit) post
.
Proof.
    intros H env_pre env_pre_fits.
    assert (pred_env_pushed pre (push_scope tag_t env_pre)) as pushed_env_pre';
        [exists env_pre; easy|].
    specialize (H (push_scope tag_t env_pre) pushed_env_pre').
    destruct H as [env_post' [env_post'_fits eval_block_result]].
    destruct env_post'_fits as [env_post [Heqenv_post post_env_fits]].
    exists env_post.
    split; [exact post_env_fits|].
    (* Essentially this replacement works because we are replacing part of the
       current goal with a slightly more unfolded version. I would like to
       eliminate it so that the proof depends less on the implementation, but
       the "unfold" tactic seems way too coarse to get there... *)
    replace (eval_statement tag_t tag (MkStatement tag_t tag (StatBlock tag_t block) StmUnit))
        with (map_env tag_t (push_scope tag_t);;
              eval_block tag_t tag block;;
              lift_env_fn tag_t (pop_scope tag_t));
        [|reflexivity].
    simpl; unfold state_bind.
    simpl; rewrite eval_block_result.
    unfold lift_env_fn; rewrite Heqenv_post.
    reflexivity.
Qed.

(* A Hoare triple holds for an empty block if the pre- and postcondition are
   the same. *)
Lemma hoare_block_empty
    (pre: pred)
:
    hoare_triple_block pre (BlockEmpty tag_t tag) pre
.
Proof.
    unfold hoare_triple_block; intros.
    exists env_pre.
    easy.
Qed.

(* A weaker version of the Hoare rule for sequential composition, but with
   just one statement on the left. If the postcondition of the Hoare triple
   for the statement matches the precondition of the Hoare triple for the
   remaining block, we can get a Hoare triple for the block. *)
Lemma hoare_block_nonempty
    (pre: pred)
    (stmt: Statement tag_t)
    (inter: pred)
    (block: Block tag_t)
    (post: pred)
:
    hoare_triple pre stmt inter ->
    hoare_triple_block inter block post ->
    hoare_triple_block pre (BlockCons tag_t stmt block) post
.
Proof.
    intros H H'.
    unfold hoare_triple_block; intros env_pre env_pre_fits.
    destruct (H env_pre env_pre_fits)
        as [env_inter [inter_env_fits eval_statement_result]].
    destruct (H' env_inter inter_env_fits)
        as [env_post [post_env_fits eval_block_result]].
    exists env_post; split; [exact post_env_fits|]. 
    replace (eval_block tag_t tag (BlockCons tag_t stmt block))
        with (eval_statement tag_t tag stmt ;; eval_block tag_t tag block);
        [|reflexivity].
    simpl; unfold state_bind.
    rewrite eval_statement_result.
    exact eval_block_result.
Qed.

Definition pred_good := fun env => env = good_env.

Lemma intparser_state_correct:
    hoare_triple pred_good (MkStatement tag_t tag (StatBlock tag_t (states_to_block tag_t tag body)) StmUnit) pred_trivial
.
    apply hoare_lift_block.
    simpl states_to_block.
    apply hoare_block_nonempty with (inter := pred_env_popped pred_trivial).
    2:{ apply hoare_block_empty. }
    (* At this point we need something to prove a Hoare triple about
       extract_stmt, so probably some new tooling above. *)
Admitted.
