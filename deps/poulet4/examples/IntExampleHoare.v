Require Import Syntax.
Require Import Eval.
Require Import Monads.Monad.
Require Import Monads.State.
Require Import Step.
Require Import Typed.
Require Import Environment.
Require Import Strings.String.
Require Import Vectors.VectorDef.
Require Import ZArith.BinIntDef.
Import VectorNotations.
Open Scope vector_scope.
Open Scope monad_scope.
Open Scope monad.
Open Scope list_scope.
Open Scope Z_scope.
Require Import IntExample.

Definition pred {A: Type} := A -> Prop.

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
Definition pred_trivial {A: Type} := fun a : A => True.

Fixpoint pred_list {A: Type} (elems_preds: list (A * pred)) :=
    match elems_preds with
    | List.nil => True
    | (elem, pred) :: elems_preds' =>
      pred elem /\ pred_list elems_preds'
    end
.

Declare Scope hoare_scope.
Delimit Scope hoare_scope with hoare.

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

Notation "(| P |) s (| Q |)" := (hoare_triple P s Q)
  (at level 100, s at next level, right associativity) : hoare_scope.

Notation "x |-> v" := (MapsToE tag_t x v)
    (at level 100, v at next level, right associativity) : hoare_scope.

Notation "P &&& Q" := (fun env => P env /\ Q env)
    (at level 100, Q at next level, right associativity) : hoare_scope.

Open Scope hoare_scope.
Open Scope string_scope.

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

(* A Hoare triple for total correctness of an expression, including the
   possibility to make assertions about the computed value. *)
Definition hoare_triple_expression
    (pre: pred)
    (expr: Expression tag_t)
    (constraint: pred)
    (post: pred)
:=
    forall env_pre,
        pre env_pre ->
        exists env_post result,
            post env_post /\
            constraint result /\
            eval_expression tag_t tag expr env_pre = (inl result, env_post)
.

(* Same as above, but for the expression as an lvalue. *)
Definition hoare_triple_expression_lvalue
    (pre: pred)
    (expr: Expression tag_t)
    (constraint: pred)
    (post: pred)
:=
    forall env_pre,
        pre env_pre ->
        exists env_post result,
            post env_post /\
            constraint (ValLvalue tag_t result) /\
            eval_lvalue tag_t expr env_pre = (inl result, env_post)
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
        (| pre |) (MkStatement tag_t tag (StatBlock tag_t block) StmUnit) (| post |)
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
    (| pre |) stmt (| inter |) ->
    (* hoare_triple pre stmt post -> *)
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

Fixpoint hoare_triples_arguments
    (pre: pred)
    (constrained_exprs: list (option (Expression tag_t) * P4Parameter * pred * pred))
    (post: pred)
:=
    match constrained_exprs with
    | List.nil => forall env, pre env -> post env
    | constrained_expr :: constrained_exprs' =>
      let '(maybe_expr, param, constraint_pre, constraint_post) := constrained_expr in
      constraint_pre maybe_expr ->
      match maybe_expr with
      | None =>
        constraint_post None /\
        hoare_triples_arguments pre constrained_exprs' post
      | Some expr =>
        exists inter,
            let constraint_post' := fun val => constraint_post (Some val) in
            let '(MkParameter _ dir _ _) := param in
            match dir with
            | Typed.In => hoare_triple_expression pre expr constraint_post' inter
            | Typed.Out => hoare_triple_expression_lvalue pre expr constraint_post' inter
            (* TODO: Implement InOut and Directionless *)
            | _ => False
            end /\
            hoare_triples_arguments inter constrained_exprs' post
      end
    end
.

Fixpoint project {A B: Type} (l: list (A * B)) :=
    match l with
    | List.nil => (List.nil, List.nil)
    | (a, b) :: l' =>
      let (ll, lr) := project l' in
      (a :: ll, b :: lr)
    end
.

Definition hoare_triple_arguments
    (pre: pred)
    (exprs_params_pre_post: list (option (Expression tag_t) * P4Parameter * pred * pred))
    (post: pred)
:=
    forall env_pre,
        pre env_pre ->
        let (exprs_params_pre, constraints_post) := project exprs_params_pre_post in
        let (exprs_params, constraints_pre) := project exprs_params_pre in
        let (exprs, params) := project exprs_params in
        pred_list (List.combine exprs constraints_pre) ->
        exists constrained_results results env_post,
            project constrained_results = (results, constraints_post) /\
            post env_post /\
            pred_list constrained_results /\
            eval_arguments tag_t tag params exprs env_pre = (inl results, env_post)
.

(* This doesn't compile: where is hoare_triples_expressions? *)

(* Lemma hoare_lift_arguments
    (pre: pred)
    (constrained_exprs: list (option (Expression tag_t) * pred * pred))
    (post: pred)
:
    hoare_triples_expressions pre constrained_exprs post ->
        hoare_triple_arguments pre constrained_exprs post
.
Proof.
    generalize pre as pre'.
    unfold hoare_triple_arguments.
    induction constrained_exprs;
    intros pre' H env_pre env_pre_fits.
    - exists List.nil, List.nil, env_pre.
      simpl; repeat split.
      f_equal; try reflexivity.
      exact (H env_pre env_pre_fits).
    - intros.
      destruct a as [[maybe_expr expr_pre] expr_post]; intros.
      remember (project constrained_exprs) as p; destruct p as (constrained_exprs_pre, constraints_post).
      remember (project constrained_exprs_pre) as p; destruct p as (exprs, constraints_pre).
      simpl project; rewrite <- Heqp.
      intros.
      destruct H0 as [maybe_expr_fits constrained_exprs_pre_fit].
      simpl in H.
      specialize (H maybe_expr_fits).
      destruct maybe_expr.
      * destruct H as [inter [H_first H_rest]].
        specialize (H_first env_pre env_pre_fits).
        destruct H_first as [env_inter [result [env_inter_fits [expr_inter_fits eval_expression_result]]]].
        specialize (IHconstrained_exprs inter H_rest env_inter env_inter_fits constrained_exprs_pre_fit).
        destruct IHconstrained_exprs as [constrained_results [results [env_post H]]].
        destruct H as [Heqp1 [env_post_fits [constrained_results_fit eval_arguments_result]]].
        exists ((Some result, expr_post) :: constrained_results).
        exists (Some result :: results).
        exists env_post; simpl.
        rewrite <- Heqp0; simpl.
        rewrite Heqp1.
        repeat split; try easy.
        unfold state_bind.
        rewrite eval_expression_result.
        rewrite eval_arguments_result.
        reflexivity.
      * destruct H as [expr_post_fits H_rest].
        specialize (IHconstrained_exprs pre' H_rest env_pre env_pre_fits constrained_exprs_pre_fit).
        destruct IHconstrained_exprs as [constrained_results [results [env_post H]]].
        destruct H as [Heqp1 [env_post_fits [constrained_results_fit eval_arguments_result]]].
        exists ((None, expr_post) :: constrained_results).
        exists (None :: results).
        exists env_post; simpl.
        rewrite <- Heqp0; simpl.
        rewrite Heqp1.
        repeat split; try easy.
        unfold state_bind.
        rewrite eval_arguments_result.
        reflexivity.
Qed. *)

Definition hoare_triple_builtin_function
    (pre: @pred (environment tag_t))
    (name: String.t)
    (obj: ValueLvalue)
    (type_args: list P4Type)
    (constraints: list (@pred (option (Value tag_t))))
    (constraint: @pred (Value tag_t))
    (post: @pred (environment tag_t))
:= True
(* This does not typecheck, because eval_builtin_func takes expressions instead of arguments.
    forall env_pre obj type_args constrained_args args,
        pre env_pre ->
        project constrained_args = (args, constraints) ->
        pred_list constrained_args ->
        exists env_post result,
            constraint result /\
            post env_post /\
            eval_builtin_func tag_t tag name obj type_args args env_pre = (inl result, env_post) *)
.

(* Lemma hoare_lift_method_call
    (pre: pred)
    (callee: Expression tag_t)
    (inter: pred)
    (type_args: list P4Type)
    (constrained_args: list (option (Expression tag_t) * pred * (@pred (option (Value tag_t)))))
    (inter': pred)
    (post: pred)
:
    let (constrained_args_pre, constraints_post) := project constrained_args in
    let (args, constraints_pre) := project constrained_args_pre in
    let is_call := 
        fun val => match val with
        | ValObj _ (ValObjBuiltinFun _ name obj) =>
            hoare_triple_builtin_function inter' name obj type_args constraints_post pred_trivial post
        | _ => False
        end in
    hoare_triple_expression pre callee is_call inter ->
    hoare_triple_arguments inter' constrained_args inter' ->
    hoare_triple pre (MkStatement tag_t tag (StatMethodCall tag_t callee type_args args) StmVoid) post
.

Admitted. *)

(*
Proof.
    intros.
    destruct H as [inter [inter' [constraints [Hexpr Hargs]]]].
    unfold hoare_triple.
    intros env_pre env_pre_fits.
    specialize (Hexpr env_pre env_pre_fits).
    destruct Hexpr as [env_inter [result [env_inter_fits [Hcall eval_expression_result]]]].
    destruct result; try contradiction.
    destruct v; try contradiction.
    specialize (Hargs env_inter env_inter_fits).
Admitted. *)

Definition pred_good := fun env => env = good_env.

Lemma hoare_transitivity:
    forall env env' (P: pred) (P': pred) (Q: pred) (Q': pred) stmt ,
    (P' env -> P env) ->
    (Q env' -> Q' env') ->
    (| P |) stmt (| Q |) ->
    (| P' |) stmt (| Q' |).
Proof.
Admitted.

Definition x : Expression tag_t := MkExpression _ tt (ExpName _ (BareName "x")) TypInteger Directionless.
Definition one : Expression tag_t := MkExpression _ tt (ExpInt _ (MkP4Int _ tt Z.one None)) TypInteger Directionless.
Definition x_p1 : Expression tag_t := MkExpression _ tt (ExpBinaryOp _ Plus (x, one)) TypInteger Directionless.

Definition one_v : Value tag_t := ValBase _ (ValBaseInteger _ Z.one).

Definition x_p1_stmt : Statement tag_t := MkStatement _ tt (StatAssignment _ x x_p1) StmUnit.

Lemma hoare_spc_inc : 
    forall v v_inner v' v_inner',
    v = ValBase _ (ValBaseInteger _ v_inner) ->
    v' = ValBase _ (ValBaseInteger _ v_inner') ->
    (| "x" |-> v |) x_p1_stmt (| "x" |-> v' |) /\ v_inner' = Z.add v_inner 1.
Proof.
Admitted.

Lemma Z_incr_increasing:
    forall n,
    Z.gtb n 0 = true -> 
    Z.gtb (Z.succ n) 0 = true.
Proof.
    intros.
    induction n.
        - unfold Z.gtb in *. simpl in *. auto.
        - unfold Z.gtb in *. simpl in *. auto.
        - 
            exfalso.
            eapply Bool.eq_true_false_abs with (b := false).
            unfold Z.gtb in *. 
            simpl in *.
            auto.
            auto.
Qed.
            


Lemma hoare_incr_increasing :
    forall v v_inner v' v_inner',
    v = ValBase _ (ValBaseInteger _ v_inner) ->
    Z.gtb v_inner 0 = true ->
    v' = ValBase _ (ValBaseInteger _ v_inner') ->
    (| "x" |-> v |) x_p1_stmt (| "x" |-> v' |) /\ Z.gtb v_inner' 0 = true.
Proof.
    intros.
    split.
    assert (H2 := hoare_spc_inc). 
    eapply hoare_transitivity with (P := "x" |-> v).
    specialize (H2 v v_inner v' v_inner').
    specialize (H2 H H1).
    assert (H3 := H2).
    3 : {
        eapply H2; eauto.
    }
    - auto.
    - auto.
    -
        assert (H2 := hoare_spc_inc). 
        specialize (H2 v v_inner v' v_inner').
        specialize (H2 H H1).
        destruct H2 as [_ H2].
        rewrite H2.
        apply Z_incr_increasing.
        assumption.
    Grab Existential Variables.
    exact List.nil.
    exact List.nil.
Qed.


Lemma hoare_extract_stmt: 
    forall out_expr (out_name: string) dir v pkt_value pkt_value' bits b1 b2,
    out_expr = MkExpression _ tt (ExpName _ (BareName out_name)) (TypInt 2) dir -> 
    pkt_value = ValObj _ (ValObjPacket _ (b1 :: b2 :: bits)) ->
    (| out_name |-> v &&& ("pkt" |-> pkt_value) |) 
        build_extract_stmt (TypInt 2) out_expr 
    (| out_name |-> out_value &&& ("pkt" |-> pkt_value') |) /\
    pkt_value' = ValObj _ (ValObjPacket _ bits) /\
    out_value  = ValBase _ (ValBaseInt _ 2 [b1 ; b2]).
Proof.
Admitted.

Lemma MapsToE_push_scope:
    forall s v (env: Environment.environment tag_t),
    MapsToE _ s v env ->
    MapsToE _ s v (push_scope _ env).
Proof.
Admitted.

Lemma find_env_corr_2 : 
    forall s v (env : Environment.environment tag_t) (scope : Environment.scope tag_t) env_pre env_post, 
    Environment.MapsToE _ s v env ->
      env = (env_pre ++ (scope :: env_post))%list ->
      Environment.find_environment _ s env = (inl v, env).
Proof.
Admitted.


Lemma intparser_state_correct:
    hoare_triple pred_good (MkStatement tag_t tag (StatBlock tag_t (states_to_block tag_t tag body)) StmUnit) pred_trivial
.
    apply hoare_lift_block.
    simpl states_to_block.
    apply hoare_block_nonempty with (inter := pred_env_popped pred_trivial).
    2:{ apply hoare_block_empty. }

    unfold extract_stmt.

    eapply hoare_transitivity.
    3 : {
        eapply hoare_extract_stmt.
        - unfold output_expr. auto.
        - eauto.
    }
    -
        intros.
        unfold pred_env_pushed, pred_good in *.
        destruct H as [env' [HPS EGE]].
        rewrite HPS.
        split.
        --
            eapply MapsToE_push_scope.
            unfold good_env in *.
            rewrite EGE.
            eapply MapsToES.
            unfold top_scope.
            apply Environment.MapsToSI.
            --- apply String.eqb_neq. auto.
            --- apply Environment.MapsToSE.
        -- 
            eapply MapsToE_push_scope.
            unfold good_env in *.
            rewrite EGE.
            eapply MapsToES.
            unfold top_scope.
            apply Environment.MapsToSE.
          
    -
        intros.
        unfold pred_env_popped, pred_trivial.
Admitted.

Lemma intparser_state_correct_2:
    forall out_expr dir v pkt_value pkt_value' bits b1 b2,
    out_expr = MkExpression _ tt (ExpName _ (BareName "out")) (TypInt 2) dir -> 
    pkt_value = ValObj _ (ValObjPacket _ (b1 :: b2 :: bits)) ->
    (| "output" |-> v &&& ("pkt" |-> pkt_value) |) 
        MkStatement tag_t tag (StatBlock tag_t (states_to_block tag_t tag body)) StmUnit 
    (| "output" |-> out_value &&& ("pkt" |-> pkt_value') |) /\
    pkt_value' = ValObj _ (ValObjPacket _ bits) /\
    out_value  = ValBase _ (ValBaseInt _ 2 [b1 ; b2]).
Proof.
    intros.
    split.
    -
        apply hoare_lift_block.
        simpl states_to_block.
        apply hoare_block_nonempty with (inter := pred_env_popped (("output" |-> out_value) &&& ("pkt" |-> pkt_value'))).
        2:{ 
            apply hoare_block_empty. 
        }

        eapply hoare_transitivity.
        3 : {
            eapply hoare_extract_stmt.
            -- unfold output_expr. eauto.
            -- eauto.
        }

        -- 
            intros. 
            unfold pred_env_pushed in H1.
            destruct H1 as [env'' [H1 H2]].
            unfold push_scope in *.
            rewrite H1.
            split.
            destruct H2 as [H2 H3].
            --- eapply MapsToE_push_scope. eauto.
            --- eapply MapsToE_push_scope. apply H2.
        --
            intros.
            unfold pred_env_popped in *.
            (* exact ?env'. *)
Admitted.
