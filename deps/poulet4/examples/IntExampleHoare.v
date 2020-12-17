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

Fixpoint pred_list {A: Type} (elems: list A) (preds: list pred) :=
    match (elems, preds) with
    | (List.nil, List.nil) => True
    | (elem :: elems', pred :: preds') =>
      pred elem /\ pred_list elems' preds'
    | _ => False
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
            constraint result /\
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

(* Hoare triple for the evaluation of arguments. In an environment satisfying
 * the precondition and given expressions satisfying exprs_pre, yields an
   environment and values satisfying the postcondition and exprs_post. *)
Definition hoare_triple_arguments
    (pre: pred)
    (exprs: list (option (Expression tag_t)))
    (params: list P4Parameter)
    (exprs_pre: list pred)
    (exprs_post: list pred)
    (post: pred)
:=
    forall env_pre,
        pre env_pre ->
        pred_list exprs exprs_pre ->
        exists results env_post,
            post env_post /\
            pred_list results exprs_post /\
            eval_arguments tag_t tag params exprs env_pre = (inl results, env_post)
.

(* Trivializes evaluation of an empty list of arguments. *)
Lemma hoare_triple_arguments_base (pre: pred):
    hoare_triple_arguments pre List.nil List.nil List.nil List.nil pre
.
Proof.
    intros env_pre env_pre_fits exprs_pre_fit.
    exists List.nil, env_pre.
    repeat split.
    exact env_pre_fits.
Qed.

(* Simplifies a Hoare triple for argument evaluation when the first argument
   is omitted, by decomposing it into an assertion that this first value is
   allowed to be omitted by the preconditions on parameters and a Hoare triple
   abou thte remaining arguments; there is no intermediate environment. *)
Lemma hoare_triple_arguments_unfold_omitted
    (pre: pred)
    (expr: Expression tag_t)
    (exprs: list (option (Expression tag_t)))
    (param: P4Parameter)
    (params: list P4Parameter)
    (expr_pre: pred)
    (exprs_pre: list pred)
    (expr_post: pred)
    (exprs_post: list pred)
    (post: pred)
:
    expr_post None ->
    hoare_triple_arguments pre exprs params exprs_pre exprs_post post ->
    hoare_triple_arguments pre (None :: exprs) (param :: params) (expr_pre :: exprs_pre) (expr_post :: exprs_post) post
.
Proof.
    intros expr_post_fits H_rest env_pre env_pre_fits exprs_pre_fit.
    destruct exprs_pre_fit as [expr_pre_fits exprs_pre_fit].
    specialize (H_rest env_pre env_pre_fits exprs_pre_fit).
    destruct H_rest as [exprs_results [env_post [env_post_fits [exprs_post_fit eval_arguments_result]]]].
    exists (None :: exprs_results), env_post.
    repeat split; try easy.
    simpl eval_arguments.
    unfold state_bind.
    rewrite eval_arguments_result.
    reflexivity.
Qed.

(* Simplifies a Hoare triple for argument evaluation when the first argument
   is an out-parameter, by decomposing it into a Hoare triple about this first
   parameter and a Hoare triple about the remaining arguments, with the
   environment inbetween described by the predicate inter. *)
Lemma hoare_triple_arguments_unfold_lvalue
    (pre: pred)
    (expr: Expression tag_t)
    (exprs: list (option (Expression tag_t)))
    (opt: bool)
    (typ: P4Type)
    (variable: String.t)
    (params: list P4Parameter)
    (expr_pre: pred)
    (exprs_pre: list pred)
    (inter: pred)
    (expr_post: pred)
    (exprs_post: list pred)
    (post: pred)
:
    let expr_post' := fun val => expr_post (Some (ValLvalue tag_t val)) in
    hoare_triple_expression_lvalue pre expr expr_post' inter ->
    hoare_triple_arguments inter exprs params exprs_pre exprs_post post ->
    hoare_triple_arguments pre (Some expr :: exprs) (MkParameter opt Typed.Out typ variable :: params) (expr_pre :: exprs_pre) (expr_post :: exprs_post) post
.
Proof.
    intros expr_post' H_first H_rest env_pre env_pre_fits exprs_pre_fit.
    specialize (H_first env_pre env_pre_fits).
    destruct H_first as [env_inter [expr_result [env_inter_fits [expr_post'_fits eval_lvalue_result]]]].
    destruct exprs_pre_fit as [expr_pre_fits exprs_pre_fit].
    specialize (H_rest env_inter env_inter_fits exprs_pre_fit).
    destruct H_rest as [exprs_results [env_post [env_post_fits [exprs_post_fit eval_arguments_result]]]].
    exists ((Some (ValLvalue tag_t expr_result)) :: exprs_results).
    exists env_post.
    repeat split; try easy.
    simpl eval_arguments.
    unfold state_bind.
    rewrite eval_lvalue_result; simpl.
    rewrite eval_arguments_result; simpl.
    reflexivity.
Qed.

(* Simplifies a Hoare triple for argument evaluation when the first argument
   is an in-parameter, by decomposing it into a Hoare triple about this first
   parameter and a Hoare triple about the remaining arguments, with the
   environment inbetween described by the predicate inter. *)
Lemma hoare_triple_arguments_unfold_value
    (pre: pred)
    (expr: Expression tag_t)
    (exprs: list (option (Expression tag_t)))
    (opt: bool)
    (typ: P4Type)
    (variable: String.t)
    (params: list P4Parameter)
    (expr_pre: pred)
    (exprs_pre: list pred)
    (inter: pred)
    (expr_post: pred)
    (exprs_post: list pred)
    (post: pred)
:
    let expr_post' := fun val => expr_post (Some val) in
    hoare_triple_expression pre expr expr_post' inter ->
    hoare_triple_arguments inter exprs params exprs_pre exprs_post post ->
    hoare_triple_arguments pre (Some expr :: exprs) (MkParameter opt Typed.In typ variable :: params) (expr_pre :: exprs_pre) (expr_post :: exprs_post) post
.
Proof.
    intros expr_post' H_first H_rest env_pre env_pre_fits exprs_pre_fit.
    specialize (H_first env_pre env_pre_fits).
    destruct H_first as [env_inter [expr_result [env_inter_fits [expr_post'_fits eval_expression_result]]]].
    destruct exprs_pre_fit as [expr_pre_fits exprs_pre_fit].
    specialize (H_rest env_inter env_inter_fits exprs_pre_fit).
    destruct H_rest as [exprs_results [env_post [env_post_fits [exprs_post_fit eval_arguments_result]]]].
    exists (Some expr_result :: exprs_results).
    exists env_post.
    repeat split; try easy.
    simpl eval_arguments.
    unfold state_bind.
    rewrite eval_expression_result.
    rewrite eval_arguments_result.
    reflexivity.
Qed.

(* A Hoare triple for builtin function calls. All calls in an environment
   satisfying pre and with argument values satisfying the exprs_pre will yield
   a value satisfying expr_post, and an environment satisfying post. *)
Definition hoare_triple_builtin_function
    (pre: pred)
    (name: String.t)
    (obj: ValueLvalue)
    (type_args: list P4Type)
    (values_pre: list pred)
    (value_post: pred)
    (post: pred)
:=
    forall obj type_args args env_pre,
        pre env_pre ->
        pred_list args values_pre ->
        exists env_post result,
            value_post result /\
            post env_post /\
            eval_builtin_func tag_t tag name obj type_args args env_pre = (inl result, env_post)
.

(* To prove a Hoare triple for a method call, you need to show that
   (1) that the evaluation of the callee expression in an environment 
       satisfying the precondition will take you to an environment described 
       by intermediate environment predicate inter; and
   (2) that, given the arguments satisfy the predicates in exprs_pre,
       evaluating the arguments in an environment satisfying inter will take 
       you to an environment described by another predicate, inter', with
       the resulting values described by the predicates in exprs_post; and
   (3) that evaluating the function call in an environment satisfying inter',
       and with arguments satisfyiing the predicates in exprs_post will lead
       to an environment satisfying the postcondition. 

    Caveat emptor: for now only builtin methods are supported. *)
Lemma hoare_lift_method_call
    (pre: pred)
    (callee: Expression tag_t)
    (inter: pred)
    (type_args: list P4Type)
    (exprs: list (option (Expression tag_t)))
    (exprs_pre: list pred)
    (exprs_post: list pred)
    (inter': pred)
    (post: pred)
:
    pred_list exprs exprs_pre ->
    let validate_call := fun val => match val with
    | ValObj _ (ValObjFun _ params (ValFuncImplBuiltin _ name obj)) =>
        hoare_triple_arguments inter exprs params exprs_pre exprs_post inter' /\
        hoare_triple_builtin_function inter' name obj type_args exprs_post pred_trivial post
    | _ => False
    end in
    hoare_triple_expression pre callee validate_call inter ->
    (| pre |) (MkStatement tag_t tag (StatMethodCall tag_t callee type_args exprs) StmVoid) (| post |)
.
Proof.
    intros.
    intros env_pre env_pre_fits.
    specialize (H0 env_pre env_pre_fits).
    destruct H0 as [env_inter [func [env_inter_fits [validate_call_fits eval_expression_result]]]].
    unfold validate_call in validate_call_fits; clear validate_call.
    destruct func; try contradiction.
    destruct v; try contradiction.
    destruct impl; try contradiction.
    destruct validate_call_fits as [H_arguments H_call].
    specialize (H_arguments env_inter env_inter_fits H).
    destruct H_arguments as [results [env_inter' [env_inter'_fits [exprs_post_fit eval_arguments_result]]]].
    specialize (H_call caller type_args results env_inter' env_inter'_fits exprs_post_fit).
    destruct  H_call as [env_post [result [_ [env_post_fits eval_builtin_func_result]]]].
    exists env_post.
    split; try easy.
    unfold eval_statement, toss_value, eval_method_call; simpl.
    unfold state_bind.
    rewrite eval_expression_result; simpl.
    rewrite eval_arguments_result; simpl.
    rewrite eval_builtin_func_result; simpl.
    reflexivity.
Qed.

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
Proof.
    apply hoare_lift_block.
    simpl states_to_block.
    apply hoare_block_nonempty with (inter := pred_env_popped pred_trivial).
    2:{ apply hoare_block_empty. }

    (* At this point, you could run
    apply hoare_lift_method_call with
        (inter := pred_env_pushed pred_good)
        (exprs_pre := pred_trivial :: List.nil)
        (exprs_post := pred_trivial :: List.nil)
        (inter' := pred_trivial); try easy.
    *)

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
