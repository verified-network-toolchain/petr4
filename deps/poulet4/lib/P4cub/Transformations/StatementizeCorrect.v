Set Warnings "-custom-entry-overridden".
Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Transformations.Statementize.
Require Export Poulet4.P4cub.BigStep.BigStep
        Poulet4.P4cub.Envn Poulet4.P4cub.Transformations.Lifted.
Import AllCubNotations Env.EnvNotations
       Val.ValueNotations Step.

Ltac if_destr :=
  match goal with
    |- context [if ?trm then _ else _]
    => destruct trm as [? | ?] eqn:?
  end; unfold "===" in *; try contradiction; auto.

Section Correct.
  Context {tags_t : Type}.

  Local Hint Constructors expr_big_step : core.
  Local Hint Constructors stmt_big_step : core.
  Local Hint Constructors lvalue_big_step : core.

  Arguments String.append (*"_p_4_s_e_l_" s*) : simpl never.
  
  Ltac solve_this_stuff :=
    match goal with
    | |- exists eps',
        ⟪ ?pkt, _, ?eps, _, var ?x := ?e @ _ ⟫ ⤋ ⟪ _,C,?pkt ⟫
        /\ ⟨ eps', Var ?x:_ @ _ ⟩ ⇓ ?v
      => (* TODO: fix notation.
        exists !{ x ↦ v;; x ↦ v';; eps }!; split;
        [ apply sbs_seq_cont
            with (pkt' := pkt)
                 (ϵ' := !{ x ↦ v';; eps }!); eauto;
          try eapply sbs_assign; eauto; try reflexivity
        | apply ebs_var; cbn; if_destr ] *) idtac
    end; assumption.
  
  (* Type Soundness for statements
     would be useful for this.
     Knowing [exists] an environment for
     the statement to evaluate to
     (worry about this later). *)
  Lemma expr_semantic_pres : forall (e : Expr.e tags_t) env,
      let '(s, e', _) := TransformExpr e env in
      forall ϵ v pkt fe ctx, (* ctx & fe shouldn't matter. *)
        ⟨ ϵ, e ⟩ ⇓ v ->
        exists ϵ',
          ⟪ pkt , fe , ϵ , ctx , s ⟫ ⤋ ⟪ ϵ' , C , pkt ⟫ /\
          (* packet [pkt] shouldn't change in stmt evalution. *)
          ⟨ ϵ', e' ⟩ ⇓ v (*/\ ϵ ⊆ ϵ' (define sub-env relation) *).
  Proof.
    intro e; induction e using custom_e_ind; intro env;
      try transformExpr_destr;
      try match goal with
          | H: (_,_,_) = (_,_,_) |- _ => inv H
          end;
      intros eps v pkt fe cx Hev; inv Hev; eauto;
        try solve_this_stuff.
    - admit.
    - admit.
  Admitted.
End Correct.
