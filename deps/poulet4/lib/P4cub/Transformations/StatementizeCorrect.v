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
  Local Hint Resolve Env.bind_sound : core.
  
  Arguments String.append (*"_p_4_s_e_l_" s*) : simpl never.

  Ltac triplet_inv :=
    match goal with
    | H: (_,_,_) = (_,_,_) |- _ => inv H
    end.
  
  Ltac solve_this_stuff :=
    match goal with
    | |- exists eps',
        ⟪ ?pkt, _, ?eps, _, _ ⟫ ⤋ ⟪ _,C,?pkt ⟫
        /\ ⟨ eps', Var ?x:_ @ _ ⟩ ⇓ ?v
      => exists !{ x ↦ v;; eps }!; eauto
    end; assumption.

  Ltac solve_this_stuff_with eps v :=
    match goal with
    | |- exists eps',
        ⟪ ?pkt, _, _, _, _ ⟫ ⤋ ⟪ _,C,?pkt ⟫
        /\ ⟨ eps', Var ?x:_ @ _ ⟩ ⇓ _
      => exists !{ x ↦ v;; eps }!; eauto 6
    end.

  (* Type Soundness for statements
     would be useful for this.
     Knowing [exists] an environment for
     the statement to evaluate to
     (worry about this later). *)
  Lemma expr_semantic_pres : forall (e : Expr.e tags_t) v ϵ,
      ⟨ ϵ, e ⟩ ⇓ v ->
      forall env pkt fe ctx, (* ctx & fe shouldn't matter *)
        let '(s, e', _) := TransformExpr e env in
        exists ϵ',
          ⟪ pkt , fe , ϵ , ctx , s ⟫ ⤋ ⟪ ϵ' , C , pkt ⟫ /\
          (* packet [pkt] shouldn't change in stmt evalution. *)
          ⟨ ϵ', e' ⟩ ⇓ v (*/\ ϵ ⊆ ϵ' (define sub-env relation) *).
  Proof.
    intros ? ? ? ebs;
      induction ebs
      as [ eps b i 
         | eps w n i
         | eps w z i
         | eps x t i v Hxv
         | eps e hi lo i v v' Hslice Hev IHev
         | eps t e i v v' Hcast Hev IHev
         | eps err i
         | eps mk i
         | eps t op e i v v' Huop Hev IHev
         | eps t op e1 e2 i v v1 v2 Hbop Hev1 IHev1 Hev2 IHev2
         | eps t e x i v v' Hmem Hev IHev
         | eps es i vs Hevs IHevs
         | eps es i vs Hevs IHevs
         | eps es e i b vs Hevs IHevs Hev IHev
         | eps ts es ni i vss Hevsss IHevsss
         | eps e i n ni ts vss b vs Haccess Hevss IHevss
         ] using custom_expr_big_step_ind;
      intros env pkt fe cx; try transformExpr_destr;
        unfold decl_var_env in *; cbn in *; try triplet_inv;
          cbn in *; eauto; try solve_this_stuff.
    - specialize IHev with env pkt fe cx.
      transformExpr_destr_hyp; triplet_inv.
      destruct IHev as (eps' & Hs & He).
      solve_this_stuff_with eps' v'.
    - specialize IHev with env pkt fe cx.
      transformExpr_destr_hyp; triplet_inv.
      destruct IHev as (eps' & Hs & He).
      solve_this_stuff_with eps' v'.
    - specialize IHev with env pkt fe cx.
      transformExpr_destr_hyp; triplet_inv.
      destruct IHev as (eps' & Hs & He).
      solve_this_stuff_with eps' v'.
    - specialize IHev1 with env pkt fe cx.
      transformExpr_destr_hyp.
      specialize IHev2 with t1 pkt fe cx.
      transformExpr_destr_hyp; triplet_inv.
      destruct IHev1 as (eps'1 & Hs1 & He1).
      destruct IHev2 as (eps'2 & Hs2 & He2).
      solve_this_stuff_with eps'2 v; intuition.
      apply sbs_seq_cont with eps'2 pkt.
      + apply sbs_seq_cont with eps'1 pkt; auto.
        (* TODO: need helper lemmas
         about environments and
         statement evalution. *) admit.
      + repeat econstructor; eauto.
        (* TODO: need helper lemmas
         about environments and
         expression evalution. *) admit.
    - specialize IHev with env pkt fe cx.
      transformExpr_destr_hyp; triplet_inv.
      destruct IHev as (eps' & Hs & He); eauto.
    - (* Has a similar problem to
         binary operation case. *)
      admit.
    - (* Has a similar problem to
         binary operation case. *)
      admit.
    - (* Has a similar problem to
         binary operation case. *)
      admit.
    - (* Has a similar problem to
         binary operation case. *)
      admit.
    - specialize IHevss with env pkt fe cx.
      transformExpr_destr_hyp; triplet_inv.
      destruct IHevss as (eps' & Hs & He); eauto.
  Admitted.
End Correct.

(* Old formulation has the same problem.
  Lemma expr_semantic_pres : forall (e : Expr.e tags_t) env,
      let '(s, e', _) := TransformExpr e env in
      forall ϵ v pkt fe ctx, (* ctx & fe shouldn't matter. *)
        ⟨ ϵ, e ⟩ ⇓ v ->
        exists ϵ',
          ⟪ pkt , fe , ϵ , ctx , s ⟫ ⤋ ⟪ ϵ' , C , pkt ⟫ /\
          (* packet [pkt] shouldn't change in stmt evalution. *)
          ⟨ ϵ', e' ⟩ ⇓ v (*/\ ϵ ⊆ ϵ' (define sub-env relation) *).
  Proof.
    intro e;
      induction e
      as [ b i
         | w n i
         | w z i
         | t x i
         | e hi lo i IHe
         | t e i IHe
         | t op e i IHe
         | t op e1 e2 i IHe1 IHe2
         | es i IHes
         | es i IHes
         | es e i IHe IHes
         | t x e i IHe
         | err i
         | mk i
         | ts es ni i IHes
         | t e n i IHe
         ] using custom_e_ind;
      intro env; transformExpr_destr;
        unfold decl_var_env in *; cbn in *; try triplet_inv;
          intros eps v pkt fe cx Hev; inv Hev; eauto;
            try solve_this_stuff.
    - specialize IHe with env.
      transformExpr_destr_hyp.
      pose proof IHe _ _ pkt fe cx H5 as (eps' & Hs & He); clear IHe.
      triplet_inv.
      solve_this_stuff_with eps' v.
    - specialize IHe with env.
      transformExpr_destr_hyp.
      pose proof IHe _ _ pkt fe cx H4 as (eps' & Hs & He); clear IHe.
      triplet_inv.
      solve_this_stuff_with eps' v.
    - specialize IHe with env.
      transformExpr_destr_hyp.
      pose proof IHe _ _ pkt fe cx H5 as (eps' & Hs & He); clear IHe.
      triplet_inv.
      solve_this_stuff_with eps' v.
    - specialize IHe1 with env.
      transformExpr_destr_hyp.
      pose proof IHe1 _ _ pkt fe cx H6 as (eps'1 & Hs1 & He1); clear IHe1.
      specialize IHe2 with t1.
      transformExpr_destr_hyp.
      pose proof IHe2 _ _ pkt fe cx H7 as (eps'2 & Hs2 & He2); clear IHe2.
      triplet_inv.
      solve_this_stuff_with eps'2 v.
      intuition.
  Abort. *)
