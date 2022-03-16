Set Warnings "-custom-entry-overridden".
From Poulet4 Require Import P4cub.Syntax.Syntax P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Syntax BigStep.Semantics BigStep.IndPrincip.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations F.FieldTactics Step.

Section Properties.
  Lemma lv_update_sub_env : forall lv v ϵ,
    ϵ ⊆ lv_update lv v ϵ.
  Proof.
    intro lv;
      induction lv; intros v eps; simpl.
    - (* not generally true. *) admit.
  Abort.
  
  Context {tags_t : Type}.
  Local Hint Resolve ForallMap.Forall2_dumb : core.
  Local Hint Resolve Clmt.union_sub_env : core.
  Local Hint Constructors expr_big_step : core.
  
  Lemma expr_big_step_sub_env : forall ϵ ϵ' (e : Expr.e tags_t) v,
      ϵ ⊆ ϵ' -> ⟨ ϵ, e ⟩ ⇓ v -> ⟨ ϵ', e ⟩ ⇓ v.
  Proof.
    intros eps eps' e v Heps Hev;
      induction Hev using custom_expr_big_step_ind; eauto;
        try (constructor; unfold F.relfs, F.relf in *; unravel in *;
             rewrite ForallMap.Forall2_conj in *; firstorder eauto).
  Qed.

  Local Hint Resolve expr_big_step_sub_env : core.
  Local Hint Resolve Clmt.disjoint_union_sub_env : core.

  Lemma expr_big_step_disjoint_union : forall ϵ ϵ' ϵ'' (e : Expr.e tags_t) v,
      Clmt.disjoint_union ϵ ϵ' ϵ'' ->
      ⟨ ϵ, e ⟩ ⇓ v -> ⟨ ϵ'', e ⟩ ⇓ v.
  Proof.
    eauto.
  Qed.

  Local Hint Resolve expr_big_step_disjoint_union : core.
  
  Lemma expr_big_step_disjoint_app : forall ϵ ϵ' (e : Expr.e tags_t) v,
      Clmt.disjoint ϵ ϵ' ->
      ⟨ ϵ, e ⟩ ⇓ v -> ⟨ (Clmt.union ϵ' ϵ), e ⟩ ⇓ v.
  Proof.
    intros eps eps' e v Hd Hev.
    apply expr_big_step_disjoint_union with (ϵ := eps) (ϵ' := eps'); auto.
    unfold Clmt.disjoint_union; split; auto.
    apply Clmt.disjoint_union_eq_env; auto.
  Qed.

  Local Hint Resolve expr_big_step_disjoint_app : core.
  Local Hint Constructors stmt_big_step : core.
  Local Hint Resolve Clmt.disjoint_union_unique_eq_env : core.
  
  Lemma stmt_big_step_disjoint_union :
    forall ϵ₁ ϵ₁' ϵ₂ ϵ₂' μ (s : Stmt.s tags_t) pkt pkt' fs cx sig,
      Clmt.disjoint_union ϵ₁  μ ϵ₂ ->
      Clmt.disjoint_union ϵ₁' μ ϵ₂' ->
      ⟪ pkt , fs , ϵ₁ , cx , s ⟫ ⤋ ⟪ ϵ₁' , sig , pkt' ⟫ ->
      ⟪ pkt , fs , ϵ₂ , cx , s ⟫ ⤋ ⟪ ϵ₂' , sig , pkt' ⟫.
  Proof.
    intros eps1 eps1' eps2 eps2' mu s pkt pkt' fs cx sig Hdu Hdu' Hsbs.
    induction Hsbs; eauto 4.
    - assert (Heqenv: eps2 = eps2') by eauto; subst; auto.
  Abort.

  Lemma stmt_big_step_disjoint_union :
    forall ϵ ϵ' μ (s : Stmt.s tags_t) pkt pkt' fs cx sig,
      Clmt.disjoint ϵ μ ->
      ⟪ pkt , fs ,  ϵ       , cx , s ⟫ ⤋ ⟪  ϵ'       , sig , pkt' ⟫ ->
      ⟪ pkt , fs , (Clmt.union μ ϵ) , cx , s ⟫ ⤋ ⟪ (Clmt.union μ ϵ') , sig , pkt' ⟫.
  Proof.
    intros eps eps' mu s pkt pkt' fs cx sig Hd Hsbs.
    induction Hsbs; eauto 4.
    - apply sbs_seq_cont with (ϵ'0 := Clmt.union mu ϵ') (pkt'0 := pkt'); auto.
      apply IHHsbs2.
      (* Needs assumption that [disjoint ϵ' μ] *)
      admit.
  Abort.
End Properties.
