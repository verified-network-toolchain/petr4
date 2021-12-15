Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.Envn
        Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.P4cub.BigStep.Semantics
        Poulet4.P4cub.BigStep.IndPrincip.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations F.FieldTactics Step.

Section Properties.
  Context {tags_t : Type}.
  Local Hint Resolve Env.shadow_sub_env_l : core.
  Local Hint Resolve Utils.Forall2_dumb : core.
  Local Hint Constructors expr_big_step : core.
  
  Lemma expr_big_step_sub_env : forall ϵ ϵ' (e : Expr.e tags_t) v,
      ϵ ⊆ ϵ' -> ⟨ ϵ, e ⟩ ⇓ v -> ⟨ ϵ', e ⟩ ⇓ v.
  Proof.
    intros eps eps' e v Heps Hev;
      induction Hev using custom_expr_big_step_ind; eauto;
        try (constructor; unfold F.relfs, F.relf in *; unravel in *;
             rewrite Utils.Forall2_conj in *; firstorder eauto).
  Qed.

  Local Hint Resolve expr_big_step_sub_env : core.
  Local Hint Resolve Env.disjoint_union_sub_env : core.

  Lemma expr_big_step_disjoint_union : forall ϵ ϵ' ϵ'' (e : Expr.e tags_t) v,
      Env.disjoint_union ϵ ϵ' ϵ'' ->
      ⟨ ϵ, e ⟩ ⇓ v -> ⟨ ϵ'', e ⟩ ⇓ v.
  Proof.
    eauto.
  Qed.

  Local Hint Resolve expr_big_step_disjoint_union : core.
  
  Lemma expr_big_step_disjoint_app : forall ϵ ϵ' (e : Expr.e tags_t) v,
      Env.disjoint ϵ ϵ' ->
      ⟨ ϵ, e ⟩ ⇓ v -> ⟨ (ϵ' ++ ϵ), e ⟩ ⇓ v.
  Proof.
    intros eps eps' e v Hd Hev.
    apply expr_big_step_disjoint_union with (ϵ := eps) (ϵ' := eps'); auto.
    unfold Env.disjoint_union; split; auto.
    apply Env.disjoint_append_eq_env; auto.
  Qed.

  Local Hint Resolve expr_big_step_disjoint_app : core.
  Local Hint Constructors stmt_big_step : core.
  Local Hint Resolve Env.disjoint_union_unique_eq_env : core.
  
  Lemma stmt_big_step_disjoint_union :
    forall ϵ₁ ϵ₁' ϵ₂ μ (s : Stmt.s tags_t) pkt pkt' fs cx sig,
      Env.disjoint_union ϵ₁ μ ϵ₂ ->
      ⟪ pkt , fs , ϵ₁ , cx , s ⟫ ⤋ ⟪ ϵ₁' , sig , pkt' ⟫ ->
      exists ϵ₂',
        ⟪ pkt , fs , ϵ₂ , cx , s ⟫ ⤋ ⟪ ϵ₂' , sig , pkt' ⟫
        /\ Env.disjoint_union ϵ₁' μ ϵ₂'.
  Proof.
    intros eps1 eps1' eps2 mu s pkt pkt' fs cx sig Hdu Hsbs.
    induction Hsbs; eauto 3.
    - admit.
  Admitted.
End Properties.
