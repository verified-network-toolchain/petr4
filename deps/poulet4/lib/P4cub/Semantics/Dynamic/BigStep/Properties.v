From Poulet4 Require Import P4cub.Syntax.Syntax
     P4cub.Semantics.Climate Utils.ForallMap.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Syntax BigStep.Semantics BigStep.IndPrincip
     BigStep.Value.Typing.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations.

Section Properties.
  Local Hint Constructors type_value : core.
  Local Hint Constructors Static.Util.type_lists_ok : core.
  
  Lemma lv_update_length : forall lv v ϵ,
      length (lv_update lv v ϵ) = length ϵ.
  Proof.
    intro lv;
      induction lv; intros v eps; simpl.
    - rewrite nth_update_length; reflexivity.
    - destruct v; auto;
        destruct (lv_lookup eps lv) eqn:hlook; auto;
        destruct v; auto.
    - destruct (lv_lookup eps lv) eqn:hlook; auto.
      destruct v0; auto. destruct ls; auto.
    - destruct (lv_lookup eps lv) eqn:hlook; auto.
      destruct v0; auto. destruct ls; auto.
  Qed.

  Lemma lv_lookup_types : forall lv τ v Γ ϵ,
      Forall2 type_value ϵ Γ ->
      Γ ⊢ₗ lv ∈ τ ->
      lv_lookup ϵ lv = Some v ->
      ⊢ᵥ v ∈ τ.
  Proof.
    intros lv t v g eps henv hlvt;
      generalize dependent v.
    induction hlvt; intros v hv; cbn in *.
    - rewrite ForallMap.Forall2_forall_nth_error in henv.
      firstorder.
    - destruct (lv_lookup eps LV) as [V |] eqn:Veq;
        cbn in *; try discriminate.
      pose proof IHhlvt _ eq_refl as ihv; clear IHhlvt.
      inv H0; inv ihv; unravel in *; inv hv.
      + admit.
      + admit.
    - destruct (lv_lookup eps LV) as [V |] eqn:Veq;
        cbn in *; try discriminate.
      destruct V; cbn in *; try discriminate.
      pose proof IHhlvt _ eq_refl as ih; clear IHhlvt; inv ih.
      inv H2; eauto using ExprUtil.eval_member_types.
    - destruct (lv_lookup eps lv) as [V |] eqn:Veq;
        cbn in *; try discriminate.
      destruct V; cbn in *; try discriminate.
      pose proof IHhlvt _ eq_refl as ih; clear IHhlvt; inv ih.
      inv H2; unravel in *.
      apply Forall2_repeat_r_Forall in H4.
      rewrite Forall_forall in H4.
      eauto using nth_error_In.
  Admitted.

  Local Hint Resolve nth_update_length : core.
  
  Lemma lv_update_correct : forall lv v v' ϵ τ Γ,
      Forall2 type_value ϵ Γ ->
      Γ ⊢ₗ lv ∈ τ ->
      ⊢ᵥ v ∈ τ ->
      ⊢ᵥ v' ∈ τ ->
      lv_lookup ϵ lv = Some v' ->
      lv_lookup (lv_update lv v ϵ) lv = Some v.
  Proof.
    intros lv v v' eps t g h hlv;
      generalize dependent v';
      generalize dependent v;
      generalize dependent eps.
    induction hlv; intros eps henv v v' hv hv' h; cbn in *.
    - apply nth_update_correct.
      eauto using ForallMap.nth_error_some_length.
    - inv hv; inv hv'.
      destruct (lv_lookup eps LV) as [V |] eqn:hlook;
        cbn in *; try discriminate. admit. admit. admit. admit.
    - destruct (lv_lookup eps LV) as [V |] eqn:hlook;
        cbn in *; try discriminate.
      destruct V; try discriminate.
      pose proof lv_lookup_types
           _ _ _ _ _ henv hlv hlook as h'.
      inv h'; inv H2; unravel;
        erewrite IHhlv; clear IHhlv; eauto;
        rename τs0 into ts;
        try (rewrite nth_update_correct; eauto using nth_error_some_length).
      + econstructor; eauto. eauto using Forall2_nth_update_r.
  Admitted.
  
  Local Hint Resolve ForallMap.Forall2_dumb : core.
  Local Hint Constructors expr_big_step : core.
  
  (*Lemma expr_big_step_sub_env : forall ϵ ϵ' (e : Expr.e tags_t) v,
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
    - apply sbs_seq_cont with (ϵ' := Clmt.union mu ϵ') (pkt' := pkt'); auto.
      apply IHHsbs2.
      (* Needs assumption that [disjoint ϵ' μ] *)
      admit.
      Abort.*)
End Properties.
