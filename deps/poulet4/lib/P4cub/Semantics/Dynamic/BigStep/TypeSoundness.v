Require Import Coq.micromega.Lia.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value BigStep.Semantics BigStep.IndPrincip.
Require Import Poulet4.P4cub.Semantics.Static.Static
        Poulet4.Utils.ForallMap.
Import AllCubNotations Val.ValueNotations Val.LValueNotations.

Section BigStepTheorems.
  Section ExprPreservation.
    Local Hint Resolve eval_slice_types : core.
    Local Hint Resolve eval_uop_types : core.
    Local Hint Resolve eval_bop_type : core.
    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_member_types : core.
    (*Local Hint Constructors ProperType.proper_nesting : core.*)
    Local Hint Constructors type_value : core.

    Theorem expr_big_step_preservation : forall ϵ e v Γ τ,
        ⟨ ϵ, e ⟩ ⇓ v ->
        Forall2 type_value ϵ (types Γ) ->
        Γ ⊢ₑ e ∈ τ ->
        ⊢ᵥ v ∈ τ.
    Proof.
      intros ϵ e v Γ τ hev henv;
        generalize dependent τ;
        induction hev using custom_expr_big_step_ind;
        intros t het; inv het; eauto.
      - pose proof IHhev henv _ H6 as hvt; inv hvt; eauto.
      - constructor.
        + destruct ob; destruct b; eauto.
        + clear dependent b.
          clear dependent ob.
          rewrite Forall2_forall in H0.
          pose proof
               (conj
                  (proj1 H0)
                  (fun u v hin => (proj2 H0) u v hin henv)) as h; clear H0.
          rewrite <- Forall2_forall in h.
          pose proof Forall2_forall_impl_Forall2
               _ _ _ _ _ _ _
               h _ H5 as hvts; assumption.
    Qed.
  End ExprPreservation.

  Section ExprProgress.
    Local Hint Constructors expr_big_step : core.
    Local Hint Constructors relop : core.

    Theorem expr_big_step_progress : forall Γ e τ ϵ,
        Forall2 type_value ϵ (types Γ) ->
        Γ ⊢ₑ e ∈ τ ->
        exists v : Val.v, ⟨ ϵ, e ⟩ ⇓ v.
    Proof.
      intros Γ e τ ϵ henv het;
        induction het using custom_type_expr_ind;
        repeat match goal with
               | IHHt: (?P -> exists _, ⟨ ϵ, ?e ⟩ ⇓ _),
                   HP: ?P, He: (Γ ⊢ₑ ?e ∈ _)
                 |- _ => pose proof IHHt HP as [? ?]; clear IHHt
               | Hev : (⟨ ϵ, ?e ⟩ ⇓ _),
                   Ht: (Γ ⊢ₑ ?e ∈ _)
                 |- _ => pose proof expr_big_step_preservation
                            _ _ _ _ _ Hev henv Ht; clear Ht
               end; eauto 2.
        eauto.
      - apply Forall2_length in henv.
        apply nth_error_some_length in H.
        rewrite <- henv in H.
        apply nth_error_exists in H as [v hv]; eauto.
      - pose proof eval_slice_exists
             _ _ _ _ _ H H0 H2 as [v' hv']; eauto.
      - pose proof eval_cast_exists
             _ _ _ H H2 as [v' hv']; eauto.
      - pose proof eval_uop_exist
             _ _ _ _ H H2 as [? ?]; eauto.
      - pose proof eval_bop_exists
             _ _ _ _ _ _ H H4 H3 as [? ?]; eauto.
      - inv H2.
        pose proof eval_member_exists
             _ _ _ _ H H7 as [? ?]; eauto.
      - rewrite Forall2_forall in H1.
        pose proof conj
             (proj1 H1)
             (fun e t hin => proj2 H1 e t hin henv) as h; clear H1.
        rewrite <- Forall2_forall in h.
        apply Forall2_only_l_Forall in h.
        rewrite Forall_exists_factor in h.
        destruct h as [vs hvs].
        destruct ob; destruct b; try contradiction; eauto.
    Qed.
  End ExprProgress.

  Section LVPreservation.
    Local Hint Constructors type_lvalue : core.

    Theorem lvalue_preservation : forall e lv Γ τ,
        e ⇓ₗ lv -> Γ ⊢ₑ e ∈ τ -> types Γ ⊢ₗ lv ∈ τ.
    Proof.
      intros e lv Γ t helv;
        generalize dependent t;
        induction helv; intros t het; inv het; eauto.
    Qed.
  End LVPreservation.

  Section LVProgress.
    Local Hint Constructors lexpr_big_step : core.

    Theorem lvalue_progress : forall Γ e τ,
        lvalue_ok e -> Γ ⊢ₑ e ∈ τ -> exists lv, e ⇓ₗ lv.
    Proof.
      intros Γ e t hok; generalize dependent t;
        induction hok; intros t het; inv het;
        try match goal with
            | IH: (forall _, Γ ⊢ₑ ?e ∈ _ -> exists _, _),
                H: (Γ ⊢ₑ ?e ∈ _)
              |- _ => apply IH in H as [? ?]
            end; eauto 3.
    Qed.
  End LVProgress.

  (* TODO: more! *)
End BigStepTheorems.
