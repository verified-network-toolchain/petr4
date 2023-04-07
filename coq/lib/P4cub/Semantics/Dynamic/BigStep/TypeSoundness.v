Require Import Coq.micromega.Lia.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value BigStep.Semantics BigStep.IndPrincip.
Require Import Poulet4.P4cub.Semantics.Static.Static
        Poulet4.Utils.ForallMap.

Section BigStepTheorems.
  Section ExpPreservation.
    Local Hint Resolve eval_index_types : core.
    Local Hint Resolve slice_val_types : core.
    Local Hint Resolve eval_una_types : core.
    Local Hint Resolve eval_bin_type : core.
    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_member_types : core.
    Local Hint Constructors type_val : core.

    Theorem exp_big_step_preservation : forall ϵ e v Δ Γ τ,
        ⟨ ϵ, e ⟩ ⇓ v ->
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        ⊢ᵥ v ∈ τ.
    Proof.
      intros ϵ e v Δ Γ τ hev henv;
        generalize dependent τ;
        induction hev using custom_exp_big_step_ind;
        intros t het; inv het; eauto.
      - pose proof IHhev henv _ H6 as hvt; inv hvt; inv H2; eauto.
      - pose proof IHhev1 henv _ H5 as het1.
        pose proof IHhev2 henv _ H6 as het2.
        inv het1; inv het2; inv H2.
        eauto using Forall2_repeat_r_Forall.
      - econstructor; eauto.
        rewrite Forall2_forall in H0.
        pose proof
             (conj
                (proj1 H0)
                (fun u v hin => (proj2 H0) u v hin henv)) as h; clear H0.
        rewrite <- Forall2_forall in h.
        pose proof Forall2_forall_impl_Forall2
             _ _ _ _ _ _ _
             h _ H6 as hvts; assumption.
    Qed.
  End ExpPreservation.

  Section ExpProgress.
    Local Hint Constructors exp_big_step : core.
    Local Hint Constructors relop : core.

    Theorem exp_big_step_progress : forall Δ Γ e τ ϵ,
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        exists v, ⟨ ϵ, e ⟩ ⇓ v.
    Proof.
      intros Δ Γ e τ ϵ henv het;
        induction het using custom_type_exp_ind;
        repeat match goal with
          | IHHt: (?P -> exists _, ⟨ ϵ, ?e ⟩ ⇓ _),
              HP: ?P, He: (`⟨ _, Γ ⟩ ⊢ ?e ∈ _)
            |- _ => pose proof IHHt HP as [? ?]; clear IHHt
          | Hev : (⟨ ϵ, ?e ⟩ ⇓ _),
              Ht: (`⟨ _, Γ ⟩ ⊢ ?e ∈ _)
            |- _ => pose proof exp_big_step_preservation
                    _ _ _ _ _ _ Hev henv Ht; clear Ht
               end; eauto 2.
      - apply Forall2_length in henv.
        apply nth_error_some_length in H.
        rewrite <- henv in H.
        apply nth_error_exists in H as [v hv]; eauto.
      - pose proof slice_val_exists
          _ _ _ _ _ H H0 H2 as [v' hv']; eauto.
      - pose proof eval_cast_exists
          _ _ _ H H2 as [v' hv']; eauto.
      - pose proof eval_una_exist
          _ _ _ _ H H2 as [? ?]; eauto.
      - pose proof eval_bin_exists
          _ _ _ _ _ _ H H4 H3 as [? ?]; eauto.
      - inv H2; inv H3; inv H2; try (inv H4; contradiction).
        pose proof Forall2_length _ _ _ _ _ H4 as hlen.
        rewrite repeat_length,Znat.Z_N_nat in hlen.
        pose proof eval_index_exists _ _ _ H6 hlen as [v hv].
        eauto.
      - inv H2. inv H3;
          pose proof eval_member_exists
               _ _ _ _ H H4 as [? ?]; eauto.
      - rewrite Forall2_forall in H2.
        pose proof conj
             (proj1 H2)
             (fun e t hin => proj2 H2 e t hin henv) as h; clear H2.
        rewrite <- Forall2_forall in h.
        apply Forall2_only_l_Forall in h.
        rewrite Forall_exists_factor in h.
        destruct h as [vs hvs]; eauto.
    Qed.
  End ExpProgress.

  Section LVPreservation.
    Local Hint Constructors type_lval : core.

    Theorem lval_preservation : forall ϵ e lv Δ Γ τ,
        l⟨ ϵ, e ⟩ ⇓ lv ->
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> Γ ⊢l lv ∈ τ.
    Proof.
      intros ϵ e lv Δ Γ t helv henv;
        generalize dependent t;
        induction helv; intros t het; inv het; eauto.
      pose proof exp_big_step_preservation _ _ _ _ _ _ H henv H6 as h.
      inv h. econstructor; eauto.
      unfold BitArith.bound in *.
      unfold BitArith.upper_bound in *. lia.
    Qed.
  End LVPreservation.

  Section LVProgress.
    Local Hint Constructors lexp_big_step : core.

    Theorem lval_progress : forall Δ Γ ϵ e τ,
        lexpr_ok e ->
        Forall2 type_val ϵ Γ ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> exists lv, l⟨ ϵ, e ⟩ ⇓ lv.
    Proof.
      intros Δ Γ vs e t hok henv; generalize dependent t;
        induction hok; intros t het; inv het;
        try match goal with
            | IH: (forall _, `⟨ _, Γ ⟩ ⊢ ?e ∈ _ -> exists _, _),
                H: (`⟨ _, Γ ⟩ ⊢ ?e ∈ _)
              |- _ => apply IH in H as [? ?]
          end; eauto 3.
      pose proof exp_big_step_progress
        _ _ _ _ _ henv H5 as [v2 h2].
      pose proof exp_big_step_preservation
        _ _ _ _ _ _
        h2 henv H5 as ht2. inv ht2. eauto. inv H0.
    Qed.
  End LVProgress.

  (* TODO: more! *)
End BigStepTheorems.
