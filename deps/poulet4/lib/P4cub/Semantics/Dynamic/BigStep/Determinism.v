Require Import Poulet4.P4cub.Syntax.Syntax Poulet4.Utils.ForallMap
        (*Poulet4.P4cub.Semantics.Climate*).
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Syntax BigStep.Semantics BigStep.IndPrincip.
Import AllCubNotations Val.ValueNotations
       Val.LValueNotations.

Section Determinism.
  Local Hint Extern 0 => solve_eqn : core.

  Section ExpressionDeterminism.
    Ltac ind_case :=
      match goal with
      | Hv1 : (⟨ ?ϵ, ?e ⟩ ⇓ ?v1), Hv2: (⟨ ?ϵ, ?e ⟩ ⇓ ?v2),
        IH: (forall _, ⟨ ?ϵ, ?e ⟩ ⇓ _ -> ?v1 = _)
        |- _ => apply IH in Hv2; inv Hv2
      end.

    Local Hint Extern 0 => ind_case : core.

    Theorem expr_deterministic : forall ϵ e v₁ v₂,
        ⟨ ϵ, e ⟩ ⇓ v₁ -> ⟨ ϵ, e ⟩ ⇓ v₂ -> v₁ = v₂.
    Proof.
      intros ϵ e v1 v2 Hv1; generalize dependent v2;
        induction Hv1 using custom_expr_big_step_ind;
        intros v2' Hv2'; inv Hv2'; f_equal; auto 4.
      - pose proof Forall2_forall_impl_Forall2
             _ _ _ _ _ _ _ H2 _ H7 as H'.
        rewrite Forall2_eq in H'; assumption.
      - destruct oe as [e |];
          destruct ob as [b |];
          destruct ob0 as [b0 |];
          cbn in *; inv H; inv H0; inv H5; eauto.
    Qed.
  End ExpressionDeterminism.

  Section LValueDeterminism.
    Ltac ind_case :=
      match goal with
      | Hv1 : (?e ⇓ₗ ?v1), Hv2: (?e ⇓ₗ ?v2),
        IH: (forall _, ?e ⇓ₗ _ -> ?v1 = _)
        |- _ => apply IH in Hv2; inv Hv2
      end.
    
    Local Hint Extern 0 => ind_case : core.

    Theorem lvalue_deterministic : forall e lv₁ lv₂,
        e ⇓ₗ lv₁ -> e ⇓ₗ lv₂ -> lv₁ = lv₂.
    Proof.
      intros e lv1 lv2 H1; generalize dependent lv2;
      induction H1; intros lv2 H2; inv H2; auto 2.
    Qed.
  End LValueDeterminism.

  Theorem parser_expr_deterministic : forall ϵ e st₁ st₂,
      p⟨ ϵ, e ⟩ ⇓ st₁ -> p⟨ ϵ, e ⟩ ⇓ st₂ -> st₁ = st₂.
  Proof.
    intros ϵ e st1 st2 Hst1 Hst2; inv Hst1; inv Hst2; auto.
    assert (v0 = v) by eauto using expr_deterministic; subst.
    reflexivity.
  Qed.
End Determinism.
