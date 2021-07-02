Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Syntax.AST Poulet4.P4cub.Envn
        Poulet4.P4cub.BigStep.Value.Syntax
        Poulet4.P4cub.BigStep.Semantics
        Poulet4.P4cub.BigStep.IndPrincip.
Module P := Poulet4.P4cub.Syntax.AST.P4cub.
Module E := P.Expr.
Module PR := P.Parser.
Module V := Val.
Import P.P4cubNotations V.ValueNotations
       V.LValueNotations F.FieldTactics Step.

Section Determinism.
  Context {tags_t : Type}.

  Local Hint Extern 0 => solve_eqn : core.

  Section ExpressionDeterminism.
    Ltac ind_case :=
      match goal with
      | Hv1 : (⟨ ?ϵ, ?e ⟩ ⇓ ?v1), Hv2: (⟨ ?ϵ, ?e ⟩ ⇓ ?v2),
        IH: (forall _, ⟨ ?ϵ, ?e ⟩ ⇓ _ -> ?v1 = _)
        |- _ => apply IH in Hv2; inv Hv2
      end.
    (**[]*)

    Local Hint Extern 0 => ind_case : core.

    Theorem expr_deterministic : forall ϵ (e : E.e tags_t) v1 v2,
        ⟨ ϵ, e ⟩ ⇓ v1 -> ⟨ ϵ, e ⟩ ⇓ v2 -> v1 = v2.
    Proof.
      intros ϵ e v1 v2 Hv1; generalize dependent v2;
        induction Hv1 using custom_expr_big_step_ind;
        intros v2' Hv2'; inv Hv2'; f_equal; auto 4.
      - generalize dependent vs0.
        induction H; inv H0; intros vs2 Hvs2; inv Hvs2; f_equal; auto 2.
      - generalize dependent vfs0.
        induction H; inv H0; intros vfs2 Hvfs2;
        inv Hvfs2; repeat relf_destruct; f_equal; auto 2.
      - generalize dependent vfs0.
        induction H; inv H0; intros vfs2 Hvfs2;
        inv Hvfs2; repeat relf_destruct; f_equal; auto 2.
      - generalize dependent vss0.
        induction H; inv H0; intros vss2 Hvss2;
        inv Hvss2; f_equal; auto 2.
        destruct y; destruct y0; unravel in *; intuition.
    Qed.
  End ExpressionDeterminism.

  Section LValueDeterminism.
    Ltac ind_case :=
      match goal with
      | Hv1 : (⧠ ?e ⇓ ?v1), Hv2: (⧠ ?e ⇓ ?v2),
        IH: (forall _, ⧠ ?e ⇓ _ -> ?v1 = _)
        |- _ => apply IH in Hv2; inv Hv2
      end.
    (**[]*)

    Local Hint Extern 0 => ind_case : core.

    Theorem lvalue_deterministic : forall (e : E.e tags_t) lv1 lv2,
        ⧠ e ⇓ lv1 -> ⧠ e ⇓ lv2 -> lv1 = lv2.
    Proof.
      intros e lv1 lv2 H1; generalize dependent lv2;
      induction H1; intros lv2 H2; inv H2; auto 2.
    Qed.
  End LValueDeterminism.

  Theorem parser_expr_deterministic :
    forall (ϵ : epsilon) (e : PR.e tags_t) (st1 st2 : PR.state),
      ⦑ ϵ, e ⦒ ⇓ st1 -> ⦑ ϵ, e ⦒ ⇓ st2 -> st1 = st2.
  Proof.
    intros ϵ e st1 st2 Hst1; generalize dependent st2;
    induction Hst1 using custom_parser_expr_big_step_ind;
    intros st2 Hst2; inv Hst2; try reflexivity.
    subst st; subst st0.
    assert (Hv: v0 = v) by eauto using expr_deterministic; subst.
    assert (Hdef: st_def = st_def0) by auto.
    symmetry in Hdef; subst.
    assert (Hcases: vcases = vcases0).
    { generalize dependent vcases0.
      induction H0; intros [| [? ?] ?] ?;
      repeat inv_Forall2_cons; try reflexivity.
      destruct x as [? ?]; destruct y as [? ?]; unravel in *.
      intuition; subst. apply H8 in H4; subst.
      apply H5 in H11; subst; reflexivity. }
    rewrite Hcases; reflexivity.
  Qed.
End Determinism.
