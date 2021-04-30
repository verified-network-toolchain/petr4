Require Import Poulet4.P4cub.Value.
Require Import Poulet4.P4cub.BigStep.

Module P := Poulet4.P4cub.AST.P4cub.
Module E := P.Expr.
Module V := Val.
Import P.P4cubNotations.
Import V.ValueNotations.
Import V.LValueNotations.
Import F.FieldTactics.
Import Step.

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
End Determinism.
