From Poulet4 Require Import P4cub.Syntax.Syntax.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     SmallStep.Value SmallStep.Semantics.
Import AllCubNotations Step Field.FieldTactics.

Section Determinism.
  Local Hint Constructors value : core.
  
  Section Lemmas.
    Local Hint Rewrite Forall_app : core.
    Local Hint Rewrite map_app : core.
    Local Hint Extern 0 => inv_Forall_cons : core.

    Lemma step_value_false : forall ϵ e e',
        ⟨ ϵ, e ⟩ -->  e' -> ~ value e.
    Proof.
      intros ϵ e e' He Hv; induction He; inv Hv;
      repeat subst_term; autorewrite with core in *;
      intuition; unravel in *; auto 3.
    Qed.
  End Lemmas.

  Ltac step_value :=
    match goal with
    | He : (⟨ _, ?e ⟩ -->  _), Hv : (value ?e)
      |- _ => apply step_value_false in He; contradiction
    | He : (⟨ _, ?e ⟩ -->  _)
      |- ~ value ?e => apply step_value_false in He; assumption
    end.
  (**[]*)

  Local Hint Extern 0 => solve_eqn : core.

  Section ExprDeterminism.
    Local Hint Extern 0 => step_value : core.

    Ltac ind_case :=
      match goal with
      | H1: (⟨ ?ϵ, ?e ⟩ -->  ?e1), H2: (⟨?ϵ, ?e ⟩ -->  ?e2),
            IH: (forall _, ⟨ ?ϵ, ?e ⟩ -->  _ -> ?e1 = _)
        |- _ => apply IH in H2; inv H2
      end.
    (**[]*)

    Local Hint Extern 0 => ind_case : core.
    Local Hint Extern 0 => contradiction : core.

    Theorem expr_deterministic : forall ϵ e e1 e2,
        ⟨ ϵ, e ⟩ -->  e1 -> ⟨ ϵ, e ⟩ -->  e2 -> e1 = e2.
    Proof.
      intros ϵ e e1 e2 He1; generalize dependent e2;
      induction He1; intros e2' He2'; inv He2';
        f_equal; auto 2; subst; repeat subst_term.
      - inv He1. rewrite Forall_app in H4.
        destruct H4 as [_ h]; inv h; auto.
      - inv H5. rewrite Forall_app in H0.
        destruct H0 as [_ h]; inv h; auto.
      - assert (Hv : value (Expr.Lists ls vs)) by eauto.
        step_value.
      - assert (Hv : value (w `W n)%expr) by eauto.
        step_value.
      - assert (Hv : value (Expr.Lists ls vs)) by eauto.
        step_value.
      - assert (Hv : value (w `W n)%expr) by eauto.
        step_value.
      - assert (He: ~ value e) by auto 1.
        assert (He0: ~ value e0) by auto 1.
        eapply Forall_until_eq in H1 as [? [? ?]]; eauto 1; subst.
        repeat f_equal; auto 2.
    Qed.
  End ExprDeterminism.

  Lemma lvalue_deterministic : forall e e1 e2,
      lvalue_step e e1 -> lvalue_step e e2 -> e1 = e2.
  Proof.
    intros e e1 e2 H1; generalize dependent e2;
    induction H1; intros e2 H2; inv H2; f_equal; auto 2.
  Qed.
  
  Section ParserExprDeterminism.
    Local Hint Extern 0 => step_value : core.
    Local Hint Resolve expr_deterministic : core.
    Hint Rewrite Forall_app : core.
    Local Hint Extern 0 => inv_Forall_cons : core.

    Lemma parser_expr_deterministic :
      forall ϵ e e1 e2,
        π ϵ, e -->  e1 -> π ϵ, e -->  e2 -> e1 = e2.
    Proof.
      intros ϵ e e1 e2 He1; generalize dependent e2;
      induction He1; intros e2 He2;
      inv He2; f_equal; repeat subst_term;
      autorewrite with core in *; intuition; unravel in *; eauto 2.
    Qed.
  End ParserExprDeterminism.
End Determinism.
