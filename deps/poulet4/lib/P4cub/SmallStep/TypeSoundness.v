Set Warnings "-custom-entry-overridden".
Require Import Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Static.Static
        Poulet4.P4cub.SmallStep.Value
        Poulet4.P4cub.SmallStep.Util
        Poulet4.P4cub.SmallStep.Semantics.
Import CanonicalForms Step.
Module P := P4cub.Syntax.AST.P4cub.
Module E := P.Expr.
Import P.P4cubNotations TypeEquivalence
       ProperType F.FieldTactics Env.EnvNotations.

Section LValueTheorems.
  Variable errs : errors.
  Variable Γ : gamma.

  Context {tags_t : Type}.

  Section LValuePreservation.
    Local Hint Constructors check_expr : core.

    Theorem lvalue_preservation : forall (e e' : E.e tags_t) τ,
      ℶ e -->  e' -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> ⟦ errs, Γ ⟧ ⊢ e' ∈ τ.
    Proof.
      intros e e' τ He; generalize dependent τ;
      induction He; intros t Ht; inv Ht; eauto 3.
    Qed.
  End LValuePreservation.

  Section LValueProgress.
    Hint Constructors lvalue : core.
    Hint Constructors lvalue_step : core.

    Theorem lvalue_progress : forall (e : E.e tags_t) τ,
        lvalue_ok e -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        lvalue e \/ exists e', ℶ e -->  e'.
    Proof.
      intros e τ Hlv; generalize dependent τ;
      induction Hlv; intros t Ht; inv Ht;
      try match goal with
          | IH: (forall _, ⟦ errs, Γ ⟧ ⊢ ?e ∈ _ -> _ \/ exists _, _),
            H: ⟦ errs, Γ ⟧ ⊢ ?e ∈ _
            |- _ => apply IH in H as [? | [? ?]]
          end; eauto 4.
    Qed.
  End LValueProgress.
End LValueTheorems.

Section ExprTheorems.
  Variable Γ : gamma.

  Context {tags_t : Type}.

  Variable ϵ : @eenv tags_t.

  (** Epsilon is a subset of Gamma. *)
  Definition envs_subset : Prop :=
    forall (x : string) (τ : E.t),
      Env.find x Γ = Some τ -> exists v, Env.find x ϵ = Some v.
  (**[]*)

  Variable errs : errors.

  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type : Prop :=
    forall (x : string) (τ : E.t) (v : E.e tags_t),
      Env.find x Γ = Some τ -> Env.find x ϵ = Some v -> ⟦ errs , Γ ⟧ ⊢ v ∈ τ.
  (**[]*)

  Definition envs_sound : Prop := envs_type /\ envs_subset.

  Section Preservation.
    Hypothesis Henvs_type : envs_type.

    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_slice_types : core.
    Local Hint Resolve eval_uop_types : core.
    Local Hint Resolve eval_bop_types : core.
    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_member_types : core.
    Hint Rewrite Forall_app : core.
    Hint Rewrite app_length : core.
    Local Hint Resolve Forall2_app : core.
    Local Hint Constructors check_expr : core.
    Local Hint Constructors PT.proper_nesting : core.

    Theorem expr_small_step_preservation : forall e e' τ,
        ℵ ϵ, e -->  e' -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> ⟦ errs, Γ ⟧ ⊢ e' ∈ τ.
    Proof.
      unfold envs_type in Henvs_type; intros;
      generalize dependent τ;
      match goal with
      | H: ℵ ϵ, _ -->  _ |- _ => induction H; intros
      end; try invert_expr_check; unravel in *; try subst w';
      repeat assert_canonical_forms; unravel in *;
      try match goal with
          | H: Some _ = Some _ |- _ => inv H
          end;
      try invert_proper_nesting; eauto 4.
      - eapply Forall_nth_error in H12; eauto 1.
      - subst es; subst es';
        apply Forall2_app_inv_l in H5 as [? [? [? [? ?]]]];
        inv_Forall2_cons; eauto.
      - subst fs; subst fs';
        apply Forall2_app_inv_l in H5 as [? [? [? [? ?]]]];
        inv_Forall2_cons; relf_destruct; intuition; subst.
        constructor. apply Forall2_app; auto 1.
        repeat constructor; auto 2.
      - subst fs; subst fs';
        apply Forall2_app_inv_l in H8 as [? [? [? [? ?]]]];
        inv_Forall2_cons; relf_destruct; intuition; subst.
        constructor; eauto 2.
        apply Forall2_app; auto 1.
        repeat constructor; unravel; auto 2.
      - subst hs; subst hs'; constructor;
        autorewrite with core in *; intuition;
        try inv_Forall_cons; eauto 3.
    Qed.
  End Preservation.

  Section Progress.
    Hypothesis Henvs_sound : envs_sound.

    Ltac progress_simpl :=
      match goal with
      | H: value _ \/ (exists _, ℵ ϵ, _ -->  _)
        |- _ => destruct H as [? | ?]
      | H: exists _, ℵ ϵ, _ -->  _ |- _ => destruct H as [? ?]
      | |- _ => assert_canonical_forms
      | IH: (?P -> ?Q -> value _ \/ exists _, ℵ ϵ, _ -->  _),
            HP: ?P, HQ: ?Q |- _ => pose proof IH HP HQ as [? | ?]; clear IH
      end.
    (**[]*)

    Local Hint Constructors value : core.
    Local Hint Constructors expr_step : core.

    Theorem expr_small_step_progress : forall e τ,
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> value e \/ exists e', ℵ ϵ, e -->  e'.
    Proof.
      destruct Henvs_sound as [Henvs_type Henvs_subset];
      clear Henvs_sound; unfold envs_type, envs_subset in *; intros.
      match goal with
      | H: ⟦ errs, Γ ⟧ ⊢ _ ∈ _
        |- _ => induction H using custom_check_expr_ind
      end;
      try match goal with
          | |- value ?e \/ _ =>
            assert (value e); [ repeat constructor; eassumption
                          | left; assumption ]
          end;
      repeat progress_simpl; eauto 4.
      - right; apply Henvs_subset in H as [? ?]; eauto 3.
      - right; pose proof eval_slice_exists
                    _ _ _ _ _ _ _ H2 H H0 H1 as [? ?]; eauto 3.
      - pose proof eval_cast_exists _ _ _ _ _ H1 H H0 as [? ?]; eauto 4.
      - pose proof eval_uop_exists _ _ _ _ _ _ H H1 H0 as [? ?]; eauto 4.
      - pose proof eval_bop_exists _ _ _ _ _ _ i _ _ H H3 H2 H0 H1 as [? ?]; eauto 4.
      - pose proof eval_member_exists _ _ _ _ _ _ _ H2 H0 H H1 as [? ?]; eauto 4.
      - induction H; repeat inv_Forall2_cons;
        repeat progress_simpl; intuition.
        + inv H3; eauto 4.
        + destruct H3 as [? ?]. inv H2.
          subst es; subst es'.
          repeat rewrite app_comm_cons in *; eauto 5.
        + rewrite <- (app_nil_l (x :: l)); eauto 4.
        + rewrite <- (app_nil_l (x :: l)); eauto 4.
      - induction H; repeat invert_cons_cons_relate;
        repeat progress_simpl; intuition.
        + left. repeat constructor.
        + inv H4. left. repeat constructor; unravel; eauto 1.
        + destruct H4 as [? ?]. inv H2.
          subst fs; subst fs'.
          repeat rewrite app_comm_cons in *. right.
          exists (E.EStruct (((s0, p) :: prefix) ++ (x0, (τ, e')) :: suffix) i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)).
          right. exists (E.EStruct ([] ++ (s, (t', x)) :: l) i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)).
          right. exists (E.EStruct ([] ++ (s, (t', x)) :: l) i).
          repeat constructor; unravel; eauto 1.
      - clear H. rename H0 into H; rename H1 into H0.
        induction H; repeat invert_cons_cons_relate;
        repeat progress_simpl; intuition.
        + left. repeat constructor.
        + inv H4. left. repeat constructor; unravel; eauto 1.
        + destruct H4 as [? ?]. inv H2.
          * subst fs; subst fs'.
            repeat rewrite app_comm_cons in *. right.
            exists (E.EHeader
                 (((s0, p) :: prefix) ++ (x2, (τ, e')) :: suffix)
               <{ BOOL x @ x0 }> i).
            repeat constructor; unravel; eauto 1.
          * inv H9.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)). right.
          exists (E.EHeader ([] ++ (s, (t', x1)) :: l) <{ BOOL x @ x0 }> i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)). right.
          exists (E.EHeader ([] ++ (s, (t', x1)) :: l) <{ BOOL x @ x0 }> i).
          repeat constructor; unravel; eauto 1.
      - clear H H0 H1 H2.
        induction H3; intros; repeat inv_Forall_cons; eauto 2;
        intuition; repeat assert_canonical_forms.
        + inv H2; eauto 5.
        + destruct H2 as [v Hv]. inv Hv. subst hs; subst hs'.
          repeat rewrite app_comm_cons in *; eauto 6.
        + destruct H0 as [v Hv]. rewrite <- (app_nil_l (x :: l)); eauto 4.
        + destruct H0 as [v Hv]. rewrite <- (app_nil_l (x :: l)); eauto 4.
      - invert_proper_nesting.
        assert (Hidx : (BinIntDef.Z.to_nat idx < length x)%nat) by lia.
        pose proof nth_error_exists _ _ Hidx as [v ?]; eauto 5.
    Qed.
  End Progress.
End ExprTheorems.

Section ParserExprTheorems.
  Variable sts : user_states.

  Variable errs : errors.

  Variable Γ : gamma.

  Context {tags_t : Type}.

  Variable ϵ : @eenv tags_t.

  Section Preservation.
    Local Hint Constructors check_prsrexpr : core.
    Local Hint Resolve expr_small_step_preservation : core.
    Hint Rewrite Forall_app : core.

    Hypothesis Henvs_type : envs_type Γ ϵ errs.

    Theorem parser_expr_preservation : forall e e',
      π ϵ, e -->  e' -> ⟅ sts, errs, Γ ⟆ ⊢ e -> ⟅ sts, errs, Γ ⟆ ⊢ e'.
    Proof.
      intros e e' Hpi Ht; induction Hpi; inv Ht; repeat subst_term; eauto 3.
      (*- econstructor; eauto 1; autorewrite with core in *;
        unravel in *; intuition; inv_Forall_cons;
        constructor; unravel in *; intuition; eauto 2.*)
      - destruct (F.find_value (fun _ => false) cases) as [? |] eqn:Hget; eauto.
        (* TODO: Need helper lemma for get. *)
        clear d H5.
        generalize dependent e.
        induction cases as [| [e pe] cases ?];
        intros pst Hget; unravel in *;
          try inv_Forall_cons; try discriminate.
        inv_eq; intuition.
    Qed.
  End Preservation.

  Section Progress.
    Local Hint Constructors step_parser_expr : core.
    Hint Rewrite Forall_app : core.
    Hint Resolve value_exm : core.

    Inductive select_expr : PR.e tags_t -> Prop :=
      Select_select e d cases i :
        select_expr p{ select e { cases } default:=d @ i }p.
    (**[]*)

    Hypothesis Henvs_sound : envs_sound Γ ϵ errs.

    Theorem parser_expr_progress : forall e,
        select_expr e -> ⟅ sts, errs, Γ ⟆ ⊢ e -> exists e', π ϵ, e -->  e'.
    Proof.
      intros e Hs He; induction He using check_prsrexpr_ind; inv Hs.
      eapply expr_small_step_progress in H as [Hev | [e' He']]; eauto 3.
    Qed.
  End Progress.
End ParserExprTheorems.
