Set Warnings "-custom-entry-overridden".
Require Import Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Static.Static
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Value
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Util
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Semantics.
Import CanonicalForms Step.
Import Field.FieldTactics.

Section LValueTheorems.
  Variable Δ : nat.
  Variable Γ : list Typ.t.

  Section LValuePreservation.
    Local Hint Constructors type_exp : core.

    Theorem lvalue_preservation : forall e e' τ,
      lvalue_step e e' -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> `⟨ Δ, Γ ⟩ ⊢ e' ∈ τ.
    Proof.
      intros e e' τ He; generalize dependent τ;
        induction He; intros t Ht; inv Ht; eauto 3.
    Qed.
  End LValuePreservation.

  Section LValueProgress.
    Hint Constructors lvalue : core.
    Hint Constructors lvalue_step : core.

    Theorem lvalue_progress : forall e τ,
        lexpr_ok e -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        lvalue e \/ exists e', lvalue_step e e'.
    Proof.
      intros e τ Hlv; generalize dependent τ;
        induction Hlv; intros t' Ht; inv Ht;
      try match goal with
          | IH: (forall _, `⟨ Δ, Γ ⟩ ⊢ ?e ∈ _ -> _ \/ exists _, _),
                H: `⟨ Δ, Γ ⟩ ⊢ ?e ∈ _
            |- _ => apply IH in H as [? | [? ?]]
          end; eauto 4.
      - (* TODO: add indexing to lvalue-evaluation. *)
    Admitted.
  End LValueProgress.
End LValueTheorems.

Section ExpTheorems.
  Variable Δ : nat.
  Variable Γ : list Typ.t.
  Variable ϵ : list Exp.t.

  Hypothesis Henvs_type :
      Forall2
        (type_exp 0 [])
        ϵ Γ.
  
  Section Preservation.
    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_slice_types : core.
    Local Hint Resolve eval_una_types : core.
    Local Hint Resolve eval_bin_types : core.
    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_member_types : core.
    Hint Rewrite Forall_app : core.
    Hint Rewrite app_length : core.
    Local Hint Resolve Forall2_app : core.
    Local Hint Constructors type_exp : core.

    Theorem exp_small_step_preservation : forall e e' τ,
        ⟨ ϵ, e ⟩ -->  e' -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> `⟨ Δ, Γ ⟩ ⊢ e' ∈ τ.
    Proof.
      intros;
      generalize dependent τ;
      match goal with
      | H: ⟨ϵ, _ ⟩ -->  _ |- _ => induction H; intros
      end; try invert_type_exp; unravel in *; try subst w';
      repeat assert_canonical_forms; unravel in *;
      try match goal with
          | H: Some _ = Some _ |- _ => inv H
          end; eauto 4.
      (*
      - eapply Forall_nth_error in H12; eauto 1.
      - subst es; subst es';
        apply Forall2_app_inv_l in H5 as [? [? [? [? ?]]]];
        inv_Forall2_cons; eauto.*) admit.
      - (*subst fs; subst fs';
        apply Forall2_app_inv_l in H5 as [? [? [? [? ?]]]];
        inv_Forall2_cons; relf_destruct; intuition; subst.
        constructor. apply Forall2_app; auto 1.
        repeat constructor; auto 2.*) admit.
      - (*subst fs; subst fs';
        apply Forall2_app_inv_l in H8 as [? [? [? [? ?]]]];
        inv_Forall2_cons; relf_destruct; intuition; subst.
        constructor; eauto 2.
        apply Forall2_app; auto 1.
        repeat constructor; unravel; auto 2.*) admit.
      - (*subst hs; subst hs'; constructor;
        autorewrite with core in *; intuition;
        try inv_Forall_cons; eauto 3.
*)
    Admitted.
  End Preservation.

  Section Progress.
    Ltac progress_simpl :=
      match goal with
      | H: value _ \/ (exists _, ⟨ ϵ, _ ⟩ -->  _)
        |- _ => destruct H as [? | ?]
      | H: exists _, ⟨ ϵ, _ ⟩ -->  _ |- _ => destruct H as [? ?]
      | |- _ => assert_canonical_forms
      | IH: (?P -> ?Q -> value _ \/ exists _, ⟨ ϵ, _ ⟩ -->  _),
            HP: ?P, HQ: ?Q |- _ => pose proof IH HP HQ as [? | ?]; clear IH
      end.
    (**[]*)

    Local Hint Constructors value : core.
    Local Hint Constructors exp_step : core.

    Theorem exp_small_step_progress : forall e τ,
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> value e \/ exists e', ⟨ ϵ, e ⟩ -->  e'.
    Proof.
      intros e t H; induction H using custom_type_exp_ind;
        try match goal with
            | |- value ?e \/ _ =>
                assert (value e); [ repeat constructor; eassumption
                                  | left; assumption ]
            end;
        repeat progress_simpl; eauto 4. (*
      - right; apply Henvs_subset in H as [? ?]; eauto 3.
      - right; pose proof eval_slice_exists
                    _ _ _ _ _ _ _ H2 H H0 H1 as [? ?]; eauto 3.
      - pose proof eval_cast_exists _ _ _ _ _ H1 H H0 as [? ?]; eauto 4.
      - (*pose proof eval_uop_exists _ _ _ _ _ _ H H1 H0 as [? ?]; eauto 4.*) admit.
      - (*pose proof eval_bop_exists _ _ _ _ _ _ i _ _ H H3 H2 H0 H1 as [? ?]; eauto 4.*) admit.
      - (*pose proof eval_member_exists _ _ _ _ _ _ _ H2 H0 H H1 as [? ?]; eauto 4.*) admit.
      - induction H; repeat inv_Forall2_cons;
        repeat progress_simpl; intuition. (*
        + inv H3; eauto 4.
        + destruct H3 as [? ?]. inv H2.
          subst es; subst es'.
          repeat rewrite app_comm_cons in *; eauto 5.
        + rewrite <- (app_nil_l (x :: l)); eauto 4.
        + rewrite <- (app_nil_l (x :: l)); eauto 4. *) admit. admit.
      - (*induction H; repeat invert_cons_cons_relate;
        repeat progress_simpl; intuition.
        + left. repeat constructor. admit.
        + inv H4. left. repeat constructor; unravel; eauto 1.
        + destruct H4 as [? ?]. inv H2.
          subst fs; subst fs'.
          repeat rewrite app_comm_cons in *. right.
          exists (Exp.EStruct (((s0, p) :: prefix) ++ (x0, (τ, e')) :: suffix) i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)).
          right. exists (Exp.EStruct ([] ++ (s, (t', x)) :: l) i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)).
          right. exists (Exp.EStruct ([] ++ (s, (t', x)) :: l) i).
          repeat constructor; unravel; eauto 1.
      - clear H. rename H0 into H; rename H1 into H0.
        induction H; repeat invert_cons_cons_relate;
        repeat progress_simpl; intuition.
        + left. repeat constructor.
        + inv H4. left. repeat constructor; unravel; eauto 1.
        + destruct H4 as [? ?]. inv H2.
          * subst fs; subst fs'.
            repeat rewrite app_comm_cons in *. right.
            exists (Exp.EHeader
                 (((s0, p) :: prefix) ++ (x2, (τ, e')) :: suffix)
               <{ BOOL x @ x0 }> i).
            repeat constructor; unravel; eauto 1.
          * inv H9.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)). right.
          exists (Exp.EHeader ([] ++ (s, (t', x1)) :: l) <{ BOOL x @ x0 }> i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t' e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t', e)) :: l)). right.
          exists (Exp.EHeader ([] ++ (s, (t', x1)) :: l) <{ BOOL x @ x0 }> i).
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
    Qed. *) *)
    Admitted.
  End Progress.
End ExpTheorems.

(*
Section ParserExpTheorems.
  Variable sts : user_states.

  Variable D : Delta.

  Variable Γ : Gamma.

  Context {tags_t : Type}.

  Variable ϵ : @eenv tags_t.

  Section Preservation.
    Local Hint Constructors check_prsrexp : core.
    Local Hint Resolve exp_small_step_preservation : core.
    Hint Rewrite Forall_app : core.

    Hypothesis Henvs_type : envs_type Γ ϵ D.

    Theorem parser_exp_preservation : forall e e',
      π ϵ, e -->  e' -> ⟅ sts, D, Γ ⟆ ⊢ e -> ⟅ sts, D, Γ ⟆ ⊢ e'.
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
    Local Hint Constructors step_parser_exp : core.
    Hint Rewrite Forall_app : core.
    Hint Resolve value_exm : core.

    Inductive select_exp : AST.Parser.e tags_t -> Prop :=
      Select_select e d cases i :
        select_exp p{ select e { cases } default:=d @ i }p.
    (**[]*)

    Hypothesis Henvs_sound : envs_sound Γ ϵ D.

    Theorem parser_exp_progress : forall e,
        select_exp e -> ⟅ sts, D, Γ ⟆ ⊢ e -> exists e', π ϵ, e -->  e'.
    Proof.
      intros e Hs He; induction He using check_prsrexp_ind; inv Hs.
      eapply exp_small_step_progress in H as [Hev | [e' He']]; eauto 3.
    Qed.
  End Progress.
End ParserExpTheorems.
*)
