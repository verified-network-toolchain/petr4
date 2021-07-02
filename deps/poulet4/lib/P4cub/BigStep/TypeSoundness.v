Set Warnings "-custom-entry-overridden".
Require Import Coq.micromega.Lia
        Poulet4.P4cub.BigStep.Value.Value
        Poulet4.P4cub.BigStep.Semantics
        Poulet4.P4cub.BigStep.IndPrincip.
Require Import Poulet4.P4cub.Static.Static.

Module P := Poulet4.P4cub.Syntax.AST.P4cub.
Module E := P.Expr.
Module ST := P.Stmt.
Module PR := P.Parser.
Module V := Val.
Import P.P4cubNotations Step
       V.ValueNotations V.LValueNotations
       F.FieldTactics ProperType.

Section BigStepTheorems.
  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type (errs : errors) (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : string) (τ : E.t) (v : V.v),
      Env.find x Γ = Some τ -> Env.find x ϵ = Some v -> ∇ errs ⊢ v ∈ τ.
  (**[]*)

  (** Epsilon is a subset of Gamma. *)
  Definition envs_subset (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : string) (τ : E.t),
      Env.find x Γ = Some τ -> exists v, Env.find x ϵ = Some v.
  (**[]*)

  Definition envs_sound Γ ϵ errs : Prop :=
    envs_type errs Γ ϵ /\ envs_subset Γ ϵ.
  (**[]*)

  Context {tags_t : Type}.

  Section ExprPreservation.
    Local Hint Resolve eval_slice_types : core.
    Local Hint Resolve eval_uop_types : core.
    Local Hint Resolve eval_bop_type : core.
    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_member_types : core.
    Local Hint Constructors PT.proper_nesting : core.
    Local Hint Constructors type_value : core.

    Theorem expr_big_step_preservation :
      forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
        (τ : E.t) (ϵ : epsilon) (v : V.v),
        envs_type errs Γ ϵ ->
        ⟨ ϵ, e ⟩ ⇓ v ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        ∇ errs ⊢ v ∈ τ.
    Proof.
      unfold envs_type; intros errs Γ e τ ϵ v Het Hev.
      generalize dependent τ.
      induction Hev using custom_expr_big_step_ind; intros t Ht; inv Ht;
      try constructor; eauto 4;
        repeat match goal with
               | w' := _ |- context [ ?w' ] => subst w'; eauto 3
               | H: error_ok _ _ |- _ => inv H; auto 1
               | IHHev: (?P -> forall _, ⟦ errs, Γ ⟧ ⊢ ?e ∈ _ -> ∇ errs ⊢ _ ∈ _),
                 HP : ?P, He: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
                 |- _ => pose proof IHHev HP _ He as IH; clear IHHev; inv IH
               end; eauto 2.
      - generalize dependent ts; induction H; intros [];
        intros; repeat inv_Forall2_cons; intuition.
      - generalize dependent tfs;
        ind_relfs; intros [| [? ?] ?]; intros;
        repeat invert_nil_cons_relate; repeat invert_cons_cons_relate;
        constructor; unfold F.relf in *; unravel; intuition.
        apply H2; auto 1.
      - generalize dependent tfs;
        ind_relfs; intros [| [? ?] ?]; intros;
        repeat invert_nil_cons_relate; repeat invert_cons_cons_relate;
        constructor; unfold F.relf in *; unravel; intuition;
        invert_proper_nesting; invert_cons_predfs; apply H2; auto 2.
      - apply Forall2_length in H; lia.
      - clear n ni H6 H8 H9 H10; generalize dependent ts;
        induction H; intros []; intros;
        try inv_Forall2_cons; try inv_Forall_cons; intuition.
      - invert_proper_nesting; auto 2.
      - eapply Forall_nth_error in H12; simpl in *; eauto 1.
        simpl in *; inv H12; auto.
    Qed.
  End ExprPreservation.

  Section ExprProgress.
    Local Hint Constructors expr_big_step : core.

    Theorem expr_big_step_progress :
      forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
        (τ : E.t) (ϵ : epsilon),
        envs_sound Γ ϵ errs ->
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
        exists v : V.v, ⟨ ϵ, e ⟩ ⇓ v.
    Proof.
      intros errs Γ τ e ϵ [Htyp Hsub] Ht;
      unfold envs_subset, envs_type in *;
      induction Ht using custom_check_expr_ind;
        repeat match goal with
               | IHHt: (?P -> ?Q -> exists _, ⟨ ϵ, ?e ⟩ ⇓ _),
                 HP: ?P, HQ: ?Q, He: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
                 |- _ => pose proof IHHt HP HQ as [? ?]; clear IHHt
               | Hev : (⟨ ϵ, ?e ⟩ ⇓ _),
                 Ht: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
                 |- _ => pose proof expr_big_step_preservation
                            _ _ _ _ _ _ Htyp Hev Ht; clear Ht
               end; eauto 2.
      - apply Hsub in H as [? ?]; eauto 3.
      - pose proof eval_slice_exists _ _ _ _ _ _ H H0 H2 as [? ?]; eauto 3.
      - pose proof eval_cast_exists _ _ _ _ H H1 as [? ?]; eauto 3.
      - pose proof eval_uop_exist _ _ _ _ _ H H1 as [? ?]; eauto 3.
      - pose proof eval_bop_exists _ _ _ _ _ _ _ H H3 H2 as [? ?]; eauto 3.
      - pose proof eval_member_exists _ _ _ _ _ _ H0 H H2 as [? ?]; eauto 3.
      - assert (Hvs: exists vs, Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs).
        { induction H; repeat inv_Forall2_cons; eauto 2.
          intuition. destruct H2; destruct H0; eauto 3. }
        destruct Hvs; eauto 3.
      - assert
          (Hvs: exists vfs,
              F.relfs (fun te v => let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs).
        { ind_relfs; repeat invert_nil_cons_relate;
          repeat invert_cons_cons_relate.
          - exists []. constructor.
          - intuition. destruct H2 as [v Hv]; destruct H0 as [vfs Hvfs].
            exists ((s0, v) :: vfs). repeat constructor; eauto 3. }
        destruct Hvs; eauto 3.
      - assert
          (Hvs: exists vfs,
              F.relfs (fun te v => let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs).
        { inv H; try match goal with
                     | H: PT.base_type {{ hdr {_} }} |- _ => inv H
                     end.
          ind_relfs; repeat invert_nil_cons_relate;
          repeat invert_cons_cons_relate; try invert_cons_predfs.
          - exists []. constructor.
          - intuition. destruct H4 as [v Hv]; destruct H7 as [vfs Hvfs].
            exists ((s0, v) :: vfs). repeat constructor; eauto 3. }
        inv H3. destruct Hvs; eauto.
      - assert
          (Hbvss : exists bvss,
              Forall2
                (fun e bvs =>
                   let b := fst bvs in
                   let vs := snd bvs in
                   ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b) hs bvss).
        { clear n ni H H0 H1 H2.
          induction H3; repeat inv_Forall_cons; eauto 2.
          intuition. destruct H1 as [v Hv]; destruct H0 as [bvss Hbvss].
          pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp Hv H as IH; inv IH.
          exists ((b,vs) :: bvss); eauto 2. }
        destruct Hbvss; eauto 3.
      - inv H1. assert (Hnihs : BinInt.Z.to_nat idx < length hs) by lia.
        pose proof nth_error_exists _ _ Hnihs as [[? ?] ?]; eauto 3.
    Qed.
  End ExprProgress.

  Section LVPreservation.
    Local Hint Constructors type_lvalue : core.

    Theorem lvalue_preservation : forall errs Γ (e : E.e tags_t) lv τ,
        ⧠ e ⇓ lv -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> LL Γ ⊢ lv ∈ τ.
    Proof.
      intros errs Γ e lv τ Hlv; generalize dependent τ;
      induction Hlv; intros t Ht; inv Ht; eauto 3.
    Qed.
  End LVPreservation.

  Section LVProgress.
    Local Hint Constructors lvalue_big_step : core.

    Theorem lvalue_progress : forall errs Γ (e : E.e tags_t) τ,
        lvalue_ok e -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> exists lv, ⧠ e ⇓ lv.
    Proof.
      intros errs Γ e τ Hlv; generalize dependent τ;
      induction Hlv; intros t Ht; inv Ht;
      try match goal with
          | IH: (forall _, ⟦ errs, Γ ⟧ ⊢ ?e ∈ _ -> exists _, _),
            H: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
            |- _ => apply IH in H as [? ?]
          end; eauto 3.
    Qed.
  End LVProgress.

  Section ParserExprProgress.
    Hint Constructors parser_expr_big_step : core.

    Theorem parser_expr_progress : forall sts errs Γ ϵ (e : PR.e tags_t),
      envs_sound Γ ϵ errs -> ⟅ sts, errs, Γ ⟆ ⊢ e -> exists st, ⦑ ϵ, e ⦒ ⇓ st.
    Proof.
      intros sts errs Γ ϵ e Hsound He.
      induction He using custom_check_prsrexpr_ind; eauto.
      assert (Hvcases :
                exists vcases, Forall2
                            (fun pe pv =>
                               let p := fst pe in
                               let p' := fst pv in
                               let e := snd pe in
                               let s := snd pv in
                               p = p' /\ ⦑ ϵ, e ⦒ ⇓ s)
                            cases vcases).
      { clear e def H He IHHe.
        ind_list_Forall; repeat inv_Forall_cons;
        try invert_cons_predfs; eauto 2; intuition.
        (*eapply expr_big_step_progress in H0 as [v ?];
        destruct H1 as [st ?]; destruct H3 as [vcases ?]; eauto 1.
        exists ((v,st) :: vcases); auto 3. }
      eapply expr_big_step_progress in H as [v ?]; eauto 1.
      pose proof IHHe Hsound as [dst ?].
      destruct Hvcases as [vcases ?].
      exists (match F.get v vcases with None => dst | Some st => st end); auto 2.*)
    Admitted.
  End ParserExprProgress.
End BigStepTheorems.
