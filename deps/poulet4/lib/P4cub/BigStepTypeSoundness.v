Require Import Coq.micromega.Lia.
Require Import Poulet4.P4cub.Value.
Require Import Poulet4.P4cub.BigStep.

Module P := Poulet4.P4cub.AST.P4cub.
Module E := P.Expr.
Module S := P.Stmt.
Module V := Val.
Import P.P4cubNotations.

Import Step.
Import Typecheck.
Import V.ValueNotations.
Import V.ValueTyping.
Import F.FieldTactics.

Section BigStepTheorems.
  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type (errs : errors) (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : string) (τ : E.t) (v : V.v),
      Γ x = Some τ -> ϵ x = Some v -> ∇ errs ⊢ v ∈ τ.
  (**[]*)

  (** Epsilon is a subset of Gamma. *)
  Definition envs_subset (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : string) (τ : E.t),
      Γ x = Some τ -> exists v, ϵ x = Some v.
  (**[]*)

  Definition envs_sound Γ ϵ errs : Prop :=
    envs_type errs Γ ϵ /\ envs_subset Γ ϵ.
  (**[]*)

  Context {tags_t : Type}.

  Theorem expr_big_step_preservation :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
      (τ : E.t) (ϵ : epsilon) (v : V.v),
      envs_type errs Γ ϵ ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ∇ errs ⊢ v ∈ τ.
  Proof. (*
    Hint Resolve eval_uop_types : core.
    Hint Resolve eval_bop_type : core.
    Hint Resolve eval_cast_types : core.
    Hint Resolve eval_hdr_op_types : core.
    Hint Resolve eval_stk_op_types : core.
    Hint Resolve eval_member_types : core.
    Hint Constructors PT.proper_nesting : core.
    Hint Constructors check_expr : core.
    unfold envs_type; intros errs Γ e τ ϵ v Het Hev.
    generalize dependent τ.
    induction Hev using custom_expr_big_step_ind; intros t Ht; inv Ht;
    try constructor; eauto;
    repeat match goal with
           | H: error_ok _ _ |- _ => inv H; eauto
           | IHHev: (?P -> forall _, ⟦ errs, Γ ⟧ ⊢ ?e ∈ _ -> ∇ errs ⊢ _ ∈ _),
             HP : ?P, He: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
             |- _ => pose proof IHHev HP _ He as IH; clear IHHev; inv IH
           end; eauto.
    - generalize dependent ts;
      induction H; intros []; intros; repeat inv_Forall2_cons; intuition.
    - generalize dependent tfs;
      ind_relfs; intros [| [? ?] ?]; intros;
      repeat invert_nil_cons_relate; repeat invert_cons_cons_relate;
      constructor; unfold F.relf in *; unravel; intuition.
      apply H2; auto.
    - generalize dependent tfs;
      ind_relfs; intros [| [? ?] ?]; intros;
      repeat invert_nil_cons_relate; repeat invert_cons_cons_relate;
      constructor; unfold F.relf in *; unravel; intuition.
      inv H4; try match goal with
                  | H: PT.base_type {{ hdr { _ } }} |- _ => inv H
                  end.
      invert_cons_predfs ; apply H2; auto.
    - apply Forall2_length in H; lia.
    - clear n ni H5 H6 H8 H9; generalize dependent ts;
      induction H; intros []; intros;
        try inv_Forall2_cons; try inv_Forall_cons; intuition.
    - inv H11; try match goal with
                   | H: PT.base_type {{ stack _[_] }} |- _ => inv H
                   end; auto.
    - eapply Forall_nth_error in H12; simpl in *; eauto.
      simpl in *; inv H12; auto.
  Qed. *)
  Admitted.

  Theorem expr_big_step_progress :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
      (τ : E.t) (ϵ : epsilon),
      envs_sound Γ ϵ errs ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      exists v : V.v, ⟨ ϵ, e ⟩ ⇓ v.
  Proof. (*
    Hint Resolve eval_uop_exist : core.
    Hint Resolve eval_bop_exists : core.
    Hint Resolve eval_cast_exists : core.
    Hint Resolve eval_stk_op_exists : core.
    Hint Resolve eval_member_exists : core.
    Hint Resolve expr_big_step_preservation : core.
    Hint Constructors expr_big_step : core.
    intros errs Γ τ e ϵ [Htyp Hsub] Ht.
    unfold envs_subset, envs_type in *.
    induction Ht using custom_check_expr_ind;
    repeat match goal with
           | IHHt: (?P -> ?Q -> exists _, ⟨ ϵ, ?e ⟩ ⇓ _),
             HP: ?P, HQ: ?Q, He: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
             |- _ => pose proof IHHt HP HQ as [? ?]; clear IHHt
           | Hev : (⟨ ϵ, ?e ⟩ ⇓ _),
             Ht: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
             |- _ => pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp Hev Ht;
                   clear Ht
           end; eauto.
    - apply Hsub in H as [? ?]; eexists; eauto.
    - pose proof eval_cast_exists _ _ _ _ H H1 as [? ?]; eauto.
    - pose proof eval_uop_exist _ _ _ _ H H1 as [? ?]; eauto.
    - pose proof eval_bop_exists _ _ _ _ _ _ _ H H3 H2 as [? ?]; eauto.
    - pose proof eval_member_exists _ _ _ _ _ _ H0 H H2 as [? ?]; eauto.
    - assert (Hvs: exists vs, Forall2 (fun e v => ⟨ ϵ, e ⟩ ⇓ v) es vs).
      { induction H; repeat inv_Forall2_cons; eauto.
        intuition. destruct H2; destruct H0; eauto. }
      destruct Hvs; eauto.
    - assert
        (Hvs: exists vfs,
            F.relfs (fun te v => let e := snd te in ⟨ ϵ, e ⟩ ⇓ v) efs vfs).
      { ind_relfs; repeat invert_nil_cons_relate;
          repeat invert_cons_cons_relate.
        - exists []. constructor.
        - intuition. destruct H2 as [v Hv]; destruct H0 as [vfs Hvfs].
          exists ((s0, v) :: vfs). repeat constructor; eauto. }
      destruct Hvs; eauto.
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
          exists ((s0, v) :: vfs). repeat constructor; eauto. }
      inv H3. destruct Hvs; eauto.
    - inv H1. exists (eval_hdr_op op vs b); eauto.
    - assert
        (Hbvss : exists bvss,
            Forall2
              (fun e bvs =>
                 let b := fst bvs in
                 let vs := snd bvs in
                 ⟨ ϵ, e ⟩ ⇓ HDR { vs } VALID:=b) hs bvss).
      { clear n ni H H0 H1 H2.
        induction H3; repeat inv_Forall_cons; eauto.
        intuition. destruct H1 as [v Hv]; destruct H0 as [bvss Hbvss].
        pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp Hv H as IH; inv IH.
        exists ((b,vs) :: bvss); eauto. }
      destruct Hbvss; eauto.
    - inv H1. assert (Hnihs : N.to_nat idx < length hs) by lia.
      pose proof nth_error_exists _ _ Hnihs as [[? ?] ?]; eauto.
    - inv H1.
      pose proof eval_stk_op_exists
           _ op _ _ _ _ H4 H5 H6 H8 H9 as [? ?]; eauto.
  Qed. *)
  Admitted.
End BigStepTheorems.
