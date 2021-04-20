Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Require Import P4cub.SmallStep.
Import IsValue.
Import Step.
Import Typecheck.
Module P := P4cub.AST.P4cub.
Module E := P.Expr.

Import P.P4cubNotations.
Import E.TypeEquivalence.
Import E.ProperType.
Import F.FieldTactics.

Ltac invert_value :=
  match goal with
  | H: value _ |- _ => inv H
  end.

Ltac invert_expr_check :=
  match goal with
  | H: ⟦ _, _ ⟧ ⊢ _ ∈ _ |- _ => inv H
  end.

Ltac invert_canonical := invert_value; invert_expr_check.

Ltac crush_canonical := intros; invert_canonical; eauto.

Section Lemmas.

  Variable errs : errors.

  Variable Γ : gamma.

  Section CanonicalForms.
    Context {tags_t : Type}.

    Variable v : E.e tags_t.

    Hypothesis Hv : value v.

    Lemma canonical_forms_bool :
      ⟦ errs, Γ ⟧ ⊢ v ∈ Bool -> exists b i, v = <{ BOOL b @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_bit : forall w,
        ⟦ errs, Γ ⟧ ⊢ v ∈ bit<w> -> exists n i, v = <{ w W n @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_int : forall w,
        ⟦ errs, Γ ⟧ ⊢ v ∈ int<w> -> exists z i, v = <{ w S z @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_tuple : forall ts,
        ⟦ errs, Γ ⟧ ⊢ v ∈ tuple ts -> exists es i, v = <{ tup es @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_record : forall ts,
        ⟦ errs, Γ ⟧ ⊢ v ∈ rec { ts } -> exists fs i, v = <{ rec { fs } @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_header : forall ts,
        ⟦ errs, Γ ⟧ ⊢ v ∈ hdr { ts } -> exists fs b i, v = <{ hdr { fs } valid:=b @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_error :
      ⟦ errs, Γ ⟧ ⊢ v ∈ error -> exists err i, v = <{ Error err @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_matchkind :
      ⟦ errs, Γ ⟧ ⊢ v ∈ matchkind -> exists mk i, v = <{ Matchkind mk @ i }>.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_headerstack : forall ts n,
        ⟦ errs, Γ ⟧ ⊢ v ∈ stack ts[n] ->
        exists hs ni, v = <{ Stack hs:ts[n] nextIndex:= ni }>.
    Proof. crush_canonical. Qed.
  End CanonicalForms.
End Lemmas.

Ltac inv_eq_val_expr :=
  match goal with
  | H: <{ BOOL _ @ _ }> = <{ BOOL _ @ _ }> |- _ => inv H
  | H: <{ _ W _ @ _ }> = <{ _ W _ @ _ }> |- _ => inv H
  | H: <{ _ S _ @ _ }> = <{ _ S _ @ _ }> |- _ => inv H
  | H: <{ tup _ @ _ }> = <{ tup _ @ _ }> |- _ => inv H
  | H: <{ rec { _ } @ _ }> = <{ rec { _ } @ _ }> |- _ => inv H
  | H: <{ hdr { _ } valid:=_ @ _ }> = <{ hdr { _ } valid:=_ @ _ }> |- _ => inv H
  | H: <{ Stack _:_[_] nextIndex:=_ }> = <{ Stack _:_[_] nextIndex:=_ }> |- _ => inv H
  end.
(**[]*)

Ltac assert_canonical_forms :=
  match goal with
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ Bool |- _
    => pose proof canonical_forms_bool _ _ _ Hv Ht as [? [? ?]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ bit<_> |- _
    => pose proof canonical_forms_bit _ _ _ Hv _ Ht as [? [? ?]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ int<_> |- _
    => pose proof canonical_forms_int _ _ _ Hv _ Ht as [? [? ?]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ tuple _ |- _
    => pose proof canonical_forms_tuple _ _ _ Hv _ Ht as [? [? ?]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ rec { _ } |- _
    => pose proof canonical_forms_record _ _ _ Hv _ Ht as [? [? ?]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ hdr { _ } |- _
    => pose proof canonical_forms_header _ _ _ Hv _ Ht as [? [? [? ?]]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ error |- _
    => pose proof canonical_forms_error _ _ _ Hv Ht as [? [? ?]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ matchkind |- _
    => pose proof canonical_forms_matchkind _ _ _ Hv Ht as [? [? ?]]; inv Hv; inv Ht
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ stack _[_] |- _
    => pose proof canonical_forms_headerstack _ _ _ Hv _ _ Ht as [? [? ?]]; inv Hv; inv Ht
  end; subst; try discriminate; try inv_eq_val_expr.
(**[]*)

Section Theorems.
  Variable Γ : gamma.

  Context {tags_t : Type}.

  Variable ϵ : @eenv tags_t.

  (** Epsilon is a subset of Gamma. *)
  Definition envs_subset : Prop :=
    forall (x : string) (τ : E.t),
      Γ x = Some τ -> exists v, ϵ x = Some v.
  (**[]*)

  Variable errs : errors.

  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type : Prop :=
    forall (x : string) (τ : E.t) (v : E.e tags_t),
      Γ x = Some τ -> ϵ x = Some v -> ⟦ errs , Γ ⟧ ⊢ v ∈ τ.
  (**[]*)

  Definition envs_sound : Prop := envs_type /\ envs_subset.

  Section Preservation.
    Hypothesis Henvs_type : envs_type.

    Local Hint Resolve eval_cast_types : core.
    Local Hint Resolve eval_slice_types : core.
    Local Hint Resolve eval_hdr_op_types : core.
    Local Hint Resolve eval_stk_op_types : core.
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
        ℵ ϵ ** e -->  e' -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> ⟦ errs, Γ ⟧ ⊢ e' ∈ τ.
    Proof.
      unfold envs_type in Henvs_type; intros;
      generalize dependent τ;
      match goal with
      | H: ℵ ϵ ** _ -->  _ |- _ => induction H; intros
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
      | H: value _ \/ (exists _, ℵ ϵ ** _ -->  _)
        |- _ => destruct H as [? | ?]
      | H: exists _, ℵ ϵ ** _ -->  _ |- _ => destruct H as [? ?]
      | |- _ => assert_canonical_forms
      | IH: (?P -> ?Q -> value _ \/ exists _, ℵ ϵ ** _ -->  _),
            HP: ?P, HQ: ?Q |- _ => pose proof IH HP HQ as [? | ?]; clear IH
      end.
    (**[]*)

    Local Hint Constructors value : core.
    Local Hint Constructors expr_step : core.

    Theorem expr_small_step_progress : forall e τ,
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> value e \/ exists e', ℵ ϵ ** e -->  e'.
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
      - pose proof eval_uop_exists _ _ _ _ _ H H1 H0 as [? ?]; eauto 4.
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
          exists (E.ERecord (((s0, p) :: prefix) ++ (x0, (τ, e')) :: suffix) i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t, e)) :: l)).
          right. exists (E.ERecord ([] ++ (s, (t, x)) :: l) i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t, e)) :: l)).
          right. exists (E.ERecord ([] ++ (s, (t, x)) :: l) i).
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
        + destruct p as [t e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t, e)) :: l)). right.
          exists (E.EHeader ([] ++ (s, (t, x1)) :: l) <{ BOOL x @ x0 }> i).
          repeat constructor; unravel; eauto 1.
        + destruct p as [t e]; simpl in *. unfold F.f.
          rewrite <- (app_nil_l ((s, (t, e)) :: l)). right.
          exists (E.EHeader ([] ++ (s, (t, x1)) :: l) <{ BOOL x @ x0 }> i).
          repeat constructor; unravel; eauto 1.
      - invert_proper_nesting.
        right. exists (eval_hdr_op op x x2 x3 x1). eauto 3.
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
      - pose proof eval_stk_op_exists
             _ _ i op _ _ _ _ H6 H7 H8 H9 H10 as [? ?]; eauto 5.
    Qed.
  End Progress.
End Theorems.
