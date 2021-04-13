Require Import Coq.PArith.BinPosDef.
Require Import Coq.PArith.BinPos.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.
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
  end; subst; try discriminate.
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

    Theorem expr_small_step_preservation : forall e e' τ,
        ℵ ϵ ** e -->  e' -> ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> ⟦ errs, Γ ⟧ ⊢ e' ∈ τ.
    Proof.
      Hint Resolve eval_cast_types : core.
      Hint Resolve BitArith.return_bound_bound : core.
      Hint Resolve BitArith.neg_bound : core.
      Hint Resolve BitArith.plus_mod_bound : core.
      Hint Resolve IntArith.return_bound_bound : core. (*
      Hint Resolve eval_bit_binop_numeric : core.
      Hint Resolve eval_bit_binop_comp : core.
      Hint Resolve eval_int_binop_numeric : core.
      Hint Resolve eval_int_binop_comp : core.
      Hint Resolve eval_hdr_op_types : core.
      Hint Resolve eval_stk_op_types : core.
      Hint Rewrite Pos.eqb_refl.
      unfold envs_type in Henvs_type; intros;
      generalize dependent τ;
      match goal with
      | H: ℵ ϵ ** _ -->  _ |- _ => induction H; intros
      end;
      try match goal with
          | H: ⟦ errs, Γ ⟧ ⊢ _ ∈ _ |- _ => inv H
          end;
      repeat assert_canonical_forms;
      try (unravel in *; econstructor; eauto; eassumption);
      try (unravel in *; match goal with
                       | H: Some _ = Some _ |- _ => inv H
                       end; econstructor; eauto);
      try match goal with
          | |- BitArith.bound _ _ => unfold_bit_operation
          | |- IntArith.bound _ _ => unfold_int_operation
          | H: uop_type _ _ |- _ => inv H
          end; eauto.
      - inv H0; inv H8; simpl in *; inv H; constructor.
      - inv H0; inv H8; simpl in *; inv H; constructor; auto.
      - inv H0; inv H8; simpl in *; inv H; constructor;
        unfold_int_operation; auto.
      - inv H2. apply chk_bool_bop; auto; constructor.
      - inv H2. constructor; auto; constructor; auto.
      - inv H10. inv H2; repeat assert_canonical_forms.
        + inv H3; inv H4; unravel in *; inv H11;
          autorewrite with core in *; unravel in *; inv H;
          constructor; try unfold_bit_operation; unravel in *; auto.
        + inv H3; inv H4; unravel in *;
            autorewrite with core in *; inv H11;
              unravel in *; inv H; constructor;
                try unfold_int_operation; auto.
      - inv H10; inv H2; repeat assert_canonical_forms;
          inv H3; inv H4; inv H11; unravel in *;
            autorewrite with core in *; inv H; constructor.
      - inv H3; inv H2; inv H10; unravel in *; inv H; constructor.
      - unfold eval_binop in H; inv H0; inv H1; unravel in *;
          try (inv H; constructor);
          try match goal with
              | H: (if ?b then Some _ else None) = Some _
                |- _ => destruct b eqn:?; inv H
              end; constructor.
      - unfold eval_binop in H; inv H0; inv H1; unravel in *;
          try (inv H; constructor);
          try match goal with
              | H: (if ?b then Some _ else None) = Some _
                |- _ => destruct b eqn:?; inv H
              end; constructor.
      - inv H3; inv H4; inv H;
          try match goal with
              | H: (if ?b then None else Some _) = Some _
                |- _ => destruct b eqn:?; inv H
              end; constructor; auto; unfold BitArith.bit_concat; auto.
      - unravel in *; inv H4.
        assert_canonical_forms. inv H1; unravel in *.
        inv H0. auto.
      - inv H3. unravel in *; eauto.
      - constructor. subst es; subst es'.
        apply Forall2_app_inv_l in H5 as
            [ts_prefix [ts_suffix [Hprefix [Hsuffix Hts]]]]; subst.
        apply Forall2_app; auto. inv Hsuffix; constructor; eauto.
      - constructor. subst fs; subst fs'.
        apply Forall2_app_inv_l in H5 as
            [ts_prefix [ts_suffix [Hprefix [Hsuffix Hts]]]]; subst.
        apply Forall2_app; auto. inv Hsuffix; repeat relf_destruct.
        repeat constructor; eauto; unfold equiv in *; unravel in *; subst;
        intuition.
      - inv H3. constructor; auto.
        + subst fs; subst fs'.
          apply Forall2_app_inv_l in H8 as
              [ts_prefix [ts_suffix [Hprefix [Hsuffix Hts]]]]; subst.
          apply Forall2_app; auto. inv Hsuffix; repeat relf_destruct.
          repeat constructor; eauto; unravel in *; subst;
          intuition.
        + constructor.
      - constructor; auto; subst hs; subst hs'.
        rewrite app_length in *; unravel in *. lia.
        apply Forall_app in H11 as [? Hsuffix]; apply Forall_app; split;
          inv Hsuffix; auto. *)
    Admitted.
  End Preservation.

  Section Progress.
    Hypothesis Henvs_sound : envs_sound.

    Theorem expr_small_step_progress : forall e τ,
        ⟦ errs, Γ ⟧ ⊢ e ∈ τ -> value e \/ exists e', ℵ ϵ ** e -->  e'.
    Proof.
      Hint Constructors expr_step : core.
      Hint Resolve eval_cast_exists : core.
      Hint Resolve eval_uop_exists : core.
      destruct Henvs_sound as [Henvs_type Henvs_subset];
      clear Henvs_sound; unfold envs_type, envs_subset in *; intros.
      match goal with H: ⟦ errs, Γ ⟧ ⊢ _ ∈ _ |- _ => induction H end;
      try match goal with
          | |- value ?e \/ _ =>
            assert (value e); [ repeat constructor; eassumption
                          | left; assumption ]
          end;
      repeat match goal with
             | H: value _ \/ (exists _, ℵ ϵ ** _ -->  _)
               |- _ => destruct H as [? | ?]
             | H: exists _, ℵ ϵ ** _ -->  _ |- _ => destruct H as [? ?]
             end; eauto.
      - right; apply Henvs_subset in H as [? ?]; eauto.
      - pose proof eval_cast_exists _ _ _ _ _ H1 H H0 as [? ?]; eauto.
      - pose proof eval_uop_exists _ _ _ _ _ H H1 H0 as [? Huop]; eauto.
    Admitted.
  End Progress.
End Theorems.
