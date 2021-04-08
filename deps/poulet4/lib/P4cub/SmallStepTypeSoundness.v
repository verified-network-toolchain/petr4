(* TODO: UNDER MAINTENANCE
Require Import P4cub.SmallStep.
Import IsValue.
Import Step.
Import Typecheck.
Module P := P4cub.AST.P4cub.
Module E := P.Expr.

Import P.P4cubNotations.
Import E.TypeEquivalence.

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
  Context {tags_t : Type}.

  Variable errs : @errors tags_t.

  Variable Γ : @gamma tags_t.

  Section CanonicalForms.
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
    => pose proof canonical_forms_bool _ _ _ Hv Ht as [? [? ?]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ bit<_> |- _
    => pose proof canonical_forms_bit _ _ _ Hv _ Ht as [? [? ?]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ int<_> |- _
    => pose proof canonical_forms_int _ _ _ Hv _ Ht as [? [? ?]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ tuple _ |- _
    => pose proof canonical_forms_tuple _ _ _ Hv _ Ht as [? [? ?]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ rec { _ } |- _
    => pose proof canonical_forms_record _ _ _ Hv _ Ht as [? [? ?]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ hdr { _ } |- _
    => pose proof canonical_forms_header _ _ _ Hv _ Ht as [? [? [? ?]]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ error |- _
    => pose proof canonical_forms_error _ _ _ Hv Ht as [? [? ?]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ matchkind |- _
    => pose proof canonical_forms_matchkind _ _ _ Hv Ht as [? [? ?]]
  | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ stack _[_] |- _
    => pose proof canonical_forms_headerstack _ _ _ Hv _ _ Ht as [? [? ?]]
  end; subst.
(**[]*)

Section Theorems.
  Context {tags_t : Type}.

  Variable Γ : @gamma tags_t.

  Variable ϵ : @eenv tags_t.

  (** Epsilon is a subset of Gamma. *)
  Definition envs_subset : Prop :=
    forall (x : name tags_t) (τ : E.t tags_t),
      Γ x = Some τ -> exists v, ϵ x = Some v.
  (**[]*)

  Variable errs : @errors tags_t.

  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type : Prop :=
    forall (x : name tags_t) (τ : E.t tags_t) (v : E.e tags_t),
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
      Hint Resolve IntArith.return_bound_bound : core.
      Hint Resolve eval_bit_binop_numeric : core.
      Hint Resolve eval_bit_binop_comp : core.
      Hint Resolve eval_int_binop_numeric : core.
      Hint Resolve eval_int_binop_comp : core.
      unfold envs_type in Henvs_type; intros;
      generalize dependent τ;
      match goal with
      | H: ℵ ϵ ** _ -->  _ |- _ => induction H; intros
      end;
      try match goal with
          | H: ∫ ?t1 ≡ ?t2 |- _ => rewrite H in *; clear H
          end;
      try match goal with
          | H : ⟦ errs, Γ ⟧ ⊢ _ ∈ _ |- _ => inv H
          end;
      try assert_canonical_forms;
      try (simpl in *; econstructor; eauto; eassumption);
      try (simpl in *; match goal with
                       | H: Some _ = Some _ |- _ => inv H
                       end; econstructor; eauto);
      try match goal with
          | |- BitArith.bound _ _ => unfold_bit_operation
          | |- IntArith.bound _ _ => unfold_int_operation
          end; eauto.
      - Fail rewrite H10 in H13.
    Admitted.
  End Preservation.
End Theorems.
*)
