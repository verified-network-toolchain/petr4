Require Import P4cub.SmallStep.
Import IsValue.
Import Typecheck.
Module P := P4cub.AST.P4cub.
Module E := P.Expr.

Import P.P4cubNotations.

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

Section CanonicalForms.
  Context {tags_t : Type}.

  Variable errs : @errors tags_t.

  Variable Γ : @gamma tags_t.

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
