Require Import Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics Require Import Static.Static
     Dynamic.BigStep.Value.Value
     Dynamic.BigStep.Semantics
     Dynamic.BigStep.TypeSoundness.
Import AllCubNotations Val.ValueNotations Val.LValueNotations.

(** An expression [e] evaluates in a "well-typed" way.
    Progress & preservation included all in one. *)
Definition semantic_expr_typing
  (Δ : nat) (Γ : list Expr.t) (e: Expr.e) (τ : Expr.t) : Prop :=
  forall ϵ : list Val.v,
    Forall2 type_value ϵ Γ ->
    (exists v : Val.v, ⟨ ϵ, e ⟩ ⇓ v) /\
      (forall v : Val.v, ⟨ ϵ, e ⟩ ⇓ v -> ⊢ᵥ v ∈ τ).

Notation "⟪ Δ , Γ ⟫ ⊢ e ∈ τ"
  := (semantic_expr_typing Δ Γ e τ)
       (at level 80, no associativity) : type_scope.

Ltac unfold_sem_typ_expr_goal :=
  match goal with
  | |- ⟪ _ , _ ⟫ ⊢ _ ∈ _
    => unfold semantic_expr_typing;
      intros ϵ henv; split;
      [| intros v Hv; inv Hv]
  end.

Ltac unfold_sem_typ_expr_hyp :=
  match goal with
  | H: ⟪ _ , _ ⟫ ⊢ _ ∈ _
    |- _ => unfold semantic_expr_typing in H
  end.

Ltac unfold_sem_typ_expr :=
  repeat unfold_sem_typ_expr_hyp;
  unfold_sem_typ_expr_goal.

(** Typing Derivations. *)
Section Rules.
  Variable Δ : nat.
  Variable Γ : list Expr.t.

  Local Hint Constructors expr_big_step : core.
  Local Hint Constructors type_value : core.
  
  Lemma sem_typ_bool : forall b : bool,
      ⟪ Δ , Γ ⟫ ⊢ b ∈ Expr.TBool.
  Proof.
    intros b; unfold_sem_typ_expr; eauto.
  Qed.
  
  Lemma sem_typ_uop : forall op τ τ' e,
      uop_type op τ τ' ->
      ⟪ Δ , Γ ⟫ ⊢ e ∈ τ ->
      ⟪ Δ , Γ ⟫ ⊢ Expr.Uop τ' op e ∈ τ'.
  Proof.
    intros op t t' e Huop He; unfold_sem_typ_expr.
  Abort.

  Local Hint Resolve expr_big_step_preservation : core.
  Local Hint Resolve expr_big_step_progress : core.
  
  Lemma soundness : forall e τ,
      `⟨ Δ , Γ ⟩ ⊢ e ∈ τ -> ⟪ Δ , Γ ⟫ ⊢ e ∈ τ.
  Proof.
    intros e t Ht; intros ϵ H; split; eauto;
      destruct H as (? & ?); eauto.
  Qed.

  Local Hint Constructors type_expr : core.
  
  Lemma completeness : forall e τ,
      ⟪ Δ , Γ ⟫ ⊢ e ∈ τ -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ.
  Proof.
    intro e; induction e using custom_e_ind;
      intros t Hsem; unfold_sem_typ_expr_hyp.
    - (* hmmmm... *)
  Abort.
End Rules.
