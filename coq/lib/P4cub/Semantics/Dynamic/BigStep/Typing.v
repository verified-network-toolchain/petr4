Require Import Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics Require Import Static.Static
     Dynamic.BigStep.Value.Value
     Dynamic.BigStep.Semantics
     Dynamic.BigStep.TypeSoundness.

(** An expession [e] evaluates in a "well-typed" way.
    Progress & preservation included all in one. *)
Definition semantic_exp_typing
  (Δ : nat) (Γ : list Typ.t) (e: Exp.t) (τ : Typ.t) : Prop :=
  forall ϵ : list Val.t,
    Forall2 type_val ϵ Γ ->
    (exists v : Val.t, ⟨ ϵ, e ⟩ ⇓ v) /\
      (forall v : Val.t, ⟨ ϵ, e ⟩ ⇓ v -> ⊢ᵥ v ∈ τ).

Notation "⟪ Δ , Γ ⟫ ⊢ e ∈ τ"
  := (semantic_exp_typing Δ Γ e τ)
       (at level 80, no associativity) : type_scope.

Ltac unfold_sem_typ_exp_goal :=
  match goal with
  | |- ⟪ _ , _ ⟫ ⊢ _ ∈ _
    => unfold semantic_exp_typing;
      intros ϵ henv; split;
      [| intros v Hv; inv Hv]
  end.

Ltac unfold_sem_typ_exp_hyp :=
  match goal with
  | H: ⟪ _ , _ ⟫ ⊢ _ ∈ _
    |- _ => unfold semantic_exp_typing in H
  end.

Ltac unfold_sem_typ_exp :=
  repeat unfold_sem_typ_exp_hyp;
  unfold_sem_typ_exp_goal.

(** Typing Derivations. *)
Section Rules.
  Variable Δ : nat.
  Variable Γ : list Typ.t.

  Local Hint Constructors exp_big_step : core.
  Local Hint Constructors type_val : core.
  
  Lemma sem_typ_bool : forall b : bool,
      ⟪ Δ , Γ ⟫ ⊢ Exp.Bool b ∈ Typ.Bool.
  Proof.
    intros b; unfold_sem_typ_exp; eauto.
  Qed.
  
  Lemma sem_typ_uop : forall op τ τ' e,
      una_type op τ τ' ->
      ⟪ Δ , Γ ⟫ ⊢ e ∈ τ ->
      ⟪ Δ , Γ ⟫ ⊢ Exp.Uop τ' op e ∈ τ'.
  Proof.
    intros op t t' e Huna He; unfold_sem_typ_exp.
  Abort.

  Local Hint Resolve exp_big_step_preservation : core.
  Local Hint Resolve exp_big_step_progress : core.
  
  Lemma soundness : forall e τ,
      `⟨ Δ , Γ ⟩ ⊢ e ∈ τ -> ⟪ Δ , Γ ⟫ ⊢ e ∈ τ.
  Proof.
    intros e t Ht; intros ϵ H; split; eauto;
      destruct H as (? & ?); eauto.
  Qed.

  Local Hint Constructors type_exp : core.
  
  Lemma completeness : forall e τ,
      ⟪ Δ , Γ ⟫ ⊢ e ∈ τ -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ.
  Proof.
    intro e; induction e using custom_exp_ind;
      intros t Hsem; unfold_sem_typ_exp_hyp.
    - (* hmmmm... *)
  Abort.
End Rules.
