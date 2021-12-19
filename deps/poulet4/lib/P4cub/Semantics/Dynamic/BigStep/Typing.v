Set Warnings "-custom-entry-overridden".
Require Import Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Climate.
From Poulet4.P4cub.Semantics Require Import Static.Static
     Dynamic.BigStep.Value.Value
     Dynamic.BigStep.Semantics
     Dynamic.BigStep.TypeSoundness.
Module V := Val.
Import Step AllCubNotations
       V.ValueNotations V.LValueNotations
       F.FieldTactics ProperType.

(** Semantic expression typing. *)
Reserved Notation "'⟦⟦' dl , gm '⟧⟧' ⊨ e ∈ t"
         (at level 40, e custom p4expr, t custom p4type).

(** An expression [e] evaluates in a "well-typed" way.
    Progress & preservation included all in one. *)
Definition semantic_expr_typing
           {tags_t : Type} (D : Delta) (Γ : Gamma)
           (e: Expr.e tags_t) (t: Expr.t) : Prop :=
  forall ϵ : epsilon,
    envs_sound Γ ϵ D ->
    (exists v : V.v, ⟨ ϵ, e ⟩ ⇓ v) /\
    (forall v : V.v, ⟨ ϵ, e ⟩ ⇓ v -> ∇ ⊢ v ∈ t).

Notation "'⟦⟦' ers , gm '⟧⟧' ⊨ e ∈ t"
  := (semantic_expr_typing ers gm e t).

Ltac unfold_sem_typ_expr_goal :=
  match goal with
  | |- ⟦⟦ _, _ ⟧⟧ ⊨ _ ∈ _
    => unfold semantic_expr_typing,
      envs_sound, envs_type, envs_subset;
      intros ϵ [Het Hes]; split;
      [| intros v Hv; inv Hv]
  end.

Ltac unfold_sem_typ_expr_hyp :=
  match goal with
  | H: ⟦⟦ _, _ ⟧⟧ ⊨ _ ∈ _ |- _
    => unfold semantic_expr_typing,
      envs_sound, envs_type, envs_subset in H
  end.

Ltac unfold_sem_typ_expr :=
  repeat unfold_sem_typ_expr_hyp;
  unfold_sem_typ_expr_goal.

(** Typing Derivations. *)
Section Rules.
  Context {tags_t : Type}.
  Variable Γ : Gamma.
  Variable D : Delta.
  Variable i : tags_t.

  Local Hint Constructors expr_big_step : core.
  Local Hint Constructors type_value : core.
  
  Lemma sem_typ_bool : forall b,
      ⟦⟦ D, Γ ⟧⟧ ⊨ BOOL b @ i ∈ Bool.
  Proof.
    intros b; unfold_sem_typ_expr; eauto.
  Qed.
  
  Lemma sem_typ_uop : forall (op : Expr.uop) (τ τ' : Expr.t) (e : Expr.e tags_t),
      uop_type op τ τ' ->
      ⟦⟦ D, Γ ⟧⟧ ⊨ e ∈ τ ->
      ⟦⟦ D, Γ ⟧⟧ ⊨ UOP op e : τ' @ i ∈ τ'.
  Proof.
    intros op t t' e Huop He; unfold_sem_typ_expr.
    (* Tedious proof... *)
  Abort.

  Local Hint Resolve expr_big_step_preservation : core.
  Local Hint Resolve expr_big_step_progress : core.
  
  Lemma soundness : forall (e : Expr.e tags_t) τ,
      ⟦ D, Γ ⟧ ⊢ e ∈ τ -> ⟦⟦ D, Γ ⟧⟧ ⊨ e ∈ τ.
  Proof.
    intros e t Ht; intros ϵ H; split; eauto;
      destruct H as (? & ?); eauto.
  Qed.

  Local Hint Constructors check_expr : core.
  
  Lemma completeness : forall (e : Expr.e tags_t) τ,
      ⟦⟦ D, Γ ⟧⟧ ⊨ e ∈ τ -> ⟦ D, Γ ⟧ ⊢ e ∈ τ.
  Proof.
    intro e; induction e using custom_e_ind;
      intros t Hsem; unfold_sem_typ_expr_hyp.
    - specialize Hsem with (ϵ := ∅); simpl in *.
      (* hmmmm... *)
  Abort.
End Rules.
