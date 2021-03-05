Require Import P4cub.Value.
Require Import P4cub.BigStep.
Module P := P4cub.AST.P4cub.
Module E := P.Expr.
Module S := P.Stmt.
Module V := Val.

Import Typecheck.
Import Step.
Import P.P4cubNotations.
Import V.ValueNotations.
Import V.ValueTyping.

Section Theorems.
  Context {tags_t : Type}.

  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type (errs : errors) (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : name tags_t) (τ : E.t tags_t) (v : V.v tags_t),
      Γ x = Some τ -> ϵ x = Some v /\ ∇ errs ⊢ v ∈ τ.
  (**[]*)

  (* TODO: figure out how to use notations...*)
  Theorem big_step_preservation :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t) (τ : E.t tags_t)
      (ϵ : epsilon) (v : V.v tags_t),
      envs_type errs Γ ϵ ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ∇ errs ⊢ v ∈ τ.
  Proof.
  Abort.
End Theorems.
