Require Import P4cub.BigStep.
Module P := P4cub.AST.P4cub.
Module E := P.Expr.
Module S := P.Stmt.
Module V := Val.

Import Typecheck.
Import Step.
Import P.P4cubNotations.

Section Theorems.
  Context {tags_t : Type}.

  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type (errs : errors) (Γ : gam) (ϵ : epsilon) : Prop :=
    forall (x : name tags_t) (τ : E.t tags_t) (v : V.v tags_t),
      Γ x = Some τ -> ϵ x = Some v /\ V.type_value errs v τ.
  (**[]*)

  (* TODO: figure out how to use notations...*)
  Theorem big_step_preservation :
    forall (errs : errors) (Γ : gam) (e : E.e tags_t) (τ : E.t tags_t)
      (ϵ : epsilon) (v : V.v tags_t),
      envs_type errs Γ ϵ ->
      expr_big_step ϵ e v ->
      check_expr errs Γ e τ ->
      V.type_value errs v τ.
  Proof.
  Abort.
End Theorems.
