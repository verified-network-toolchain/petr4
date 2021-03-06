Require Import Coq.micromega.Lia.
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
Import F.FieldTactics.

Section BigStepTheorems.
  Context {tags_t : Type}.

  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type (errs : errors) (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : name tags_t) (τ : E.t tags_t) (v : V.v tags_t),
      Γ x = Some τ -> ϵ x = Some v -> ∇ errs ⊢ v ∈ τ.
  (**[]*)

  Theorem expr_big_step_preservation :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
      (τ : E.t tags_t) (ϵ : epsilon) (v : V.v tags_t),
      envs_type errs Γ ϵ ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ∇ errs ⊢ v ∈ τ.
  Proof.
    intros errs Γ e τ ϵ v Het Hev.
    generalize dependent τ.
    unfold envs_type in Het.
    induction Hev using custom_expr_big_step_ind;
      intros t Ht; inv Ht; try constructor; eauto.
    - inv H2; auto.
    - apply BitArith.neg_bound.
    - unfold_int_operation; apply IntArith.return_bound_bound.
    - apply IHHev1 in H10; auto; clear IHHev1.
      apply IHHev2 in H11; auto; clear IHHev2.
      destruct op; unfold eval_bit_binop in *;
        inv H; inv H9; constructor;
          try apply BitArith.plus_mod_bound;
          try unfold_bit_operation;
          try apply BitArith.return_bound_bound.
      inv H10; inv H11.
      unfold BitArith.bound, BitArith.upper_bound in *. lia.
    - destruct op; unfold eval_bool_binop in *;
        inv H; inv H9; constructor.
    - unfold eval_bit_binop in *; inv H; constructor.
    - unfold eval_bit_binop in *; inv H; constructor.
    - unfold eval_bit_binop in *; inv H; constructor.
    - inv H10.
    - inv H10.
    - inv H8; constructor.
      unfold BitArith.bit_concat; apply BitArith.return_bound_bound.
    - apply IHHev1 in H10; auto; clear IHHev1.
      apply IHHev2 in H11; auto; clear IHHev2.
      destruct op; unfold eval_bit_binop in *;
        inv H; inv H9; constructor;
          unfold_int_operation;
          try apply IntArith.return_bound_bound.
    - destruct op; unfold eval_bool_binop in *;
        inv H; inv H9; constructor.
    - inv H; constructor.
    - inv H; constructor.
    - inv H9.
    - inv H9.
    - pose proof IHHev Het _ H6 as IH; clear IHHev; inv IH.
      eapply F.get_relfs in H2; eauto.
    - pose proof IHHev Het _ H6 as IH; clear IHHev; inv IH.
      eapply F.get_relfs in H1; eauto.
    - generalize dependent tfs; rename H0 into Hesvs.
      induction H; inv Hesvs;
        intros ts Hests; inv Hests; constructor.
      destruct x as [x [τ e]]; destruct y as [y v];
        destruct y0 as [z t]; repeat invert_relf; simpl in *.
      + split; simpl;
          try (transitivity x; auto; symmetry; assumption);
          destruct H2; auto.
      + apply IHForall2; auto.
    - clear e H6 IHHev Hev.
      generalize dependent tfs; rename H0 into Hesvs.
      induction H; inv Hesvs;
        intros ts Hests; inv Hests; constructor.
      destruct x as [x [τ e]]; destruct y as [y v];
        destruct y0 as [z t]; repeat invert_relf; simpl in *.
      + split; simpl;
          try (transitivity x; auto; symmetry; assumption);
          destruct H2; auto.
      + apply IHForall2; auto.
    - destruct op; simpl in *; constructor;
        pose proof IHHev Het _ H5 as IH; clear IHHev; inv IH; auto.
    - rewrite H8. eapply Forall2_length; eauto.
    - clear n ni H5 H7 H8.
      rename H0 into Hhsvss; rename H9 into Hhs.
      induction H; inv Hhsvss; inv Hhs; constructor;
        destruct y as [b vs]; eauto.
    - pose proof IHHev Het _ H5 as IH; clear IHHev; inv IH.
      eapply Forall_nth_error in H11; eauto; simpl in *.
      inv H11; auto.
  Qed.
End BigStepTheorems.
