Require Import Coq.micromega.Lia.
Require Import P4cub.Value.
Require Import P4cub.BigStep.
Module P := P4cub.AST.P4cub.
Module E := P.Expr.
Module S := P.Stmt.
Module V := Val.
Import P.P4cubNotations.

Import Typecheck.
Import Step.
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

  (** Epsilon is a subset of Gamma. *)
  Definition envs_subset (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : name tags_t) (τ : E.t tags_t),
      Γ x = Some τ -> exists v, ϵ x = Some v.
  (**[]*)

  Definition envs_sound Γ ϵ errs : Prop :=
    envs_type errs Γ ϵ /\ envs_subset Γ ϵ.
  (**[]*)

  Lemma envs_subset_type : forall Γ ϵ errs,
      envs_subset Γ ϵ -> envs_type errs Γ ϵ.
  Proof.
    unfold envs_subset, envs_type.
    intros Γ ϵ errs H x t v Ht Hv.
    apply H in Ht as [v' Hv'].
  Abort.

  Lemma envs_type_subset : forall Γ ϵ errs,
      envs_type errs Γ ϵ -> envs_subset Γ ϵ.
  Proof.
    unfold envs_subset, envs_type.
    intros Γ ϵ errs H x t Ht.
  Abort.

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
    - unfold BitArith.bit_concat; apply BitArith.return_bound_bound.
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
      eapply F.get_relfs in H4; eauto.
    - generalize dependent tfs; rename H0 into Hesvs.
      induction H; inv Hesvs;
        intros ts Hests; inv Hests; constructor.
      destruct x as [x [τ e]]; destruct y as [y v];
        destruct y0 as [z t]; repeat invert_relf; simpl in *.
      + split; simpl;
          try (transitivity x; auto; symmetry; assumption);
          destruct H2; auto.
      + apply IHForall2; auto.
    - clear e H4 H7 IHHev Hev.
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
    - clear n ni H5 H6 H8 H9.
      rename H0 into Hhsvss; rename H10 into Hhs.
      induction H; inv Hhsvss; inv Hhs; constructor;
        destruct y as [b vs]; eauto.
    - pose proof IHHev Het _ H5 as IH; clear IHHev; inv IH.
      inv H11. inv H0. apply PT.pn_header. assumption.
    - pose proof IHHev Het _ H5 as IH; clear IHHev; inv IH.
      eapply Forall_nth_error in H12; eauto; simpl in *.
      inv H12; auto.
  Qed.

  Theorem expr_big_step_progress :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
      (τ : E.t tags_t) (ϵ : epsilon),
      envs_sound Γ ϵ errs ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      exists v : V.v tags_t, ⟨ ϵ, e ⟩ ⇓ v.
  Proof.
    intros errs Γ τ e ϵ [Htyp Hsub] Ht.
    unfold envs_subset, envs_type in *.
    induction Ht using custom_check_expr_ind;
      try (eexists; constructor; assumption).
    - apply Hsub in H. destruct H as [v H'].
      exists v; constructor; auto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as Hpres.
      inv Hpres. exists (V.VBool (negb b)); econstructor; eauto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as Hpres.
      inv Hpres. exists (V.VBit w (BitArith.neg w n)); econstructor; eauto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as Hpres.
      inv Hpres. exists (V.VInt w (IntArith.neg w z)); econstructor; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH1 Ht1 as HP1.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH2 Ht2 as HP2.
      inv H0; inv H2; inv H; inv HP1; inv HP2.
      + remember (@eval_bit_binop tags_t op w n n0) as ebb eqn:eqnop.
        inversion H1; subst op; simpl in *;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto.
      + remember (@eval_int_binop tags_t op w z z0) as ebb eqn:eqnop.
        inversion H1; subst op; simpl in *;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH1 Ht1 as HP1.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH2 Ht2 as HP2.
      inv H0; inv H2; inv H; inv HP1; inv HP2.
      + remember (@eval_bit_binop tags_t op w n n0) as ebb eqn:eqnop.
        inversion H1; subst op; simpl in *;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto.
      + remember (@eval_int_binop tags_t op w z z0) as ebb eqn:eqnop.
        inversion H1; subst op; simpl in *;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH1 Ht1 as HP1.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH2 Ht2 as HP2.
      inv HP1; inv HP2.
      remember (eval_bool_binop op b b0) as ebb eqn:eqnop.
      inversion H; subst op; simpl in *;
        match goal with
        | H: _ = Some ?b |- _ => exists (V.VBool b)
        end; econstructor; simpl in *; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      exists (V.VBool (V.eqbv _ v1 v2)).
      econstructor; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      exists (V.VBool (negb (V.eqbv _ v1 v2))).
      econstructor; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH1 Ht1 as HP1.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH2 Ht2 as HP2.
      inv HP1; inv HP2.
      exists (V.VBit (m + n) (BitArith.bit_concat m n n0 n1));
        econstructor; eauto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      eapply F.relfs_get_r in H3 as [v [Hget HR]]; eauto.
      exists v. econstructor; eauto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      eapply F.relfs_get_r in H2 as [v [Hget HR]]; eauto.
      exists v. econstructor; eauto.
    - induction H; inv H0.
      + exists *{ REC { [] } }*. repeat constructor.
      + destruct x as [x [τ e]]. destruct y as [x' τ'].
        rename l into es. rename l' into ts.
        repeat invert_relf; simpl in *.
        pose proof IHForall2 H7 as [v IH]; clear IHForall2 H7.
        assert (Hes : ⟦ errs, Γ ⟧ ⊢ rec {es} @ i ∈ rec {ts}).
        { econstructor; eauto. }
        pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Hes as HP; inv HP.
        destruct H4 as [Hequivt He].
        pose proof H2 Htyp Hsub as [v Hev]. inv IH.
        exists (V.VRecord ((x,v)::vs)). repeat constructor; auto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      rename H into HPT; rename H0 into H; rename H1 into H0.
      induction H; inv H0.
      + exists *{ HDR { [] } VALID:=b0 }*. repeat constructor; auto.
      + destruct x as [x [τ e]]. destruct y as [x' τ'].
        rename l into es. rename l' into ts.
        repeat invert_relf; simpl in *.
        assert (HPT' : PT.proper_nesting {{ hdr { ts } }}).
        { inv HPT. inv H. inv H5.
          apply PT.pn_header; assumption. }
        pose proof IHForall2 HPT' H7 as [v IHs]; clear IHForall2 H7.
        assert (Hes : ⟦ errs, Γ ⟧ ⊢ hdr {es} valid:=b @ i ∈ hdr {ts}).
        { econstructor; eauto. }
        pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IHs Hes as HP; inv HP.
        destruct H4 as [Hequivt He].
        pose proof H2 Htyp Hsub as [v Hev]. inv IHs.
        exists (V.VHeader ((x,v)::vs) b0). repeat constructor; auto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      destruct op.
      + exists *{ VBOOL b }*. econstructor; simpl; eauto.
      + exists *{ HDR {vs} VALID:=true}*. econstructor; simpl; eauto.
      + exists *{ HDR {vs} VALID:=false}*. econstructor; simpl; eauto.
    - generalize dependent n;
        generalize dependent ni.
      induction H3; inv H4; intros ni n Hbound Hni Hlen Hproper;
        simpl in *; try lia.
      rename l into hs.
      pose proof H2 Htyp Hsub as [v IH]; clear H2.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH H as HP; inv HP.
      destruct hs as [| h hs]; simpl in *.
      + assert (Hn : n = 1%positive) by lia.
        exists (V.VHeaderStack ts [(b,vs)] n ni).
        econstructor; eauto.
      + pose proof IHForall H5 (ni - 1)%N (n - 1)%positive as IHs; clear IHForall H5.
        assert (Hbound' : BitArith.bound 32 (N.pos (n - 1))).
        { unfold BitArith.bound in *; lia. }
        assert (Hni' : (ni - 1 < N.pos (n - 1))%N) by lia.
        assert (Hlen' : (to_nat (n - 1)%positive = 1 + (length hs))%nat) by lia.
        assert (Hproper' : PT.proper_nesting (E.THeaderStack ts (n-1)%positive)).
        { inv Hproper. inv H0.
          apply PT.pn_header_stack. assumption. }
        simpl in *. pose proof IHs Hbound' Hni' Hlen' Hproper' as [v IHs']; clear IHs.
        assert (Hstk : check_expr
                           errs Γ
                           (E.EHeaderStack ts (h::hs) (n-1) (ni-1))
                           (E.THeaderStack ts (n-1))).
        { econstructor; eauto. }
        pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IHs' Hstk as HP; inv HP.
        exists (V.VHeaderStack ts ((b,vs)::hs0) n ni). inv IHs'.
        econstructor; eauto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      assert (Hidx : N.to_nat idx < length hs) by lia.
      pose proof nth_error_exists _ _ Hidx as [[b vs] Hnth].
      pose proof Forall_nth_error _ _ _ _ H7 Hnth as HP; simpl in *.
      exists *{ HDR {vs} VALID:=b }*. econstructor; eauto.
  Qed.
End BigStepTheorems.
