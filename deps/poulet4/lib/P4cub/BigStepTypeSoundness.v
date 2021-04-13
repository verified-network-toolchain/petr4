Require Import Coq.micromega.Lia.
Require Import Poulet4.P4cub.Value.
Require Import Poulet4.P4cub.BigStep.

Module P := Poulet4.P4cub.AST.P4cub.
Module E := P.Expr.
Module S := P.Stmt.
Module V := Val.
Import P.P4cubNotations.

Import Step.
Import Typecheck.
Import V.ValueNotations.
Import V.ValueTyping.
Import F.FieldTactics.

Section BigStepTheorems.
  (** Epsilon's values type's agree with Gamma. *)
  Definition envs_type (errs : errors) (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : string) (τ : E.t) (v : V.v),
      Γ x = Some τ -> ϵ x = Some v -> ∇ errs ⊢ v ∈ τ.
  (**[]*)

  (** Epsilon is a subset of Gamma. *)
  Definition envs_subset (Γ : gamma) (ϵ : epsilon) : Prop :=
    forall (x : string) (τ : E.t),
      Γ x = Some τ -> exists v, ϵ x = Some v.
  (**[]*)

  Definition envs_sound Γ ϵ errs : Prop :=
    envs_type errs Γ ϵ /\ envs_subset Γ ϵ.
  (**[]*)

  Context {tags_t : Type}.

  Theorem expr_big_step_preservation :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
      (τ : E.t) (ϵ : epsilon) (v : V.v),
      envs_type errs Γ ϵ ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      ∇ errs ⊢ v ∈ τ.
  Proof.
    Hint Resolve eval_uop_types : core.
    Hint Resolve eval_bop_type : core.
    Hint Resolve eval_cast_types : core.
    Hint Resolve eval_hdr_op_types : core.
    Hint Resolve eval_stk_op_types : core.
    Hint Constructors PT.proper_nesting : core.
    Hint Constructors check_expr : core.
    unfold envs_type; intros errs Γ e τ ϵ v Het Hev.
    generalize dependent τ.
    induction Hev using custom_expr_big_step_ind; intros t Ht; inv Ht;
    try constructor; eauto;
    repeat match goal with
           | H: error_ok _ _ |- _ => inv H; eauto
           | IHHev: (?P -> forall _, ⟦ errs, Γ ⟧ ⊢ ?e ∈ _ -> ∇ errs ⊢ _ ∈ _),
             HP : ?P, He: (⟦ errs, Γ ⟧ ⊢ ?e ∈ _)
             |- _ => pose proof IHHev HP _ He as IH; clear IHHev; inv IH
           | Hget: F.get _ ?fs = Some ?t, Hfs: F.relfs _ _ ?fs
             |- context [ ?t ] => eapply F.get_relfs in Hfs
           end; eauto.
    - generalize dependent ts;
      induction H; intros []; intros; repeat inv_Forall2_cons; intuition.
    - generalize dependent tfs;
      ind_relfs; intros [| [? ?] ?]; intros;
      repeat invert_nil_cons_relate; repeat invert_cons_cons_relate;
      constructor; unfold F.relf in *; unravel; intuition.
      apply H2; auto.
    - generalize dependent tfs;
      ind_relfs; intros [| [? ?] ?]; intros;
      repeat invert_nil_cons_relate; repeat invert_cons_cons_relate;
      constructor; unfold F.relf in *; unravel; intuition.
      inv H4; try match goal with
                  | H: PT.base_type {{ hdr { _ } }} |- _ => inv H
                  end.
      invert_cons_predfs ; apply H2; auto.
    - apply Forall2_length in H; lia.
    - clear n ni H5 H6 H8 H9; generalize dependent ts;
      induction H; intros []; intros;
        try inv_Forall2_cons; try inv_Forall_cons; intuition.
    - inv H11; try match goal with
                   | H: PT.base_type {{ stack _[_] }} |- _ => inv H
                   end; auto.
    - eapply Forall_nth_error in H12; simpl in *; eauto.
      simpl in *; inv H12; auto.
  Qed.

  Theorem expr_big_step_progress :
    forall (errs : errors) (Γ : gamma) (e : E.e tags_t)
      (τ : E.t) (ϵ : epsilon),
      envs_sound Γ ϵ errs ->
      ⟦ errs, Γ ⟧ ⊢ e ∈ τ ->
      exists v : V.v, ⟨ ϵ, e ⟩ ⇓ v.
  Proof.
    intros errs Γ τ e ϵ [Htyp Hsub] Ht.
    unfold envs_subset, envs_type in *.
    induction Ht using custom_check_expr_ind;
      try (eexists; constructor; assumption).
    - apply Hsub in H. destruct H as [v H'].
      exists v; constructor; auto.
    (*
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as Hpres.
      inv H; inv Hpres.
      + unfold BitArith.bound, BitArith.upper_bound in *;
          simpl in *. assert (Hn : n = 0%N \/ n = 1%N); try lia.
        destruct Hn as [Hn | Hn]; subst;
          [ exists ~{ FALSE }~ | exists ~{ TRUE }~ ];
          econstructor; eauto; reflexivity.
      + destruct z;
          [ exists ~{ w VW N0 }~
          | exists (V.VBit w (BitArith.return_bound w (Npos p)))
          | exists (V.VBit w (BitArith.return_bound w (Npos p))) ];
          econstructor; eauto; destruct w; reflexivity.
      + exists (V.VBit w1 (BitArith.return_bound w1 n));
          econstructor; eauto; destruct w1; reflexivity.
      + exists (V.VInt w1 (IntArith.return_bound w1 z));
          econstructor; eauto; destruct w1; reflexivity.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as Hpres.
      inv H; inv Hpres; eexists; econstructor; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH1 Ht1 as HP1.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH2 Ht2 as HP2.
      inv H; inv H1; inv HP1; inv HP2.
      + remember (eval_bit_binop op w n n0) as ebb eqn:eqnop.
        inversion H0; subst op; simpl in *;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto.
      + remember (eval_int_binop op w z z0) as ebb eqn:eqnop.
        inversion H0; subst op; simpl in *;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH1 Ht1 as HP1.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH2 Ht2 as HP2.
      inv H; inv H1; inv HP1; inv HP2.
      + remember (eval_bit_binop op w n n0) as ebb eqn:eqnop.
        inversion H0; subst op; simpl in *;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto.
      + remember (eval_int_binop op w z z0) as ebb eqn:eqnop.
        inversion H0; subst op; simpl in *;
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
      exists (V.VBool (V.eqbv v1 v2)).
      econstructor; eauto.
    - pose proof IHHt1 Htyp Hsub as [v1 IH1]; clear IHHt1.
      pose proof IHHt2 Htyp Hsub as [v2 IH2]; clear IHHt2.
      exists (V.VBool (negb (V.eqbv v1 v2))).
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
      + exists ~{ TUPLE [] }~. repeat constructor.
      + pose proof IHForall2 H7 as [v IH]; clear IHForall2 H7.
        assert (Hes : ⟦ errs, Γ ⟧ ⊢ tup l @ i ∈ tuple l').
        { econstructor; eauto. }
        pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Hes as HP; inv HP.
        pose proof H5 Htyp Hsub as [v Hev]. inv IH.
        exists (V.VTuple (v :: vs)). repeat constructor; auto.
    - induction H; inv H0.
      + exists ~{ REC { [] } }~. repeat constructor.
      + destruct x as [x [τ e]]. destruct y as [x' τ'].
        rename l into es. rename l' into ts.
        repeat relf_destruct; unfold equiv; simpl in *; subst.
        pose proof IHForall2 H7 as [v IH]; clear IHForall2 H7.
        assert (Hes : ⟦ errs, Γ ⟧ ⊢ rec {es} @ i ∈ rec {ts}).
        { econstructor; eauto. }
        pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Hes as HP; inv HP.
        unfold equiv in *; subst.
        destruct H3 as [Hequivt He]; subst.
        pose proof H2 Htyp Hsub as [v Hev]. inv IH.
        exists (V.VRecord ((x',v)::vs)). repeat constructor; auto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      rename H into HPT; rename H0 into H; rename H1 into H0.
      induction H; inv H0.
      + exists ~{ HDR { [] } VALID:=b0 }~. repeat constructor; auto.
      + destruct x as [x [τ e]]. destruct y as [x' τ'].
        rename l into es. rename l' into ts.
        repeat relf_destruct; unfold equiv in *; simpl in *; subst.
        assert (HPT' : PT.proper_nesting {{ hdr { ts } }}).
        { inv HPT. inv H. invert_cons_predfs.
          apply PT.pn_header; assumption. }
        pose proof IHForall2 HPT' H7 as [v IHs]; clear IHForall2 H7.
        assert (Hes : ⟦ errs, Γ ⟧ ⊢ hdr {es} valid:=b @ i ∈ hdr {ts}).
        { econstructor; eauto. }
        pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IHs Hes as HP; inv HP.
        destruct H3 as [Hequivt He]; unfold equiv in *; subst.
        pose proof H2 Htyp Hsub as [v Hev]. inv IHs.
        exists (V.VHeader ((x',v)::vs) b0). repeat constructor; auto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      destruct op.
      + exists ~{ VBOOL b }~. econstructor; simpl; eauto.
      + exists ~{ HDR {vs} VALID:=true}~. econstructor; simpl; eauto.
      + exists ~{ HDR {vs} VALID:=false}~. econstructor; simpl; eauto.
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
          apply PT.pn_header_stack; assumption. }
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
      exists ~{ HDR {vs} VALID:=b }~. econstructor; eauto.
    - pose proof IHHt Htyp Hsub as [v IH]; clear IHHt.
      pose proof expr_big_step_preservation _ _ _ _ _ _ Htyp IH Ht as HP; inv HP.
      remember (eval_stk_op op size0 ni ts hs) as result eqn:evalopeq.
      destruct op; simpl in *;
        try (match goal with
        | H: context [if ?exp then _ else _] |- _ => destruct exp
        end;
          match goal with
          | H: _ = Some ?v |- _ => exists v
          end; econstructor; simpl in *; eauto;
            match goal with
            | |- context [ if ?exp then _ else _ ] => destruct exp
            end; auto; contradiction).
      + assert (Hnth : exists v, nth_error hs (N.to_nat ni) = Some v).
        { apply nth_error_exists; lia. }
        destruct Hnth as [[b vs] Hnth];
        exists ~{ HDR {vs}VALID := b }~. econstructor; simpl; eauto.
        rewrite Hnth; reflexivity.
      + exists (BigStep.V.VBit 32 (N.pos size0)).
        econstructor; simpl; eauto. *)
  Admitted.
End BigStepTheorems.
