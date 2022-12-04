Require Import Coq.NArith.BinNat.
From Poulet4 Require Export
     P4cub.Semantics.Static.Typing
     P4cub.Semantics.Static.IndPrincip
     P4cub.Semantics.Static.Util
     P4cub.Syntax.Shift
     Utils.ForallMap.

Ltac inv_numeric_width :=
  match goal with
  | H: numeric_width _ _ |- _ => inv H
  end.

Ltac inv_numeric :=
  match goal with
  | H: numeric _ |- _ => inv H; try inv_numeric_width
  end.

Ltac invert_type_expr :=
  match goal with
  | H: `⟨ _, _ ⟩ ⊢ _ ∈ _ |- _ => inv H
  end.

Ltac invert_type_lists_ok :=
  match goal with
  | H: type_lists_ok _ _ _ |- _ => inv H
  end.

Section Lemmas.
  Local Hint Constructors lvalue_ok : core.
  
  Lemma shift_lvalue_ok : forall sh e,
      lvalue_ok e -> lvalue_ok (shift_e sh e).
  Proof.
    intros sh e h; induction h; unravel; auto.
  Qed.
      
  Local Hint Resolve shift_lvalue_ok : core.
  Local Hint Constructors t_ok : core.
  
  Lemma t_ok_le : forall Δ₁ Δ₂ τ,
      (Δ₁ <= Δ₂)%nat -> t_ok Δ₁ τ -> t_ok Δ₂ τ.
  Proof.
    intros m n t hmn h;
      induction t using custom_t_ind;
      inv h; eauto using Forall_impl_Forall.
    constructor. lia.
  Qed.

  Lemma t_ok_0 : forall Δ τ,
      t_ok 0 τ -> t_ok Δ τ.
  Proof. intros n t; apply t_ok_le; lia. Qed.
  
  Local Hint Resolve type_lists : core.
  Local Hint Constructors type_lists_ok : core.
  Local Hint Constructors t_ok_lists : core.

  Variable Δ : nat.
  Variable Γ : list Expr.t.

  Lemma type_expr_t_ok : forall e τ,
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
      Forall (t_ok Δ) Γ ->
      t_ok Δ τ.
  Proof using.
    intros e t het hok;
      induction het using custom_type_expr_ind; auto.
    apply Forall2_only_r_Forall in H2.
    rewrite Forall_forall in H2.
    pose proof (fun t hin => H2 t hin hok) as h; clear H2.
    rewrite <- Forall_forall in h.
    inv H; inv H0; auto.
  Qed.
  
  Lemma t_of_e_correct : forall e τ,
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> t_of_e e = τ.
  Proof using.
    intros e τ H.
    induction H using custom_type_expr_ind;
      unravel in *; try reflexivity.
    rewrite <- sublist.Forall2_map1,
      Forall2_eq in H2; inv H0; f_equal.
    apply f_equal with (f := @List.length Expr.t) in H5.
    rewrite map_length, repeat_length in H5.
    rewrite <- H5; lia.
  Qed.

  Lemma map_t_of_e_correct : forall ts es,
      Forall2 (type_expr Δ Γ) es ts ->
      map t_of_e es = ts.
  Proof using.
    intros ts es h.
    rewrite Forall2_forall_nth_error in h.
    destruct h as [hlen h].
    pose proof
      (fun n e t he ht =>
         t_of_e_correct _ _ (h n e t he ht)) as H; clear h.
    pose proof (conj hlen H) as h.
    rewrite <- Forall2_forall_nth_error,
      Forall2_map_l, Forall2_eq in h.
    assumption.
  Qed.

  Local Hint Resolve map_t_of_e_correct : core.
  
  Lemma t_of_lists_correct : forall ls t ts es,
      type_lists_ok ls t ts ->
      Forall2 (type_expr Δ Γ) es ts ->
      t_of_lists ls es = t.
  Proof using.
    intros ls t ts es hok h.
    inv hok; unravel; f_equal; auto.
    apply Forall2_length in h.
    rewrite h, repeat_length.
    lia.
  Qed.
  
  Lemma type_array : forall τ es,
      t_ok Δ τ ->
      Forall (fun e => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ) es ->
      `⟨ Δ, Γ ⟩ ⊢ Expr.Lists (Expr.lists_array τ) es
        ∈ Expr.TArray (N.of_nat (length es)) τ.
  Proof using.
    intros t es tok Hes; econstructor; eauto.
    rewrite Nnat.Nat2N.id.
    auto using Forall2_repeat_r.
  Qed.

  Lemma type_struct : forall es τs,
      Forall2 (type_expr Δ Γ) es τs ->
      `⟨ Δ, Γ ⟩ ⊢ Expr.Lists Expr.lists_struct es ∈ Expr.TStruct false τs.
  Proof using. eauto. Qed.

  Lemma type_header : forall b es τs,
      Forall2 (type_expr Δ Γ) es τs ->
      `⟨ Δ, Γ ⟩ ⊢ Expr.Lists (Expr.lists_header b) es ∈ Expr.TStruct true τs.
  Proof using. eauto. Qed.
  
  Local Hint Constructors type_expr : core.
  
  Lemma rename_type_expr : forall τs e τ,
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
      `⟨ Δ, τs ++ Γ ⟩
        ⊢ rename_e (Nat.add (length τs)) e ∈ τ.
  Proof using.
    intros ts e t het.
    induction het using custom_type_expr_ind; unravel in *; eauto.
    - constructor; auto; unravel.
      rewrite nth_error_app3; assumption.
    - econstructor; eauto.
    - econstructor; eauto.
      rewrite <- Forall2_map_l; unravel; assumption.
  Qed.

  Lemma shift_type_expr : forall ts1 ts2 τ e,
      `⟨ Δ, ts1 ++ Γ ⟩ ⊢ e ∈ τ ->
      `⟨ Δ, ts1 ++ ts2 ++ Γ ⟩
        ⊢ shift_e (Shifter (length ts1) (length ts2)) e ∈ τ.
  Proof using.
    intros ts1 ts2 t e h.
    (*generalize dependent ts2.*)
    remember (ts1 ++ Γ) as TS eqn:hTS.
    induction h using custom_type_expr_ind;
      (*intros ts2;*) subst; unravel; eauto.
    - constructor; auto.
      unfold shift_var. destruct_if.
      + assert (length (ts1 ++ ts2) <= length ts2 + x) as h.
        { rewrite app_length. lia. }
        rewrite app_assoc.
        rewrite nth_error_app2 in * by assumption.
        rewrite app_length.
        replace (length ts2 + x - (length ts1 + length ts2))
          with (x - length ts1) by lia.
        assumption.
      + rewrite nth_error_app1 in * by assumption.
        assumption.
    - econstructor; eauto.
    - econstructor; eauto.
      rewrite <- Forall2_map_l; unravel.
      apply Forall2_dumb in H2; assumption || reflexivity.
  Qed.

  Local Hint Resolve shift_type_expr : core.
  Local Hint Constructors rel_paramarg : core.
  
  Lemma shift_type_arg : forall ts1 ts2 arg param,
      type_arg Δ (ts1 ++ Γ) arg param ->
      type_arg Δ (ts1 ++ ts2 ++ Γ)
        (shift_arg (Shifter (length ts1) (length ts2)) arg) param.
  Proof using.
    unfold type_arg.
    intros ts1 ts2 arg param h; inv h; cbn; firstorder auto.
  Qed.
End Lemmas.
