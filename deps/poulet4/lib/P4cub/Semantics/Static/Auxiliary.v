Require Import Coq.NArith.BinNat.
From Poulet4 Require Export
     P4cub.Semantics.Static.Typing
     P4cub.Semantics.Static.IndPrincip
     P4cub.Semantics.Static.Util
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
  | H: _ ⊢ₑ _ ∈ _ |- _ => inv H
  end.

Ltac invert_type_lists_ok :=
  match goal with
  | H: type_lists_ok _ _ _ |- _ => inv H
  end.

Section Lemmas.
  Local Hint Resolve type_lists : core.
  Local Hint Constructors type_lists_ok : core.
  Local Hint Constructors t_ok_lists : core.

  Lemma type_array : forall Γ τ es,
      t_ok (type_vars Γ) τ ->
      Forall (fun e => Γ ⊢ₑ e ∈ τ) es ->
      Γ ⊢ₑ Expr.Lists (Expr.lists_array τ) es
        ∈ Expr.TArray (N.of_nat (length es)) τ.
  Proof.
    intros G t es tok Hes; econstructor; eauto.
    rewrite Nnat.Nat2N.id.
    auto using Forall2_repeat_r.
  Qed.

  Lemma type_struct : forall Γ es τs,
      Forall2 (type_expr Γ) es τs ->
      Γ ⊢ₑ Expr.Lists Expr.lists_struct es ∈ Expr.TStruct false τs.
  Proof. eauto. Qed.

  Lemma type_header : forall Γ b es τs,
      Forall2 (type_expr Γ) es τs ->
      Γ ⊢ₑ Expr.Lists (Expr.lists_header b) es ∈ Expr.TStruct true τs.
  Proof. eauto. Qed.

  Local Hint Constructors t_ok : core.
  
  Lemma type_expr_t_ok : forall Γ e τ,
      Γ ⊢ₑ e ∈ τ ->
      Forall (t_ok (type_vars Γ)) (types Γ) ->
      t_ok (type_vars Γ) τ.
  Proof.
    intros G e t het hok;
      induction het using custom_type_expr_ind; auto.
    apply Forall2_only_r_Forall in H2.
    rewrite Forall_forall in H2.
    pose proof (fun t hin => H2 t hin hok) as h; clear H2.
    rewrite <- Forall_forall in h.
    inv H; inv H0; auto.
  Qed.

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
End Lemmas.
