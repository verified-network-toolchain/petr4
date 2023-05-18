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

Ltac invert_type_exp :=
  match goal with
  | H: `⟨ _, _ ⟩ ⊢ _ ∈ _ |- _ => inv H
  end.

Ltac invert_type_lst_ok :=
  match goal with
  | H: type_lst_ok _ _ _ |- _ => inv H
  end.

Section Lemmas.
  Local Hint Constructors lexpr_ok : core.
  
  Lemma shift_lexpr_ok : forall c a e,
      lexpr_ok e -> lexpr_ok (shift_exp c a e).
  Proof.
    intros c a e h; induction h; unravel; auto.
  Qed.
      
  Local Hint Resolve shift_lexpr_ok : core.

  Lemma lexpr_ok_shift : forall c a e,
      lexpr_ok (shift_exp c a e) -> lexpr_ok e.
  Proof.
    intros c a e h; induction e; cbn in *; inv h; auto.
  Qed.

  Local Hint Resolve lexpr_ok_shift : core.
  Local Hint Resolve Forall_impl : core.

  Lemma shift_lexprs_ok : forall c a es,
      Forall lexpr_ok es -> Forall lexpr_ok (map (shift_exp c a) es).
  Proof using.
    intros. rewrite Forall_map. eauto.
  Qed.
  
  Local Hint Constructors typ_ok : core.
  
  Lemma typ_ok_le : forall Δ₁ Δ₂ τ,
      (Δ₁ <= Δ₂)%nat -> typ_ok Δ₁ τ -> typ_ok Δ₂ τ.
  Proof.
    intros m n t hmn h;
      induction t using custom_typ_ind;
      inv h; eauto using Forall_impl_Forall.
    constructor. lia.
  Qed.

  Lemma typ_ok_0 : forall Δ τ,
      typ_ok 0 τ -> typ_ok Δ τ.
  Proof. intros n t; apply typ_ok_le; lia. Qed.
  
  Local Hint Resolve type_lists : core.
  Local Hint Constructors type_lst_ok : core.
  Local Hint Constructors typ_ok_lists : core.

  Variable Δ : nat.
  Variable Γ : list Typ.t.

  Lemma type_exp_typ_ok : forall e τ,
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
      Forall (typ_ok Δ) Γ ->
      typ_ok Δ τ.
  Proof using.
    intros e t het hok;
      induction het using custom_type_exp_ind; auto.
    apply Forall2_only_r_Forall in H2.
    rewrite Forall_forall in H2.
    pose proof (fun t hin => H2 t hin hok) as h; clear H2.
    rewrite <- Forall_forall in h.
    inv H; inv H0; auto.
  Qed.
  
  Lemma typ_of_exp_correct : forall e τ,
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> typ_of_exp e = τ.
  Proof using.
    intros e τ H.
    induction H using custom_type_exp_ind;
      unravel in *; try reflexivity.
    rewrite <- sublist.Forall2_map1,
      Forall2_eq in H2; inv H0; f_equal.
    apply f_equal with (f := @List.length Typ.t) in H5.
    rewrite map_length, repeat_length in H5.
    rewrite <- H5; lia.
  Qed.

  Lemma map_typ_of_exp_correct : forall ts es,
      Forall2 (type_exp Δ Γ) es ts ->
      map typ_of_exp es = ts.
  Proof using.
    intros ts es h.
    rewrite Forall2_forall_nth_error in h.
    destruct h as [hlen h].
    pose proof
      (fun n e t he ht =>
         typ_of_exp_correct _ _ (h n e t he ht)) as H; clear h.
    pose proof (conj hlen H) as h.
    rewrite <- Forall2_forall_nth_error,
      Forall2_map_l, Forall2_eq in h.
    assumption.
  Qed.

  Local Hint Resolve map_typ_of_exp_correct : core.
  
  Lemma typ_of_lists_correct : forall ls t ts es,
      type_lst_ok ls t ts ->
      Forall2 (type_exp Δ Γ) es ts ->
      typ_of_lists ls es = t.
  Proof using.
    intros ls t ts es hok h.
    inv hok; unravel; f_equal; auto.
    apply Forall2_length in h.
    rewrite h, repeat_length.
    lia.
  Qed.
  
  Lemma type_array : forall τ es,
      typ_ok Δ τ ->
      Forall (fun e => `⟨ Δ, Γ ⟩ ⊢ e ∈ τ) es ->
      `⟨ Δ, Γ ⟩ ⊢ Exp.Lists (Lst.Array τ) es
        ∈ Typ.Array (N.of_nat (length es)) τ.
  Proof using.
    intros t es tok Hes; econstructor; eauto.
    rewrite Nnat.Nat2N.id.
    auto using Forall2_repeat_r.
  Qed.

  Lemma type_struct : forall es τs,
      Forall2 (type_exp Δ Γ) es τs ->
      `⟨ Δ, Γ ⟩ ⊢ Exp.Lists Lst.Struct es ∈ Typ.Struct false τs.
  Proof using. eauto. Qed.

  Lemma type_header : forall b es τs,
      Forall2 (type_exp Δ Γ) es τs ->
      `⟨ Δ, Γ ⟩ ⊢ Exp.Lists (Lst.Header b) es ∈ Typ.Struct true τs.
  Proof using. eauto. Qed.
  
  Local Hint Constructors type_exp : core.
  
  Lemma rename_type_exp : forall τs e τ,
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
      `⟨ Δ, τs ++ Γ ⟩
        ⊢ rename_exp (Nat.add (length τs)) e ∈ τ.
  Proof using.
    intros ts e t het.
    induction het using custom_type_exp_ind; unravel in *; eauto.
    - constructor; auto; unravel.
      rewrite nth_error_app3; assumption.
    - econstructor; eauto.
    - econstructor; eauto.
      rewrite <- Forall2_map_l; unravel; assumption.
  Qed.

  Local Hint Rewrite nth_error_shift_var : core.
  
  Lemma shift_type_exp : forall ts1 ts2 e τ,
      `⟨ Δ, ts1 ++ Γ ⟩ ⊢ e ∈ τ ->
      `⟨ Δ, ts1 ++ ts2 ++ Γ ⟩
        ⊢ shift_exp (length ts1) (length ts2) e ∈ τ.
  Proof using.
    intros ts1 ts2 t e h.
    (*generalize dependent ts2.*)
    remember (ts1 ++ Γ) as TS eqn:hTS.
    induction h using custom_type_exp_ind;
      (*intros ts2;*) subst; unravel;
      autorewrite with core; eauto.
    - constructor; autorewrite with core; auto.
    - econstructor; eauto.
    - econstructor; eauto.
      rewrite <- Forall2_map_l; unravel.
      apply Forall2_dumb in H2; assumption || reflexivity.
  Qed.
  
  Local Hint Resolve shift_type_exp : core.
  Local Hint Resolve Forall2_length : core.

  Lemma type_exp_shift : forall ts1 ts2 e τ,
      `⟨ Δ, ts1 ++ ts2 ++ Γ ⟩
        ⊢ shift_exp (length ts1) (length ts2) e ∈ τ ->
      `⟨ Δ, ts1 ++ Γ ⟩ ⊢ e ∈ τ.
  Proof using.
    intros ts1 ts2 e;
      induction e using custom_exp_ind; intros t h;
      cbn in *; inv h; autorewrite with core in *; eauto.
    rewrite <- Forall2_map_l in H5.
    apply Forall_specialize_Forall2 with (vs:=τs) in H; eauto.
    eapply Forall2_impl with
      (R:=fun e t => `⟨ Δ, ts1 ++ ts2 ++ Γ ⟩ ⊢ shift_exp (length ts1) (length ts2) e ∈ t)
      (Q:=fun e t => `⟨ Δ, ts1 ++ Γ ⟩ ⊢ e ∈ t) in H; eauto.
  Qed.
      
  Local Hint Resolve type_exp_shift : core.
  Local Hint Resolve sublist.Forall2_impl : core.

  Lemma shift_type_exps : forall ts1 ts2 es τs,
      Forall2 (type_exp Δ (ts1 ++ Γ)) es τs ->
      Forall2 (type_exp Δ (ts1 ++ ts2 ++ Γ))
        (map (shift_exp (length ts1) (length ts2)) es) τs.
  Proof using.
    intros ts1 ts2 es ts h.
    rewrite <- Forall2_map_l. eauto.
  Qed.

  Lemma shift_type_inn_arg : forall ts1 ts2 e param,
      type_inn_arg Δ (ts1 ++ Γ) e param ->
      type_inn_arg Δ (ts1 ++ ts2 ++ Γ)
        (shift_exp (length ts1) (length ts2) e) param.
  Proof using.
    unfold type_inn_arg.
    intros ts1 ts2 e [_ t].
    auto.
  Qed.

  Local Hint Resolve shift_type_inn_arg : core.

  Lemma type_inn_arg_shift : forall ts1 ts2 e param,
      type_inn_arg Δ (ts1 ++ ts2 ++ Γ)
        (shift_exp (length ts1) (length ts2) e) param ->
      type_inn_arg Δ (ts1 ++ Γ) e param.
  Proof using.
    unfold type_inn_arg.
    intros ts1 ts2 e [_ t].
    eauto.
  Qed.

  Local Hint Resolve type_inn_arg_shift : core.
  
  Lemma shift_type_inn_args : forall ts1 ts2 es params,
      Forall2 (type_inn_arg Δ (ts1 ++ Γ)) es params ->
      Forall2
        (type_inn_arg Δ (ts1 ++ ts2 ++ Γ))
        (map (shift_exp (length ts1) (length ts2)) es)
        params.
  Proof using.
    intros. rewrite <- Forall2_map_l. eauto.
  Qed.

  Local Hint Resolve shift_type_inn_args : core.

  Lemma shift_type_out_arg : forall ts1 ts2 e param,
      type_out_arg Δ (ts1 ++ Γ) e param ->
      type_out_arg Δ (ts1 ++ ts2 ++ Γ)
        (shift_exp (length ts1) (length ts2) e) param.
  Proof using.
    unfold type_out_arg.
    intros ts1 ts2 e [_ t] [ht hl].
    auto.
  Qed.

  Local Hint Resolve shift_type_out_arg : core.

  Lemma type_out_arg_shift : forall ts1 ts2 e param,
      type_out_arg Δ (ts1 ++ ts2 ++ Γ)
        (shift_exp (length ts1) (length ts2) e) param ->
      type_out_arg Δ (ts1 ++ Γ) e param.
  Proof using.
    unfold type_out_arg.
    intros ts1 ts2 e [_ t] [ht hl].
    eauto.
  Qed.

  Local Hint Resolve type_out_arg_shift : core.

  Lemma shift_type_out_args : forall ts1 ts2 es params,
      Forall2 (type_out_arg Δ (ts1 ++ Γ)) es params ->
      Forall2
        (type_out_arg Δ (ts1 ++ ts2 ++ Γ))
        (map (shift_exp (length ts1) (length ts2)) es)
        params.
  Proof using.
    intros. rewrite <- Forall2_map_l. eauto.
  Qed.

  Local Hint Resolve shift_type_out_args : core.
  Local Hint Constructors InOut.Forall2 : core.
  
  Lemma shift_type_args : forall ts1 ts2 args params,
      type_args  Δ (ts1 ++ Γ) args params ->
      type_args Δ (ts1 ++ ts2 ++ Γ)
        (shift_args (length ts1) (length ts2) args) params.
  Proof using.
    unfold type_args.
    intros ts1 ts2 [innargs outargs] [innparams outparams] [hinn hout].
    constructor; cbn in *; eauto.
  Qed.

  Local Hint Resolve shift_type_args : core.

  Lemma type_args_shift : forall ts1 ts2 args params,
      type_args Δ (ts1 ++ ts2 ++ Γ)
        (shift_args (length ts1) (length ts2) args) params ->
      type_args  Δ (ts1 ++ Γ) args params.
  Proof using.
    unfold type_args.
    intros ts1 ts2 [innargs outargs] [innparams outparams] [hinn hout].
    cbn in *.
    rewrite <- Forall2_map_l in hinn,hout.
    apply (sublist.Forall2_impl _ _ (type_inn_arg_shift _ _)) in hinn.
    apply (sublist.Forall2_impl _ _ (type_out_arg_shift _ _)) in hout.
    constructor; cbn; auto.
  Qed.

  Local Hint Resolve type_args_shift : core.
  Local Hint Constructors type_trns : core.

  Lemma shift_type_trns : forall Γ₁ Γ₂ n p,
      type_trns n Δ (Γ₁ ++ Γ) p ->
      type_trns n Δ (Γ₁ ++ Γ₂ ++ Γ) (shift_trns (length Γ₁) (length Γ₂) p).
  Proof using.
    intros G1 G2 n p h; inv h; unravel; eauto.
  Qed.

  Local Hint Resolve shift_type_trns : core.

  Lemma type_trns_shift : forall Γ₁ Γ₂ n p,
      type_trns n Δ (Γ₁ ++ Γ₂ ++ Γ) (shift_trns (length Γ₁) (length Γ₂) p) ->
      type_trns n Δ (Γ₁ ++ Γ) p.
  Proof using.
    intros G1 G2 n p h; destruct p; cbn in *; inv h; eauto.
  Qed.

  Local Hint Resolve type_trns_shift : core.
  Local Hint Constructors type_call : core.
  Local Hint Constructors predop : core.
  Local Hint Constructors relop : core.
  Local Hint Resolve predop_forall_impl : core.
  Local Hint Resolve relop_forall_impl : core.
  Local Hint Resolve shift_type_exps : core.
  
  Lemma shift_type_call : forall Γ₁ Γ₂ fs cx c τs params,
      type_call Δ (Γ₁ ++ Γ) fs cx c τs params ->
      type_call Δ (Γ₁ ++ Γ₂ ++ Γ) fs cx (shift_call (length Γ₁) (length Γ₂) c) τs params.
  Proof using.
    intros G1 G2 fs cx c ts params h; inv h; unravel; eauto.
    - econstructor; eauto.
      + rewrite predop_map. eauto.
      + rewrite relop_map_l. eauto.
    - econstructor; eauto.
      + rewrite predop_map. eauto.
      + rewrite relop_map_l. eauto.
  Qed.

  Local Hint Resolve shift_type_call : core.

  Lemma type_call_shift : forall Γ₁ Γ₂ fs cx c τs params,
      type_call Δ (Γ₁ ++ Γ₂ ++ Γ) fs cx (shift_call (length Γ₁) (length Γ₂) c) τs params ->
      type_call Δ (Γ₁ ++ Γ) fs cx c τs params.
  Proof using.
    intros G1 G2 fs cx c ts params h;
      destruct c; unravel in *; inv h; eauto.
    - rewrite relop_map_l in H6.
      rewrite predop_map in H5.
      apply (predop_forall_impl _ _ (lexpr_ok_shift _ _)) in H5.
      apply (relop_forall_impl _ _ (type_exp_shift _ _)) in H6.
      eauto.
    - rewrite <- Forall2_map_l in H5.
      apply (sublist.Forall2_impl _ _ (type_exp_shift _ _)) in H5.
      eauto.
    - rewrite relop_map_l in H9.
      rewrite predop_map in H8.
      apply (predop_forall_impl _ _ (lexpr_ok_shift _ _)) in H8.
      apply (relop_forall_impl _ _ (type_exp_shift _ _)) in H9.
      eauto.
  Qed.

  Local Hint Resolve type_call_shift : core.
  Local Hint Constructors return_ok : core.
  Local Hint Constructors return_void_ok : core.

  Lemma shift_return_ok : forall Γ₁ Γ₂ cx eo,
      return_ok Δ (Γ₁ ++ Γ) cx eo ->
      return_ok Δ (Γ₁ ++ Γ₂ ++ Γ) cx (option_map (shift_exp (length Γ₁) (length Γ₂)) eo).
  Proof using.
    intros G1 G2 c eo h; inv h; cbn; auto.
  Qed.

  Local Hint Resolve shift_return_ok : core.

  Lemma return_ok_shift : forall Γ₁ Γ₂ cx eo,
      return_ok Δ (Γ₁ ++ Γ₂ ++ Γ) cx (option_map (shift_exp (length Γ₁) (length Γ₂)) eo) ->
      return_ok Δ (Γ₁ ++ Γ) cx eo.
  Proof using.
    intros G1 G2 c [e |] h; inv h; cbn in *; eauto.
  Qed.

  Local Hint Resolve return_ok_shift : core.
  Local Hint Constructors type_stm : core.
  Local Hint Resolve SumForall_forall_impl : core.
  Local Hint Constructors SumForall : core.
  
  Lemma shift_type_stm : forall Γ₁ Γ₂ fs cx s sig,
      `⧼ Δ, Γ₁ ++ Γ, fs, cx ⧽ ⊢ s ⊣ sig ->
      `⧼ Δ, Γ₁ ++ Γ₂  ++ Γ, fs, cx ⧽ ⊢ shift_stm (length Γ₁) (length Γ₂) s ⊣ sig.
  Proof using.
    intros G1 G2 fs cx s sig h.
    remember (G1 ++ Γ) as G.
    generalize dependent G1.
    induction h; intros G1 hG; subst; unravel; eauto.
    - inv H0; cbn; eauto.
    - econstructor; eauto.
      + inv H; cbn; try conj_destr; subst; eauto.
      + unfold id.
        replace (S (length G1)) with (length (τ :: G1)) by reflexivity.
        replace (τ :: G1 ++ G2 ++ Γ) with ((τ :: G1) ++ G2 ++ Γ) by reflexivity.
        eauto.
  Qed.

  Lemma type_stm_shift : forall Γ₁ Γ₂ fs cx s sig,
      `⧼ Δ, Γ₁ ++ Γ₂  ++ Γ, fs, cx ⧽ ⊢ shift_stm (length Γ₁) (length Γ₂) s ⊣ sig ->
      `⧼ Δ, Γ₁ ++ Γ, fs, cx ⧽ ⊢ s ⊣ sig.
  Proof using.
    intros G1 G2 fs cx s;
      generalize dependent cx;
      generalize dependent fs;
      generalize dependent G2;
      generalize dependent G1.
    induction s; intros G1 G2 fs xs sig h; unravel in h; inv h; eauto.
    - destruct lhs; inv H4; eauto.
    - specialize IHs with (G1 := τ :: G1); cbn in IHs.
      destruct init; unravel in *; unfold id in *; inv H4;
        try conj_destr; subst; econstructor; eauto.
  Qed.
End Lemmas.
