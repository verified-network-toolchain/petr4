Require Export Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.Utils.ForallMap.
From Poulet4.P4cub Require Export Semantics.Static.Static
  Syntax.Shift
  Semantics.Static.Auxiliary
  Transformations.Lifting.Lift
  Transformations.Lifting.LiftSpec.
From RecordUpdate Require Import RecordSet.
Import AllCubNotations RecordSetNotations.

(** Typing specification for lifting in [Statementize.v] *)

Section TypeDeclList.
  Variable Δ : nat.
  Variable Γ : list Expr.t.

  Definition type_decl_list : list Expr.e -> list Expr.t -> Prop :=
    relate_decl_list (type_expr Δ) Γ.

  Local Hint Resolve relate_decl_list_length : core.
  
  Lemma type_decl_list_length : forall es ts,
      type_decl_list es ts -> length es = length ts.
  Proof using.
    unfold type_decl_list; eauto.
  Qed.
  
  Local Hint Resolve shift_type_expr : core.
  Local Hint Resolve relate_decl_list_app : core.
    
  Lemma type_decl_list_app : forall τs1 τs2 es1 es2,
      type_decl_list es1 τs1 ->
      type_decl_list es2 τs2 ->
      type_decl_list (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1) (τs2 ++ τs1).
  Proof using.
    unfold type_decl_list. eauto.
  Qed.

  Local Hint Resolve shift_pairs_relate_snd : core.
    
  Lemma shift_pairs_type_snd : forall ess tss,
      Forall2 type_decl_list (map snd ess) tss ->
      type_decl_list
        (concat (map snd (shift_pairs shift_e ess)))
        (concat tss).
  Proof using.
    unfold type_decl_list. eauto.
  Qed.
  
  Local Hint Resolve shift_pairs_relate_fst : core.
  
  Lemma shift_pairs_relate_fst : forall es ess ts tss,
      length es = length ess ->
      Forall3 (fun ts e t => `⟨ Δ, ts ++ Γ ⟩ ⊢ e ∈ t) tss es ts ->
      Forall2 type_decl_list ess tss ->
      Forall2
        (type_expr Δ (concat tss ++ Γ))
        (map fst (shift_pairs shift_e (combine es ess))) ts.
  Proof using.
    unfold type_decl_list. eauto.
  Qed.
End TypeDeclList.

Section TypeExpr.
  Variable Δ : nat.
  Variable Γ : list Expr.t.

  Local Hint Constructors relate_decl_list : core.
  Local Hint Resolve relate_decl_list_app : core.
  Local Hint Constructors type_expr : core.
  Local Hint Resolve shift_type_expr : core.
  Local Hint Constructors relop : core.
  Local Hint Constructors t_ok : core.
  Local Hint Resolve type_array : core.
  Local Hint Resolve type_struct : core.
  Local Hint Resolve type_header : core.
  Local Hint Constructors type_lists_ok : core.
  Local Hint Constructors t_ok_lists : core.
  Local Hint Constructors Forall3 : core.
  Local Hint Resolve type_expr_t_ok : core.

  Ltac esolve_lift := eexists; esplit; eauto; assumption.

  Local Hint Extern 5 => esolve_lift : core.

  Hypothesis hG : Forall (t_ok Δ) Γ.
  
  Theorem Lift_e_type_expr : forall e τ,
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> forall e' es,
          Lift_e e e' es -> exists τs,
            type_decl_list Δ Γ es τs
            /\ `⟨ Δ, τs ++ Γ ⟩ ⊢ e' ∈ τ.
  Proof using hG Γ Δ.
    unfold type_decl_list.
    intros e t het;
      induction het using custom_type_expr_ind;
      intros E Es h; inv h; eauto.
    - pose proof IHhet hG _ _ H6 as (ts & hts & ht); eauto.
    - pose proof IHhet hG _ _ H5 as (ts & hts & ht); eauto.
    - pose proof IHhet hG _ _ H6 as (ts & hts & ht); eauto.
    - pose proof IHhet1 hG _ _ H7
        as (ts1 & hts1 & ht1); clear IHhet1; eauto.
      pose proof IHhet2 hG _ _ H8
        as (ts2 & hts2 & ht2); clear IHhet2; eauto.
      exists (τ :: ts2 ++ ts1).
      split; eauto.
      constructor; eauto.
      rewrite <- app_assoc.
      erewrite relate_decl_list_length
        with (lb := es1) (la := ts1) by eassumption.
      erewrite relate_decl_list_length
        with (lb := es2) (la := ts2) by eassumption.
      econstructor; eauto.
      eapply shift_type_expr with
        (ts1 := []) (ts2 := ts2); cbn; eauto.
    - pose proof IHhet1 hG _ _ H5
        as (ts1 & hts1 & ht1); clear IHhet1; eauto.
      pose proof IHhet2 hG _ _ H6
        as (ts2 & hts2 & ht2); clear IHhet2; eauto.
      exists (ts2 ++ ts1).
      split; eauto.
      rewrite <- app_assoc.
      erewrite relate_decl_list_length
        with (lb := es1) (la := ts1) by eassumption.
      erewrite relate_decl_list_length
        with (lb := es2) (la := ts2) by eassumption.
      econstructor; eauto.
      eapply shift_type_expr with
        (ts1 := []) (ts2 := ts2); cbn; eauto.
    - pose proof IHhet hG _ _ H6 as (ts & hts & ht); eauto.
    - pose proof Forall2_dumb _ _ _ _ _ _ hG H2 as H'; clear H2.
      pose proof Forall2_specialize_Forall3
        _ _ _ _ _ _ H' as h; clear H'.
      assert (hlenests : length es = length τs)
        by eauto using Forall2_length.
      assert (hlentses' : length τs = length es').
      { rewrite <- hlenests.
        eauto using Forall3_length12. }
      pose proof h _ hlentses' as h'; clear h; rename h' into h.
      clear hlenests hlentses'.
      assert
        (exists tss,
            Forall2 (type_decl_list Δ Γ) ess tss
            /\ Forall3 (fun ts e' t => `⟨ Δ, ts ++ Γ ⟩ ⊢ e' ∈ t) tss es' τs)
        as (tss & htss & hes').
      { clear dependent ls.
        generalize dependent ess.
        generalize dependent es'.
        induction H1; intros es' ih ess IH; inv ih; inv IH; firstorder eauto. }
      clear h.
      pose proof t_of_lists_correct _ _ _ _ _ _ H0 H1; subst.
      exists (t_of_lists ls es :: concat tss).
      split; eauto.
      constructor.
      + econstructor; eauto.
        apply shift_pairs_relate_fst;
          eauto using Forall3_length23.
      + apply shift_pairs_relate_snd; eauto.
        rewrite sublist.combine_snd
          by eauto using Forall3_length23.
        assumption.
  Qed.

  Local Hint Resolve Lift_e_type_expr : core.
  Local Hint Constructors type_prsrexpr : core.

  Lemma Lift_trans_type_prsrexpr : forall total_states pe,
      type_prsrexpr total_states Δ Γ pe -> forall pe' es,
        Lift_trans pe pe' es -> exists ts,
          type_decl_list Δ Γ es ts
          /\ type_prsrexpr total_states Δ (ts ++ Γ) pe'.
    Proof using hG Γ Δ.
      unfold type_decl_list.
      intros n pe hpe pe' es ht.
      inv hpe; inv ht; eauto.
      pose proof Lift_e_type_expr _ _ H0 _ _ H7 as (ts & hts & ht).
      eauto.
    Qed.

    Local Hint Constructors lvalue_ok : core.
    Local Hint Resolve shift_lvalue_ok : core.

    Lemma Lift_e_lvalue_ok : forall e,
        lvalue_ok e -> forall e' es,
          Lift_e e e' es -> lvalue_ok e'.
    Proof using.
      intros e h; induction h;
        intros e' es H; inv H; eauto.
    Qed.

    Local Hint Resolve Lift_e_lvalue_ok : core.
    Local Hint Constructors rel_paramarg : core.

    Lemma Lift_arg_type_arg : forall arg param,
        type_arg Δ Γ arg param -> forall arg' es,
          Lift_arg arg arg' es -> exists ts,
            type_decl_list Δ Γ es ts
            /\ type_arg Δ (ts ++ Γ) arg' param.
    Proof using hG Γ Δ.
      unfold type_arg.
      intros arg param ht arg' es h.
      inv ht; inv h;
        try match goal with
          | h: _ /\ _ |- _ => destruct h as [? ?]
          end;
        try match goal with
          | h: `⟨ _, _ ⟩ ⊢ ?e ∈ _, H: Lift_e ?e _ _
            |- _ => pose proof Lift_e_type_expr _ _ h _ _ H as (ts & hts & ht)
          end; eauto.
    Qed.
End TypeExpr.
(*          
Lemma lift_e_list_type_expr : forall Δ Γ es τs,
    Forall (t_ok Δ) Γ ->
    Forall2 (type_expr Δ Γ) es τs -> forall us les es',
      lift_e_list (length us) es = (les, es') -> exists τs',
        type_decl_list Δ (us ++ Γ) les τs'
        /\ Forall2
            (type_expr Δ (τs' ++ us ++ Γ))
            es' τs.
Proof.
  intros D G es ts hG hets;
    induction hets as [| e t es ts het hests ih];
    intros us les es' h; unravel in *.
  - inv h; eauto.
  - destruct (lift_e (length us) e) as [le e'] eqn:eqle.
    destruct (lift_e_list (length le + length us) es)
      as [les'' es''] eqn:eqles; inv h.
    rename les'' into les; rename es'' into es'.
    eapply lift_e_type_expr in eqle as (ets & hets & he); eauto.
    assert (hleets : length le = length ets) by eauto.
    rewrite hleets, <- app_length in eqles.
    apply ih in eqles as (τs & hτs & ihτs); clear ih.
    rewrite <- app_assoc in *.
    exists (τs ++ ets); split; eauto.
    assert (hlesτs : length les = length τs) by eauto.
    rewrite hlesτs.
    constructor; rewrite <- app_assoc; eauto.
Qed.

Local Hint Constructors type_prsrexpr : core.

Theorem lift_trans_type_expr : forall total_states Δ Γ p,
    Forall (t_ok Δ) Γ ->
    type_prsrexpr total_states Δ Γ p -> forall us l p',
        lift_trans (length us) p = (l, p') -> exists τs,
          type_decl_list Δ (us ++ Γ) l τs
          /\ type_prsrexpr total_states Δ (τs ++ us ++ Γ) p'.
Proof.
  intros n D G p hok ht us l p' hlift.
  inv ht; cbn in hlift.
  - inv hlift. exists []; cbn; split; eauto.
  - destruct (lift_e (length us) e) as [le e'] eqn:hlifte.
    inv hlift.
    pose proof lift_e_type_expr
      _ _ _ _ hok H0 _ _ _ hlifte as (ts' & hts' & Hts').
    exists ts'. split; eauto.
Qed.

Local Hint Constructors lvalue_ok : core.

Lemma lvalue_rename_e : forall ρ e,
    lvalue_ok e -> lvalue_ok (Shift.rename_e ρ e).
Proof.
  intros r e he; induction he; unravel; eauto.
Qed.

Local Hint Resolve lvalue_rename_e : core.

Lemma lvalue_lift_e : forall e,
    lvalue_ok e -> forall e' up l,
      lift_e up e = (l, e') ->
      lvalue_ok e'.
Proof.
  intros e he; induction he;
    intros e' up le hlift; cbn in *.
  - inv hlift; auto.
  - destruct (lift_e up e) as [l' e''] eqn:he''.
    inv hlift; auto.
  - destruct (lift_e up e₁) as [l1 e1] eqn:he1.
    destruct (lift_e (length l1 + up) e₂) as [l2 e2] eqn:he2.
    inv hlift; unravel. eauto.
  - destruct (lift_e up e) as [l' e''] eqn:he''.
    inv hlift; eauto.
Qed.

Local Hint Resolve lvalue_lift_e : core.
Local Hint Constructors type_fun_kind : core.
Local Hint Constructors predop : core.

Lemma type_fun_kind_lift : forall Δ Γ fs c fk τs params,
    Forall (t_ok Δ) Γ ->
    type_fun_kind Δ Γ fs c fk τs params -> forall us l fk',
        lift_fun_kind (length us) fk = (l, fk') -> exists τs',
          type_decl_list Δ (us ++ Γ) l τs'
          /\ type_fun_kind Δ (τs' ++ us ++ Γ) fs c fk' τs params.
Proof.
  intros d G fs c fk ts params hok hfk us l fk' hlift;
    inv hfk; unravel in *.
  - destruct oe as [e |]; unravel in *.
    + inv H0; inv H1.
      destruct (lift_e (length us) e) as [le e'] eqn:hlifte.
      inv hlift.
      pose proof lift_e_type_expr
        _ _ _ _ hok H4 _ _ _ hlifte as (ts' & hts' & Hts').
      exists ts'. split; auto. econstructor; eauto.
      rewrite <- H2. auto.
    + inv H0; inv H1; inv hlift.
      exists []; unravel; split; auto.
      econstructor; eauto. rewrite <- H0. auto.
  - destruct (lift_e_list (length us) cargs) as [le cargs'] eqn:hliftes.
    inv hlift.
    pose proof lift_e_list_type_expr
      _ _ _ _ hok H1 _ _ _ hliftes as (ts' & hts' & Hts').
    exists ts'. split; auto. econstructor; eauto.
  - destruct oe as [e |]; unravel in *.
    + inv H2; inv H3.
      destruct (lift_e (length us) e) as [le e'] eqn:hlifte.
      inv hlift.
      pose proof lift_e_type_expr
        _ _ _ _ hok H6 _ _ _ hlifte as (ts' & hts' & Hts').
      exists ts'. split; auto. econstructor; eauto.
      rewrite <- H4. auto.
    + inv H2; inv H3; inv hlift.
      exists []; unravel; split; auto.
      econstructor; eauto. rewrite <- H2. auto.
Qed.
  
Local Hint Resolve type_fun_kind_lift : core.
Local Hint Constructors type_stmt : core.

Lemma type_decl_list_unwind_vars : forall Δ Γ es τs,
    type_decl_list Δ Γ es τs ->
    forall fs c s sig,
      `⧼ Δ, τs ++ Γ, fs, c ⧽ ⊢ s ⊣ sig ->
      `⧼ Δ, Γ, fs, c ⧽ ⊢ unwind_vars es s ⊣ sig.
Proof.
  unfold unwind_vars.
  intros D G es ts hes; induction hes;
    intros fs c s sig hst; cbn in *; eauto.
Qed.

Local Hint Resolve type_decl_list_unwind_vars : core.
Local Hint Constructors return_void_ok : core.

Theorem lift_s_type_stmt : forall s Δ Γ₁ Γ₂ fs c sig,
    Forall (t_ok Δ) Γ₁ ->
    Forall (t_ok Δ) Γ₂ ->
    `⧼ Δ, Γ₁ ++ Γ₂, fs, c ⧽ ⊢ s ⊣ sig -> forall τs,
        `⧼ Δ, Γ₁ ++ τs ++ Γ₂, fs, c ⧽ ⊢ lift_s (length τs) s ⊣ sig.
Proof.
  intro s; induction s;
    intros D G1 G2 fs c sig hG1 hG2 h ts; inv h; unravel; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct expr as [t | e].
    + destruct H4 as [? hokt]; subst.
      econstructor; eauto.
      replace (τ :: G1 ++ ts ++ G2) with ((τ :: G1) ++ ts ++ G2) by reflexivity.
      eauto.
      (*
      apply IHs.
  - destruct c; destruct e as [e |];
      try contradiction.
    + inv H1; eauto.
    + destruct return_type; try contradiction; eauto.
      destruct (lift_e (length ts) e) as [l e'] eqn:heqlift; unravel.
      pose proof lift_e_type_expr
        _ _ _ _ hok H1 _ _ _ heqlift as (ts' & hts' & Hts').
      eauto.
    + destruct return_type; inv H1; auto.
    + inv H1; auto.
    + inv H1; auto.
  - destruct (lift_trans (length ts) trns) as [le e'] eqn:hlift.
    pose proof lift_trans_type_expr
      _ _ _ _ hok H1 _ _ _ hlift as (ts' & hts' & Hts').
    eauto.
  - destruct (lift_e (length ts) lhs) as [le₁ e₁'] eqn:hlift₁.
    destruct (lift_e (length le₁ + length ts) rhs) as [le₂ e₂'] eqn:hlift₂.
    pose proof lift_e_type_expr
      _ _ _ _ hok H3 _ _ _ hlift₁ as (ts₁ & hts₁ & Hts₁).
    pose proof type_decl_list_length _ _ _ _ hts₁ as hlen₁.
    rewrite hlen₁ in hlift₂.
    rewrite <- app_length in hlift₂.
    pose proof lift_e_type_expr
      _ _ _ _ hok H5 _ _ _ hlift₂ as (ts₂ & hts₂ & Hts₂).
    pose proof type_decl_list_length _ _ _ _ hts₂ as hlen₂.
    rewrite <- app_assoc in hts₂, Hts₂.
    pose proof shift_type ts₂ _ _ _ _ Hts₁ as h₂.
    rewrite hlen₂.
    eapply type_decl_list_unwind_vars; eauto.
    rewrite <- app_assoc. econstructor; eauto.
  - destruct (lift_fun_kind (length ts) call) as [lfk fk'] eqn:hliftfk.
    pose proof type_fun_kind_lift
      _ _ _ _ _ _ _ hok H1 _ _ _ hliftfk as (ts' & hts' & Hts').
    admit.
  - admit.
  - destruct expr as [t | e].
    + destruct H4 as [? H]; subst. econstructor; eauto.*)
      
      
Admitted.*)
