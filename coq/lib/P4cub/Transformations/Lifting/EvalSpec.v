Require Export Coq.micromega.Lia Poulet4.P4cub.Syntax.Syntax Coq.Arith.PeanoNat.
From Poulet4.P4cub Require Export Syntax.Shift Semantics.Dynamic.BigStep.BigStep
  Transformations.Lifting.Lift Semantics.Dynamic.BigStep.Properties
  Transformations.Lifting.Statementize Transformations.Lifting.LiftSpec.
Import Nat.

(** Big-step evaluation specification for lifting in [Statementize.v] *)

Open Scope list_scope.

Notation eval_decl_list := (relate_decl_list exp_big_step).

Section EvalDeclList.
  Variable ϵ : list Val.t.

  Local Hint Resolve relate_decl_list_length : core.
  
  Lemma eval_decl_list_length : forall es vs,
      eval_decl_list ϵ es vs -> length es = length vs.
  Proof using. eauto. Qed.
  
  Local Hint Resolve shift_exp_eval : core.
  Local Hint Resolve relate_decl_list_app : core.
    
  Lemma eval_decl_list_app : forall vs1 vs2 es1 es2,
      eval_decl_list ϵ es1 vs1 ->
      eval_decl_list ϵ es2 vs2 ->
      eval_decl_list ϵ (shift_list shift_exp 0 (length es1) es2 ++ es1) (vs2 ++ vs1).
  Proof using. eauto. Qed.
  
  Local Hint Resolve shift_pairs_relate_snd : core.
  
  Lemma shift_pairs_exp_eval_snd : forall ess vss,
      Forall2 (eval_decl_list ϵ) (map snd ess) vss ->
      eval_decl_list
        ϵ
        (concat (snd (shift_pairs shift_exp ess)))
        (concat vss).
  Proof using. eauto. Qed.

  Local Hint Resolve shift_pairs_relate_fst : core.
  Local Hint Resolve shift_exp_eval : core.
  
  Lemma shift_pairs_exp_eval_fst : forall es ess vs vss,
      length es = length ess ->
      Forall3 (fun vs e v => ⟨ vs ++ ϵ, e ⟩ ⇓ v) vss es vs ->
      Forall2 (eval_decl_list ϵ) ess vss ->
      Forall2
        (exp_big_step (concat vss ++ ϵ))
        (fst (shift_pairs shift_exp (combine es ess))) vs.
  Proof using.
    eapply shift_pairs_relate_fst; eauto.
  Qed.

  Local Hint Resolve shift_couple_relate_decl_list : core.

  Lemma shift_couple_exp_eval_decl_list : forall e1 e2 es1 es2 vs1 vs2,
      eval_decl_list ϵ es1 vs1 ->
      eval_decl_list ϵ es2 vs2 ->
      eval_decl_list
        ϵ
        (snd (shift_couple shift_exp shift_exp e1 e2 es1 es2) ++ es1)
        (vs2 ++ vs1).
  Proof using. eauto. Qed.

  Local Hint Resolve shift_couple_relate_couple : core.

  Lemma shift_couple_exp_eval_couple : forall e1 e2 es1 es2 v1 v2 vs1 vs2,
      eval_decl_list ϵ es1 vs1 ->
      eval_decl_list ϵ es2 vs2 ->
      ⟨ vs1 ++ ϵ, e1 ⟩ ⇓ v1 ->
      ⟨ vs2 ++ ϵ, e2 ⟩ ⇓ v2 ->
      ⟨ vs2 ++ vs1 ++ ϵ, fst (fst (shift_couple shift_exp shift_exp e1 e2 es1 es2)) ⟩ ⇓ v1
      /\ ⟨ vs2 ++ vs1 ++ ϵ, snd (fst (shift_couple shift_exp shift_exp e1 e2 es1 es2)) ⟩ ⇓ v2.
  Proof using. eauto. Qed.
      
End EvalDeclList.

Section EvalExp.
  Variable ϵ : list Val.t.

  Local Hint Resolve eval_decl_list_length : core.
  Local Hint Resolve eval_decl_list_app : core.
  Local Hint Constructors relate_decl_list : core.
  Local Hint Resolve relate_decl_list_length : core.
  Local Hint Resolve relate_decl_list_app : core.
  Local Hint Constructors exp_big_step : core.
  Local Hint Resolve shift_exp_eval : core.
  Local Hint Constructors Forall3 : core.
  Local Hint Resolve shift_couple_exp_eval_couple : core.
  Local Hint Resolve shift_couple_exp_eval_decl_list : core.
  Local Hint Resolve shift_pairs_exp_eval_fst : core.
  Local Hint Resolve shift_pairs_exp_eval_snd : core.
  Local Hint Resolve Forall3_length23 : core.

  Ltac shift_couple_resolve :=
    match goal with
      hes1: eval_decl_list _ ?es1 ?vs1,
      hes2: eval_decl_list _ ?es2 ?vs2,
      he1: ⟨ ?vs1 ++ _, ?e1 ⟩ ⇓ ?v1,
      he2: ⟨ ?vs2 ++ _, ?e2 ⟩ ⇓ ?v2
      |- _ => pose proof shift_couple_exp_eval_couple
              _ _ _ _ _ _ _ _ _ hes1 hes2 he1 he2 as [? ?]
    end.

  Local Hint Extern 3 => shift_couple_resolve : core.
  
  Lemma Lift_exp_good : forall e v,
      ⟨ ϵ, e ⟩ ⇓ v -> forall e' es,
        Lift_exp e e' es -> exists vs,
          eval_decl_list ϵ es vs /\ ⟨ vs ++ ϵ, e' ⟩ ⇓ v.
  Proof using.
    intros e v hev;
      induction hev using custom_exp_big_step_ind;
      intros E Es hn; inv hn; eauto.
    - pose proof IHhev _ _ H5 as (vs & hvs & hv).
      exists (v' :: vs). split; eauto.
    - pose proof IHhev _ _ H4 as (vs & hvs & hv).
      exists (v' :: vs). split; eauto.
    - pose proof IHhev _ _ H5 as (vs & hvs & hv).
      exists (v' :: vs). split; eauto.
    - pose proof IHhev1 _ _ H6 as (vs1 & hvs1 & hv1); clear IHhev1.
      pose proof IHhev2 _ _ H7 as (vs2 & hvs2 & hv2); clear IHhev2.
      exists (v :: vs2 ++ vs1). split; eauto.
      constructor; eauto.
      rewrite <- app_assoc.
      econstructor; eauto.
    - firstorder eauto.
    - pose proof IHhev1 _ _ H5 as (vs1 & hvs1 & hv1); clear IHhev1.
      pose proof IHhev2 _ _ H6 as (vs2 & hvs2 & hv2); clear IHhev2.
      exists (vs2 ++ vs1). rewrite <- app_assoc.
      eauto.
    - pose proof Forall2_specialize_Forall3
        _ _ _ _ _ _ H0 as h; clear H0.
      assert (hlenesvs : length es = length vs)
        by eauto using Forall2_length.
      assert (hlenvses' : length vs = length es').
      { rewrite <- hlenesvs.
        eauto using Forall3_length12. }
      pose proof h _ hlenvses' as h'; clear h; rename h' into h.
      clear hlenesvs hlenvses'.
      assert
        (exists vss,
            Forall2 (eval_decl_list ϵ) ess vss
            /\ Forall3 (fun vs e' v => ⟨ vs ++ ϵ, e' ⟩ ⇓ v) vss es' vs)
        as (vss & hvss & hes').
      { clear dependent ls.
        generalize dependent ess.
        generalize dependent es'.
        induction H; intros es' ih ess IH; inv ih; inv IH; firstorder eauto. }
      clear h.
      exists (Val.Lists ls vs :: concat vss).
      split; auto.
      constructor; eauto.
      apply shift_pairs_exp_eval_snd ; eauto.
      rewrite sublist.combine_snd
        by eauto using Forall3_length23.
      assumption.
  Qed.

  Local Hint Resolve Lift_exp_good : core.
  Local Hint Constructors trns_big_step : core.

  Lemma Lift_trns_good : forall pe lbl,
      p⟨ ϵ, pe ⟩ ⇓ lbl -> forall pe' es,
        Lift_trns pe pe' es -> exists vs,
          eval_decl_list ϵ es vs /\ p⟨ vs ++ ϵ, pe' ⟩ ⇓ lbl.
  Proof using.
    intros pe lbl he pe' es hl.
    inv he; inv hl; eauto.
    pose proof Lift_exp_good _ _ H _ _ H5 as (vs & hvs & hv).
    eauto.
  Qed.

  Local Hint Resolve Lift_trns_good : core.
  Local Hint Resolve shift_lv_eval : core.
  Local Hint Constructors lexp_big_step : core.
  Local Hint Resolve relate_decl_list_det : core.
  Local Hint Resolve exp_deterministic : core.

  Lemma Lift_exp_good_lv : forall e lv,
      l⟨ ϵ, e ⟩ ⇓ lv -> forall e' es,
        Lift_exp e e' es -> exists vs lv',
          eval_decl_list ϵ es vs
          /\ l⟨ vs ++ ϵ, e' ⟩ ⇓ lv'
          /\ lv_lookup ϵ lv = lv_lookup (vs ++ ϵ) lv'.
  Proof using.
    intros e lv H; induction H;
      intros e' es h; inv h; unravel; eauto.
    - pose proof IHlexp_big_step _ _ H5 as (vs & lv' & hvs & hlv' & hlu);
        clear IHlexp_big_step.
      assert (exists v v', ⟨ϵ, e⟩ ⇓ v /\ slice_val hi lo v = Some v')
        as (v & v' & hv & hv').
      { (* TODO: need typing? *) admit. }
      exists (v' :: vs), (Lval.Var 0). cbn.
      repeat split; eauto.
      + constructor; auto.
        econstructor; eauto.
        pose proof Lift_exp_good _ _ hv _ _ H5 as (vs' & hvs' & hv'').
        assert (vs' = vs) by eauto; subst.
        assumption.
      + pose proof lexp_exp_big_step
          _ _ _ _ H hv as hlveq.
        rewrite hlveq.
        destruct v; cbn in *; inv hv'; f_equal.
    - pose proof IHlexp_big_step _ _ H5 as (vs & lv' & hvs & hlv' & hlu).
      eexists; repeat esplit; eauto; cbn.
      rewrite hlu. unfold option_bind.
      reflexivity.
    - pose proof Lift_exp_good _ _ H _ _ H7 as (vs2 & hvs2 & hv2).
      pose proof IHlexp_big_step _ _ H6 as (vs1 & lv1 & hvs1 & hlv1 & hlu).
      eexists; repeat esplit; eauto; cbn; rewrite <- app_assoc.
      + econstructor; eauto. admit. admit.
      + cbn; unfold option_bind.
        replace (vs2 ++ vs1 ++ ϵ) with ([] ++ vs2 ++ vs1 ++ ϵ) by reflexivity.
        rewrite shift_lv_lookup with (rs := []) (us := vs2) (lv := lv1); cbn.
        rewrite hlu. unravel. reflexivity.
  Admitted.
End EvalExp.

Section StatementLifting.
  Context `{ext_sem : Extern_Sem}.

  Local Hint Constructors stm_big_step : core.
  Local Hint Constructors SumForall : core.

  (** Specification of [unwind_vars]. *)
  Lemma eval_decl_list_Unwind : forall ϵ es vs,
      eval_decl_list ϵ es vs ->
      forall vs' ϵ' c Ψ s sig ψ,
        length vs = length vs' ->
        ⧼ Ψ, vs ++ ϵ, c, s ⧽ ⤋ ⧼ vs' ++ ϵ', sig, ψ ⧽ ->
        ⧼ Ψ, ϵ, c, Unwind es s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
  Proof using.
    intros eps es vs h;
      induction h; intros; unravel in *.
    - symmetry in H.
      rewrite length_zero_iff_nil in H.
      subst; assumption.
    - destruct vs' as [| h' vs']; cbn in *; try lia.
      inv H0. eauto.
  Qed.

  Local Hint Resolve eval_decl_list_Unwind : core.
  Local Hint Resolve eval_decl_list_length : core.
  Local Hint Resolve eval_decl_list_app : core.
  Local Hint Resolve relate_decl_list_length : core.
  Local Hint Resolve relate_decl_list_app : core.
  Local Hint Resolve shift_stm_eval : core.
  Local Hint Constructors relop : core.
  Local Hint Constructors ctx_cutoff : core.
  Local Hint Resolve ctx_cutoff_le : core.
  
  Lemma Lift_stm_good : forall Ψ ϵ ϵ' c s sig ψ,
      ctx_cutoff (length ϵ) c ->
      ⧼ Ψ, ϵ, c, s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ -> forall s',
          Lift_stm s s' ->
          ⧼ Ψ, ϵ, c, s' ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
  Proof using.
    intros Psi eps eps' c s sg psi hc hs;
      induction hs; intros σ hσ; inv hσ; eauto.
    - inv H.
      pose proof Lift_exp_good _ _ _ H2 _ _ H1 as (vs & hvs & hv).
      eauto.
    - inv hc. (*eapply eval_decl_list_Unwind; eauto.*) admit.
    - admit.
    - pose proof Lift_exp_good_lv _ _ _ H _ _ H3 as (vs1 & hvs1 & hv1).
      pose proof Lift_exp_good _ _ _ H0 _ _ H5 as (vs2 & hvs2 & hv2).
      eapply eval_decl_list_Unwind; eauto. admit. admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - econstructor; eauto.
      eapply IHhs; cbn; eauto.
    - inv H.
      pose proof Lift_exp_good _ _ _ H1 _ _ H4 as (vs & hvs & hv).
      eapply eval_decl_list_Unwind; eauto.
      apply sbs_letin with (v := v) (v' := v'); auto.
      replace (v :: vs ++ ϵ) with ([v] ++ vs ++ ϵ) by reflexivity.
      replace (v' :: vs ++ ϵ') with ([v'] ++ vs ++ ϵ') by reflexivity.
      replace 1 with (length [v]) by reflexivity.
      rewrite (eval_decl_list_length _ _ _ hvs). 
      eapply shift_stm_eval; cbn; eauto.
      apply IHhs; cbn; eauto.
    - eapply sbs_seq_cont; eauto.
      apply IHhs2; auto.
      erewrite <- sbs_length by eauto; assumption.
    - pose proof Lift_exp_good _ _ _ H _ _ H3 as (vs & hvs & hv).
      rewrite (eval_decl_list_length _ _ _ hvs).
      eapply eval_decl_list_Unwind; eauto.
      econstructor; eauto.
      replace 0 with (@length Val.t []) by reflexivity.
      replace (vs ++ ϵ) with ([] ++ vs ++ ϵ) by reflexivity.
      replace (vs ++ ϵ') with ([] ++ vs ++ ϵ') by reflexivity.
      destruct b; eauto.
  Admitted.
End StatementLifting.
