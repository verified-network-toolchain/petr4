Require Export Coq.micromega.Lia Poulet4.P4cub.Syntax.Syntax Coq.Arith.PeanoNat.
From Poulet4.P4cub Require Export Syntax.Shift Semantics.Dynamic.BigStep.BigStep
  Transformations.Lifting.Lift Semantics.Dynamic.BigStep.Properties
  Transformations.Lifting.Statementize.
Import Nat AllCubNotations (*Clmt.Notations*) Val.ValueNotations.

(** Big-step evaluation specification for lifting in [Statementize.v] *)

Open Scope list_scope.

Section EvalDeclList.
  Variable ϵ : list Val.v.

  Inductive eval_decl_list
    : list Expr.e -> list Val.v -> Prop :=
  | eval_decl_nil :
    eval_decl_list [] []
  | eval_decl_cons h hv t tv :
    ⟨ tv ++ ϵ, h ⟩ ⇓ hv ->
    eval_decl_list t tv ->
    eval_decl_list (h :: t) (hv :: tv).

  Local Hint Constructors eval_decl_list : core.

  Lemma eval_decl_list_length : forall l vs,
      eval_decl_list l vs -> length l = length vs.
  Proof using.
    intros l vs h; induction h; cbn; auto.
  Qed.

  Local Hint Resolve shift_e_eval : core.

  Lemma eval_decl_list_app : forall es1 es2 vs1 vs2,
      eval_decl_list es1 vs1 ->
      eval_decl_list es2 vs2 ->
      eval_decl_list (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1) (vs2 ++ vs1).
  Proof using.
    intros es1 es2 vs1 vs2 h1 h2.
    generalize dependent vs1.
    generalize dependent es1.
    induction h2; intros es1 vs1 h1; cbn; auto.
    unfold smother, RecordSet.set; cbn.
    rewrite add_0_r.
    constructor; auto. rewrite <- app_assoc.
    rewrite (eval_decl_list_length _ _ h1).
    rewrite (eval_decl_list_length _ _ h2).
    eauto.
  Qed.

  Lemma shift_pairs_eval_snd : forall ess vss,
      Forall2 eval_decl_list (map snd ess) vss ->
      eval_decl_list
        (concat (map snd (shift_pairs shift_e ess)))
        (concat vss).
  Proof using.
    intros ess vss h.
    remember (map snd ess) as sess eqn:hess.
    generalize dependent ess.
    induction h; intros [| [e es] ess] hess; inv hess;
      unravel in *; auto.
    pose proof IHh ess ltac:(auto) as ih; clear IHh.
    rewrite map_snd_map, map_id.
    assert (list_sum (map (length (A:=Expr.e)) (map snd ess))
            = length (concat (map snd (shift_pairs shift_e ess)))) as hlen.
    { unfold list_sum.
      rewrite <- sublist.length_concat.
      do 2 rewrite <- flat_map_concat_map.
      admit. }
    rewrite hlen. auto.
  Admitted.

  Lemma shift_pairs_eval_fst : forall es ess vs vss,
      length es = length ess ->
      Forall3 (fun vs e' v => ⟨ vs ++ ϵ, e' ⟩ ⇓ v) vss es vs ->
      Forall2 eval_decl_list ess vss ->
      Forall2
        (expr_big_step (concat vss ++ ϵ))
        (map fst (shift_pairs shift_e (combine es ess))) vs.
  Proof.
    intros es ess vs vss hl hF3.
    generalize dependent ess.
    induction hF3; intros [| E ess] hl hF2;
      inv hF2; unravel in *; auto; try discriminate.
    inv hl.
    rewrite <- app_assoc.
    rewrite map_snd_combine by assumption.
    rewrite map_fst_map.
    unfold list_sum.
    rewrite <- sublist.length_concat.
    assert (hlen : length (concat ess) = length (concat ts)).
    { rewrite <- map_snd_combine with (us := us) (vs := ess)
        in H5 by assumption.
      apply shift_pairs_eval_snd in H5.
      apply eval_decl_list_length in H5.
      admit. }
    rewrite hlen.
    rewrite (eval_decl_list_length _ _ H3).
    constructor; auto using shift_e_eval.
    pose proof IHhF3 _ H1 H5 as ih; clear IHhF3.
    clear dependent v.
    clear dependent E.
    clear dependent u.
    clear hlen H5 hF3.
    rewrite Forall2_forall_nth_error in *.
    destruct ih as [hlen ih].
    split.
    - repeat rewrite map_length in *.
      assumption.
    - intros n e v he hv.
      rewrite nth_error_map in he.
      destruct (nth_error (map fst (shift_pairs shift_e (combine us ess))) n)
        as [se |] eqn:hse;
        cbn in *;
        try discriminate.
      inv he.
      pose proof ih _ _ _ hse hv as h.
      pose proof shift_e_eval [] t0 _ _ _ h as H;
        cbn in H.
      assumption.
  Admitted.
End EvalDeclList.

Lemma eval_decl_list_append : forall ϵ vs1 vs2 l1 l2,
    eval_decl_list ϵ l1 vs1 ->
    eval_decl_list (vs1 ++ ϵ) l2 vs2 ->
    eval_decl_list ϵ (l2 ++ l1) (vs2 ++ vs1).
Proof.
  intros ϵ vs1 vs2.
  generalize dependent vs1.
  induction vs2 as [| v2 vs2 ih];
    intros vs1 l1 [| e2 l2] h1 h2; inv h2; cbn; auto.
  constructor; eauto.
  rewrite <- app_assoc; assumption.
Qed.

Section EvalExpr.
  Variable ϵ : list Val.v.

  Local Hint Resolve eval_decl_list_length : core.
  Local Hint Resolve eval_decl_list_app : core.
  Local Hint Constructors eval_decl_list : core.
  Local Hint Constructors expr_big_step : core.
  Local Hint Resolve shift_e_eval : core.
  
  Lemma Lift_e_good : forall e v,
      ⟨ ϵ, e ⟩ ⇓ v -> forall e' es,
        Lift_e e e' es -> exists vs,
          eval_decl_list ϵ es vs /\ ⟨ vs ++ ϵ, e' ⟩ ⇓ v.
  Proof.
    intros e v hev;
      induction hev using custom_expr_big_step_ind;
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
      rewrite (eval_decl_list_length _ _ _ hvs2).
      rewrite (eval_decl_list_length _ _ _ hvs1).
      econstructor; eauto.
      eapply shift_e_eval with (us := []); assumption.
    - firstorder eauto.
    - pose proof IHhev1 _ _ H5 as (vs1 & hvs1 & hv1); clear IHhev1.
      pose proof IHhev2 _ _ H6 as (vs2 & hvs2 & hv2); clear IHhev2.
      exists (vs2 ++ vs1). rewrite <- app_assoc.
      split; eauto.
      rewrite (eval_decl_list_length _ _ _ hvs1).
      rewrite (eval_decl_list_length _ _ _ hvs2).
      econstructor; eauto.
      eapply shift_e_eval with (us := []); eassumption.
    - pose proof Forall2_specialize_Forall3
        _ _ _ _ _ _ H0 as h; clear H0.
      assert (hlenesvs : length es = length vs)
        by eauto using Forall2_length.
      assert (hlenvses' : length vs = length es').
      { rewrite <- hlenesvs.
        eauto using Forall3_length12. }
      pose proof h _ hlenvses' as h'; clear h; rename h' into h.
      clear hlenesvs hlenvses'.
      assert (exists vss, Forall2 (eval_decl_list ϵ) ess vss)
        as [vss hvss] by admit.
      assert (Forall3 (fun vs e' v => ⟨ vs ++ ϵ, e' ⟩ ⇓ v) vss es' vs)
        as hes' by admit.
      clear h.
      exists (Val.Lists ls vs :: concat vss).
      split; auto.
      constructor.
      + constructor.
        apply shift_pairs_eval_fst;
          eauto using Forall3_length23.
      + apply shift_pairs_eval_snd.
        rewrite sublist.combine_snd
          by eauto using Forall3_length23.
        assumption.
  Admitted.

  Local Hint Constructors lexpr_big_step : core.
  Local Hint Resolve Lift_e_good : core.

  Lemma Lift_e_good_lv : forall e lv,
      l⟨ ϵ, e ⟩ ⇓ lv -> forall e' es,
        Lift_e e e' es -> exists vs,
          eval_decl_list ϵ es vs /\ l⟨ vs ++ ϵ, e' ⟩ ⇓ shift_lv (Shifter 0 (length vs)) lv.
  Proof.
    intros e lv H; induction H;
      intros e' es h; inv h; unravel.
    - unfold shift_var; cbn. eexists; eauto.
    - pose proof IHlexpr_big_step _ _ H5 as (vs & hvs & ih); clear IHlexpr_big_step.
      (* May need more complex specification.
         The lvalues may not be syntactically the same
         because of lifting, but should be "equivalent" *)
      admit.
    - pose proof IHlexpr_big_step _ _ H5 as (vs & hvs & ih); clear IHlexpr_big_step.
      eexists; esplit; eauto.
    - pose proof IHlexpr_big_step _ _ H6 as (vs1 & hvs1 & ih); clear IHlexpr_big_step.
      pose proof Lift_e_good _ _ H _ _ H7 as (vs2 & hvs2 & hv2).
      exists (vs2 ++ vs1). split; auto.
      rewrite <- app_assoc.
      rewrite (eval_decl_list_length _ _ _ hvs1).
      rewrite (eval_decl_list_length _ _ _ hvs2).
      econstructor; eauto.
      rewrite app_length.
      rewrite shift_lv_0_add.
      apply shift_lv_eval with (us := []); auto.
  Admitted.
End EvalExpr.

Section StatementLifting.
  Context `{ext_sem : Extern_Sem}.

  Local Hint Constructors stmt_big_step : core.

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
  Local Hint Resolve shift_s_eval : core.
  Local Hint Constructors relop : core.
  Local Hint Constructors ctx_cuttoff : core.
  Local Hint Resolve ctx_cuttoff_le : core.
  
  Lemma Lift_s_good : forall Ψ ϵ ϵ' c s sig ψ,
      ctx_cuttoff (length ϵ) c ->
      ⧼ Ψ, ϵ, c, s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ -> forall s',
          Lift_s s s' ->
          ⧼ Ψ, ϵ, c, s' ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
  Proof using.
    intros Psi eps eps' c s sg psi hc hs;
      induction hs; intros σ hσ; inv hσ; eauto.
    - inv H.
      pose proof Lift_e_good _ _ _ H2 _ _ H1 as (vs & hvs & hv).
      eauto.
    - inv hc. (*eapply eval_decl_list_Unwind; eauto.*) admit.
    - admit.
    - pose proof Lift_e_good_lv _ _ _ H _ _ H3 as (vs1 & hvs1 & hv1).
      pose proof Lift_e_good _ _ _ H0 _ _ H5 as (vs2 & hvs2 & hv2).
      eapply eval_decl_list_Unwind; eauto. admit.
    - admit.
    - admit.
    - admit.
    - econstructor; eauto.
      eapply IHhs; cbn; eauto.
    - pose proof Lift_e_good _ _ _ H _ _ H4 as (vs & hvs & hv).
      eapply eval_decl_list_Unwind; eauto.
      apply sbs_var with (v := v) (v' := v'); auto.
      replace (v :: vs ++ ϵ) with ([v] ++ vs ++ ϵ) by reflexivity.
      replace (v' :: vs ++ ϵ') with ([v'] ++ vs ++ ϵ') by reflexivity.
      replace 1 with (length [v]) by reflexivity.
      rewrite (eval_decl_list_length _ _ _ hvs). 
      eapply shift_s_eval; cbn; eauto.
      apply IHhs; cbn; eauto.
    - eapply sbs_seq_cont; eauto.
      apply IHhs2; auto.
      erewrite <- sbs_length by eauto; assumption.
    - pose proof Lift_e_good _ _ _ H _ _ H3 as (vs & hvs & hv).
      rewrite (eval_decl_list_length _ _ _ hvs).
      eapply eval_decl_list_Unwind; eauto.
      econstructor; eauto.
      replace 0 with (@length Val.v []) by reflexivity.
      replace (vs ++ ϵ) with ([] ++ vs ++ ϵ) by reflexivity.
      replace (vs ++ ϵ') with ([] ++ vs ++ ϵ') by reflexivity.
      destruct b; eauto.
  Admitted.
End StatementLifting.
