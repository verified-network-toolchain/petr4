Require Import Coq.Arith.PeanoNat.
From Poulet4 Require Import P4cub.Syntax.Syntax
  P4cub.Semantics.Climate Utils.ForallMap
  P4cub.Syntax.Shift.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Syntax BigStep.Semantics BigStep.IndPrincip
     BigStep.Value.Typing BigStep.Determinism.
Import AllCubNotations Val.ValueNotations
  Val.LValueNotations Nat.

Ltac len_app :=
  match goal with
| hlen: length ?l1 = length ?l2, happ: ?l1 ++ _ = ?l2 ++ _
  |- _ => pose proof sublist.app_eq_len_eq happ hlen as [? ?]; subst
  end.

Variant ctx_cuttoff (m : nat) : ctx -> Prop :=
  | ctx_cuttoff_action aa :
    ctx_cuttoff m (CAction aa)
  | ctx_cuttoff_function :
    ctx_cuttoff m CFunction
  | ctx_cuttoff_applyblock ts aa ac :
    ctx_cuttoff m (CApplyBlock ts aa ac)
  | ctx_cuttoff_parserstate n strt sts ap :
    n <= m ->
    ctx_cuttoff m (CParserState n strt sts ap).

Section Properties.
  Local Hint Constructors ctx_cuttoff : core.

  Lemma ctx_cuttoff_le : forall l m c,
      m <= l ->
      ctx_cuttoff m c ->
      ctx_cuttoff l c.
  Proof using.
    intros l m c hml hc; inv hc; auto.
    constructor. lia.
  Qed.

  Local Hint Resolve ctx_cuttoff_le : core.
  Local Hint Resolve ForallMap.Forall2_dumb : core.
  Local Hint Constructors expr_big_step : core.
  Local Hint Extern 1 => len_app : core.

  Lemma shift_e_eval : forall us vs ϵ e v,
      ⟨ us ++ ϵ, e ⟩ ⇓ v ->
      ⟨ us ++ vs ++ ϵ,
        shift_e
          (Shifter (length us) (length vs)) e ⟩ ⇓ v.
  Proof using.
    intros us vs ϵ e v h.
    remember (us ++ ϵ) as usϵ eqn:husϵ.
    generalize dependent ϵ.
    generalize dependent us.
    induction h using custom_expr_big_step_ind;
      intros us eps huseps; subst;
      unravel; eauto.
    - unfold shift_var. unravel.
      constructor. destruct_if.
      + rewrite nth_error_app2 in * by lia.
        rewrite <- Nat.add_sub_assoc by lia.
        rewrite nth_error_app3.
        assumption.
      + rewrite nth_error_app1 in * by lia.
        assumption.
    - rewrite Forall2_forall_nth_error in H0.
      destruct H0 as [Hlen HF2].
      pose proof
        (conj Hlen
           (fun n e v he hv =>
              HF2 n e v he hv us eps Logic.eq_refl))
        as HF2'.
      rewrite <- Forall2_forall_nth_error in HF2'.
      clear HF2 Hlen.
      constructor.
      rewrite sublist.Forall2_map1.
      assumption.
  Qed.

  Local Hint Resolve shift_e_eval : core.
  Local Hint Constructors parser_expr_big_step : core.

  Lemma shift_trans_eval : forall us ϵ p st,
      p⟨ us ++ ϵ , p ⟩ ⇓ st -> forall vs,
        p⟨ us ++ vs ++ ϵ , shift_transition (Shifter (length us) (length vs)) p ⟩ ⇓ st.
  Proof using.
    intros us eps p st h vs.
    inv h; unravel; auto.
  Qed.

  Local Hint Resolve shift_trans_eval : core.

  Fixpoint shift_lv (sh : shifter) (lv : Val.lv) : Val.lv :=
  match lv with
  | Val.Var x => Val.Var $ shift_var sh x
  | Val.Slice hi lo lv => Val.Slice hi lo $ shift_lv sh lv
  | Val.Member x lv => Val.Member x $ shift_lv sh lv
  | Val.Index n lv => Val.Index n $ shift_lv sh lv
  end.

  Lemma shift_lv_0_add : forall lv m n,
      shift_lv (Shifter 0 (m + n)) lv = shift_lv (Shifter 0 m) (shift_lv (Shifter 0 n) lv).
  Proof using.
    intro lv; induction lv; intros m n; unravel; f_equal; auto.
    unfold shift_var; cbn. lia.
  Qed.
  
  Lemma shift_lv_0 : forall lv c, shift_lv (Shifter c 0) lv = lv.
  Proof using.
    intros lv c; induction lv; unravel; f_equal; auto.
    unfold shift_var. destruct_if; reflexivity.
  Qed.
  
  Local Hint Constructors lexpr_big_step : core.

  Lemma shift_lv_eval : forall us vs ϵ e lv,
      l⟨ us ++ ϵ, e ⟩ ⇓ lv ->
      l⟨ us ++ vs ++ ϵ,
          shift_e
            (Shifter (length us) (length vs)) e ⟩
        ⇓ shift_lv (Shifter (length us) (length vs)) lv.
  Proof using.
    intros us vs eps e lv h.
    remember (us ++ eps) as useps eqn:huseps.
    generalize dependent eps.
    generalize dependent us.
    induction h; intros; subst; unravel; eauto.
  Qed.

  Local Hint Resolve shift_lv_eval : core.

  Lemma shift_lv_lookup : forall lv rs us ϵ,
      lv_lookup (rs ++ us ++ ϵ) (shift_lv (Shifter (length rs) (length us)) lv)
      = lv_lookup (rs ++ ϵ) lv.
  Proof using.
    intro lv; induction lv; intros; unravel.
    - unfold shift_var, cutoff,amt.
      destruct_if.
      + rewrite nth_error_app2
          with (n := x) by assumption.
        rewrite nth_error_app2
          with (n := length us + x) by lia.
        replace (length us + x - length rs)
          with (length us + (x - length rs)) by lia.
        rewrite nth_error_app3.
        reflexivity.
      + rewrite nth_error_app1 by lia.
        rewrite nth_error_app1 by assumption.
        reflexivity.
    - rewrite IHlv. reflexivity.
    - rewrite IHlv. reflexivity.
    - rewrite IHlv. reflexivity.
  Qed.

  Local Hint Rewrite shift_lv_lookup : core.

  Lemma shift_lv_update : forall lv v rs ϵ rs' ϵ',
      length rs = length rs' ->
      lv_update lv v (rs ++ ϵ) = rs' ++ ϵ' -> forall us,
          lv_update (shift_lv (Shifter (length rs) (length us)) lv) v (rs ++ us ++ ϵ)
          = rs' ++ us ++ ϵ'.
  Proof using.
    intro lv; induction lv;
      intros v rs eps rs' eps' hrs hlv us;
      unravel in *; autorewrite with core.
    - unfold shift_var, cutoff, amt.
      destruct_if.
      + rewrite nth_update_app1 in * by lia.
        replace (length us + x - length rs)
          with (length us + (x - length rs)) by lia.
        rewrite nth_update_app3.
        pose proof sublist.app_eq_len_eq hlv hrs as [hrs' heps]; subst.
        reflexivity.
      + rewrite nth_update_app2 in * by lia.
        assert (length (nth_update x v rs) = length rs') as hup.
      { rewrite nth_update_length. assumption. }
      pose proof sublist.app_eq_len_eq hlv hup as [hrs' heps]; subst.
      reflexivity.
    - destruct v; auto.
      destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
    - destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
    - destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
  Qed.

  Local Hint Resolve lv_update_length : core.
  Local Hint Rewrite lv_update_length : core.
  
  Lemma lv_update_signal_length : forall olv sig ϵ,
      length (lv_update_signal olv sig ϵ) = length ϵ.
  Proof using.
    intros [] [| | | | []] ϵ; cbn; auto.
  Qed.

  Local Hint Resolve lv_update_signal_length : core.
  Local Hint Rewrite lv_update_signal_length : core.
  
  Lemma copy_out_from_args_length : forall vs₁ vs₂ ϵ,
      length (copy_out_from_args vs₁ vs₂ ϵ) = length ϵ.
  Proof using.
    intro vs1; induction vs1 as [| [] vs1 ih];
      intros [| [] vs2] ϵ; cbn in *;
      try rewrite ih; auto.
  Qed.

  Local Hint Resolve copy_out_length : core.
  Local Hint Rewrite copy_out_length : core.
  Local Hint Resolve copy_out_from_args_length : core.
  Local Hint Rewrite copy_out_from_args_length : core.

  Lemma lexpr_expr_big_step : forall ϵ e lv v,
      l⟨ ϵ, e ⟩ ⇓ lv -> ⟨ ϵ, e ⟩ ⇓ v -> lv_lookup ϵ lv = Some v.
  Proof.
    intros eps e lv v helv; generalize dependent v.
    induction helv; intros V hv; inv hv; unravel; auto.
    - rewrite (IHhelv _ H4).
      destruct v; unravel in *; inv H3; do 2 f_equal.
    - rewrite (IHhelv _ H4). assumption.
    - rewrite (IHhelv _ H5).
      rewrite <- H3. f_equal.
      pose proof expr_deterministic _ _ _ _ H H6 as h; inv h. lia.
  Qed.
  
  Context `{ext_sem : Extern_Sem}.

  Local Hint Rewrite app_length : core.
  
  Lemma sbs_length : forall Ψ ϵ ϵ' c s sig ψ,
      ⧼ Ψ, ϵ, c, s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ -> length ϵ = length ϵ'.
  Proof using.
    intros Ψ ϵ ϵ' c s sig ψ h;
      induction h; autorewrite with core in *; auto; lia.
  Qed.

  Local Hint Constructors relop : core.
  Local Hint Constructors stmt_big_step : core.

  Lemma shift_args_eval : forall us eps c data_args vdata_args vs,
      cutoff c = length us ->
      amt c = length vs ->
      args_big_step (us ++ eps) data_args vdata_args ->
      args_big_step (us ++ vs ++ eps)
                    (map (shift_arg c)
                         data_args)
                    (map (paramarg_map id (shift_lv c))
                       vdata_args).
  Proof.
    unfold args_big_step, arg_big_step.
    intros.
    destruct c; simpl in *; subst.
    eapply Forall2_map_l with (lc := data_args).
    eapply Forall2_map_r with (lc := vdata_args).
    eapply sublist.Forall2_impl; try eassumption.
    intros.
    inversion H; subst; constructor; eauto.
  Qed.

  Lemma shift_copy_in :
    forall c us vs vargs eps eps',
      cutoff c = length us ->
      amt c = length vs ->
      copy_in vargs (us ++ eps) = Some eps' ->
      copy_in
        (map (paramarg_map id (shift_lv c)) vargs)
        (us ++ vs ++ eps) = Some eps'.
  Proof.
    intros.
    revert H1.
    unfold copy_in, pipeline.
    destruct c; cbn in *; subst.
    rewrite !map_map.
    intro.
    apply Forall2_sequence_iff.
    apply Forall2_map_l with (lc := vargs).
    apply Forall2_sequence_iff in H1.
    apply Forall2_map_l with (lc := vargs) in H1.
    eapply sublist.Forall2_impl; try eassumption.
    intros.
    destruct a; simpl in *; auto;
      now rewrite shift_lv_lookup.
  Qed.

  Lemma split_by_length:
    forall A (l: list A) m n,
      length l = n + m ->
      exists xs ys,
        l = xs ++ ys /\
        length xs = n /\
        length ys = m.
  Proof.
    intros.
    exists (firstn n l).
    exists (skipn n l).
    intuition.
    - auto using firstn_skipn.
    - rewrite firstn_length.
      lia.
    - rewrite skipn_length.
      lia.
  Qed.

  Lemma shift_copy_out :
    forall vargs c us vs eus eps eps'' eps' us',
      cutoff c = Datatypes.length us ->
      amt c = Datatypes.length vs ->
      length us = length us' ->
      length eus = length us' ->
      copy_out vargs (eus ++ eps'') (us ++ eps) = us' ++ eps' ->
      copy_out (map (paramarg_map id (shift_lv c)) vargs)
               (eus ++ vs ++ eps'')
               (us ++ vs ++ eps) = us' ++ vs ++ eps'.
  Proof.
    induction vargs; intros.
    - simpl in *.
      apply sublist.app_eq_len_eq in H3; eauto.
      intuition congruence.
    - simpl in *.
      revert H3.
      cut ((copy_out vargs (eus ++ eps'') (us ++ eps) = us' ++ eps' ->
           copy_out (map (paramarg_map id (shift_lv c)) vargs)
                    (eus ++ vs ++ eps'') (us ++ vs ++ eps) =
             us' ++ vs ++ eps') /\
             (forall b,
                 (a = PAOut b \/ a = PAInOut b) ->
                 match lv_lookup (eus ++ eps'') b with
                 | Some v =>
                     lv_update b v
                               (copy_out vargs (eus ++ eps'') (us ++ eps))
                 | None => copy_out vargs (eus ++ eps'') (us ++ eps)
                 end = us' ++ eps' ->
                 match lv_lookup (eus ++ vs ++ eps'') (shift_lv c b) with
                 | Some v =>
                     lv_update (shift_lv c b) v
                               (copy_out (map (paramarg_map id (shift_lv c)) vargs)
                                         (eus ++ vs ++ eps'') (us ++ vs ++ eps))
                 | None =>
                     copy_out (map (paramarg_map id (shift_lv c)) vargs)
                              (eus ++ vs ++ eps'') (us ++ vs ++ eps)
                 end = us' ++ vs ++ eps')).
      {
        intros.
        destruct a; cbn in *; intuition.
      }
      split.
      + apply IHvargs; eauto.
      + intros.
        destruct c.
        simpl in H, H0.
        rewrite H, H0.
        simpl in *.
        replace (Datatypes.length us) with (Datatypes.length eus)
          by congruence.
        erewrite shift_lv_lookup.
        destruct (lv_lookup _ _); cbn in *.
        * pose proof (copy_out_length vargs (eus ++ eps'') (us ++ eps)).
          rewrite app_length in *.
          apply split_by_length in H5.
          destruct H5 as [xs [ys [? [? ?]]]].
          rewrite H5 in *.
          erewrite IHvargs with (us' := xs);
             cbn; eauto; try congruence.
          replace (length eus) with (length xs) by congruence.
          eapply shift_lv_update; eauto; congruence.
        * eapply IHvargs; eauto.
          simpl.
          congruence.
  Qed.

  Lemma shift_lv_update_signal :
    forall olv sig vargs c us eps eps' us' eus vs eps'',
      cutoff c = length us ->
      amt c = length vs ->
      length us = length us' ->
      length eus = length us' ->
      lv_update_signal olv sig (copy_out vargs (eus ++ eps'') (us ++ eps))
      = us' ++ eps' ->
      lv_update_signal
        (option_map (shift_lv c) olv)
        sig
        (copy_out (map (paramarg_map id (shift_lv c)) vargs)
                  (eus ++ vs ++ eps'')
                  (us ++ vs ++ eps))
      = us' ++ vs ++ eps'.
  Proof.
    unfold lv_update_signal.
    intros.
    destruct olv; simpl in *.
    - destruct sig; eauto using shift_copy_out.
      destruct v; simpl in *; eauto using shift_copy_out.
      remember (copy_out _ _ _) as es in *.
      set (vargs' := (map _ _)).
      remember (copy_out vargs' _ _) as es'.
      symmetry in Heqes, Heqes'.
      pose proof (copy_out_length vargs eps'' (us ++ eps)).
      pose proof (copy_out_length vargs eps'' (us ++ eps)).
      assert (length es = length (us ++ eps))
        by (subst es; apply copy_out_length).
      pose proof (firstn_skipn (length us) es).
      set (us0 := firstn _ es) in *.
      set (es0 := skipn _ es) in *.
      destruct c.
      rewrite !app_length in *.
      assert (cutoff = length us0).
      {
        cbn in *.
        unfold us0.
        rewrite firstn_length.
        subst es.
        erewrite copy_out_length.
        rewrite app_length.
        lia.
      }
      subst cutoff.
      replace amt with (length vs).
      rewrite <- H7 in Heqes.
      eapply shift_copy_out with (vs := vs) in Heqes;
        eauto; [|cbn in *; congruence].
      subst vargs'.
      rewrite Heqes in Heqes'.
      subst es'.
      rewrite <- H7 in *.
      unfold us0.
      cbn in *.
      eapply shift_lv_update; eauto.
      rewrite firstn_length.
      rewrite <- H7.
      rewrite app_length.
      lia.
    - eauto using shift_copy_out.
  Qed.

  Lemma length_copy_in :
    forall vargs l eps,
      copy_in vargs l = Some eps ->
      length eps = length vargs.
  Proof.
    unfold copy_in.
    intros.
    apply sequence_length in H.
    simpl in H.
    unfold pipeline in H.
    rewrite map_length in H.
    auto.
  Qed.

  Lemma shift_s_eval : forall Ψ us us' ϵ ϵ' c s sig ψ,
      length us = length us' ->
      ctx_cuttoff (length ϵ) c ->
      ⧼ Ψ , us ++ ϵ , c , s ⧽ ⤋ ⧼ us' ++ ϵ' , sig , ψ ⧽ -> forall vs,
          ⧼ Ψ , us ++ vs ++ ϵ , c ,
            shift_s (Shifter (length us) (length vs)) s ⧽
            ⤋ ⧼ us' ++ vs ++ ϵ' , sig , ψ ⧽.
  Proof using.
    intros Psi us us' eps eps' c s sig psi hus hc hs.
    remember (us ++ eps) as useps eqn:huseps.
    remember (us' ++ eps') as useps' eqn:huseps'.
    generalize dependent eps'.
    generalize dependent us'.
    generalize dependent eps.
    generalize dependent us.
    induction hs; intros; unravel; subst; eauto.
    - inv H; unravel; auto.
    - pose proof sbs_length _ _ _ _ _ _ _ hs as hlen.
      pose proof app_eq_app _ _ _ _ huseps as [l2 heps2].
      pose proof app_eq_app _ _ _ _ huseps' as [l3 heps3].
      inv hc.
      destruct heps2 as [[hl2 heps2] | [hl2 hesp2]];
        destruct heps3 as [[hl3 heps3] | [hl3 hesp3]]; subst.
      + rewrite <- app_assoc in huseps,  huseps'.
        pose proof sublist.app_eq_len_eq huseps' hus as [huseq heps]; subst.
        rewrite app_inv_head_iff in hl3, huseps'; subst.
        do 4 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc in H1.
        do 2 rewrite <- app_assoc.
        eauto.
      + rewrite <- app_assoc in hus.
        repeat rewrite app_length in *.
        assert (hlen2 : length l2 = 0) by lia.
        assert (hlen3 : length l3 = 0) by lia.
        rewrite length_zero_iff_nil in hlen2.
        rewrite length_zero_iff_nil in hlen3.
        subst; cbn in *.
        repeat rewrite <- app_assoc in *; cbn in *.
        do 2 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc.
        eauto.
      + rewrite <- app_assoc in hus.
        repeat rewrite app_length in *.
        assert (hlen2 : length l2 = 0) by lia.
        assert (hlen3 : length l3 = 0) by lia.
        rewrite length_zero_iff_nil in hlen2.
        rewrite length_zero_iff_nil in hlen3.
        subst; cbn in *.
        repeat rewrite <- app_assoc in *; cbn in *.
        do 2 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc.
        do 2 rewrite add_0_r.
        eauto.
      + repeat rewrite app_length in * |-.
        assert (hl23 : length l2 = length l3) by lia.
        assert (hepslen : length eps = length eps') by lia.
        assert (hlen2 : length l2 = 0) by lia.
        rewrite length_zero_iff_nil in hlen2.
        subst; cbn in *.
        symmetry in hl23.
        rewrite length_zero_iff_nil in hl23.
        subst; cbn in *.
        repeat rewrite app_nil_r.
        do 2 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc. auto.
    - pose proof shift_lv_update _ _ _ _ _ _ hus huseps' vs as hvs.
      rewrite <- hvs.
      constructor; auto.
    - set (vargs' :=
             map (paramarg_map id (shift_lv
                                     {|
                                       cutoff := Datatypes.length us;
                                       amt := Datatypes.length vs
                                     |})) vargs) in *.
      set (olv' :=
             option_map (shift_lv
             {|
               cutoff := Datatypes.length us; amt := Datatypes.length vs
             |}) olv) in *.
      replace (us' ++ vs ++ eps')
        with (lv_update_signal olv' sig (copy_out vargs' ϵ'' (us ++ vs ++ eps))).
      eapply sbs_funct_call; eauto.
      + inversion H0; subst; cbn in *; constructor.
        eauto using shift_lv_eval.
      + eauto using shift_args_eval.
      + eauto using shift_copy_in.
      + (* This feels like a shift bug *)
        apply shift_lv_update_signal.
        admit.
    - replace (us' ++ vs ++ eps')
        with (lv_update_signal olv sig
                               (copy_out vdata_args ϵ''
                                         (us ++ vs ++ eps))).
      eapply sbs_action_call; try eassumption.
      + eapply Forall2_map_l with (lc := ctrl_args).
        eauto using sublist.Forall2_impl, shift_e_eval.
      + admit.
      + admit.
    - (* method call case, will be a repeat of the other call cases *)
      admit.
    - (* invoke case, will be a repeat of the other call cases *)
      admit.
    - (* another invoke case, will be a repeat *)
      admit. 
    - (* parser case... *)
      admit.
    - econstructor; eauto.
      + destruct te; simpl in *.
        * apply H.
        * auto.
      + instantiate (1:=v').
        replace (v :: us ++ vs ++ eps) with
          ((v :: us) ++ vs ++ eps)
          by eauto.
        replace (v' :: us' ++ vs ++ eps') with
          ((v' :: us') ++ vs ++ eps')
          by eauto.
        eapply IHhs; simpl; eauto.
    - assert (hϵ' : length (us ++ eps) = length ϵ') by
        eauto using sbs_length.
      rewrite app_length in hϵ'.
      eapply sbs_seq_cont with (ϵ' := firstn (length us) ϵ' ++ vs ++ skipn (length us) ϵ'); eauto.
      + eapply IHhs1; eauto.
        * rewrite firstn_length. lia.
        * rewrite firstn_skipn. reflexivity.
      + replace (length us) with
          (length (firstn (length us) ϵ')) at 3
          by (rewrite firstn_length; lia).
        eapply IHhs2; eauto.
        * rewrite skipn_length, <- hϵ'.
          replace (length us + length eps - length us) with (length eps) by lia.
          assumption.
        * rewrite firstn_skipn. reflexivity.
        * rewrite firstn_length; lia.
    - econstructor; eauto.
      destruct b; auto.
  Admitted.
End Properties.
