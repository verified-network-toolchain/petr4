Require Import Coq.Arith.PeanoNat.
From RecordUpdate Require Import RecordSet.
From Poulet4 Require Import P4cub.Syntax.Syntax
  P4cub.Semantics.Climate Utils.ForallMap
  P4cub.Syntax.Shift.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Syntax BigStep.Semantics BigStep.IndPrincip
     BigStep.Value.Typing BigStep.Determinism.
Import Nat RecordSetNotations.

Ltac len_app :=
  lazymatch goal with
  | hlen: length ?l1 = length ?l2, happ: ?l1 ++ _ = ?l2 ++ _
    |- _ => pose proof sublist.app_eq_len_eq happ hlen as [? ?]; subst; clear happ
  | hlen: length ?l2 = length ?l1, happ: ?l1 ++ _ = ?l2 ++ _
    |- _ => pose proof sublist.app_eq_len_eq happ (eq_sym hlen) as [? ?]; subst; clear happ
  | hlen: length ?l1 = length ?l2, happ: _ ++ ?l1 = _ ++ ?l2
    |- _ => pose proof app_eq_len_tail_app happ hlen as [? ?]; subst; clear happ
  | hlen: length ?l2 = length ?l1, happ: _ ++ ?l1 = _ ++ ?l2
    |- _ => pose proof app_eq_len_tail_app happ (eq_sym hlen) as [? ?]; subst; clear happ
  end.

Ltac app_inv_head_solve :=
  lazymatch goal with
  | h: ?x ++ _ = ?x ++ _ |- _ => apply app_inv_head in h; subst
  end.

Ltac app_inv_tail_solve :=
  lazymatch goal with
  | h: _ ++ ?x = _ ++ ?x |- _ => apply app_inv_tail in h; subst
  end.

Local Hint Extern 5 => len_app : core.
Local Hint Extern 5 => app_inv_head_solve : core.
Local Hint Extern 5 => app_inv_tail_solve : core.

Definition table_cutoff (m : nat) (tbl : Table.t) : Prop :=
  exists n, m = n + Table.scope tbl.

Variant ctx_cutoff : nat -> ctx -> Prop :=
  | ctx_cuttoff_action m aa :
    ctx_cutoff m (CAction aa)
  | ctx_cutoff_function m :
    ctx_cutoff m CFunction
  | ctx_cutoff_applyblock m ts aa ac :
    Clmt.all (table_cutoff m) ts ->
    ctx_cutoff m (CApplyBlock ts aa ac)
  | ctx_cutoff_parserstate m n strt sts ap :
    ctx_cutoff (m + n) (CParserState n strt sts ap).

Section Properties.
  Local Hint Constructors ctx_cutoff : core.
  Local Hint Constructors predop : core.

  Lemma ctx_cutoff_add : forall l m c,
      ctx_cutoff m c ->
      ctx_cutoff (l + m) c.
  Proof using.
    intros l m c hc. inv hc; auto.
    - constructor.
      unfold Clmt.all,table_cutoff in *.
      intro y. specialize H with y.
      inv H; auto.
      constructor.
      destruct H1 as [x ?]; subst.
      exists (l + x). lia.
    - rewrite Nat.add_assoc. auto.
  Qed.

  Local Hint Resolve ctx_cutoff_add : core.
  Local Hint Resolve ForallMap.Forall2_dumb : core.
  Local Hint Constructors exp_big_step : core.
  Local Hint Extern 1 => len_app : core.

  Lemma shift_exp_eval : forall us vs ϵ e v,
      ⟨ us ++ ϵ, e ⟩ ⇓ v ->
      ⟨ us ++ vs ++ ϵ,
        shift_exp
          (length us) (length vs) e ⟩ ⇓ v.
  Proof using.
    intros us vs ϵ e v h.
    remember (us ++ ϵ) as usϵ eqn:husϵ.
    generalize dependent ϵ.
    generalize dependent us.
    induction h using custom_exp_big_step_ind;
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

  Local Hint Resolve shift_exp_eval : core.

  Lemma e_eval_shift : forall e v us vs ϵ,
      ⟨ us ++ vs ++ ϵ,
        shift_exp
          (length us) (length vs) e ⟩ ⇓ v ->
      ⟨ us ++ ϵ, e ⟩ ⇓ v.
  Proof using.
    intro e; induction e using custom_exp_ind;
      intros v us vs eps h; inv h; cbn in *; eauto.
    - unfold shift_var in * |-.
      destruct_if_hyp.
      + rewrite nth_error_app2 in H3 by lia.
        rewrite <- Nat.add_sub_assoc in H3 by lia.
        rewrite nth_error_app3 in H3.
        constructor.
        rewrite nth_error_app2 by assumption.
        assumption.
      + rewrite nth_error_app1 in H3 by assumption.
        constructor.
        rewrite nth_error_app1 by assumption.
        assumption.
    - constructor.
      rewrite Forall2_forall_nth_error in *.
      rewrite Forall_forall in * |-.
      destruct H3 as [hlen h].
      rewrite map_length in hlen.
      split; try assumption.
      intros n e v hnthe hnthv.
      eauto using nth_error_In, map_nth_error.
  Qed.
    
  Local Hint Resolve e_eval_shift : core.
  Local Hint Constructors trns_big_step : core.

  Lemma shift_trns_eval : forall us ϵ p st,
      p⟨ us ++ ϵ , p ⟩ ⇓ st -> forall vs,
        p⟨ us ++ vs ++ ϵ , shift_trns (length us) (length vs) p ⟩ ⇓ st.
  Proof using.
    intros us eps p st h vs.
    inv h; unravel; auto.
  Qed.

  Local Hint Resolve shift_trns_eval : core.

  Lemma trns_eval_shift : forall p st us vs ϵ,
      p⟨ us ++ vs ++ ϵ , shift_trns (length us) (length vs) p ⟩ ⇓ st ->
      p⟨ us ++ ϵ , p ⟩ ⇓ st.
  Proof using.
    intros [lbl | e lbl cases] st us vs eps h; cbn in h; inv h; eauto.
  Qed.

  Local Hint Resolve trns_eval_shift : core.
  
  Fixpoint shift_lv (c a : nat) (lv : Lval.t) : Lval.t :=
  match lv with
  | Lval.Var x => Lval.Var $ shift_var c a x
  | Lval.Slice hi lo lv => Lval.Slice hi lo $ shift_lv c a lv
  | Lval.Member x lv => Lval.Member x $ shift_lv c a lv
  | Lval.Index n lv => Lval.Index n $ shift_lv c a lv
  end.

  Lemma shift_lv_0_add : forall lv m n,
      shift_lv 0 (m + n) lv = shift_lv 0 m (shift_lv 0 n lv).
  Proof using.
    intro lv; induction lv; intros m n; unravel; f_equal; auto.
    unfold shift_var; cbn. lia.
  Qed.
  
  Lemma shift_lv_0 : forall lv c, shift_lv c 0 lv = lv.
  Proof using.
    intros lv c; induction lv; unravel; f_equal; auto.
    unfold shift_var. destruct_if; reflexivity.
  Qed.
  
  Local Hint Constructors lexp_big_step : core.

  Lemma shift_lv_eval : forall us vs ϵ e lv,
      l⟨ us ++ ϵ, e ⟩ ⇓ lv ->
      l⟨ us ++ vs ++ ϵ,
          shift_exp
            (length us) (length vs) e ⟩
        ⇓ shift_lv (length us) (length vs) lv.
  Proof using.
    intros us vs eps e lv h.
    remember (us ++ eps) as useps eqn:huseps.
    generalize dependent eps.
    generalize dependent us.
    induction h; intros; subst; unravel; eauto.
  Qed.

  Local Hint Resolve shift_lv_eval : core.

  Lemma lv_eval_shift : forall e lv us vs ϵ,
      l⟨ us ++ vs ++ ϵ,
          shift_exp
            (length us) (length vs) e ⟩
        ⇓ shift_lv (length us) (length vs) lv ->
      l⟨ us ++ ϵ, e ⟩ ⇓ lv.
  Proof using.
    intro e; induction e using custom_exp_ind;
      intros [] us vs eps h; cbn in *; inv h; eauto.
    unfold shift_var in * |-.
    do 2 destruct_if_hyp; subst; try lia; auto.
    assert (x0 = x) by lia; subst; auto.
  Qed.

  Local Hint Resolve lv_eval_shift : core.

  Lemma shift_exp_lv_eval_shift_lv_exists :
    forall e lv us vs eps,
      l⟨ us ++ vs ++ eps, shift_exp (length us) (length vs) e ⟩ ⇓ lv -> exists lv',
        lv = shift_lv (length us) (length vs) lv'.
  Proof.
    intro e; induction e; intros lv us vs eps h;
      unravel in h; inv h; unravel; eauto.
    - exists (Lval.Var x). reflexivity.
    - apply IHe in H3 as [lv h]; subst.
      exists (Lval.Slice hi lo lv). reflexivity.
    - apply IHe1 in H4 as [lv h]; subst.
      exists (Lval.Index (BinInt.Z.to_N n) lv).
      reflexivity.
    - apply IHe in H3 as [lv h]; subst.
      exists (lv DOT mem)%lval. reflexivity.
  Qed.
  
  Lemma shift_exps_lvs_eval_shift_lvs_exists : forall es lvs us vs eps,
      Forall2 (lexp_big_step (us ++ vs ++ eps)) (map (shift_exp (length us) (length vs)) es) lvs ->
      exists lvs', lvs = map (shift_lv (length us) (length vs)) lvs'.
  Proof using.
    intros es; induction es as [| e es ih];
      intros [| lv lvs] us vs eps h; inv h.
    - exists []. reflexivity.
    - apply shift_exp_lv_eval_shift_lv_exists in H2 as [lv' hlv].
      apply ih in H4 as [lvs' hlvs].
      exists (lv' :: lvs'). subst. reflexivity.
  Qed.
  
  Lemma shift_lv_lookup : forall lv rs us ϵ,
      lv_lookup (rs ++ us ++ ϵ) (shift_lv (length rs) (length us) lv)
      = lv_lookup (rs ++ ϵ) lv.
  Proof using.
    intro lv; induction lv; intros; unravel.
    - unfold shift_var.
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
  Local Hint Rewrite @InOut.map_inn : core.
  Local Hint Rewrite @InOut.map_out : core.

  Lemma shift_lv_update : forall lv v rs ϵ rs' ϵ',
      length rs = length rs' ->
      lv_update lv v (rs ++ ϵ) = rs' ++ ϵ' -> forall us,
          lv_update (shift_lv (length rs) (length us) lv) v (rs ++ us ++ ϵ)
          = rs' ++ us ++ ϵ'.
  Proof using.
    intro lv; induction lv;
      intros v rs eps rs' eps' hrs hlv us;
      unravel in *; autorewrite with core.
    - unfold shift_var.
      destruct_if.
      + rewrite nth_update_app1 in * by lia.
        replace (length us + x - length rs)
          with (length us + (x - length rs)) by lia.
        rewrite nth_update_app3. auto.
      + rewrite nth_update_app2 in * by lia.
        assert (length (nth_update x v rs) = length rs') as hup.
        { rewrite nth_update_length. assumption. } auto.
    - destruct v; auto.
      destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
    - destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
    - destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
  Qed.

  Local Hint Resolve shift_lv_update : core.
  Local Hint Rewrite shift_lv_update : core.

  Lemma lv_update_shift : forall lv v rs ϵ rs' ϵ' us,
      length rs = length rs' ->
      lv_update (shift_lv (length rs) (length us) lv) v (rs ++ us ++ ϵ)
      = rs' ++ us ++ ϵ' ->
      lv_update lv v (rs ++ ϵ) = rs' ++ ϵ'.
  Proof using.
    intro lv; induction lv;
      intros v rs eps rs' eps' us hrs h; cbn in *.
    - unfold shift_var in * |-.
      destruct_if_hyp.
      + rewrite app_assoc in h.
        assert (husrsx : length rs + length us <= length us + x) by lia.
        rewrite <- app_length in husrsx.
        rewrite nth_update_app1 by assumption.
        rewrite nth_update_app1 in h by assumption.
        rewrite <- app_assoc in h. len_app. app_inv_head_solve.
        f_equal.
        rewrite app_length.
        f_equal. lia.
      + rewrite nth_update_app2 in h |- * by assumption.
        rewrite <- nth_update_length with (n:=x) (a:=v) (l:=rs) in hrs. auto.
    - destruct v; unravel in *; auto.
      rewrite shift_lv_lookup in h.
      destruct (lv_lookup (rs ++ eps) lv) as [[] |]; cbn in *; eauto.
    - rewrite shift_lv_lookup in h.
      destruct (lv_lookup (rs ++ eps) lv) as [[] |]; cbn in *; eauto.
    - rewrite shift_lv_lookup in h.
      destruct (lv_lookup (rs ++ eps) lv) as [[] |]; cbn in *; eauto.
  Qed.

  Local Hint Resolve lv_update_shift : core.
  Local Hint Rewrite lv_update_shift : core.
  Local Hint Resolve lv_update_length : core.
  Local Hint Rewrite lv_update_length : core.
  
  Lemma lv_update_signal_length : forall olv sig ϵ,
      length (lv_update_signal olv sig ϵ) = length ϵ.
  Proof using.
    intros [] [| | | | []] ϵ; cbn; auto.
  Qed.

  Local Hint Resolve lv_update_signal_length : core.
  Local Hint Rewrite lv_update_signal_length : core.
  Local Hint Resolve copy_out_length : core.
  Local Hint Rewrite copy_out_length : core.

  Lemma lexp_exp_big_step : forall ϵ e lv v,
      l⟨ ϵ, e ⟩ ⇓ lv -> ⟨ ϵ, e ⟩ ⇓ v -> lv_lookup ϵ lv = Some v.
  Proof using.
    intros eps e lv v helv; generalize dependent v.
    induction helv; intros V hv; inv hv; unravel; auto.
    - rewrite (IHhelv _ H4).
      destruct v; unravel in *; inv H3; do 2 f_equal.
    - rewrite (IHhelv _ H4). assumption.
    - rewrite (IHhelv _ H5).
      rewrite <- H3. f_equal.
      pose proof exp_deterministic _ _ _ _ H H6 as h; inv h. lia.
  Qed.

  Local Hint Rewrite app_length : core.
  Local Hint Constructors relop : core.
  Local Hint Resolve sublist.Forall2_impl : core.

  Lemma shift_args_eval : forall us vs eps args vargs,
      args_big_step (us ++ eps) args vargs ->
      args_big_step
        (us ++ vs ++ eps)
        (shift_args (length us) (length vs) args)
        (InOut.map id (shift_lv (length us) (length vs)) vargs).
  Proof using.
    unfold args_big_step.
    intros us vs eps [in_args out_args] [in_vargs out_vargs] [hinn hout];
      constructor; cbn in *.
    - rewrite map_id.
      erewrite <- Forall2_map_l with (lc := in_args). eauto.
    - erewrite <- Forall2_map_l with (lc := out_args).
      erewrite <- Forall2_map_r with (lc := out_vargs). eauto.
  Qed.

  Local Hint Resolve shift_args_eval : core.
  
  Lemma args_eval_shift : forall us vs eps args vargs,
      args_big_step (us ++ vs ++ eps)
        (shift_args (length us) (length vs) args)
        (InOut.map id (shift_lv (length us) (length vs)) vargs) ->
      args_big_step (us ++ eps) args vargs.
  Proof using.
    unfold args_big_step.
    intros us vs eps [in_args out_args] [in_vargs out_vargs] [hinn hout];
      constructor; cbn in *.
    - rewrite map_id in hinn.
      erewrite <- Forall2_map_l with (lc := in_args) in hinn.
      revert hinn.
      eapply sublist.Forall2_impl; eauto.
    - erewrite <- Forall2_map_l with (lc := out_args) in hout.
      erewrite <- Forall2_map_r with (lc := out_vargs) in hout.
      revert hout.
      eapply sublist.Forall2_impl; eauto.
  Qed.

  Local Hint Resolve args_eval_shift : core.

  Lemma args_eval_shift_exp_exists_shift_varg : forall us vs eps args vargs,
      args_big_step
        (us ++ vs ++ eps)
        (shift_args (length us) (length vs) args)
        vargs -> exists vargs',
        vargs = (InOut.map  id (shift_lv (length us) (length vs)) vargs').
  Proof using.
    unfold args_big_step.
    intros us vs eps [in_args out_args] [in_vargs out_vargs] [hinn hout].
    cbn in *.
    apply shift_exps_lvs_eval_shift_lvs_exists in hout as [lvs hlvs].
    exists (InOut.mk_t in_vargs lvs). subst.
    unfold InOut.map. rewrite map_id. reflexivity.
  Qed.
  
  Lemma split_by_length:
    forall A (l: list A) m n,
      length l = n + m ->
      exists xs ys,
        l = xs ++ ys /\
        length xs = n /\
        length ys = m.
  Proof using.
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

  Lemma split_by_length3:
    forall A (l: list A) m n o,
      length l = n + m + o ->
      exists xs ys zs,
        l = xs ++ ys ++ zs /\
        length xs = n /\
        length ys = m /\
        length zs = o.  
  Proof using.
    intros A l m n o h.
    exists (firstn n l), (firstn m (skipn n l)), (skipn (n + m) l).
    do 2 rewrite firstn_length.
    do 2 rewrite skipn_length.
    repeat split; try lia.
    rewrite <- sublist.skipn_skipn.
    do 2 rewrite firstn_skipn.
    reflexivity.
  Qed.

  Local Hint Rewrite copy_out_nil : core.
  Local Hint Rewrite copy_out_cons : core.
  Local Hint Extern 4 => rewrite firstn_length : core.
  Local Hint Rewrite copy_out_length : core.
  Local Hint Rewrite app_length : core.
  
  Lemma shift_copy_out :
    forall lvs out_vals us vs eps eps' us',
      length us = length us' ->
      copy_out lvs out_vals (us ++ eps) = us' ++ eps' ->
      copy_out
        (map (shift_lv (length us) (length vs)) lvs)
        out_vals (us ++ vs ++ eps) = us' ++ vs ++ eps'.
  Proof using.
    intro lvs; induction lvs as [| lv lvs ih];
      intros [| outv outvs] us vs eps eps' us' hus hcpy;
      simpl in *; autorewrite with core in *; cbn in *; auto.
    pose proof firstn_skipn
      (length us)
      (copy_out lvs outvs (us ++ eps)) as h.
    symmetry in h.
    rewrite h in hcpy.
    apply ih with (vs:=vs) in h;
      try rewrite firstn_length;
      autorewrite with core; try lia.
    rewrite h.
    replace (length us) with (length (firstn (length us) (copy_out lvs outvs (us ++ eps)))) at 1
      by (rewrite firstn_length; autorewrite with core; lia).
    apply shift_lv_update; auto.
    rewrite firstn_length. autorewrite with core. lia.
  Qed.

  Local Hint Resolve shift_copy_out : core.
  Local Hint Rewrite shift_copy_out : core.

  Lemma lv_update_shift_amt :
    forall lv v us us' vs vs' eps eps',
      length us = length us' ->
      length vs = length vs' ->
      lv_update
        (shift_lv (length us) (length vs) lv)
        v (us ++ vs ++ eps) = us' ++ vs' ++ eps' ->
      vs = vs'.
  Proof using.
    intro lv; induction lv; intros v us us' vs vs' eps eps' hus hlen h;
      unravel in h.
    - unfold shift_var in h.
      destruct_if_hyp.
      + rewrite app_assoc in h.
        assert (length (us ++ vs) <= length vs + x)
          by (rewrite app_length; lia).
        rewrite nth_update_app1 in h by assumption.
        rewrite app_length in h.
        replace (length vs + x - (length us + length vs)) with (x - length us) in h by lia.
        rewrite <- app_assoc in h. auto.
      + rewrite nth_update_app2 in h by assumption.
        assert (length (nth_update x v us) = length us')
          by (rewrite nth_update_length; assumption).
        auto.
    - destruct v; auto.
      rewrite shift_lv_lookup in h.
      destruct (lv_lookup (us ++ eps) lv) as [[] |]; unravel in h; eauto.
    - rewrite shift_lv_lookup in h.
      destruct (lv_lookup (us ++ eps) lv) as [[] |]; unravel in h; eauto.
    - rewrite shift_lv_lookup in h.
      destruct (lv_lookup (us ++ eps) lv) as [[] |]; unravel in h; eauto.
  Qed.

  Local Hint Resolve lv_update_shift_amt : core.

  Lemma copy_out_shift_amt :
    forall lvs outvs us us' vs vs' eps eps',
      length us = length us' ->
      length vs = length vs' ->
      copy_out
        (map (shift_lv (length us) (length vs)) lvs)
        outvs (us ++ vs ++ eps) = us' ++ vs' ++ eps' ->
      vs = vs'.
  Proof using.
    intro lvs;
      induction lvs as [| lv lvs ih];
      intros [| outv outvs] us us' vs vs' eps eps' hus hvs hcpy;
      simpl in hcpy; autorewrite with core in hcpy; cbn in hcpy; auto.
    pose proof copy_out_length
      (map (shift_lv (length us) (length vs)) lvs)
      outvs (us ++ vs ++ eps) as hlen.
    repeat rewrite app_length in hlen.
    rewrite Nat.add_assoc in hlen.
    pose proof split_by_length3 _ _ _ _ _ hlen as (xs & ys & zs & h & hxs & hys & hzs).
    rewrite h, <- hxs in hcpy.
    apply ih in h; auto. subst.
    apply lv_update_shift_amt in hcpy; auto; try lia.
  Qed.

  Local Hint Resolve copy_out_shift_amt : core.

  Lemma copy_out_shift :
    forall lvs outvs us vs eps eps' us',
      length us = length us' ->
      copy_out
        (map (shift_lv (length us) (length vs)) lvs)
        outvs (us ++ vs ++ eps) = us' ++ vs ++ eps' ->
      copy_out lvs outvs (us ++ eps) = us' ++ eps'.
  Proof using.
    intro lvs; induction lvs as [| lv lvs ih];
      intros [| outv outvs] us vs eps eps' us' hus hcpy;
      simpl in *; autorewrite with core in *; cbn in *; auto.
    pose proof copy_out_length
      (map (shift_lv (length us) (length vs)) lvs)
      outvs (us ++ vs ++ eps) as hlen.
    repeat rewrite app_length in hlen.
    rewrite Nat.add_assoc in hlen.
    pose proof split_by_length3 _ _ _ _ _ hlen
      as (xs & ys & zs & h & hxs & hys & hzs).
    assert (vs = ys).
    { apply copy_out_shift_amt in h; auto. }
    subst; clear hys.
    rewrite h, <- hxs in hcpy.
    apply ih in h; auto. rewrite h.
    apply lv_update_shift in hcpy; auto; try lia.
  Qed.

  Local Hint Resolve copy_out_shift : core.

  Lemma shift_lv_update_signal : forall olv sig us us' eps eps' vs,
      length us = length us' ->
      lv_update_signal olv sig (us ++ eps) = us' ++ eps' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv) sig
        (us ++ vs ++ eps) = us' ++ vs ++ eps'.
  Proof using.
    unfold lv_update_signal.
    intros olv sig us us' eps eps' vs hus h.
    destruct olv; simpl in *; eauto;
      destruct sig; eauto.
    destruct v; eauto.
  Qed.

  Local Hint Resolve shift_lv_update_signal : core.

  Lemma lv_update_signal_shift :
    forall olv sig us us' eps eps' vs,
      length us = length us' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv)
        sig
        (us ++ vs ++ eps) = us' ++ vs ++ eps' ->
      lv_update_signal olv sig (us ++ eps) = us' ++ eps'.
  Proof using.
    unfold lv_update_signal.
    intros olv sig us us' eps eps' vs hus h.
    destruct olv; simpl in *; eauto;
      destruct sig; eauto.
    destruct v; eauto.
  Qed.

  Local Hint Resolve lv_update_signal_shift : core.

  Lemma lv_update_signal_shift_amt :
    forall olv sig us us' eps eps' vs vs',
      length us = length us' ->
      length vs = length vs' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv)
        sig
        (us ++ vs ++ eps) = us' ++ vs' ++ eps' ->
      vs = vs'.
  Proof using.
    intros [lv |] [] us us' eps eps' vs vs' hus hvs h;
      unravel in *; eauto 3.
    destruct v; eauto 3.
  Qed.
    
  Local Hint Resolve lv_update_signal_shift_amt : core.
  
  Lemma shift_lv_update_signal_copy_out :
    forall olv sig lvs outvs us eps eps' us' vs,
      length us = length us' ->
      lv_update_signal olv sig (copy_out lvs outvs (us ++ eps)) = us' ++ eps' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv) sig
        (copy_out (map (shift_lv (length us) (length vs)) lvs)
           outvs (us ++ vs ++ eps))
      = us' ++ vs ++ eps'.
  Proof using.
    intros olv sig lvs outvs us eps eps' us' vs hus h.
    pose proof copy_out_length lvs outvs (us ++ eps) as hcpy.
    rewrite app_length in hcpy.
    apply split_by_length in hcpy as (xs & ys & hcpy & hxs & hys).
    rewrite hcpy in h.
    apply shift_copy_out with (vs:=vs) in hcpy; auto.
    rewrite hcpy, <- hxs.
    apply shift_lv_update_signal; auto; try lia.
  Qed.

  Local Hint Resolve shift_lv_update_signal_copy_out : core.

  Lemma lv_update_signal_copy_out_shift :
    forall olv sig lvs outvs us eps eps' us' vs,
      length us = length us' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv)
        sig
        (copy_out (map (shift_lv (length us) (length vs)) lvs)
           outvs (us ++ vs ++ eps))
      = us' ++ vs ++ eps' ->
      lv_update_signal olv sig (copy_out lvs outvs (us ++ eps))
      = us' ++ eps'.
  Proof using.
    intros olv sig lvs outvs us eps eps' us' vs hus h; unravel in *; eauto.
    pose proof copy_out_length
      (map (shift_lv (length us) (length vs)) lvs)
      outvs (us ++ vs ++ eps) as hcpy.
    do 2 rewrite app_length in hcpy.
    rewrite Nat.add_assoc in hcpy.
    apply split_by_length3 in hcpy as (xs & ys & zs & hcpy & hxs & hys & hzs).
    pose proof copy_out_shift_amt _ _ _ _ _ _ _ _ (eq_sym hxs) (eq_sym hys) hcpy; subst.
    rewrite hcpy, <- hxs in h.
    apply copy_out_shift in hcpy; auto. rewrite hcpy.
    apply lv_update_signal_shift in h; auto. lia.
  Qed.

  Local Hint Resolve lv_update_signal_copy_out_shift : core.

  Lemma lv_update_signal_copy_out_shift_amt :
    forall olv sig lvs outvs us eps eps' us' vs vs',
      length us = length us' ->
      length vs = length vs' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv)
        sig
        (copy_out (map (shift_lv (length us) (length vs)) lvs)
           outvs (us ++ vs ++ eps))
      = us' ++ vs' ++ eps' ->
      vs = vs'.
  Proof using.
    intros olv sig lvs outvs us eps eps' us' vs vs' hus hvs h.
    pose proof copy_out_length
      (map (shift_lv (length us) (length vs)) lvs)
      outvs (us ++ vs ++ eps) as hcpy.
    do 2 rewrite app_length in hcpy.
    rewrite Nat.add_assoc in hcpy.
    apply split_by_length3 in hcpy as (x & y & z & hcpy & hx & hy & hz).
    rewrite hcpy in h.
    apply copy_out_shift_amt in hcpy; auto. subst.
    rewrite <- hx in h.
    apply lv_update_signal_shift_amt in h; auto. lia.
  Qed.

  Context `{ext_sem : Extern_Sem}.

  Lemma sbs_length : forall Ψ ϵ ϵ' c s sig ψ,
      ⧼ Ψ, ϵ, c, s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ -> length ϵ = length ϵ'.
  Proof using.
    intros Ψ ϵ ϵ' c s sig ψ h;
      induction h; autorewrite with core in *; auto; lia.
  Qed.

  Local Hint Constructors SumForall : core.
  Local Hint Constructors stm_big_step : core.
  Local Hint Constructors actions_of_ctx : core.
  
  Lemma shift_stm_eval : forall Ψ us us' ϵ ϵ' c s sig ψ,
      length us = length us' ->
      ctx_cutoff (length ϵ) c ->
      ⧼ Ψ , us ++ ϵ , c , s ⧽ ⤋ ⧼ us' ++ ϵ' , sig , ψ ⧽ -> forall vs,
          ⧼ Ψ , us ++ vs ++ ϵ , c,
            shift_stm (length us) (length vs) s ⧽
            ⤋ ⧼ us' ++ vs ++ ϵ' , sig , ψ ⧽.
  Proof using.
    intros Psi us us' eps eps' c s sig psi hus hc hs.
    remember (us ++ eps) as useps eqn:huseps.
    remember (us' ++ eps') as useps' eqn:huseps'.
    generalize dependent eps'.
    generalize dependent us'.
    generalize dependent eps.
    generalize dependent us.
    induction hs; intros; unravel; subst; eauto 4.
    - inv H; unravel; auto.
    - inv hc.
      symmetry in H3.
      apply split_by_length in H3 as (x & y & hxy & hx & hy); subst.
      pose proof sbs_length _ _ _ _ _ _ _ hs as hlen.
      rewrite app_assoc in huseps. len_app.
      rewrite <- app_assoc in huseps'. len_app.
      replace (us' ++ vs ++ x ++ y) with
        ((us' ++ vs ++ x) ++ y) by (repeat rewrite <- app_assoc; reflexivity).
      replace (us' ++ vs ++ x ++ ϵ₃) with
        ((us' ++ vs ++ x) ++ ϵ₃) by (repeat rewrite <- app_assoc; reflexivity).
      econstructor; eauto.
      repeat rewrite <- app_assoc in *. eauto.
    - pose proof shift_lv_update _ _ _ _ _ _ hus huseps' vs as hvs.
      rewrite <- hvs.
      constructor; auto.
    - apply shift_lv_update with (us:=vs0) in huseps'; auto.
      rewrite <- huseps'. eauto.
    - set (lvs' :=
             (InOut.map id (shift_lv (length us) (length vs)) vargs).(InOut.out)) in *.
      set (olv' := option_map (shift_lv (length us) (length vs)) olv) in *.
      replace (us' ++ vs ++ eps')
        with (lv_update_signal olv' sig (copy_out lvs' out_vals (us ++ vs ++ eps))).
      eapply sbs_funct_call with (prefix:=prefix); eauto using shift_args_eval.
      + rewrite InOut.map_inn,map_id. assumption.
      + inv H1; subst olv'; cbn in *; eauto.
      + destruct args. cbn in *.
        rewrite typ_of_shift_exps. eauto.
      + rewrite InOut.map_inn, map_id in *. eauto.
      + subst olv'. eapply shift_lv_update_signal_copy_out; eauto.
    - replace (us' ++ vs ++ eps')
        with (copy_out
                (InOut.out (InOut.map id (shift_lv (length us) (length vs)) vdata_args))
                out_vals (us ++ vs ++ eps)).
      eapply sbs_action_call with
        (ctrl_prefix:=ctrl_prefix)
        (data_prefix:=data_prefix); try eassumption; eauto 3.
      + rewrite InOut.map_inn,map_id; assumption.
      + eapply Forall2_map_l with (lc := ctrl_args).
        eauto using sublist.Forall2_impl, shift_exp_eval.
      + destruct data_args. cbn in *.
        rewrite typ_of_shift_exps. assumption.
      + rewrite InOut.map_inn,map_id. eauto.
      + rewrite InOut.map_out. eauto.
    - apply shift_lv_update_signal_copy_out with (vs:=vs) in huseps'; try assumption.
      rewrite <- huseps'.
      rewrite <- InOut.map_out with (f:=id).
      econstructor; eauto 3.
      + inv H; cbn; auto.
      + rewrite InOut.map_inn,map_id. assumption.
    - inv hc. unfold Clmt.all in H10.
      specialize H10 with t0. rewrite H0 in H10.
      inv H10. unfold table_cutoff in H9.
      cbn in H9.
      destruct H9 as [n hn].
      apply split_by_length in hn as (x & y & hxy & hx & hy); subst.
      apply sbs_length in hs as hlenϵ'ϵ₂.
      rewrite app_assoc in huseps. len_app.
      rewrite <- app_assoc in huseps'.
      apply shift_lv_update_signal with (vs:=vs0) in huseps'; auto.
      rewrite <- huseps'. clear huseps'.
      replace (us ++ vs0 ++ x ++ y) with
        ((us ++ vs0 ++ x) ++ y) by
        (repeat rewrite app_assoc; reflexivity).
      replace (us ++ vs0 ++ x ++ ϵ') with
        ((us ++ vs0 ++ x) ++ ϵ') by
        (repeat rewrite app_assoc; reflexivity).
      eapply sbs_invoke; eauto.
      repeat rewrite <- app_assoc in *.
      inv H; cbn; auto.
    - replace (us' ++ vs ++ eps')
        with (copy_out
                (InOut.out (InOut.map id (shift_lv (length us) (length vs)) vargs))
                out_vals (us ++ vs ++ eps)).
      eapply sbs_apply_control with (prefix:=prefix); eauto.
      + rewrite InOut.map_inn, map_id. assumption.
      + destruct args; unfold get_out_inits in *; cbn in *.
        rewrite typ_of_shift_exps. eauto.
      + rewrite InOut.map_inn, map_id. eauto.
      + rewrite InOut.map_out. eauto.
    - (* parser case... *)
      replace (us' ++ vs ++ eps')
        with (copy_out
                (InOut.out (InOut.map id (shift_lv (length us) (length vs)) vargs))
                out_vals (us ++ vs ++ eps)).
      eapply sbs_apply_parser with (prefix:=prefix); eauto.
      + rewrite InOut.map_inn, map_id. assumption.
      + destruct args; unfold get_out_inits in *; cbn in *.
        rewrite typ_of_shift_exps. eauto.
      + unfold shift_args, InOut.map_uni.
        rewrite InOut.map_inn, InOut.length_map, map_id. eauto.
      + rewrite InOut.map_out. eauto.
    - econstructor; eauto.
      + inv H; simpl in *; eauto.
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
      eapply sbs_seq_cont with (ϵ' := firstn (length us) ϵ' ++ vs ++ skipn (length us) ϵ'); eauto 2.
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
  Qed.

  Lemma relop_lexp_big_step_exists_shift : forall us vs eps oe olv,
      relop
        (lexp_big_step (us ++ vs ++ eps))
        (option_map (shift_exp (length us) (length vs)) oe) olv -> exists olv',
        olv = option_map (shift_lv (length us) (length vs)) olv'.
  Proof using.
    intros us vs eps oe olv h.
    destruct oe as [e |]; destruct olv as [lv |]; unravel in *; inv h.
    - apply shift_exp_lv_eval_shift_lv_exists in H1 as [lv' h]; subst.
      exists (Some lv'); reflexivity.
    - exists None; reflexivity.
  Qed.

  Lemma stm_eval_shift_amt : forall s Ψ us us' vs vs' ϵ ϵ' c sig ψ,
      length us = length us' ->
      length vs = length vs' ->
      ctx_cutoff (length ϵ) c ->
      ⧼ Ψ , us ++ vs ++ ϵ , c ,
        shift_stm (length us) (length vs) s ⧽
        ⤋ ⧼ us' ++ vs' ++ ϵ' , sig , ψ ⧽ ->
      vs = vs'.
  Proof using.
    intro s; induction s;
      intros Psi us us' vs vs' eps eps' c sig psi hus hvs hctx h;
      unravel in *; inv h; auto 3.
    - inv hctx.
      pose proof sbs_length _ _ _ _ _ _ _ H6 as hlen.
      symmetry in H4.
      apply split_by_length in H4 as (x & y & ? & hx & hy); subst.
      do 2 rewrite app_assoc in H. len_app.
      do 2 rewrite <- app_assoc in H1. do 2 len_app.
      reflexivity.
    - apply shift_exp_lv_eval_shift_lv_exists in H4 as [lv' ?]; subst. eauto 2.
    - apply shift_exp_lv_eval_shift_lv_exists in H4 as [lv' ?]; subst. eauto 2.
    - destruct call as [g ts oe | | |]; unravel in *; inv H.
      apply args_eval_shift_exp_exists_shift_varg in H7 as [vargs' ?]; subst.
      apply relop_lexp_big_step_exists_shift in H4 as [olv' ?]; subst.
      autorewrite with core in *.
      apply lv_update_signal_copy_out_shift_amt in H1; eauto 1.
    - destruct call as [| act cargs | |]; unravel in *; inv H.
      apply args_eval_shift_exp_exists_shift_varg in H10 as [vargs' ?]; subst.
      apply copy_out_shift_amt in H1; eauto 2.
    - destruct call as [| | extrn mthd ts ret |]; unravel in *; inv H.
      apply args_eval_shift_exp_exists_shift_varg in H3 as [vargs' ?]; subst.
      apply relop_lexp_big_step_exists_shift in H2 as [olv' ?]; subst.
      autorewrite with core in *.
      apply lv_update_signal_copy_out_shift_amt in H1; eauto 1.
    - apply args_eval_shift_exp_exists_shift_varg in H6 as [vargs' ?]; subst.
      apply copy_out_shift_amt in H1; eauto 2.
    - apply args_eval_shift_exp_exists_shift_varg in H5 as [vargs' ?]; subst.
      apply copy_out_shift_amt in H1; eauto 2.
    - apply sbs_length in H15 as hlen.
      inv hctx. unfold Clmt.all in H10.
      specialize H10 with table_name.
      rewrite H4 in H10. inv H10.
      unfold table_cutoff in H1.
      cbn in H1. destruct H1 as [n heps].
      apply split_by_length in heps as (x & y & ? & hx & hy); subst.
      replace (us ++ vs ++ x ++ y) with
        ((us ++ vs ++ x) ++ y) in H by (repeat rewrite app_assoc; reflexivity).
      len_app.
      repeat rewrite <- app_assoc in H2, H3.
      apply relop_lexp_big_step_exists_shift in H3 as [olv' ?]; subst.
      apply lv_update_signal_shift_amt in H2; auto.
    - replace (1 + length us) with (length (v :: us)) in H8 by reflexivity.
      replace (v :: us ++ vs ++ eps) with ((v :: us) ++ vs ++ eps) in H8 by reflexivity.
      replace (v' :: us' ++ vs' ++ eps') with ((v' :: us') ++ vs' ++ eps') in H8 by reflexivity.
      apply IHs in H8; cbn; auto; lia.
    - pose proof sbs_length _ _ _ _ _ _ _ H3 as hlen1.
      pose proof sbs_length _ _ _ _ _ _ _ H7 as hlen2.
      rewrite !app_length in hlen1, hlen2.
      rewrite Nat.add_assoc in hlen1,hlen2.
      rewrite <- firstn_skipn with (n:=length us) (l:=ϵ') in H3, H7.
      rewrite <- firstn_skipn with (n:=length vs) (l:=skipn (length us) ϵ') in H3, H7.
      apply IHs1 in H3; try rewrite firstn_length; try rewrite skipn_length; auto; try lia.
      rewrite H3 in H7 at 3.
      replace (length us) with (length (firstn (length us) ϵ')) in H7 at 4
          by (rewrite firstn_length; lia).
      apply IHs2 in H7;
        try rewrite firstn_length; repeat rewrite skipn_length; try lia.
      + etransitivity; eauto.
      + rewrite hlen2,hus,hvs.
        replace (length us' + length vs' + length eps' - length us' - length vs')
          with (length eps') by lia.
        rewrite hlen2 in hlen1.
        assert (hlen: length eps = length eps') by lia.
        rewrite <- hlen. assumption.
    - eapply IHs1 in H7; eauto 2.
    - destruct b.
      + eapply IHs1 in H8; eauto 2.
      + eapply IHs2 in H8; eauto 2.
  Qed.
  
  Lemma stm_eval_shift : forall s Ψ us us' vs ϵ ϵ' c sig ψ,
      length us = length us' ->
      ctx_cutoff (length ϵ) c ->
      ⧼ Ψ , us ++ vs ++ ϵ , c ,
        shift_stm (length us) (length vs) s ⧽
        ⤋ ⧼ us' ++ vs ++ ϵ' , sig , ψ ⧽ ->
      ⧼ Ψ , us ++ ϵ , c , s ⧽ ⤋ ⧼ us' ++ ϵ' , sig , ψ ⧽.
  Proof using.
    intro s; induction s;
      intros Psi us us' vs eps eps' c sig psi hus hctx h;
      unravel in *; inv h; eauto 5.
    - destruct e as [e |]; destruct vo as [v |];
        unravel in *; inv H3; eauto.
      len_app. app_inv_head_solve. eauto.
    - inv hctx.
      pose proof sbs_length _ _ _ _ _ _ _ H6 as hϵ3.
      symmetry in H4.
      apply split_by_length in H4 as (x & y & ? & hx & hy); subst.
      replace (us ++ vs ++ x ++ y) with
        ((us ++ vs ++ x) ++ y) in H
          by (repeat rewrite app_assoc; reflexivity).
      len_app.
      do 2 rewrite <- app_assoc in H1.
      len_app. app_inv_head_solve.
      do 2 rewrite app_assoc.
      eapply sbs_trans_intermediate; eauto.
      repeat rewrite <- app_assoc in *. eauto.
    - pose proof shift_exp_lv_eval_shift_lv_exists
        _ _ _ _ _ H4 as [lv' ?]; subst.
      apply lv_update_shift in H3 as h; eauto.
      rewrite <- h. eauto.
    - pose proof shift_exp_lv_eval_shift_lv_exists
        _ _ _ _ _ H4 as [lv' ?]; subst.
      apply lv_update_shift in H3 as h; eauto.
      rewrite <- h. eauto.
    - pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H7 as [vargs' ?]; subst.
      destruct call as [g ts oe| | |]; unravel in *; inv H.
      pose proof relop_lexp_big_step_exists_shift _ _ _ _ _ H4 as [olv' h]; subst.
      apply lv_update_signal_copy_out_shift in H1; eauto.
      rewrite <- H1.
      rewrite relop_map_both in H4.
      rewrite map_id in *.
      eapply sbs_funct_call with (prefix := prefix); eauto.
      + eapply relop_impl in H4; eauto.
      + unfold get_out_inits in H8 |- *.
        unravel in *.
        rewrite typ_of_shift_exps in H8.
        rewrite H8. reflexivity.
    - pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H10 as [dvargs ?]; subst.
      destruct call as [| act cargs | |]; unravel in *; inv H.
      apply copy_out_shift in H1; eauto.
      rewrite <- H1. rewrite map_id in *.
      eapply sbs_action_call with (ctrl_prefix:=ctrl_prefix); eauto 2.
      + rewrite <- Forall2_map_l in H7.
        eapply sublist.Forall2_impl in H7; eauto 2.
      + unfold get_out_inits in *.
        unravel in *.
        rewrite typ_of_shift_exps in H11.
        assumption.
    - pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H3 as [vargs' ?]; subst.
      destruct call as [| | extrn mthd ts ret |]; unravel in *; inv H.
      pose proof relop_lexp_big_step_exists_shift _ _ _ _ _ H2 as [olv' h]; subst.
      apply lv_update_signal_copy_out_shift in H1; eauto.
      rewrite <- H1. rewrite map_id in *.
      econstructor; eauto 2.
      rewrite relop_map_both in H2.
      eapply relop_impl in H2; eauto.
    - destruct call; unravel in *; inv H.
      pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H6 as [vargs' ?]; subst.
      apply copy_out_shift in H1; eauto.
      rewrite <- H1.
      autorewrite with core in *.
      rewrite map_id in *.
      eapply sbs_apply_control with (prefix:=prefix); eauto.
      unfold get_out_inits in *.
      unravel in *.
      rewrite typ_of_shift_exps in H7.
      eassumption.
    - destruct call; unravel in *; inv H.
      pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H5 as [vargs' ?]; subst.
      apply copy_out_shift in H1; eauto.
      rewrite <- H1.
      autorewrite with core in *.
      rewrite map_id in *.
      unfold shift_args, InOut.map_uni in H12.
      rewrite InOut.length_map in H12.
      eapply sbs_apply_parser with (prefix:=prefix); eauto.
      unfold get_out_inits in *.
      unravel in *.
      rewrite typ_of_shift_exps in H8.
      eassumption.
    - inv hctx.
      unfold Clmt.all in H10.
      specialize H10 with table_name.
      rewrite H4 in H10. inv H10.
      destruct H1 as [n heps]; cbn in heps.
      apply split_by_length in heps as (x & y & ? & hx & hy); subst.
      replace (us ++ vs ++ x ++ y) with
        ((us ++ vs ++ x) ++ y) in H by
          (repeat rewrite app_assoc; reflexivity).
      len_app.
      repeat rewrite <- app_assoc in *.
      pose proof relop_lexp_big_step_exists_shift _ _ _ _ _ H3 as [olv' h]; subst.
      apply lv_update_signal_shift in H2; auto.
      rewrite <- H2.
      rewrite relop_map_both in H3.
      do 2 rewrite app_assoc.
      econstructor; eauto.
      rewrite <- app_assoc.
      eapply relop_impl in H3; eauto.
    - pose proof IHs Psi (v :: us) (v' :: us') vs eps eps' c sig psi ltac:(cbn; lia) as ih.
      destruct init as [t | e]; inv H7; eauto.
    - pose proof sbs_length _ _ _ _ _ _ _ H3 as hlen1.
      pose proof sbs_length _ _ _ _ _ _ _ H7 as hlen2.
      rewrite !app_length in hlen1, hlen2.
      rewrite Nat.add_assoc in hlen1,hlen2.
      rewrite <- firstn_skipn with (n:=length us) (l:=ϵ') in H3, H7.
      rewrite <- firstn_skipn with (n:=length vs) (l:=skipn (length us) ϵ') in H3, H7.
      assert (hl1 : length us = length (firstn (length us) ϵ'))
        by (rewrite firstn_length; lia).
      assert (hl2 : length vs = length (firstn (Datatypes.length vs) (skipn (Datatypes.length us) ϵ')))
        by (rewrite firstn_length; rewrite skipn_length; lia).
      pose proof stm_eval_shift_amt _ _ _ _ _ _ _ _ _ _ _ hl1 hl2 hctx H3 as hvs.
      rewrite <- hvs in H3, H7.
      apply IHs1 in H3; auto.
      rewrite hl1 in H7 at 3.
      apply IHs2 in H7; eauto; try rewrite firstn_length; repeat rewrite skipn_length; try lia.
      replace (length ϵ' - length us - length vs) with (length eps) by lia.
      assumption.
    - destruct b; eauto.
  Qed.
End Properties.
