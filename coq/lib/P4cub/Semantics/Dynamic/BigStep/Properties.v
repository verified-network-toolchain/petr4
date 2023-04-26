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
  match goal with
  | hlen: length ?l1 = length ?l2, happ: ?l1 ++ _ = ?l2 ++ _
    |- _ => pose proof sublist.app_eq_len_eq happ hlen as [? ?]; subst
  end.

Ltac app_inv_head_solve :=
  match goal with
  | h: ?x ++ _ = ?x ++ _ |- _ => apply app_inv_head in h; subst
  end.

Ltac app_inv_tail_solve :=
  match goal with
  | h: _ ++ ?x = _ ++ ?x |- _ => apply app_inv_tail in h; subst
  end.

Local Hint Extern 5 => len_app : core.
Local Hint Extern 5 => app_inv_head_solve : core.
Local Hint Extern 5 => app_inv_tail_solve : core.

Variant ctx_cutoff (m : nat) : ctx -> Prop :=
  | ctx_cuttoff_action aa :
    ctx_cutoff m (CAction aa)
  | ctx_cutoff_function :
    ctx_cutoff m CFunction
  | ctx_cutoff_applyblock ts aa ac :
    ctx_cutoff m (CApplyBlock ts aa ac)
  | ctx_cutoff_parserstate n strt sts ap :
    n <= m ->
    ctx_cutoff m (CParserState n strt sts ap).

Section Properties.
  Local Hint Constructors ctx_cutoff : core.

  Lemma ctx_cutoff_le : forall l m c,
      m <= l ->
      ctx_cutoff m c ->
      ctx_cutoff l c.
  Proof using.
    intros l m c hml hc; inv hc; auto.
    constructor. lia.
  Qed.

  Local Hint Resolve ctx_cutoff_le : core.
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
  Local Hint Constructors stm_big_step : core.
  Local Hint Constructors rel_paramarg : core.

  Lemma shift_arg_eval : forall us vs eps arg varg,
      arg_big_step (us ++ eps) arg varg ->
      arg_big_step
        (us ++ vs ++ eps)
        (shift_arg (length us) (length vs) arg)
        (paramarg_map id (shift_lv (length us) (length vs)) varg).
  Proof using.
    unfold arg_big_step.
    intros us vs eps arg varg h; inv h; unravel; auto.
  Qed.

  Local Hint Resolve shift_arg_eval : core.

  Lemma shift_args_eval : forall us vs eps args vargs,
      args_big_step (us ++ eps) args vargs ->
      args_big_step
        (us ++ vs ++ eps)
        (map (shift_arg (length us) (length vs)) args)
        (map (paramarg_map id (shift_lv (length us) (length vs))) vargs).
  Proof using.
    unfold args_big_step.
    intros.
    eapply Forall2_map_l with (lc := args).
    eapply Forall2_map_r with (lc := vargs).
    eauto using sublist.Forall2_impl.
  Qed.

  Local Hint Resolve shift_args_eval : core.

  Lemma arg_eval_shift : forall us vs eps arg varg,
      arg_big_step
        (us ++ vs ++ eps)
        (shift_arg (length us) (length vs) arg)
        (paramarg_map id (shift_lv (length us) (length vs)) varg) ->
      arg_big_step (us ++ eps) arg varg.
  Proof using.
    unfold arg_big_step.
    intros us vs eps [] [] h; unravel in h; inv h; eauto.
  Qed.

  Local Hint Resolve arg_eval_shift : core.

  Lemma arg_eval_shift_exp_exists_shift_varg : forall us vs eps arg varg,
      arg_big_step
        (us ++ vs ++ eps)
        (shift_arg (length us) (length vs) arg)
        varg ->
      exists varg', varg = (paramarg_map id (shift_lv (length us) (length vs)) varg').
  Proof using.
    unfold arg_big_step.
    intros us vs eps [] [] h; unravel in h; inv h; unravel; eauto.
    - exists (PAIn a0). reflexivity.
    - apply shift_exp_lv_eval_shift_lv_exists in H1 as [lv h]; subst.
      exists (PAOut lv); reflexivity.
    - apply shift_exp_lv_eval_shift_lv_exists in H1 as [lv h]; subst.
      exists (PAInOut lv); reflexivity.
  Qed.
  
  Lemma args_eval_shift : forall us vs eps args vargs,
      args_big_step (us ++ vs ++ eps)
        (map (shift_arg (length us) (length vs)) args)
        (map (paramarg_map id (shift_lv (length us) (length vs))) vargs) ->
      args_big_step (us ++ eps) args vargs.
  Proof using.
    unfold args_big_step.
    intros us vs eps args vargs h.
    eapply Forall2_map_l with (lc := args) in h.
    eapply Forall2_map_r with (lc := vargs) in h.
    revert h.
    eapply sublist.Forall2_impl; eauto.
  Qed.

  Local Hint Resolve args_eval_shift : core.

  Lemma args_eval_shift_exp_exists_shift_varg : forall us vs eps args vargs,
      args_big_step
        (us ++ vs ++ eps)
        (map (shift_arg (length us) (length vs)) args)
        vargs -> exists vargs',
        vargs = (map (paramarg_map id (shift_lv (length us) (length vs))) vargs').
  Proof using.
    unfold args_big_step.
    intros us vs eps args.
    induction args as [| arg args ih];
      intros [| varg vargs] h; inv h.
    - exists []; reflexivity.
    - apply arg_eval_shift_exp_exists_shift_varg in H2 as [varg' ?]; subst.
      apply ih in H4 as [vargs' ?]; subst.
      exists (varg' :: vargs'); reflexivity.
  Qed.

  Lemma shift_copy_in :
    forall us vs eps eps' vargs,
      copy_in vargs (us ++ eps) = Some eps' ->
      copy_in
        (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
        (us ++ vs ++ eps) = Some eps'.
  Proof using.
    intros us vs eps eps' vargs h.
    unfold copy_in, pipeline in h |- *.
    rewrite !map_map.
    rewrite <- Forall2_sequence_iff in h |- *.
    rewrite <- Forall2_map_l with (lc := vargs) in h |- *.
    eapply sublist.Forall2_impl; try eassumption.
    intros a v.
    destruct a; simpl in *; auto;
      now rewrite shift_lv_lookup.
  Qed.

  Local Hint Resolve shift_copy_in : core.

  Lemma copy_in_shift :
    forall us vs eps eps' vargs,
      copy_in
        (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
        (us ++ vs ++ eps) = Some eps' ->
      copy_in vargs (us ++ eps) = Some eps'.
  Proof using.
    intros us vs eps eps' vargs h.
    unfold copy_in, pipeline in h |- *.
    rewrite !map_map in h.
    rewrite <- Forall2_sequence_iff in h |- *.
    rewrite <- Forall2_map_l with (lc := vargs) in h |- *.
    revert h.
    eapply sublist.Forall2_impl; try eassumption.
    intros [] v h; unravel in *;
      try rewrite shift_lv_lookup in h; auto.
  Qed.

  Local Hint Resolve copy_in_shift : core.
  
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
  
  Lemma shift_copy_out_argv :
    forall varg us vs eps eps'' eps' us' n,
      length us = length us' ->
      copy_out_argv n varg eps'' (us ++ eps) = us' ++ eps' ->
      copy_out_argv
        n (paramarg_map id (shift_lv (length us) (length vs)) varg)
        eps'' (us ++ vs ++ eps) = us' ++ vs ++ eps'.
  Proof using.
    intros.
    destruct varg as [v | lv | lv]; cbn in *; auto;
      try destruct (nth_error eps'' n) as [v |]; auto.
  Qed.

  Local Hint Resolve shift_copy_out_argv : core.
  Local Hint Rewrite shift_copy_out_argv : core.
  
  Lemma shift_copy_out :
    forall vargs us vs eps eps'' eps' us' n,
      length us = length us' ->
      copy_out n vargs eps'' (us ++ eps) = us' ++ eps' ->
      copy_out
        n (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
        eps'' (us ++ vs ++ eps) = us' ++ vs ++ eps'.
  Proof using.
    induction vargs; intros; unravel in *; auto.
    pose proof (copy_out_argv_length a n eps'' (us ++ eps)) as h.
    rewrite app_length in *.
    apply split_by_length in h.
    destruct h as (xs & ys & hcpy & hxs & hys).
    rewrite hcpy in *.
    eapply shift_copy_out_argv with (vs:=vs) in hcpy; eauto.
    rewrite hcpy, <- hxs.
    eapply IHvargs; eauto || congruence.
  Qed.

  Local Hint Resolve shift_copy_out : core.
  Local Hint Rewrite shift_copy_out : core.

  Lemma lv_update_shift_amt :
    forall lv v us us' vs vs' eps eps',
      length us = length us' ->
      length vs = length vs' ->
      (*length eps = length eps' ->*)
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
  
  Lemma copy_out_argv_shift_amt :
    forall varg us us' vs vs' eps eps' eps'' n,
      length us = length us' ->
      length vs = length vs' ->
      copy_out_argv
        n (paramarg_map id (shift_lv (length us) (length vs)) varg)
        eps'' (us ++ vs ++ eps) = us' ++ vs' ++ eps' ->
      vs = vs'.
  Proof using.
    intros [] us us' vs vs' eps eps' eps'' n hus hvs h; unravel in h; auto;
      try (destruct (nth_error eps'' n) as [v |]); eauto.
  Qed.

  Local Hint Resolve copy_out_argv_shift_amt : core.

  Lemma copy_out_shift_amt :
    forall vargs us us' vs vs' eps eps' eps'' n,
      length us = length us' ->
      length vs = length vs' ->
      copy_out
        n (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
        eps'' (us ++ vs ++ eps) = us' ++ vs' ++ eps' ->
      vs = vs'.
  Proof using.
    intros vargs;
      induction vargs as [| varg vargs ih];
      intros us us' vs vs' eps eps' eps'' n hus hvs h; unravel in h; auto.
    pose proof copy_out_argv_length
      (paramarg_map id (shift_lv (length us) (length vs)) varg)
      n eps'' (us ++ vs ++ eps) as hlen.
    repeat rewrite app_length in hlen.
    rewrite Nat.add_assoc in hlen.
    pose proof split_by_length3 _ _ _ _ _ hlen as
      (xs & ys & zs & hcpy & hxs & hys & hzs).
    eapply copy_out_argv_shift_amt in hcpy as ?; subst; auto.
    rewrite hcpy, <- hxs in h.
    apply ih in h; subst; auto || lia.
  Qed.

  Local Hint Resolve copy_out_shift_amt : core.
  
  Lemma copy_out_argv_shift :
    forall varg us vs eps eps'' eps' us' n,
      length us = length us' ->
      copy_out_argv
        n (paramarg_map id (shift_lv (length us) (length vs)) varg)
        eps'' (us ++ vs ++ eps) = us' ++ vs ++ eps' ->
      copy_out_argv n varg eps'' (us ++ eps) = us' ++ eps'.
  Proof using.
    intros varg us vs eps eps'' eps' us' n hus h.
    destruct varg; unravel in *; auto;
      destruct (nth_error eps'' n) as [v |]; eauto.
  Qed.

  Local Hint Resolve copy_out_argv_shift : core.

  Lemma copy_out_shift :
    forall vargs us vs eps eps'' eps' us' n,
      length us = length us' ->
      copy_out
        n (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
        eps''
        (us ++ vs ++ eps) = us' ++ vs ++ eps' ->
      copy_out n vargs eps'' (us ++ eps) = us' ++ eps'.
  Proof using.
    induction vargs; intros; unravel in *; auto.
    pose proof
      copy_out_argv_length
      (paramarg_map id (shift_lv (length us) (length vs)) a) n eps'' (us ++ vs ++ eps) as h.
    repeat rewrite app_length in *.
    rewrite Nat.add_assoc in h.
    apply split_by_length3 in h.
    destruct h as (xs & ys & zs & hcpy & hxsus & hysvs & hzseps).
    assert (eqvsys : vs = ys).
    { apply copy_out_argv_shift_amt in hcpy; auto. }
    subst.
    rewrite hcpy in *.
    eapply copy_out_argv_shift in hcpy; eauto.
    rewrite hcpy.
    rewrite <- hxsus in H0.
    eapply IHvargs in H0; eauto; try lia.
  Qed.

  Local Hint Resolve copy_out_shift : core.
  
  Lemma shift_lv_update_signal :
    forall olv sig vargs us eps eps' us' vs eps'',
      length us = length us' ->
      lv_update_signal olv sig (copy_out 0 vargs eps'' (us ++ eps))
      = us' ++ eps' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv)
        sig
        (copy_out 0 (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
           eps'' (us ++ vs ++ eps))
      = us' ++ vs ++ eps'.
  Proof using.
    unfold lv_update_signal.
    intros.
    destruct olv; simpl in *; eauto.
    destruct sig; eauto using shift_copy_out.
    destruct v; simpl in *; eauto using shift_copy_out.
    remember (copy_out _ _ _ _) as es in *.
    set (vargs' := (map _ _)).
    remember (copy_out 0 vargs' _ _) as es'.
    symmetry in Heqes, Heqes'.
    pose proof (copy_out_length vargs 0 eps'' (us ++ eps)).
    rewrite !app_length in *.
    pose proof (split_by_length _ _ _ _ H1).
    destruct H2 as [? [? [? [? ?]]]].
    pose proof H2.
    eapply shift_copy_out in H2; eauto.
    rewrite <- Heqes'.
    unfold vargs'.
    rewrite -> H2.
    replace (length us) with (length x) by congruence.
    erewrite shift_lv_update; eauto; congruence.
  Qed.

  Local Hint Resolve shift_lv_update_signal : core.

  Lemma lv_update_signal_shift :
    forall olv sig vargs us eps eps' us' vs eps'',
      length us = length us' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv)
        sig
        (copy_out 0 (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
           eps'' (us ++ vs ++ eps))
      = us' ++ vs ++ eps' ->
      lv_update_signal olv sig (copy_out 0 vargs eps'' (us ++ eps))
      = us' ++ eps'.
  Proof using.
    unfold lv_update_signal.
    intros [lv |] [] vargs us eps eps' us' vs eps'' hus h; unravel in *; eauto.
    destruct v as [v |]; unravel in *; eauto.
    pose proof copy_out_length
      (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
      0 eps'' (us ++ vs ++ eps) as H.
    repeat rewrite app_length in H.
    rewrite Nat.add_assoc in H.
    pose proof split_by_length3 _ _ _ _ _ H as
      (xs & ys & zs & hcpy & hxs & hys & hzs).
    symmetry in hxs, hys.
    pose proof copy_out_shift_amt _ _ _ _ _ _ _ _ _ hxs hys hcpy as ?; subst.
    rewrite hcpy, hxs in h.
    apply lv_update_shift in h; try lia.
    erewrite copy_out_shift by eauto. eauto.
  Qed.

  Local Hint Resolve lv_update_signal_shift : core.

  Lemma lv_update_signal_shift_amt :
    forall olv sig vargs us eps eps' us' vs vs' eps'',
      length us = length us' ->
      length vs = length vs' ->
      lv_update_signal
        (option_map (shift_lv (length us) (length vs)) olv)
        sig
        (copy_out 0 (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
           eps'' (us ++ vs ++ eps))
      = us' ++ vs' ++ eps' ->
      vs = vs'.
  Proof using.
    intros [lv |] [] vargs us eps eps' us' vs vs' eps'' hus hvs h;
      unravel in *; eauto 2.
    destruct v; eauto 2.
    pose proof copy_out_length
      (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
      0 eps'' (us ++ vs ++ eps) as H.
    repeat rewrite app_length in H.
    rewrite Nat.add_assoc in H.
    pose proof split_by_length3 _ _ _ _ _ H as
      (xs & ys & zs & hcpy & hxs & hys & hzs).
    symmetry in hxs, hys.
    pose proof copy_out_shift_amt _ _ _ _ _ _ _ _ _ hxs hys hcpy as ?; subst.
    rewrite hcpy, hxs in h.
    apply copy_out_shift_amt in hcpy; eauto 2; subst.
    apply lv_update_shift_amt in h; eauto 2; subst. lia.
  Qed.
  
  Lemma length_copy_in :
    forall vargs l eps,
      copy_in vargs l = Some eps ->
      length eps = length vargs.
  Proof using.
    unfold copy_in.
    intros.
    apply Option.sequence_length in H.
    simpl in H.
    unfold pipeline in H.
    rewrite map_length in H.
    auto.
  Qed.

  Context `{ext_sem : Extern_Sem}.
  
  Local Hint Constructors SumForall : core.

  Lemma sbs_length : forall Ψ ϵ ϵ' c s sig ψ,
      ⧼ Ψ, ϵ, c, s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ -> length ϵ = length ϵ'.
  Proof using.
    intros Ψ ϵ ϵ' c s sig ψ h;
      induction h; autorewrite with core in *; auto; lia.
  Qed.
  
  Lemma shift_stm_eval : forall Ψ us us' ϵ ϵ' c s sig ψ,
      length us = length us' ->
      ctx_cutoff (length ϵ) c ->
      ⧼ Ψ , us ++ ϵ , c , s ⧽ ⤋ ⧼ us' ++ ϵ' , sig , ψ ⧽ -> forall vs,
          ⧼ Ψ , us ++ vs ++ ϵ , c ,
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
             map
               (paramarg_map
                  id
                  (shift_lv
                     (length us)
                     (length vs))) vargs) in *.
      set (olv' :=
             option_map
               (shift_lv
                  (length us) (length vs)) olv) in *.
      replace (us' ++ vs ++ eps')
        with (lv_update_signal olv' sig (copy_out 0 vargs' ϵ'' (us ++ vs ++ eps))).
      eapply sbs_funct_call; eauto using shift_args_eval, shift_copy_in.
      + inversion H0; subst; cbn in *; constructor; eauto.
      + subst vargs' olv'.
        erewrite shift_lv_update_signal; eauto.
    - replace (us' ++ vs ++ eps')
        with (copy_out 0
                (map (paramarg_map id (shift_lv (length us) (length vs))) vdata_args)
                ϵ''
                (us ++ vs ++ eps)) by eauto.
      eapply sbs_action_call; try eassumption; eauto 3.
      eapply Forall2_map_l with (lc := ctrl_args).
      eauto using sublist.Forall2_impl, shift_exp_eval.
    - (* method call case, will be a repeat of the other call cases *)
      admit.
    - (* invoke case, will be a repeat of the other call cases *)
      admit.
    - replace (us' ++ vs ++ eps')
        with (copy_out 0
                (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
                ϵ''
                (us ++ vs ++ eps)) by eauto.
      econstructor; eauto.
    - (* parser case... *)
      replace (us' ++ vs ++ eps')
        with (copy_out 0
                (map (paramarg_map id (shift_lv (length us) (length vs))) vargs)
                ϵ''
                (us ++ vs ++ eps)) by eauto.
      econstructor; eauto.
      rewrite map_length. eauto.
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
  Admitted.

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

  Lemma s_eval_shift_amt : forall s Ψ us us' vs vs' ϵ ϵ' c sig ψ,
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
      rewrite app_assoc in H,H1.
      pose proof f_equal (length (A:=Val.t)) H as hlen1.
      pose proof f_equal (length (A:=Val.t)) H1 as hlen2.
      repeat rewrite app_length in hlen1,hlen2.
      rewrite <- firstn_skipn with
        (n := length eps - length ϵ₂) (l := eps) in H.
      rewrite <- firstn_skipn with
        (n := length eps' - length ϵ₃) (l := eps') in H1.
      rewrite app_assoc in H,H1.
      pose proof skipn_length_minus H4 as hskiplen1.
      pose proof skipn_length_minus (n:=length ϵ₃) (l:=eps') ltac:(lia) as hskiplen2.
      pose proof app_eq_len_tail_app H (Logic.eq_sym hskiplen1) as [hϵ₁ hϵ₂].
      pose proof app_eq_len_tail_app H1 (Logic.eq_sym hskiplen2) as [h hϵ₃].
      rewrite hϵ₁ in h.
      assert (hlenusvs : length (us ++ vs) = length (us' ++ vs'))
        by (rewrite !app_length; lia).
      apply sublist.app_eq_len_eq in h as [husvs _]; auto.
    - apply shift_exp_lv_eval_shift_lv_exists in H4 as [lv' ?]; subst. eauto 2.
    - destruct call as [g ts oe | | |]; unravel in *; inv H.
      apply args_eval_shift_exp_exists_shift_varg in H6 as [vargs' ?]; subst.
      apply relop_lexp_big_step_exists_shift in H3 as [olv' ?]; subst.
      apply lv_update_signal_shift_amt in H1; eauto 1.
    - destruct call as [| act cargs | |]; unravel in *; inv H.
      apply args_eval_shift_exp_exists_shift_varg in H7 as [vargs' ?]; subst.
      apply copy_out_shift_amt in H1; eauto 2.
    - admit.
    - apply args_eval_shift_exp_exists_shift_varg in H5 as [vargs' ?]; subst.
      apply copy_out_shift_amt in H1; eauto 2.
    - apply args_eval_shift_exp_exists_shift_varg in H3 as [vargs' ?]; subst.
      apply copy_out_shift_amt in H1; eauto 2.
    - admit.
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
      + eapply ctx_cutoff_le with (m:=length eps); lia || assumption.
    - eapply IHs1 in H7; eauto 2.
    - destruct b.
      + eapply IHs1 in H8; eauto 2.
      + eapply IHs2 in H8; eauto 2.
  Admitted.
  
  Lemma s_eval_shift : forall s Ψ us us' vs ϵ ϵ' c sig ψ,
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
      admit.
    - pose proof shift_exp_lv_eval_shift_lv_exists
        _ _ _ _ _ H4 as [lv' ?]; subst.
      apply lv_update_shift in H3 as h; eauto.
      rewrite <- h. eauto.
    - pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H6 as [vargs' ?]; subst.
      destruct call as [g ts oe| | |]; unravel in *; inv H.
      pose proof relop_lexp_big_step_exists_shift _ _ _ _ _ H3 as [olv' h]; subst.
      apply lv_update_signal_shift in H1; eauto.
      rewrite <- H1.
      rewrite relop_map_both in H3.
      econstructor; eauto.
      eapply relop_impl in H3; eauto.
    - pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H7 as [dvargs ?]; subst.
      destruct call as [| act cargs | |]; unravel in *; inv H.
      apply copy_out_shift in H1; eauto.
      rewrite <- H1.
      econstructor; eauto 2.
      rewrite <- Forall2_map_l in H4.
      eapply sublist.Forall2_impl in H4; eauto 2.
    - admit.
    - destruct call; unravel in *; inv H.
      pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H5 as [vargs' ?]; subst.
      apply copy_out_shift in H1; eauto.
      rewrite <- H1.
      econstructor; eauto.
    - destruct call; unravel in *; inv H.
      pose proof args_eval_shift_exp_exists_shift_varg
        _ _ _ _ _ H3 as [vargs' ?]; subst.
      apply copy_out_shift in H1; eauto.
      rewrite <- H1.
      rewrite map_length in H10.
      econstructor; eauto.
    - admit.
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
      pose proof s_eval_shift_amt _ _ _ _ _ _ _ _ _ _ _ hl1 hl2 hctx H3 as hvs.
      rewrite <- hvs in H3, H7.
      apply IHs1 in H3; auto.
      rewrite hl1 in H7 at 3.
      apply IHs2 in H7; eauto; try rewrite firstn_length; repeat rewrite skipn_length; try lia.
      replace (length ϵ' - length us - length vs) with (length eps) by lia.
      assumption.
    - destruct b; eauto.
  Admitted.
End Properties.
