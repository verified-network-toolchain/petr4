Require Export Poulet4.LightTyping.Typing.

Ltac some_inv :=
  match goal with
  | H: Some _ = Some _ |- _ => inversion H; subst; clear H
  end.

Ltac match_some_inv :=
  match goal with
  | H: match ?trm with Some _ => _ | None => _ end = Some _
    |- _ => destruct trm as [? |] eqn:? ; cbn in *;
          try discriminate
  end.

Section Lemmas.
  Context {tags_t : Type}.
  Notation typ := (@P4Type tags_t).
  Notation ident := string.
  Notation path := (list ident).

  Create HintDb option_monad.
  Local Hint Unfold option_ret : option_monad.
  Local Hint Unfold option_bind : option_monad.
  Local Hint Unfold option_monad : option_monad.
  Local Hint Unfold option_monad_inst : option_monad.
  Local Hint Constructors predopt : core.
  Local Hint Constructors member_type : core.

  Lemma get_real_member_type : forall (t r : typ) ts ge,
      get_real_type ge t = Some r ->
      member_type ts t ->
      exists rs, member_type rs r.
  Proof.
    intros t r ts ge Hge Hmem.
    inversion Hmem; subst; cbn in *;
      autounfold with option_monad in *;
      try match_some_inv; try some_inv;
        try match goal with
            | H: sequence _ = Some ?rs
              |- exists _, _ => exists rs; auto
            end.
  Qed.

  Local Hint Constructors get_member : core.

  Lemma member_get_member_ex : forall x v ts (t t' : typ),
      AList.get ts x = Some t'  ->
      member_type ts t ->
      ⊢ᵥ v \: t ->
      exists v', get_member v (P4String.str x) v'.
  Proof.
    intros x v ts t t' Htsx Hmem Hvt.
    inversion Hmem; subst; inversion Hvt; subst; cbn in *;
      unfold AList.all_values, P4String.clear_AList_tags in *;
      rewrite Forall2_conj in *;
      match goal with
      | H: Forall2 _ ?vs _ /\ Forall2 _ ?vs _
        |- _ => destruct H as [H _];
                enough (exists v', AList.get vs (P4String.str x) = Some v')
                by firstorder eauto
      end;
      match goal with
      | H: Forall2 _ ?vs _
        |- _ =>
        rewrite Forall2_map_both, Forall2_eq, map_fst_map in H;
          apply AList.get_some_in_fst in Htsx as (x' & Hxx' & Hx');
          apply in_map with (f := P4String.str) in Hx';
          rewrite <- H in Hx';
          destruct x as [ix x]; destruct x' as [ix' x']; cbn in *;
            unfold Equivalence.equiv, P4String.equiv in Hxx'; cbn in *; subst;
              apply AList.in_fst_get_some in Hx' as [v Hv]; eauto
      end.  
  Qed.

  Local Hint Constructors val_typ : core.
  
  Lemma get_member_types : forall x ts (t t' : typ) v v',
      member_type ts t ->
      AList.get ts x = Some t' ->
      get_member v (P4String.str x) v' ->
      ⊢ᵥ v \: t ->
      ⊢ᵥ v' \: t'.
  Proof.
    intros x ts t t' v v' Htst Htsx Hgm Hvt.
    inversion Htst; subst; inversion Hvt; subst;
      inversion Hgm; subst;
        rewrite P4String.get_clear_AList_tags in Htsx;
        match goal with
        | H: AList.all_values _ _ _
          |- _ => eapply AList.get_relate_values in H; eauto
        end.
  Qed.
  
  Create HintDb ind_def.
  
  Definition
    ok_get_real_type_ex_def Δ (τ : typ) := forall ge : genv_typ,
      delta_genv_prop ge Δ ->
      exists ρ, get_real_type ge τ = Some ρ.

  Local Hint Unfold ok_get_real_type_ex_def : ind_def.
  
  Definition
    ok_get_real_ctrl_ex_def Δ ct := forall ge : @genv_typ tags_t,
      delta_genv_prop ge Δ ->
      exists ct', get_real_ctrl ge ct = Some ct'.

  Local Hint Unfold ok_get_real_ctrl_ex_def : ind_def.
  
  Definition
    ok_get_real_func_ex_def Δ ft := forall ge : @genv_typ tags_t,
      delta_genv_prop ge Δ ->
      exists ft', get_real_func ge ft = Some ft'.

  Local Hint Unfold ok_get_real_func_ex_def : ind_def.

  Definition
    ok_get_real_param_ex_def Δ p := forall ge : @genv_typ tags_t,
      delta_genv_prop ge Δ ->
      exists p', get_real_param ge p = Some p'.

  Local Hint Unfold ok_get_real_param_ex_def : ind_def.
  
  Definition
    ok_get_real_type_ex_ind :=
    my_P4Type_ok_ind
      _ ok_get_real_type_ex_def
      ok_get_real_ctrl_ex_def
      ok_get_real_func_ex_def
      ok_get_real_param_ex_def.

  Lemma delta_genv_prop_remove : forall Δ (ge : @genv_typ tags_t) X,
      delta_genv_prop ge Δ ->
      delta_genv_prop (IdentMap.remove X ge) (remove_str X Δ).
  Proof.
    intros d ge X H.
    unfold delta_genv_prop in *.
    rewrite Forall_forall in *; intros Y HInY.
    apply in_remove in HInY as [HInYd HYX].
    unfold IdentMap.get, IdentMap.remove in *.
    rewrite FuncAsMap.remove_complete by assumption; eauto.
  Qed.

  Local Hint Resolve delta_genv_prop_remove : core.

  Lemma delta_genv_prop_removes : forall Xs Δ (ge : @genv_typ tags_t),
      delta_genv_prop ge Δ ->
      delta_genv_prop (IdentMap.removes Xs ge) (remove_all Δ Xs).
  Proof.
    unfold IdentMap.removes, FuncAsMap.removes.
    intro Xs; induction Xs as [| X Xs IHXs]; intros d ge Hged; cbn; auto.
  Qed.

  Local Hint Resolve delta_genv_prop_removes : core.

  Lemma list_ok_get_real_type_ex : forall Δ ts,
      Forall (fun t => Δ ⊢ok t) ts ->
      Forall
        (fun τ => forall ge,
             delta_genv_prop ge Δ ->
             exists ρ, get_real_type ge τ = Some ρ) ts ->
      forall ge : @genv_typ tags_t,
        delta_genv_prop ge Δ ->
        exists ρs,
          sequence (map (get_real_type ge) ts) = Some ρs.
  Proof.
    intros d ts Hts IHts ge Hge.
    rewrite Forall_forall in IHts.
    specialize IHts with (ge := ge).
    pose proof reduce_inner_impl _ _ _ _ IHts Hge as H; cbn in *.
    rewrite <- Forall_forall, Forall_exists_factor in H.
    destruct H as [ts' Hts'].
    rewrite Forall2_map_l
      with (R := fun a b => a = Some b) (f := get_real_type ge)
      in Hts'.
    rewrite Forall2_sequence_iff in Hts'; eauto.
  Qed.

  Local Hint Resolve list_ok_get_real_type_ex : core.
  
  Lemma alist_ok_get_real_type_ex :
    forall Δ (ts : list (P4String.t tags_t * typ)),
      Forall (fun t => Δ ⊢ok snd t) ts ->
      Forall
        (fun t => forall ge,
             delta_genv_prop ge Δ ->
             exists ρ, get_real_type ge (snd t) = Some ρ) ts ->
      forall ge : @genv_typ tags_t,
        delta_genv_prop ge Δ -> exists ρs,
          sequence
            (map
               (fun '(a, t) =>
                  match get_real_type ge t with
                  | Some t' => Some (a, t')
                  | None    => None
                  end) ts) = Some ρs.
  Proof.
    intros d xts Hxts IHxts ge Hge.
    rewrite Forall_forall in IHxts.
    specialize IHxts with (ge := ge).
    pose proof reduce_inner_impl _ _ _ _ IHxts Hge as H; cbn in *.
    rewrite <- Forall_forall, Forall_exists_factor in H.
    destruct H as [ts' Hts'].
    rewrite map_pat_both.
    assert (Hfst : map fst xts = map fst (combine (map fst xts) ts')).
    { rewrite map_fst_combine; try reflexivity.
      apply Forall2_length in Hts'.
      repeat rewrite map_length; assumption. }
    assert (Hsnd :
              Forall2
                (fun a b => get_real_type ge a = Some b)
                (map snd xts) (map snd (combine (map fst xts) ts'))).
    { rewrite map_snd_combine.
      - rewrite <- Forall2_map_l. assumption.
      - apply Forall2_length in Hts'.
        repeat rewrite map_length in *; assumption. }
    rewrite Forall2_map_l
      with (R := fun a b => a = Some b) (f := fun a => get_real_type ge (snd a))
      in Hts'.
    rewrite <- map_map with (f := snd) in Hts'.
    pose proof conj Hfst Hsnd as H.
    rewrite <- Forall2_destr_pair_eq in H.
    rewrite Forall2_map_l
      with
        (f :=
           fun uv =>
             match get_real_type ge (snd uv) with
             | Some w => Some (fst uv, w)
             | None   => None
             end)
        (R := fun uv uw => uv = Some uw) in H.
    rewrite Forall2_sequence_iff in H.
    autounfold with option_monad in *.
    rewrite H; eauto.
  Qed.

  Local Hint Resolve alist_ok_get_real_type_ex : core.

  Lemma list_ok_get_real_param_ex : forall Δ ps,
      Forall (P4Parameter_ok Δ) ps ->
      Forall
        (fun p => forall ge,
             delta_genv_prop ge Δ -> exists p',
               get_real_param ge p = Some p')
        ps -> forall ge : @genv_typ tags_t,
          delta_genv_prop ge Δ ->
          exists ps', sequence (map (get_real_param ge) ps) = Some ps'.
  Proof.
    intros d ps Hps IHps ge Hged.
    rewrite Forall_forall in IHps.
    specialize IHps with (ge := ge).
    pose proof reduce_inner_impl _ _ _ _ IHps Hged as H; cbn in *.
    rewrite <- Forall_forall, Forall_exists_factor in H.
    destruct H as [ps' Hps'].
    rewrite Forall2_map_l
      with (R := fun a b => a = Some b) (f := get_real_param ge)
      in Hps'.
    rewrite Forall2_sequence_iff in Hps'; eauto.
  Qed.

  Local Hint Resolve list_ok_get_real_param_ex : core.
  
  Lemma ok_get_real_type_ex :
    forall Δ τ, Δ ⊢ok τ ->
      ok_get_real_type_ex_def Δ τ.
  Proof.
    apply ok_get_real_type_ex_ind;
      autounfold with ind_def; cbn;
        autounfold with option_monad; eauto 2.
    - intros d t n H Hge ge Hdge.
      apply Hge in Hdge as [r Hr]; rewrite Hr; eauto 2.
    - intros d ts Hts IHts ge Hge.
      eapply list_ok_get_real_type_ex in Hts as [ts' Hts']; eauto.
      autounfold with option_monad in *.
      rewrite Hts'; eauto.
    - intros d ts Hts IHts ge Hge.
      eapply list_ok_get_real_type_ex in Hts as [ts' Hts']; eauto.
      autounfold with option_monad in *.
      rewrite Hts'; eauto.
    - intros d xts Hxts IHxts ge Hge.
      eapply alist_ok_get_real_type_ex in Hxts as [ts' Hts']; eauto.
      autounfold with option_monad in *.
      rewrite Hts'; eauto.
    - intros d t H Hge ge Hdge.
      apply Hge in Hdge as [r Hr]; rewrite Hr; eauto 2.
    - intros d xts Hxts IHxts ge Hge.
      eapply alist_ok_get_real_type_ex in Hxts as [ts' Hts']; eauto.
      autounfold with option_monad in *.
      rewrite Hts'; eauto.
    - intros d xts Hxts IHxts ge Hge.
      eapply alist_ok_get_real_type_ex in Hxts as [ts' Hts']; eauto.
      autounfold with option_monad in *.
      rewrite Hts'; eauto.
    - intros d xts Hxts IHxts ge Hge.
      eapply alist_ok_get_real_type_ex in Hxts as [ts' Hts']; eauto.
      autounfold with option_monad in *.
      rewrite Hts'; eauto.
    - intros d X ot mems H Hot ge Hdge.
      inversion Hot as [| t Ht]; subst; eauto.
      specialize Ht with (ge := IdentMap.remove (P4String.str X) ge).
      assert (HdX :
                delta_genv_prop
                  (IdentMap.remove (P4String.str X) ge)
                  (remove_str (P4String.str X) d)) by eauto.
      apply Ht in HdX as [rt Hrt]; clear Ht.
      rewrite Hrt; eauto.
    - intros d X HXd ge Hge.
      unfold delta_genv_prop in Hge.
      rewrite Forall_forall in Hge. firstorder.
    - firstorder.
    - intros d ct Hct IH ge Hdge.
      apply IH in Hdge as [ct' Hct'].
      unfold get_real_ctrl in Hct'.
      cbn in Hct'; autounfold with option_monad in Hct'.
      rewrite Hct'; eauto.
    - intros d ct Hct IH ge Hdge.
      apply IH in Hdge as [ct' Hct'].
      unfold get_real_ctrl in Hct'.
      cbn in Hct'; autounfold with option_monad in Hct'.
      rewrite Hct'; eauto.
    - intros d ct Hct IH ge Hdge.
      apply IH in Hdge as [ft' Hft'].
      unfold get_real_func in Hft'.
      cbn in Hft'; autounfold with option_monad in Hft'.
      rewrite Hft'; eauto.
    - intros d ds cs Hds IHds Hcs IHcs ge Hged.
      eapply list_ok_get_real_param_ex in Hds as [ds' Hds']; eauto.
      eapply list_ok_get_real_param_ex in Hcs as [cs' Hcs']; eauto.
      unfold get_real_param in Hds'; unfold get_real_param in Hcs'.
      cbn in Hds', Hcs';
        autounfold with option_monad in Hcs', Hds'.
      rewrite Hcs', Hds'; eauto.
    - intros d Xs Ys ps Hps IHps ge Hged.
      eapply list_ok_get_real_param_ex in Hps as [ps' Hps']; eauto.
      + unfold get_real_param in Hps'; cbn in Hps';
          autounfold with option_monad in Hps'.
        rewrite Hps'; eauto.
      + eauto.
    - intros d t ts Hts IHts Ht IHt ge Hged.
      eapply list_ok_get_real_type_ex
        in Hts as [ts' Hts']; eauto.
      apply IHt in Hged as [t' Ht'].
      autounfold with option_monad in *.
      rewrite Ht', Hts'; eauto.
    - intros d Xs Ys ps t Hps IHps Ht IHt ge Hged.
      apply delta_genv_prop_removes
        with (Xs := map P4String.str Xs) in Hged.
      eapply list_ok_get_real_param_ex
        in Hps as [ps' Hps']; eauto.
      apply IHt in Hged as [t' Ht'].
      rewrite Ht'.
      unfold get_real_param in Hps';
        cbn in Hps'; autounfold with option_monad in Hps'.
      rewrite Hps'; eauto.
    - intros d Xs ps Hps IHps ge Hged.
      apply delta_genv_prop_removes
        with (Xs := map P4String.str Xs) in Hged.
      eapply list_ok_get_real_param_ex
        in Hps as [ps' Hps']; eauto.
      unfold get_real_param in Hps';
        cbn in Hps'; autounfold with option_monad in Hps'.
      rewrite Hps'; eauto.
    - intros d Xs ps k t Hps IHps Ht IHt ge Hged.
      apply delta_genv_prop_removes
        with (Xs := map P4String.str Xs) in Hged.
      eapply list_ok_get_real_param_ex
        in Hps as [ps' Hps']; eauto.
      apply IHt in Hged as [t' Ht'].
      unfold get_real_param in Hps';
        cbn in Hps'; autounfold with option_monad in Hps'.
      rewrite Hps'; clear Hps'.
      unfold get_real_type in Ht';
        cbn in Ht'; autounfold with option_monad in Ht'.
      rewrite Ht'; eauto.
    - intros d b dr t n x Ht IHt ge Hged.
      apply IHt in Hged as [t' Ht'].
      unfold get_real_type in Ht';
        cbn in Ht'; autounfold with option_monad in Ht'.
      rewrite Ht'; eauto.
  Qed.
  
  Definition delta_genv_prop_ok_typ_nil_def
             Δ (t : typ) := forall ge rt,
      delta_genv_prop ge Δ ->
      get_real_type ge t = Some rt ->
      [] ⊢ok rt.

  Local Hint Unfold delta_genv_prop_ok_typ_nil_def : ind_def.
  
  Definition delta_genv_prop_ok_ctrl_nil_def
             Δ (ct : @ControlType tags_t) := forall ge ct',
      delta_genv_prop ge Δ ->
      get_real_ctrl ge ct = Some ct' ->
      ControlType_ok [] ct'.

  Local Hint Unfold delta_genv_prop_ok_ctrl_nil_def : ind_def.

  Definition delta_genv_prop_ok_func_nil_def
             Δ (ft : @FunctionType tags_t) := forall ge ft',
      delta_genv_prop ge Δ ->
      get_real_func ge ft = Some ft' ->
      FunctionType_ok [] ft'.

  Local Hint Unfold delta_genv_prop_ok_func_nil_def : ind_def.

  Definition delta_genv_prop_ok_param_nil_def
             Δ (p : @P4Parameter tags_t) := forall ge p',
      delta_genv_prop ge Δ ->
      get_real_param ge p = Some p' ->
      P4Parameter_ok [] p'.

  Local Hint Unfold delta_genv_prop_ok_param_nil_def : ind_def.

  Definition delta_genv_prop_ok_typ_nil_ind :=
    my_P4Type_ok_ind
      _ delta_genv_prop_ok_typ_nil_def
      delta_genv_prop_ok_ctrl_nil_def
      delta_genv_prop_ok_func_nil_def
      delta_genv_prop_ok_param_nil_def.

  Local Hint Constructors P4Type_ok : core.
  Local Hint Constructors ControlType_ok : core.
  Local Hint Constructors FunctionType_ok : core.
  Local Hint Constructors P4Parameter_ok : core.

  Local Hint Resolve nth_error_some_length : core.
  Local Hint Resolve nth_error_In : core.
  Local Hint Resolve nth_error_in_combine : core.
  Local Hint Resolve ListUtil.nth_error_exists : core.
  Local Hint Resolve In_nth_error : core.

  Lemma delta_genv_prop_ok_typ_nil_list : forall Δ ge (ts rs : list typ),
      Forall (fun t => Δ ⊢ok t) ts ->
      Forall (fun t =>
                forall ge r,
                  delta_genv_prop ge Δ ->
                  get_real_type ge t = Some r ->
                  [] ⊢ok r) ts ->
      delta_genv_prop ge Δ ->
      sequence (map (get_real_type ge) ts) = Some rs ->
      Forall (fun r => [] ⊢ok r) rs.
  Proof.
    intros d ge ts rs Hts IHts Hge Hrs.
    rewrite Forall_forall in IHts.
    specialize IHts with (ge := ge).
    rewrite Forall_forall.
    rewrite <- Forall2_sequence_iff, <- Forall2_map_l, Forall2_forall in Hrs.
    destruct Hrs as [Hlen Htsl].
    intros x Hxl.
    apply In_nth_error in Hxl as [n Hn].
    assert (Htst: exists t, nth_error ts n = Some t).
    { apply ListUtil.nth_error_exists.
      rewrite Hlen.
      eauto using nth_error_some_length. }
    firstorder eauto.
  Qed.

  Local Hint Resolve delta_genv_prop_ok_typ_nil_list : core.

  Lemma delta_genv_prop_ok_typ_nil_alist :
    forall Δ ge (xts xrs : list (P4String.t tags_t * typ)),
      Forall (fun xt => Δ ⊢ok snd xt) xts ->
      Forall (fun xt => forall ge r,
                  delta_genv_prop ge Δ ->
                  get_real_type ge (snd xt) = Some r ->
                  [] ⊢ok r) xts ->
      delta_genv_prop ge Δ ->
      sequence
        (map
           (fun '(x,t) =>
              match get_real_type ge t with
              | Some r => Some (x,r)
              | None   => None
              end)
           xts)
      = Some xrs ->
      Forall (fun xr => [] ⊢ok snd xr) xrs.
  Proof.
    intros d ge xts xrs Hxts IHxts Hge Hxrs.
    rewrite Forall_forall in IHxts.
    specialize IHxts with (ge := ge).
    rewrite Forall_forall.
    rewrite <- Forall2_sequence_iff, <- Forall2_map_l, Forall2_forall in Hxrs.
    destruct Hxrs as [Hlen Htsl].
    intros [x r] Hxl.
    apply In_nth_error in Hxl as [n Hn].
    assert (Htst: exists yt, nth_error xts n = Some yt).
    { apply ListUtil.nth_error_exists.
      rewrite Hlen.
      eauto using nth_error_some_length. }
    destruct Htst as [[y t] Hyt].
    specialize Htsl with (u := (y,t)) (v := (x,r)); cbn in *.
    assert (HIn : List.In ((y,t),(x,r)) (combine xts xrs)) by eauto.
    apply Htsl in HIn. match_some_inv; some_inv; eauto.
  Qed.

  Local Hint Resolve delta_genv_prop_ok_typ_nil_alist : core.

  Lemma delta_genv_prop_ok_param_nil_list :
    forall Δ ge (ps rs : list (@P4Parameter tags_t)),
      Forall (P4Parameter_ok Δ) ps ->
      Forall
        (fun p =>
           forall ge p',
             delta_genv_prop ge Δ ->
             get_real_param ge p = Some p' ->
             P4Parameter_ok [] p') ps ->
      delta_genv_prop ge Δ ->
      sequence (map (get_real_param ge) ps) = Some rs ->
      Forall (P4Parameter_ok []) rs.
  Proof.
    intros d ge ps rs Hps IHps Hge Hrs.
    rewrite Forall_forall in IHps.
    specialize IHps with (ge := ge).
    rewrite Forall_forall.
    rewrite <- Forall2_sequence_iff, <- Forall2_map_l, Forall2_forall in Hrs.
    destruct Hrs as [Hlen Htsl].
    intros x Hxl.
    apply In_nth_error in Hxl as [n Hn].
    assert (Htst: exists p, nth_error ps n = Some p).
    { apply ListUtil.nth_error_exists.
      rewrite Hlen.
      eauto using nth_error_some_length. }
    firstorder eauto.
  Qed.

  Local Hint Resolve delta_genv_prop_ok_param_nil_list : core.
  Hint Rewrite remove_all_nil : core.
  
  Lemma delta_genv_prop_ok_typ_nil : forall Δ t,
      Δ ⊢ok t ->
      delta_genv_prop_ok_typ_nil_def Δ t.
  Proof.
    apply delta_genv_prop_ok_typ_nil_ind;
      autounfold with ind_def; cbn;
        autounfold with option_monad;
        try (intros; repeat match_some_inv;
             some_inv; eauto; assumption).
    - intros d X t mems Ht IHt ge r Hge Hr.
      destruct t as [t |]; inversion IHt; subst;
        try match_some_inv; some_inv; eauto.
      constructor; constructor; cbn.
      apply H0 in Heqo; eauto.
    - intros d X HXd ge r Hge Hr.
      unfold delta_genv_prop in Hge.
      rewrite Forall_forall in Hge.
      apply Hge in HXd.
      destruct HXd as (t' & Hget & Ht').
      rewrite Hget in Hr; inversion Hr; subst; auto.
    - intros d X t Ht IHt ge r Hge Hr.
      apply IHt in Hr; auto.
    - intros d Xs Ts ps Hps IHps ge r Hge Hr.
      match_some_inv; some_inv.
      constructor; autorewrite with core.
      eapply delta_genv_prop_ok_param_nil_list in Hps;
        eauto using delta_genv_prop_removes.
    - intros d Xs Ys ps t Hps IHps Ht IHts ge r Hge Hr.
      repeat match_some_inv; some_inv.
      constructor; autorewrite with core.
      eapply delta_genv_prop_ok_param_nil_list in Heqo0;
        eauto using delta_genv_prop_removes.
      eapply IHts; eauto using delta_genv_prop_removes.
    - intros d Xs ps Hps IHps ge r Hge Hr.
      match_some_inv; some_inv.
      constructor; autorewrite with core.
      eapply delta_genv_prop_ok_param_nil_list in Hps;
        eauto using delta_genv_prop_removes.
    - intros d Xs ps k t Hps IHps Ht IHt ge r Hge Hr.
      repeat match_some_inv; some_inv.
      constructor; autorewrite with core.
      eapply delta_genv_prop_ok_param_nil_list in Hps;
        eauto using delta_genv_prop_removes.
      eapply IHt; eauto using delta_genv_prop_removes.
  Qed.

  Lemma member_type_get_real_type : forall ts rs (t r : typ) ge,
      member_type ts t -> member_type rs r ->
      get_real_type ge t = Some r ->
      sequence (map (fun '(x,t) => get_real_type ge t >>| pair x) ts) = Some rs.
  Proof.
    intros ts rs t r ge Hts Hrs Htr;
      inversion Hts; subst; inversion Hrs; subst;
        cbn in *; autounfold with option_monad in *;
          match_some_inv; some_inv; reflexivity.
  Qed.
End Lemmas.
