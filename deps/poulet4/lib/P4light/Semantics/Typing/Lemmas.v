From Poulet4 Require Export Utils.P4Arith
     P4light.Semantics.Typing.Typing.
Require Export Coq.ZArith.BinInt.

(** * Helper Lemmas for [Rules.v]. *)

Lemma N_of_Z_of_nat : forall n,
    Z.to_N (Z.of_nat n) = N.of_nat n.
Proof.
  intros; lia.
Qed.

Lemma length_to_lbool : forall n z,
    List.length (to_lbool n z) = N.to_nat n.
Proof.
  intros n z. pose proof Zlength_to_lbool n z as h.
  rewrite Zlength_correct in h. lia.
Qed.

Section Lemmas.
  Context {tags_t : Type}.
  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation path := (list String.string).

  Lemma sub_gamma_var_refl : forall (Γ : @gamma_var tags_t),
      sub_gamma_var Γ Γ.
  Proof.
    intros g; unfold sub_gamma_var.
    auto using FuncAsMap.submap_refl.
  Qed.

  Lemma sub_gamma_const_refl : forall p (Γ : @gamma_const tags_t),
      sub_gamma_const p Γ Γ.
  Proof.
    intros p g; unfold sub_gamma_const.
    auto using FuncAsMap.submap_refl.
  Qed.

  Local Hint Resolve sub_gamma_var_refl : core.
  Local Hint Resolve sub_gamma_const_refl : core.

  Lemma sub_gamma_expr_refl : forall p (Γ : @gamma_expr tags_t),
      sub_gamma_expr p Γ Γ.
  Proof.
    intros p g; unfold sub_gamma_expr; auto.
  Qed.

  Section SubGamma.
    Context `{T: @Target tags_t expr}.

    Lemma gamma_const_domain_sub_gamma :
      forall p (ge : @genv _ T) (Γ Γ' : @gamma_const tags_t),
        sub_gamma_const p Γ Γ' ->
        gamma_const_domain p Γ' ge ->
        gamma_const_domain p Γ ge.
    Proof.
      unfold sub_gamma_const,gamma_const_domain,FuncAsMap.submap; eauto.
    Qed.

    Lemma gamma_const_val_typ_sub_gamma :
      forall p (ge : @genv _ T) (Γ Γ' : @gamma_const tags_t),
        sub_gamma_const p Γ Γ' ->
        gamma_const_val_typ p Γ' ge ->
        gamma_const_val_typ p Γ ge.
    Proof.
      unfold sub_gamma_const,gamma_const_val_typ,FuncAsMap.submap; eauto.
    Qed.

    Local Hint Resolve gamma_const_domain_sub_gamma : core.
    Local Hint Resolve gamma_const_val_typ_sub_gamma : core.

    Lemma gamma_const_prop_sub_gamma :
      forall p (ge : @genv _ T) (Γ Γ' : @gamma_const tags_t),
        sub_gamma_const p Γ Γ' ->
        gamma_const_prop p Γ' ge ->
        gamma_const_prop p Γ ge.
    Proof.
      unfold gamma_const_prop; firstorder eauto.
    Qed.

    Variables st st' : @state _ T.

    Lemma gamma_var_domain_sub_gamma :
      forall (Γ Γ' : @gamma_var tags_t),
        sub_gamma_var Γ Γ' ->
        gamma_var_domain Γ' st' ->
        gamma_var_domain Γ st'.
    Proof.
      unfold sub_gamma_var, gamma_var_domain, FuncAsMap.submap; eauto.
    Qed.

    Lemma gamma_var_val_typ_sub_gamma :
      forall ge (Γ Γ' : @gamma_var tags_t),
        sub_gamma_var Γ Γ' ->
        gamma_var_val_typ Γ' st' ge ->
        gamma_var_val_typ Γ st' ge.
    Proof.
      unfold sub_gamma_var,gamma_var_val_typ,FuncAsMap.submap; eauto.
    Qed.

    Local Hint Resolve gamma_var_domain_sub_gamma : core.
    Local Hint Resolve gamma_var_val_typ_sub_gamma : core.

    Lemma gamma_var_prop_sub_gamma : forall ge (Γ Γ' : @gamma_var tags_t),
      sub_gamma_var Γ Γ' ->
      gamma_var_prop Γ' st' ge ->
      gamma_var_prop Γ st' ge.
    Proof.
      unfold gamma_var_prop; firstorder eauto.
    Qed.

    Variables (p : path) (ge : @genv _ T).

    Local Hint Resolve gamma_const_prop_sub_gamma : core.
    Local Hint Resolve gamma_var_prop_sub_gamma : core.

    Lemma gamma_expr_prop_sub_gamma : forall (Γ Γ' : @gamma_expr tags_t),
        sub_gamma_expr p Γ Γ' ->
        gamma_expr_prop p Γ' st' ge ->
        gamma_expr_prop p Γ st' ge.
    Proof.
      unfold sub_gamma_expr,gamma_expr_prop; firstorder eauto.
    Qed.

    Lemma gamma_stmt_prop_sub_gamma : forall Δ (Γ Γ' : @gamma_stmt tags_t),
        sub_gamma_expr p Γ Γ' ->
        gamma_stmt_prop ge p Δ Γ st ->
        gamma_stmt_prop ge p Δ Γ' st' ->
        gamma_stmt_prop ge p Δ Γ st'.
    Proof.
      unfold gamma_stmt_prop; firstorder eauto.
    Qed.
  End SubGamma.

  Section BindSub.
    Variables (l : Locator) (t : typ).

    Lemma bind_var_typ_sub_gamma_var : forall Γ : gamma_var,
        PathMap.get (get_loc_path l) Γ = None ->
        sub_gamma_var Γ (bind_var_typ l t Γ).
    Proof.
      unfold sub_gamma_var,FuncAsMap.submap,bind_var_typ.
      intros g Hl l' t' Hlt'.
      destruct l as [p | p]; destruct l' as [l' | l'];
        cbn in *; try discriminate;
          rewrite PathMap.get_set_diff;
          assumption || intros H; subst; rewrite Hl in Hlt'; discriminate.
    Qed.

    Variable p : path.

    Lemma bind_var_typ_gamma_sub_gamma : forall Γ : gamma_expr,
        PathMap.get (get_loc_path l) (var_gamma Γ) = None ->
        sub_gamma_expr p Γ (bind_var_typ_gamma_expr l t Γ).
    Proof.
      unfold bind_var_typ_gamma_expr,sub_gamma_expr.
      intros [gv gc] H; cbn in *.
      split; auto using bind_var_typ_sub_gamma_var.
    Qed.

    Lemma bind_typ_gamma_stmt_sub_gamma : forall (Γ : gamma_stmt),
        PathMap.get (get_loc_path l) (var_gamma Γ) = None ->
        sub_gamma_expr p Γ (bind_typ_gamma_stmt l t Γ).
    Proof.
      unfold bind_typ_gamma_stmt.
      intros [ge gf] H; cbn in *.
      auto using bind_var_typ_gamma_sub_gamma.
    Qed.
  End BindSub.

  Local Hint Constructors val_typ : core.
  Local Hint Resolve val_to_sval_ex : core.

  Ltac bitint_length_rewrite :=
    match goal with
    | |- ⊢ᵥ ValBaseBit ?v \: TypBit (N.of_nat (length ?bs))
      => replace (length bs) with (length v); auto
    | |- ⊢ᵥ ValBaseInt ?v \: TypInt (N.of_nat (length ?bs))
      => replace (length bs) with (length v); auto
    end.

  Lemma eval_unary_op_preserves_typ : forall o v v' (t t' : typ),
      unary_type o t t' ->
      Ops.eval_unary_op o v = Some v' ->
      ⊢ᵥ v \: t -> ⊢ᵥ v' \: t'.
  Proof.
    intros o v v' t t' Hut Heval Hvt;
      inversion Hut; subst;
        inversion Hvt; subst;
          unfold Ops.eval_unary_op in Heval;
          try discriminate; try some_inv; auto;
            try match goal with
                | H: context [let (_,_) := P4Arith.BitArith.from_lbool ?bs in _]
                  |- _ => destruct (P4Arith.BitArith.from_lbool bs)
                    as [w' n] eqn:Hbs; some_inv;
                          try inv_numeric; try inv_numeric_width
                end;
            try bitint_length_rewrite; unfold P4Arith.to_lbool;
              try rewrite P4Arith.length_to_lbool'; cbn;
                try (apply f_equal with (f:=fst) in Hbs; cbn in Hbs;
                     apply f_equal with (f:=N.to_nat) in Hbs;
                     rewrite <- Hbs,Znat.Z_N_nat,Zcomplements.Zlength_correct;
                     lia).
  Qed.

  Lemma eval_binary_op_preserves_typ : forall o (t t1 t2 : typ) v v1 v2,
      binary_type o t1 t2 t ->
      Ops.eval_binary_op o v1 v2 = Some v ->
      ⊢ᵥ v1 \: t1 -> ⊢ᵥ v2 \: t2 -> ⊢ᵥ v \: t.
  Proof.
    intros o t t1 t2 v v1 v2 Hbt Hebo Hvt1 Hvt2;
      inversion Hbt; subst;
        inversion Hvt1; subst; inversion Hvt2; subst;
          cbn in *; try discriminate;
            try inv_numeric; try inv_numeric_width;
              try some_inv;
              try rewrite <- Nnat.Nat2N.inj_add;
              try match goal with
                  | |- ⊢ᵥ ValBaseBit (?l ++ ?r) \: TypBit (N.of_nat (length ?l + length ?r))
                    => rewrite <- app_length
                  | |- ⊢ᵥ ValBaseInt (?l ++ ?r) \: TypInt (N.of_nat (length ?l + length ?r))
                    => rewrite <- app_length
                  end;
              repeat if_destruct;
              try match_some_inv; try some_inv; auto;
                try bitint_length_rewrite;
                unfold P4Arith.to_lbool;
                try rewrite length_to_lbool'; cbn;
                  try rewrite Znat.Z_N_nat,Zcomplements.Zlength_correct; try lia.
  Qed.

  Local Hint Constructors binary_type : core.
  Local Hint Constructors numeric_width : core.
  Local Hint Constructors numeric : core.
  Local Hint Constructors Eq_type : core.

  Create HintDb option_monad.
  Local Hint Unfold option_bind : option_monad.
  Local Hint Unfold option_monad_inst : option_monad.
  Local Hint Constructors predop : core.
  Local Hint Constructors member_type : core.

  Lemma Eq_type_get_real_type : forall ge (t r : typ),
      get_real_type ge t = Some r ->
      Eq_type t -> Eq_type r.
  Proof.
    intros ge t r Hget Ht; generalize dependent r;
      generalize dependent ge.
    induction Ht using my_Eq_type_ind;
      intros ge r Hget; cbn in *;
      autounfold with option_monad in *; cbn in *;
      repeat match_some_inv; some_inv; eauto;
      try match goal with
          | IH: Forall
                  ((fun t => forall ge r,
                        get_real_type ge t = Some r -> Eq_type r) ∘ snd)
                  ?xts,
              H: sequence (map (fun '(_,_) => _) ?xts) = Some ?xrs
            |- _ => constructor; rewrite <- Forall_map in *;
                  rewrite Forall_forall in IH; unravel in *;
                  specialize IH with (ge:=ge);
                  rewrite <- Forall_forall in IH;
                  apply f_equal with (f := lift_monad (map snd)) in H;
                  rewrite sequence_map in H;
                  epose proof map_lift_monad_snd_map
                        _ _ _ (get_real_type ge) as Hmsm;
                  unfold ">>|" at 2 in Hmsm;
                  unfold ">>=",option_monad_inst,option_bind in Hmsm;
                  rewrite Hmsm in H; clear Hmsm; cbn in H;
                  rewrite <- Forall2_sequence_iff, <- ForallMap.Forall2_map_l in H;
                  rewrite map_id in *;
                  rewrite <- Forall2_map_both in H;
                  eapply Forall2_Forall_impl_Forall in H; eauto; cbn;
                  rewrite Forall_forall;
                  rewrite Forall_forall in IH; eauto
          end.
    - inv H0; eauto.
    - rewrite Forall_forall in H0.
      specialize H0 with (ge:=ge).
      rewrite <- Forall_forall in H0.
      rewrite <- Forall2_sequence_iff, <- ForallMap.Forall2_map_l in Heqo.
      eauto using Forall2_Forall_impl_Forall; assumption.
  Qed.

  Local Hint Resolve Eq_type_get_real_type : core.

  Lemma binary_type_get_real_type : forall ge o (t t1 t2 r1 r2 : typ),
      binary_type o t1 t2 t ->
      get_real_type ge t1 = Some r1 ->
      get_real_type ge t2 = Some r2 ->
      exists r, get_real_type ge t = Some r /\ binary_type o r1 r2 r.
  Proof.
    intros ge o t t1 t2 r1 r2 Hbt Hr1 Hr2.
    inversion Hbt; subst;
      try inv_numeric; try inv_numeric_width;
        cbn in *; repeat some_inv; eauto;
          try (rewrite Hr1 in Hr2; some_inv; eauto).
  Qed.

  Lemma eval_binary_op_eq_ex : forall (t : typ) v1 v2,
      Eq_type t ->
      ⊢ᵥ v1 \: t ->
      ⊢ᵥ v2 \: t ->
      exists b, Ops.eval_binary_op_eq v1 v2 = Some b.
  Proof.
    intros t v1 v2 Ht;
      generalize dependent v2;
      generalize dependent v1.
    induction Ht using my_Eq_type_ind;
      intros v1 v2 Hv1 Hv2;
      inversion Hv1; subst;
      inversion Hv2; subst; cbn in *;
      repeat if_destruct; eauto;
      repeat rewrite Zcomplements.Zlength_correct in *;
      try rewrite negb_true_iff in *;
      try rewrite negb_false_iff in *;
      try match goal with
          | H: (?x =? ?x)%string = false
            |- _ => rewrite String.eqb_refl in H; discriminate
          | H: (_ =? _)%N = false
            |- _ => rewrite N.eqb_neq in H; lia
          | H: BinInt.Z.eqb _ _ = false
            |- _ => rewrite BinInt.Z.eqb_neq in H; lia
        end;
      repeat match goal with
        | H: Forall
               (fun hdr => exists vs' bits, hdr = ValBaseHeader vs' bits) _
          |- _ => clear H
        end;
      try match goal with
          | U: AList.key_unique ?vs1 && AList.key_unique ?vs2 = false
            |- _ => rewrite andb_false_iff in U; destruct U as [U | U];
                  match goal with
                  | H: AList.all_values
                         _ ?vs (P4String.clear_AList_tags ?xts),
                      Htrue: AList.key_unique ?xts = true, Hfls: AList.key_unique ?vs = false
                    |- _ => apply AListUtil.all_values_keys_eq in H;
                          apply AListUtil.map_fst_key_unique in H;
                          rewrite H,P4String.key_unique_clear_AList_tags,Htrue in Hfls;
                          discriminate
                  end
          end;
      try match goal with
          | IH: Forall
                  ((fun t => forall v1 v2,
                        ⊢ᵥ v1 \: t -> ⊢ᵥ v2 \: t -> exists b,
                            Ops.eval_binary_op_eq v1 v2 = Some b) ∘ snd) ?xts,
              Hxv1s: AList.all_values val_typ ?xv1s (P4String.clear_AList_tags ?xts),
                Hxv2s: AList.all_values val_typ ?xv2s (P4String.clear_AList_tags ?xts),
                  Heqb: AList.key_unique ?xv1s && AList.key_unique ?xv2s = true
            |- _ => unfold AList.all_values, P4String.clear_AList_tags in *;
                  rewrite <- sublist.Forall_map in IH;
                  rewrite Forall2_conj in Hxv1s,Hxv2s;
                  destruct Hxv1s as [Hfstv1s Hsndv1s];
                  destruct Hxv2s as [Hfstv2s Hsndv2s];
                  rewrite Forall2_map_both with (R := eq) (f:=fst) (g:=fst) in Hfstv1s,Hfstv2s;
                  rewrite Forall2_map_both with (f:=snd) (g:=snd) in Hsndv1s,Hsndv2s;
                  rewrite map_fst_map,Forall2_eq in Hfstv1s,Hfstv2s;
                  rewrite map_snd_map,map_id,Forall2_flip in Hsndv1s,Hsndv2s;
                  assert (Hlen_xts_v1s: length (map snd xts) = length (map snd xv1s))
                    by eauto using Forall2_length;
                  assert (Hlen_xts_v2s: length (map snd xts) = length (map snd xv2s))
                    by eauto using Forall2_length;
                  assert (Hlen_v1s_v2s: length (map snd xv1s) = length (map snd xv2s)) by lia;
                  pose proof Forall_specialize_Forall2
                       _ _ _ _ IH _ Hlen_xts_v1s as H'; clear IH Hlen_xts_v1s;
                  pose proof Forall2_specialize_Forall3
                       _ _ _ _ _ _ H' _ Hlen_v1s_v2s as H'';
                  clear H' Hlen_v1s_v2s Hlen_xts_v2s;
                  pose proof Forall3_Forall2_Forall2_impl_Forall2
                       _ _ _ _ _ _ _ _ _ H'' Hsndv1s Hsndv2s as H';
                  clear H'' Hsndv1s Hsndv2s;
                  apply Forall2_ex_factor in H';
                  destruct H' as [bs Hbs];
                  rewrite <- Forall3_map_12 in Hbs;
                  rewrite <- Hfstv2s in Hfstv1s;
                  clear dependent tags_t;
                  apply andb_prop in Heqb as [U1 U2];
                  induction Hbs as [| [x v1] [y v2] b xv1s xv2s bs Hvb Hxvbs IHxvbs];
                  cbn in *; eauto;
                  destruct (AList.get xv1s x) as [v1' |] eqn:Hv1';
                  destruct (AList.get xv2s y) as [v2' |] eqn:Hv2';
                  cbn in *; try discriminate;
                  injection Hfstv1s as Hxy Hfst; subst;
                  rewrite String.eqb_refl,Hvb; cbn; clear Hvb;
                  pose proof IHxvbs Hfst U1 U2 as [b' Hb'];
                  rewrite Hb'; clear IHxvbs Hfst U1 U2 Hb'; eauto
        end.
    - inv H0; eauto.
    - rewrite Forall2_flip in H3,H4.
      eapply Forall_specialize_Forall2 with (vs:=vs) in H0; eauto using Forall2_length.
      assert (Hlenvsvs0 : length vs = length vs0)
        by (apply Forall2_length in H3,H4; lia).
      eapply Forall2_specialize_Forall3 with (ws:=vs0) in H0; try assumption.
      eapply Forall3_Forall2_Forall2_impl_Forall2 in H0; eauto.
      clear dependent tags_t; clear Hlenvsvs0.
      apply Forall2_ex_factor in H0 as [bs Hbs].
      induction Hbs as [| v1 v2 b v1s v2s bs Hvb Hvbs [b' IHvbs]]; cbn; eauto.
      rewrite Hvb,IHvbs; clear Hvb IHvbs; eauto.
    - assert (Hlen : length vs = length vs0) by lia.
      clear Heqb H2 H4 Hv1 Hv2 n0 n Ht H0.
      generalize dependent vs0.
      induction vs as [| v1 vs1 IHvs1]; inv H3;
        intros [| v2 vs2] Hvs2 Hlen; inv Hvs2;
          cbn in *; try discriminate; eauto.
      assert (Hb: exists b, Ops.eval_binary_op_eq v1 v2 = Some b) by eauto.
      destruct Hb as [b Hb]; rewrite Hb; clear Hb.
      assert (Hlen' : length vs1 = length vs2) by lia.
      pose proof IHvs1 H2 _ H4 Hlen' as [b' Hb'];
        rewrite Hb'; clear IHvs1 H2 H4 Hlen' Hb'; eauto.
  Qed.

  Local Hint Resolve eval_binary_op_eq_ex : core.

  Definition binary_op_ctk_cases' (o : OpBin) (v₁ v₂ : @ValueBase bool) : Prop :=
    match o with
    | Div
    | Mod
      => match v₁, v₂ with
        | _, ValBaseBit bits
          => (0%Z < snd (BitArith.from_lbool bits))%Z
        | ValBaseInteger (Zpos _), ValBaseInteger (Zpos _)
          => True
        | _, _ => False
        end
    | Shl
    | Shr
      => match v₂ with
        | ValBaseBit _
        | ValBaseInteger (Z0 | Zpos _) => True
        | _ => False
        end
    | _ => True
    end.

  Lemma eval_binary_op_ex : forall o (t t1 t2 : typ) v1 v2,
      binary_op_ctk_cases' o v1 v2 ->
      binary_type o t1 t2 t ->
      ⊢ᵥ v1 \: t1 ->
      ⊢ᵥ v2 \: t2 ->
      exists v, Ops.eval_binary_op o v1 v2 = Some v.
  Proof.
    intros o t t1 t2 v1 v2 Hctk Hbt Hv1 Hv2; inv Hbt; cbn in *;
      try match goal with
          | HE: Eq_type ?t, Hv1: ⊢ᵥ ?v1 \: ?t, Hv2: ⊢ᵥ ?v2 \: ?t
            |- context [Ops.eval_binary_op_eq ?v1 ?v2]
            => pose proof eval_binary_op_eq_ex _ _ _ H Hv1 Hv2 as [b Hb];
                rewrite Hb; eauto
          end;
      try inv_numeric; try inv_numeric_width;
        inv Hv1; inv Hv2; subst; cbn; eauto;
          try if_destruct; eauto;
            repeat rewrite Zcomplements.Zlength_correct in *;
            try match goal with
                | H: (_ =? _)%N = false |- _ => rewrite N.eqb_neq in H; lia
              end;
      repeat match goal with
        | H: Forall
               (fun hdr => exists vs' bits, hdr = ValBaseHeader vs' bits) _
          |- _ => clear H
        end;
      try match goal with
                | |- context [match ?trm with Some b => Some (ValBaseBool b) | None => None end]
                  => destruct trm as [? |] eqn:?;idtac; eauto
                end; try if_destruct; eauto;
              try match goal with
                  | H: (0 <=? ?z)%Z = false
                    |- _ => destruct z; cbn in *; discriminate || contradiction
                  | H: (_ =? _)%Z = true |- _ => rewrite Z.eqb_eq in H; lia
                  | H: (?z1 <? 0)%Z || (?z2 <=? 0)%Z = true
                    |- _ => destruct z1; destruct z2; cbn in *; contradiction || discriminate
                  end.
  Qed.

  Notation ident := string.

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
      AList.get (P4String.clear_AList_tags ts) x = Some t'  ->
      member_type ts t ->
      ⊢ᵥ v \: t ->
      exists v', get_member v x v'.
  Proof.
    intros x v ts t t' Htsx Hmem Hvt.
    inversion Hmem; subst; inversion Hvt; subst; cbn in *;
      unfold AList.all_values, P4String.clear_AList_tags in *;
      rewrite Forall2_conj in *;
      match goal with
      | H: Forall2 _ ?vs _ /\ Forall2 _ ?vs _
        |- _ => destruct H as [H _];
                enough (exists v', AList.get vs x = Some v')
                by firstorder eauto
      end;
      match goal with
      | H: Forall2 _ ?vs _
        |- _ =>
        rewrite Forall2_map_both, Forall2_eq, map_fst_map in H;
        apply AList.get_some_in_fst in Htsx as (x' & Hxx' & Hx');
        rewrite map_fst_map in Hx';
        rewrite <- H in Hx';
        unfold Equivalence.equiv, P4String.equiv in Hxx'; cbn in *; subst;
        apply AList.in_fst_get_some in Hx' as [v Hv]; eauto
      end.
  Qed.

  Lemma get_member_types : forall x ts (t t' : typ) v v',
      member_type ts t ->
      AList.get (P4String.clear_AList_tags ts) x = Some t' ->
      get_member v x v' ->
      ⊢ᵥ v \: t ->
      ⊢ᵥ v' \: t'.
  Proof.
    intros x ts t t' v v' Htst Htsx Hgm Hvt.
    inversion Htst; subst; inversion Hvt; subst;
      inversion Hgm; subst;
        match goal with
        | H: AList.all_values _ _ _
          |- _ => eapply AListUtil.get_relate_values in H; eauto
        end.
  Qed.

  Local Hint Rewrite Zlength_correct : core.
  Local Hint Rewrite N_of_Z_of_nat : core.
  Local Hint Rewrite pos_N_nat : core.
  Local Hint Rewrite N.eqb_refl : core.
  Local Hint Rewrite to_lbool_bit_mod : core.
  Local Hint Rewrite Nnat.N2Nat.id : core.
  Local Hint Rewrite Nnat.Nat2N.id : core.
  Local Hint Rewrite PeanoNat.Nat.eqb_refl : core.
  Local Hint Rewrite map_length : core.
  Local Hint Constructors cast_type : core.
  Local Hint Resolve AListUtil.map_fst_key_unique : core.
  Local Hint Resolve nth_error_some_length : core.

  Ltac normalize_cast_seq :=
    repeat lazymatch goal with
    | H: sequence (map (fun _ => match _ with _ => _ end) _) = Some _ |- _ =>
        rewrite map_pat_both, <- Forall2_sequence_iff, <- ForallMap.Forall2_map_l,
        Forall2_destr_pair_eq in H;
        destruct H as [?H_fst ?H_snd]
    end.

  Lemma Forall2_get_real_cast_type:
    forall ts1 ts2 : list typ,
      Forall2 cast_type ts1 ts2 ->
      Forall2
        (fun t1 t2 : typ =>
           forall (r1 r2 : typ) (ge1 : genv_typ),
             get_real_type ge1 t1 = Some r1 ->
             forall ge2 : genv_typ, get_real_type ge2 t2 = Some r2 -> cast_type r1 r2) ts1 ts2 ->
      forall (ge1 : genv_typ) (l0 : list typ),
        Forall2 (fun c b : typ => get_real_type ge1 c = Some b) ts1 l0 ->
        forall (ge2 : genv_typ) (l : list typ),
          Forall2 (fun c b : typ => get_real_type ge2 c = Some b) ts2 l ->
          Forall2 cast_type l0 l.
  Proof.
    intros ts1 ts2 H H0 ge1 l0 Heqo0 ge2 l Heqo.
    rewrite Forall2_forall_nth_error in *.
    destruct H as [h_len_ts h_ts].
    destruct H0 as [_ ih_ts].
    destruct Heqo0 as [h_len_ts1_l0 h_ts1_l0].
    destruct Heqo as [h_len_ts2_l h_ts2_l].
    autorewrite with core in *.
    symmetry in h_len_ts1_l0.
    split; try (do 2 etransitivity; eauto; assumption).
    intros n u v hnl0u hnlv.
    assert (hx: exists x, nth_error ts1 n = Some x).
    { apply nth_error_exists.
      rewrite <- h_len_ts1_l0; eauto. }
    destruct hx as [x hx].
    assert (hy: exists y, nth_error ts2 n = Some y).
    { apply nth_error_exists.
      rewrite h_len_ts2_l; eauto. }
    destruct hy as [y hy]. eauto.
  Qed.

  Lemma get_real_cast_type_case1:
    forall (ts : list typ) xts (ge1 ge2: genv_typ) (l0 : list typ) l,
      Forall2 (fun (t : typ) (xt : P4String.t tags_t * typ) => cast_type t (snd xt)) ts xts ->
      Forall2
        (fun (t : typ) (xt : P4String.t tags_t * typ) =>
           forall (r1 r2 : typ) (ge1 : genv_typ),
             get_real_type ge1 t = Some r1 ->
             forall ge2 : genv_typ, get_real_type ge2 (snd xt) =
                                 Some r2 -> cast_type r1 r2) ts xts ->
      sequence (map (get_real_type ge1) ts) = Some l0 ->
      Forall2 (fun v w : typ => get_real_type ge2 v = Some w) (map snd xts) (map snd l) ->
      Forall2 (fun (t : typ) (xt : P4String.t tags_t * typ) => cast_type t (snd xt)) l0 l.
  Proof.
    intros ts xts ge1 ge2 l0 l H0 H1 Heqo0 h_snd.
    rewrite <- Forall2_sequence_iff in Heqo0.
    rewrite ForallMap.Forall2_map_r.
    rewrite ForallMap.Forall2_map_r in H0.
    rewrite ForallMap.Forall2_map_r with
      (R:=fun t1 t2 =>
            forall r1 r2 ge1,
              get_real_type ge1 t1 = Some r1 -> forall ge2,
                get_real_type ge2 t2 = Some r2 ->
                cast_type r1 r2) (f:=snd) in H1.
    rewrite <- ForallMap.Forall2_map_l in Heqo0.
    eapply Forall2_get_real_cast_type; eauto.
  Qed.

  Lemma get_real_cast_type_case2:
    forall xts yts (ge1 ge2: genv_typ) (l0 l : list (P4String.t tags_t * typ)),
      AList.all_values cast_type xts yts ->
      AList.all_values
        (fun t1 t2 : typ =>
           forall (r1 r2 : typ) (ge1 : genv_typ),
             get_real_type ge1 t1 = Some r1 ->
             forall ge2 : genv_typ, get_real_type ge2 t2 = Some r2 -> cast_type r1 r2) xts yts ->
      map fst xts = map fst l0 ->
      Forall2 (fun v w : typ => get_real_type ge1 v = Some w) (map snd xts) (map snd l0) ->
      map fst yts = map fst l ->
      Forall2 (fun v w : typ => get_real_type ge2 v = Some w) (map snd yts) (map snd l) ->
      AList.all_values cast_type l0 l.
  Proof.
    intros xts yts ge1 ge2 l0 l H1 H2 h_fst_xts_l0 h_snd_xts_l0 h_fst_yts_l h_snd_yts_l.
    unfold AList.all_values in *.
    rewrite Forall2_conj in *.
    repeat rewrite Forall2_map_both with (f:=fst) in *.
    repeat rewrite Forall2_map_both with (f:=snd) in *.
    rewrite Forall2_eq in *.
    rewrite Forall2_map_both with
      (R:=fun t1 t2 =>
            forall r1 r2 ge1,
              get_real_type ge1 t1 = Some r1 -> forall ge2,
                get_real_type ge2 t2 = Some r2 ->
                cast_type r1 r2) (f:=snd) in H2.
    destruct H1 as [h_fst_xts_yts h_snd_xts_yts].
    destruct H2 as [_ ih_xts_yts].
    symmetry in h_fst_xts_l0.
    split; try (do 2 etransitivity; eauto; assumption).
    clear h_fst_xts_l0 h_fst_yts_l.
    eapply Forall2_get_real_cast_type; eauto.
  Qed.

  Lemma get_real_cast_type : forall ge1 ge2 (τ₁ τ₂ r₁ r₂ : typ),
      get_real_type ge1 τ₁ = Some r₁ ->
      get_real_type ge2 τ₂ = Some r₂ ->
      cast_type τ₁ τ₂ -> cast_type r₁ r₂.
  Proof.
    intros ge1 ge2 t1 t2 r1 r2 h1 h2 hc.
    generalize dependent ge2;
      generalize dependent ge1;
      generalize dependent r2;
      generalize dependent r1.
    induction hc using my_cast_type_ind;
      intros r1 r2 ge1 hr1 ge2 hr2; cbn in *;
      autounfold with option_monad in *;
      repeat match_some_inv; repeat some_inv; eauto;
      normalize_cast_seq; constructor; eauto;
      lazymatch goal with
      | |- Forall2 (fun _ => _) _ _ => eapply get_real_cast_type_case1; eauto
      | |- AList.all_values cast_type _ _ => eapply get_real_cast_type_case2; eauto
      | _ => idtac
      end.
    rewrite <- Forall2_sequence_iff, <- ForallMap.Forall2_map_l in Heqo, Heqo0.
    eapply Forall2_get_real_cast_type; eauto.
  Qed.

  Lemma length_eq_eval_cast_type:
          forall xts yts : AList.AList (P4String.t tags_t) typ (P4String.equiv (tags_t:=tags_t)),
            AList.all_values cast_type xts yts ->
            forall vs : AList.AList ident ValueBase eq,
              AList.all_values (@val_typ bool tags_t) vs (P4String.clear_AList_tags xts) ->
              Datatypes.length yts = Datatypes.length vs.
  Proof.
    intros xts yts H1 vs H6.
    apply Forall2_length in H6, H1.
    unfold P4String.clear_AList_tags in H6.
    rewrite map_length in *.
    symmetry; etransitivity; eauto.
  Qed.

  Ltac normalize_cast_match :=
    repeat lazymatch goal with
      | H1: AList.key_unique ?x = true, H2: context[AList.key_unique ?x] |- _ =>
          rewrite H1 in H2
      | H: context [true && _] |- _ => cbn [andb] in H
      | H: context [negb true] |- _ => cbn in H
      | H: match (if negb (AList.key_unique ?x) then None else _) with
           | Some _ | None => _ end = Some _ |- _ =>
          destruct (AList.key_unique x); cbn in H; try discriminate
      | H: match (if negb (PeanoNat.Nat.eqb (Datatypes.length ?x)
                             (Datatypes.length ?y)) then None else _) with
           | Some _ => Some _ | None => None end = Some _ |- _ =>
          let hlen := fresh "hlen" in
          assert (Datatypes.length x = Datatypes.length y) as hlen by
              (eapply length_eq_eval_cast_type; eauto);
          rewrite hlen in H; autorewrite with core in H; cbn in H
      | _: match _ with | Some _ | _ => _ end = Some _ |- _ => match_some_inv
      | _: Some _ = Some _ |- _ => some_inv
      | |- ⊢ᵥ ValBaseStruct _ \: TypStruct _ => constructor; auto
      | |- ⊢ᵥ ValBaseHeader _ _ \: TypHeader _ => constructor; auto
      end.

  Lemma eval_cast_types_case1:
    forall (ts : list typ)
      (xts : AList.AList (P4String.t tags_t) typ (P4String.equiv (tags_t:=tags_t))),
      Forall2 (fun (t : typ) (xt : P4String.t tags_t * typ) => cast_type t (snd xt)) ts xts ->
      Forall2
        (fun (t : typ) (xt : P4String.t tags_t * typ) =>
           forall v1 v2 : ValueBase,
             Ops.eval_cast (snd xt) v1 = Some v2 ->
             ⊢ᵥ v1 \: t -> ⊢ᵥ v2 \: snd xt) ts xts ->
      forall (vs : list ValueBase) (f : Ops.Fields ValueBase),
        (fix fields_of_val_tuple
           (l1 : P4String.AList tags_t typ) (l2 : list ValueBase) {struct l1} :
          option (Ops.Fields ValueBase) :=
           match l1 with
           | [] => match l2 with
                  | [] => Some []
                  | _ :: _ => None
                  end
           | (k, t) :: l1' =>
               match l2 with
               | [] => None
               | oldv :: l2' =>
                   match Ops.eval_cast t oldv with
                   | Some newv =>
                       match fields_of_val_tuple l1' l2' with
                       | Some l3 => Some ((P4String.str k, newv) :: l3)
                       | None => None
                       end
                   | None => None
                   end
               end
           end) xts vs = Some f ->
        Forall2 val_typ vs ts -> AList.all_values val_typ f (P4String.clear_AList_tags xts).
  Proof.
    intros ts xts H0 H1 vs f Heqo H4.
    unfold AList.all_values.
    rewrite Forall2_conj.
    rewrite Forall2_map_both with (f:=fst).
    rewrite Forall2_map_both with (f:=snd).
    unfold P4String.clear_AList_tags.
    rewrite map_fst_map,map_snd_map,map_id.
    rewrite Forall2_map_r with (f:=snd) in H0.
    rewrite Forall2_eq.
    generalize dependent f;
      generalize dependent ts;
      generalize dependent vs.
    induction xts as [| [x t] xts ih];
      intros [| v vs] [| T TS] hc ihc hvt [| [y V] VS] H;
      inv hc; inv ihc; inv hvt; cbn in *;
      repeat match_some_inv; some_inv;
      try discriminate; eauto.
    pose proof ih _ _ H5 H7 H9 _ Heqo0 as [hfst hsnd]; clear ih.
    rewrite hfst; split; eauto.
  Qed.

  Lemma eval_cast_types_case2:
    forall xts yts : AList.AList (P4String.t tags_t) typ (P4String.equiv (tags_t:=tags_t)),
      AList.all_values cast_type xts yts ->
      AList.all_values
        (fun t1 t2 : typ =>
           forall v1 v2 : ValueBase, Ops.eval_cast t2 v1 = Some v2 -> ⊢ᵥ v1 \: t1 -> ⊢ᵥ v2 \: t2)
        xts yts ->
      forall (vs : AList.AList ident ValueBase eq) (f : Ops.Fields ValueBase),
        (fix fields_of_val_record
           (l1 : P4String.AList tags_t typ) (l2 : Ops.Fields ValueBase) {struct l1} :
          option (Ops.Fields ValueBase) :=
           match l1 with
           | [] => Some []
           | (k, t) :: l1' =>
               match AList.get l2 (P4String.str k) with
               | Some oldv =>
                   match Ops.eval_cast t oldv with
                   | Some newv =>
                       match
                         fields_of_val_record l1' (AListUtil.remove_first (P4String.str k) l2)
                       with
                       | Some l3 => Some ((P4String.str k, newv) :: l3)
                       | None => None
                       end
                   | None => None
                   end
               | None => None
               end
           end) yts vs = Some f ->
        AList.all_values val_typ vs (P4String.clear_AList_tags xts) ->
        AList.all_values val_typ f (P4String.clear_AList_tags yts).
  Proof.
    intros xts yts H1 H2 vs f Heqo H6.
    unfold AList.all_values in *.
    rewrite Forall2_conj in *.
    destruct H1 as [h_keys_xts_yts hc_xts_yts].
    destruct H2 as [_ ih_xts_yts].
    destruct H6 as [h_keys_vs_xts h_vt_vs_xts].
    unfold P4String.clear_AList_tags in *.
    repeat rewrite Forall2_map_both with (f:=fst) in *.
    repeat rewrite Forall2_map_both with (f:=snd) in *.
    rewrite map_fst_map,map_snd_map,map_id in *.
    rewrite Forall2_eq in *.
    generalize dependent xts;
      generalize dependent f;
      generalize dependent vs.
    induction yts as [| [y t] yts ih];
      intros [| [w v] vs] [| [z V] VS] hVS [| [x T] xts]
        h_fst_xts_yts h_snd_xts_yts ih_xts_yts
        h_fst_vs_xts h_snd_vs_xts;
      inv h_snd_xts_yts; inv ih_xts_yts; inv h_snd_vs_xts;
      cbn in *; repeat match_some_inv; some_inv; auto.
    injection h_fst_xts_yts as hxy h_fst_xts_yts.
    injection h_fst_vs_xts as hzx h_fst_vs_xts; subst.
    unfold StringEqDec in *.
    rewrite AList.get_eq_cons in Heqo by
        auto using Equivalence.equiv_reflexive_obligation_1.
    some_inv.
    destruct (string_dec (P4String.str y) (P4String.str y))
      as [bruh | bruh]; try contradiction; clear bruh.
    pose proof ih _ _ Heqo1 _ h_fst_xts_yts
      H4 H6 h_fst_vs_xts H8 as [hfst hvt].
    rewrite hfst. split; eauto.
  Qed.

  Lemma eval_cast_types : forall (τ₁ τ₂ : typ) v₁ v₂,
      Ops.eval_cast τ₂ v₁ = Some v₂ ->
      cast_type τ₁ τ₂ ->
      ⊢ᵥ v₁ \: τ₁ -> ⊢ᵥ v₂ \: τ₂.
  Proof.
    intros t1 t2 v1 v2 heval hcast;
      generalize dependent v2;
      generalize dependent v1.
    induction hcast using my_cast_type_ind;
      intros v1 v2 heval hv1; inv hv1; cbn in *;
      autorewrite with core in *; try some_inv; auto 2.
    - destruct v as [| [] []];
        cbn in *; try discriminate; inv heval; auto.
    - constructor.
    - pose proof length_to_lbool
        (N.of_nat (List.length v)) (IntArith.lbool_to_val v 1 0) as h.
      autorewrite with core in h; rewrite <- h at 2; auto.
    - pose proof length_to_lbool
        w₂ (BitArith.lbool_to_val v 1 0) as h.
      apply f_equal with (f:=N.of_nat) in h.
      autorewrite with core in h; rewrite <- h at 2; auto.
    - pose proof length_to_lbool w v as h.
      apply f_equal with (f:=N.of_nat) in h.
      autorewrite with core in h; rewrite <- h at 2; auto.
    - inv H1; autorewrite with core in *; some_inv; auto.
    - pose proof length_to_lbool
        (N.of_nat (List.length v))
        (IntArith.mod_bound
           (Pos.of_nat (List.length v))
           (BitArith.lbool_to_val v 1 0)) as h.
      autorewrite with core in h.
      rewrite <- h at 3; auto.
    - pose proof length_to_lbool
        w (IntArith.mod_bound (pos_of_N w) v) as h.
      apply f_equal with (f:=N.of_nat) in h.
      autorewrite with core in h; rewrite <- h at 3; auto.
    - inv H1; autorewrite with core in *; some_inv; auto.
    - inv H1; autorewrite with core in *; some_inv; auto.
    - inv H1; autorewrite with core in *; some_inv; auto.
    - normalize_cast_match. eapply eval_cast_types_case1; eauto.
    - normalize_cast_match. eapply eval_cast_types_case2; eauto.
    - normalize_cast_match. eapply eval_cast_types_case2; eauto.
    - normalize_cast_match. eapply eval_cast_types_case1; eauto.
    - normalize_cast_match. eapply eval_cast_types_case2; eauto.
    - normalize_cast_match. eapply eval_cast_types_case2; eauto.
    - match_some_inv; some_inv.
      constructor.
      generalize dependent ts1;
        generalize dependent l;
        generalize dependent vs.
      induction ts2 as [| T TS ih];
        intros [| v vs] [| V VS] h [| t ts] hc ihc hvt;
        inv hc; inv ihc; inv hvt;
        repeat match_some_inv; some_inv; eauto.
  Qed.

  Lemma eval_cast_ex_case:
    forall (vs : list (ident * ValueBase)) (ts yts: list (P4String.t tags_t * typ))
    (f: AList.StringAList (@ValueBase bool) -> (@ValueBase bool)),
      AList.key_unique ts = true ->
      AList.all_values val_typ vs (P4String.clear_AList_tags ts) ->
      AList.all_values
        (fun (v1 : ValueBase) (t1 : typ) =>
           forall t2 : typ,
             cast_type t1 t2 -> exists v₂ : ValueBase, Ops.eval_cast t2 v1 = Some v₂) vs
        (P4String.clear_AList_tags ts) ->
        AList.key_unique yts = true ->
        AList.all_values cast_type ts yts ->
        exists v₂ : ValueBase,
          match
            (if negb (AList.key_unique yts && AList.key_unique vs)
             then None
             else
               if negb (PeanoNat.Nat.eqb (Datatypes.length yts) (Datatypes.length vs))
               then None
               else
                 (fix fields_of_val_record
                    (l1 : list (P4String.t tags_t * typ)) (l2 : list (ident * ValueBase))
                    {struct l1} : option (list (ident * ValueBase)) :=
                    match l1 with
                    | [] => Some []
                    | (k, t) :: l1' =>
                        match AList.get l2 (P4String.str k) with
                        | Some oldv =>
                            match Ops.eval_cast t oldv with
                            | Some newv =>
                                match
                                  fields_of_val_record l1'
                                    (AListUtil.remove_first (P4String.str k) l2)
                                with
                                | Some l3 => Some ((P4String.str k, newv) :: l3)
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    end) yts vs)
          with
          | Some fields' => Some (f fields')
          | None => None
          end = Some v₂.
  Proof.
    intros vs ts yts f H H0 H1 H4 H5.
    rewrite H4. unfold AList.all_values in H0, H5, H1.
    rewrite Forall2_conj in H0, H1, H5.
    destruct H0 as [hkeys_vsts htyps_vsts].
    destruct H1 as [_ ih_vs_ts].
    destruct H5 as [hkeys_tsyts hcast_tsyts].
    rewrite Forall2_map_both in
      hkeys_vsts,hkeys_tsyts,htyps_vsts,hcast_tsyts.
    rewrite Forall2_eq in hkeys_tsyts,hkeys_vsts.
    assert (hlen_ts_yts:
             List.length (P4String.clear_AList_tags ts)
             = List.length (map snd yts)).
    { apply Forall2_length in hcast_tsyts.
      unfold P4String.clear_AList_tags.
      repeat rewrite map_length in *; assumption. }
    pose proof Forall2_specialize_Forall3
      _ _ _ _ _ _ ih_vs_ts _ hlen_ts_yts as h.
    rewrite <- P4String.key_unique_clear_AList_tags in *.
    rewrite (AListUtil.map_fst_key_unique _ _ hkeys_vsts).
    unfold P4String.StrEqDec,StringEqDec in *.
    rewrite H; cbn.
    assert (hlen_yts_vs: List.length yts = List.length vs).
    { apply Forall2_length in htyps_vsts,hcast_tsyts.
      unfold P4String.clear_AList_tags in *.
      repeat rewrite map_length in *.
      symmetry; etransitivity; eauto. }
    rewrite hlen_yts_vs,PeanoNat.Nat.eqb_refl; cbn.
    unfold P4String.clear_AList_tags in *.
    clear H H4 hlen_yts_vs ih_vs_ts.
    rewrite Forall3_map_12 with
      (R:=fun u v t =>
            cast_type v t ->
            exists v', Ops.eval_cast t u = Some v')
      (f:=snd) (g:=snd)
      in h.
    rewrite map_fst_map,map_snd_map,map_id in *.
    pose proof Forall3_impl_Forall2_23_Forall2_13
      _ _ _ _ _ _ _ _ h hcast_tsyts as H.
    clear hcast_tsyts h htyps_vsts hlen_ts_yts.
    apply Forall2_ex_factor in H as [VS hVS].
    lazymatch goal with
    | |- exists _: (@ValueBase bool),
        match (?f ?yts ?vs) with | Some _ | _ => _ end = Some _ =>
        let lem := fresh "lem" in
        assert (exists vs2, f yts vs = Some vs2) as lem
    end.
    { generalize dependent ts;
        generalize dependent VS;
        generalize dependent vs.
      induction yts as [| [y t] yts ih];
        intros [| [x v] vs] [| V VS] hf3
          [| [z T] TS] h_vs_TS h_TS_yts; inv hf3;
        try discriminate; eauto.
      injection h_vs_TS as hxz h_vs_TS.
      injection h_TS_yts as hzy h_TS_yts; subst.
      rewrite AList.get_eq_cons by intuition.
      rewrite H2.
      rewrite AListUtil.remove_first_cons_equiv by intuition.
      pose proof ih _ _ H6 _ h_vs_TS h_TS_yts as [Vs hVs].
      rewrite hVs; eauto. }
    destruct lem as [Vs lem].
    unfold StringEqDec in *.
    rewrite lem; eauto.
  Qed.

  Lemma eval_cast_ex : forall (τ₁ τ₂ : typ) v₁,
      cast_type τ₁ τ₂ ->
      ⊢ᵥ v₁ \: τ₁ ->
      exists v₂, Ops.eval_cast τ₂ v₁ = Some v₂.
  Proof.
    intros t1 t2 v1 hc h; generalize dependent t2;
      induction h using custom_val_typ_ind;
      intros t2 hc; inv hc; cbn; eauto;
      unfold Ops.Fields,AList.StringAList,
      P4String.AList,AList.AList in *;
      try match goal with
        | H: ⊢ᵥ _ \: TypBit _ |- _ => inv H
        | H: ⊢ᵥ _ \: TypInt _ |- _ => inv H
        end;
      try rewrite Zlength_correct;
      try match goal with
          |- context [Z.to_N (Z.of_nat (List.length ?l))]
          => replace (Z.to_N (Z.of_nat (List.length l)))
            with (N.of_nat (List.length l)) by lia;
            rewrite N.eqb_refl; eauto
        end.
    2, 3: rewrite H2; cbn; clear H2;
    lazymatch goal with
    | |- exists _: (@ValueBase bool),
        match (?f ?xts ?vs) with | Some _ | _ => _ end = Some _ =>
        let lem := fresh "lem" in
        assert (exists vs2, f xts vs = Some vs2) as lem;
        [ generalize dependent ts;
          generalize dependent vs;
          induction xts as [| [x t] xts ih];
          intros [| v vs] [| T TS] hvsTS IH hTSxts;
          inv hvsTS; inv IH; inv hTSxts; cbn in *; eauto;
          apply H3 in H5 as [v2 hv2]; rewrite hv2;
          pose proof ih _ _ H4 H6 H8 as [vs2 hvs2];
          rewrite hvs2; eauto
        | destruct lem as [vs2 lem];
          rewrite lem; eauto ]; assumption
    end.
    - destruct bits as [| [] []];
        cbn in *; try discriminate; eauto; lia.
    - lazymatch goal with
      | |- exists _: (@ValueBase bool),
          match (?f ?ts2 ?vs) with | Some _ | _ => _ end = Some _ =>
          let lem := fresh "lem" in
          assert (exists vs2, f ts2 vs = Some vs2) as lem
      end.
      { generalize dependent ts;
          generalize dependent vs.
        induction ts₂ as [| t ts ihts];
          intros [| v vs] [| T TS] hvsTS ihvsTS htsTS;
          inv hvsTS; inv ihvsTS; inv htsTS; eauto.
        apply H3 in H5 as [v2 hv2]; rewrite hv2.
        pose proof ihts _ _ H4 H6 H8 as [vs2 hvs2].
        rewrite hvs2; eauto. }
      destruct lem as [vs2 lem]; rewrite lem; eauto.
    - apply (eval_cast_ex_case vs ts yts ValBaseStruct); auto.
    - apply (eval_cast_ex_case vs ts yts (fun f => ValBaseHeader f true)); auto.
    - apply (eval_cast_ex_case vs ts yts ValBaseStruct); auto.
    - apply (eval_cast_ex_case vs ts yts (fun f => ValBaseHeader f true)); auto.
  Qed.

  Local Hint Constructors lval_typ : core.
  
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
    rewrite ForallMap.Forall2_map_l
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
      - rewrite <- ForallMap.Forall2_map_l. assumption.
      - apply Forall2_length in Hts'.
        repeat rewrite map_length in *; assumption. }
    rewrite ForallMap.Forall2_map_l
      with (R := fun a b => a = Some b) (f := fun a => get_real_type ge (snd a))
      in Hts'.
    rewrite <- map_map with (f := snd) in Hts'.
    pose proof conj Hfst Hsnd as H.
    rewrite <- Forall2_destr_pair_eq in H.
    rewrite ForallMap.Forall2_map_l
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
    rewrite ForallMap.Forall2_map_l
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
    rewrite <- Forall2_sequence_iff, <- ForallMap.Forall2_map_l, Forall2_forall in Hrs.
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
    rewrite <- Forall2_sequence_iff, <- ForallMap.Forall2_map_l, Forall2_forall in Hxrs.
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
    rewrite <- Forall2_sequence_iff, <- ForallMap.Forall2_map_l, Forall2_forall in Hrs.
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

  Lemma exec_expr_call_False :
    forall (T: @Target _ expr) (dummy: Inhabitant tags_t)
      (ge : @genv _ T) rob p st st' e sv sig,
      exec_expr ge rob p st e sv -> ~ exec_call ge rob p st e st' sig.
  Proof.
    intros T dummy ge rob p st st' e sv sig Hesv Hcall.
    inv Hesv; inv Hcall.
  Qed.

  Definition gamma_var_val_typ_real_norm `{T : Target _ expr}
    (Γ : gamma_var) (st : state) (ge : @genv_typ tags_t) : Prop := forall l (τ : typ) v,
      typ_of_loc_var l Γ = Some τ ->
      loc_to_sval l st = Some v -> ⊢ᵥ v \: τ.

  Lemma gamma_var_domain_impl_real_norm : forall `{T: Target _ expr} gt st Γ,
      gamma_var_domain Γ st ->
      gamma_var_domain
        (FuncAsMap.map_map
           (normᵗ ∘ (try_get_real_type gt)) Γ) st.
  Proof.
    unfold gamma_var_domain.
    intros T gt st G hdom l t hltv.
    specialize hdom with (l:=l).
    destruct l as [l | l]; cbn in *; try discriminate.
    unfold PathMap.get in *.
    rewrite FuncAsMap.get_map_map in hltv.
    unfold option_map in hltv. match_some_inv; some_inv.
    eauto.
  Qed.

  Lemma gamma_real_norm_impl_var_domain : forall `{T: Target _ expr} gt st Γ,
      gamma_var_domain
        (FuncAsMap.map_map
           (normᵗ ∘ (try_get_real_type gt)) Γ) st ->
      gamma_var_domain Γ st.
  Proof.
    unfold gamma_var_domain.
    intros T gt st G hdom l t hltv.
    specialize hdom with (l:=l).
    destruct l as [l | l]; cbn in *; try discriminate.
    unfold PathMap.get in *.
    rewrite FuncAsMap.get_map_map in hdom.
    specialize hdom with ((normᵗ ∘ try_get_real_type gt) t).
    unfold option_map in hdom. rewrite hltv in hdom. eauto.
  Qed.
  
  Lemma gamma_var_val_type_impl_real_norm : forall `{T:Target _ expr} gt st Γ,
      gamma_var_val_typ Γ st gt ->
      gamma_var_val_typ_real_norm
        (FuncAsMap.map_map
           (normᵗ ∘ (try_get_real_type gt)) Γ) st gt.
  Proof.
    unfold gamma_var_val_typ, gamma_var_val_typ_real_norm.
    intros T gt st G h l t v ht hv.
    specialize h with (l:=l).
    destruct l as [l | l]; cbn in *; try discriminate.
    destruct st as [st extns]; cbn in *; clear extns.
    unfold PathMap.get in *.
    rewrite FuncAsMap.get_map_map in ht.
    unfold option_map in ht.
    match_some_inv; some_inv.
    rename p into t.
    pose proof h _ _ eq_refl hv as (r & hr & hvr); clear h.
    unfold try_get_real_type, "∘". rewrite hr. assumption.
  Qed.

  Lemma gamma_real_norm_impl_var_val_type : forall `{T: Target _ expr} gt st Γ Δ,
      delta_genv_prop gt Δ ->
      gamma_var_ok Δ Γ ->
      gamma_var_val_typ_real_norm
        (FuncAsMap.map_map
           (normᵗ ∘ (try_get_real_type gt)) Γ) st gt ->
      gamma_var_val_typ Γ st gt.
  Proof.
    unfold gamma_var_val_typ, gamma_var_val_typ_real_norm.
    intros T gt st G D hD hDG h l t v ht hv.
    specialize h with (l:=l).
    destruct l as [l | l]; cbn in *; try discriminate.
    destruct st as [st extns]; cbn in *; clear extns.
    unfold PathMap.get in *.
    unfold gamma_var_ok in hDG.
    unfold FuncAsMap.forall_elem in hDG.
    rewrite FuncAsMap.get_map_map in h.
    specialize h with ((normᵗ ∘ try_get_real_type gt) t) v.
    unfold option_map in h. rewrite ht in h.
    pose proof h eq_refl hv as hvr; clear h.
    unfold FuncAsMap.get in *.
    pose proof hDG _ _ ht as h.
    pose proof ok_get_real_type_ex _ _ h _ hD as hr.
    destruct hr as [r hr].
    unfold try_get_real_type,"∘" in hvr.
    rewrite hr in hvr. eauto.  
  Qed.
  
  Local Hint Constructors exec_read : core.
  
  Lemma exec_read_preserves_typ :
    forall (T: @Target _ expr) ge st Γ lv sv (τ : typ),
      gamma_var_val_typ_real_norm Γ st ge ->
      exec_read st lv sv ->
      Γ ⊢ₗ lv \: τ ->
      ⊢ᵥ sv \: τ.
  Proof.
    intros T ge st G lv sv t hG hread hlv.
    generalize dependent t.
    induction hread; intros t hlv; inv hlv;
      eauto using get_member_types.
    - pose proof IHhread hG _ H8 as hsv. inv hsv.
      cbn in H. some_inv.
      assert (hlen: (N.to_nat lo <= N.to_nat hi < List.length bitsbl)%nat) by lia.
      pose proof Ops.bitstring_slice_length _ _ _ hlen as h.
      assert (heq: (N.to_nat hi - N.to_nat lo + 1)%nat = N.to_nat (hi - lo + 1)%N) by lia.
      rewrite heq in h.
      apply f_equal with (f:=N.of_nat) in h.
      autorewrite with core in h. rewrite <- h. auto.
    - pose proof IHhread hG _ H5 as hsv. inv hsv.
      unfold Znth. if_destruct; try lia.
      destruct (ZArith_dec.Z_lt_le_dec idx (Z.of_nat (List.length headers))) as [hlen | hlen].
      + assert (Hlen: (Z.to_nat idx < List.length headers)%nat) by lia.
        rewrite <- nth_default_eq.
        pose proof length_nth_error_some _ _ _ Hlen as [v hv].
        unfold nth_default; rewrite hv.
        eapply Forall_nth_error in H7; eauto.
      + rewrite nth_overflow by lia.
        destruct headers; cbn in *; try discriminate.
        some_inv. inv H7; auto.
  Qed.
  
  Lemma exec_read_ex :
    forall (T: @Target _ expr) (ge : @genv_typ tags_t) st Γ lv (t : typ),
      gamma_var_domain Γ st ->
      gamma_var_val_typ_real_norm Γ st ge ->
      Γ ⊢ₗ lv \: t ->
      exists sv, exec_read st lv sv.
  Proof.
    intros T ge st G lv t hGdom hG hlvt.
    induction hlvt.
    - unfold gamma_var_prop in hGdom.
      unfold gamma_var_domain in hGdom.
      pose proof hGdom _ _ H as [sv hsv].
      eauto.
    - destruct IHhlvt as [sv hsv].
      assert (hsv': exists sv', get_member sv x sv').
      { eapply member_get_member_ex; eauto.
        eauto using exec_read_preserves_typ. }
      destruct hsv' as [sv' hsv']. eauto.
    - destruct IHhlvt as [sv hsv].
      pose proof exec_read_preserves_typ _ _ _ _ _ _ _ hG hsv hlvt as hsvt.
      inv hsvt. eexists; econstructor; eauto; cbn.
      + reflexivity.
      + lia.
    - destruct IHhlvt as [sv hsv].
      pose proof exec_read_preserves_typ _ _ _ _ _ _ _ hG hsv hlvt as hsvt.
      inv hsvt.
      assert (hhd: exists dflt, hd_error vs = Some dflt).
      { destruct vs; cbn in *; lia || eauto. }
      destruct hhd as [dflt hdflt].
      exists (@Znth _ dflt z vs). econstructor; eauto.
  Qed.
  
  Lemma havoc_header_val_typ : forall f (τ : typ) v v',
      havoc_header f v = Some v' ->
      ⊢ᵥ v \: τ -> ⊢ᵥ v' \: τ.
  Proof.
    intros f t v v' h hvt.
    inv hvt; cbn in h; inv h.
    constructor; auto.
    unfold AList.all_values in *.
    unfold kv_map, kv_map_func.
    rewrite Forall2_conj in *.
    rewrite Forall2_map_both with (f:=fst) in *.
    rewrite Forall2_map_both with (f:=snd) in *.
    rewrite Forall2_eq in *.
    rewrite map_fst_map,map_snd_map,map_id.
    destruct H0 as [hfst hsnd]; split; auto.
    rewrite Forall2_map1.
    rewrite Forall2_forall_nth_error in *.
    repeat rewrite map_length in *.
    destruct hsnd as [hlen h].
    split; eauto using uninit_sval_of_sval_preserves_typ.
  Qed.

  Lemma havoc_headers_is_header :
    forall f (vs vs' : list (string * @ValueBase (option bool))),
      lift_option_kv (kv_map (havoc_header f) vs) = Some vs' ->
      Forall (fun hdr => exists vs bits, hdr = ValBaseHeader vs bits) (map snd vs) ->
      Forall (fun hdr => exists vs bits, hdr = ValBaseHeader vs bits) (map snd vs').
  Proof.
    unfold lift_option_kv, kv_map.
    intros f vs; induction vs as [| [x v] vs ih];
      intros [| [y v'] vs'] h H; cbn in *;
      unfold option_bind in h; inv H;
      repeat match_some_inv; discriminate || some_inv; auto.
    destruct H2 as (hdr & bits & hhdr); subst. cbn in *.
    some_inv. constructor; eauto.
  Qed.
  
  Lemma havoc_headers_all_values_val_typ : forall f (ts : list (string * typ)) vs vs',
      lift_option_kv (kv_map (havoc_header f) vs) = Some vs' ->
      AList.all_values val_typ vs ts ->
      AList.all_values val_typ vs' ts.
  Proof.
    unfold AList.all_values, lift_option_kv.
    intros f ts; induction ts as [| [x t] ts ih];
      intros [| [y v] vs] [| [z v'] vs'] hvs' hvts; cbn in *;
      try discriminate; inv hvts; repeat match_some_inv; some_inv; auto.
    destruct H2 as [? hvt]; subst.
    eauto using havoc_header_val_typ.
  Qed.

  Lemma havoc_headers_ex : forall f (vs : list (string * ValueBase)),
      Forall (fun v => exists hdr bits, v = ValBaseHeader hdr bits) (map snd vs) ->
      exists vs', lift_option_kv (kv_map (havoc_header f) vs) = Some vs'.
  Proof.
    unfold lift_option_kv,kv_map,kv_map_func.
    intros f vs; induction vs as [| [x v] vs ih];
      intros hall; inv hall; cbn; eauto.
    destruct H1 as (hdr & bits & hhdr); subst. cbn.
    pose proof ih H2 as [vs' IH]; clear ih H2. cbn in *.
    rewrite IH. eauto.
  Qed.
  
  Local Hint Constructors update_member : core.

  Ltac solve_update_member_preserves_typ :=
    match goal with
    | hget: AList.get (P4String.clear_AList_tags ?ts) ?x = Some ?t,
        huniqts: AList.key_unique ?ts = true,
          hall: AList.all_values val_typ ?vs (P4String.clear_AList_tags ?ts),
            hset: AList.set ?vs ?x ?u = Some ?vs'
      |- _ => rewrite <- P4String.key_unique_clear_AList_tags in huniqts;
            assert (huniqvs: AList.key_unique vs = true)
              by (rewrite <- huniqts; apply AListUtil.all_values_key_unique in hall; assumption);
            apply AListUtil.AList_get_some_split in hget as hget';
            destruct hget' as (K & ts1 & ts2 & hxK & hts & hts1); subst; rewrite hts in *;
            apply AListUtil.AList_set_some_split in hset as H';
            destruct H' as (ky & vf & vs1 & vs2 & hxk & hyp_fields & hyp_fields' & hvs1); subst;
            assert (HkK: ky === K) by (setoid_rewrite <- hxk; assumption);
            pose proof AListUtil.key_unique_all_values_split
              _ _ _ _ _ _ _ _ _ HkK huniqvs hall
              as (hkK & htyp & h1 & h2); subst;
            apply Forall2_app; auto; constructor; cbn; auto
    end.

  Lemma update_member_preserves_typ : forall sv₁ sv₂ fv x (τ fτ : typ) τs,
      update_member sv₁ x fv sv₂ ->
      AList.get (P4String.clear_AList_tags τs) x = Some fτ ->
      member_type τs τ ->
      ⊢ᵥ fv \: fτ -> ⊢ᵥ sv₁ \: τ -> ⊢ᵥ sv₂ \: τ.
  Proof.
    intros sv1 sv2 v x t ft ts hum hget hmem hfvt hsv1.
    inv hum; inv hsv1; inv hmem.
    - constructor; auto. solve_update_member_preserves_typ.
    - inv H; constructor; auto;
        solve_update_member_preserves_typ;
        unfold "===" in *; split; auto using uninit_sval_of_sval_preserves_typ.
    - constructor; auto.
      + unfold update_union_member in H.
        match_some_inv.
        pose proof havoc_headers_is_header _ _ _ Heqo H2 as h.
        clear dependent ts0.
        pose proof AListUtil.AList_set_some_split
          _ _ _ _ H as hsplit.
        destruct hsplit as (k & v & vs1 & vs2 & hxk & heq & heq' & hget).
        unfold "===" in *. subst.
        rewrite map_app in *; cbn in *.
        rewrite Forall_app in *.
        destruct h as [h1 h2]; inv h2. split; eauto.
      + unfold update_union_member in H.
        match_some_inv.
        pose proof havoc_headers_all_values_val_typ _ _ _ _ Heqo H3 as h.
        solve_update_member_preserves_typ.
  Qed.

  Local Hint Constructors write_header_field : core.
  
  Lemma update_member_ex : forall sv₁ fv x (τ τ' : typ) τs,
      AList.get (P4String.clear_AList_tags τs) x = Some τ' ->
      member_type τs τ ->
      ⊢ᵥ fv \: τ' -> ⊢ᵥ sv₁ \: τ ->
      exists sv₂, update_member sv₁ x fv sv₂.
  Proof.
    intros sv1 fv x t t' ts hget hmem hfvt hsvt.
    inv hmem; inv hsvt.
    - pose proof AListUtil.all_values_keys_eq _ _ _ _ _ _ _ H2 as hfst.
      pose proof AList.get_some_in_fst _ _ _ hget as hin.
      destruct hin as(kx & hkx & hkxin).
      symmetry in hkx; unfold "==="in hkx; subst.
      rewrite <- hfst in hkxin.
      apply AList.in_fst_get_some in hkxin as [vorig hget_vorig].
      apply AList.get_some_set with (v2:=fv) in hget_vorig as hset.
      eexists; eauto.
    - assert (hsv: exists sv, write_header_field (ValBaseHeader vs b) x fv sv).
      { destruct b as [[] |].
        - pose proof AListUtil.all_values_keys_eq _ _ _ _ _ _ _ H2 as hfst.
          pose proof AList.get_some_in_fst _ _ _ hget as hin.
          destruct hin as(kx & hkx & hkxin).
          symmetry in hkx; unfold "==="in hkx; subst.
          rewrite <- hfst in hkxin.
          apply AList.in_fst_get_some in hkxin as [vorig hget_vorig].
          apply AList.get_some_set with (v2:=fv) in hget_vorig as hset.
          eauto.
        - pose proof AListUtil.all_values_keys_eq _ _ _ _ _ _ _ H2 as hfst.
          pose proof AList.get_some_in_fst _ _ _ hget as hin.
          destruct hin as(kx & hkx & hkxin).
          symmetry in hkx; unfold "==="in hkx; subst.
          rewrite <- hfst in hkxin.
          apply AList.in_fst_get_some in hkxin as [vorig hget_vorig].
          apply AList.get_some_set with
            (v2:=uninit_sval_of_sval None fv) in hget_vorig as hset.
          eauto.
        - pose proof AListUtil.all_values_keys_eq _ _ _ _ _ _ _ H2 as hfst.
          pose proof AList.get_some_in_fst _ _ _ hget as hin.
          destruct hin as(kx & hkx & hkxin).
          symmetry in hkx; unfold "==="in hkx; subst.
          rewrite <- hfst in hkxin.
          apply AList.in_fst_get_some in hkxin as [vorig hget_vorig].
          apply AList.get_some_set with
            (v2:=uninit_sval_of_sval None fv) in hget_vorig as hset.
          eauto. }
      destruct hsv as [sv hsv]; eauto.
    - pose proof AListUtil.get_some_pair_in _ _ _ hget as hin.
      unfold "===" in hin.
      destruct hin as (kx & hkx & hin); subst kx.      
      assert (ht': exists ts', t' = TypHeader ts').
      { rewrite Forall_forall in H1.
        apply in_map with (f:=snd) in hin.
        cbn in hin. unfold P4String.clear_AList_tags in hin.
        rewrite map_snd_map,map_id in hin.
        pose proof AList.get_some_in_fst _ _ _ hget as hinfst.
        destruct hinfst as (k' & hxk' & hxin).
        unfold "===" in hxk'; symmetry in hxk'; subst.
        pose proof AListUtil.all_values_keys_eq _ _ _ _ _ _ _ H3 as hfsteq.
        rewrite <- hfsteq in hxin.
        apply AList.in_fst_get_some in hxin.
        destruct hxin as [v hv].
        pose proof AListUtil.get_relate_values _ _ _ _ _ _ H3 hv hget as hvt.
        apply AListUtil.get_some_pair_in in hv.
        destruct hv as (kx & hkx & hxvin).
        apply in_map with (f:= snd) in hxvin. cbn in *.
        apply H1 in hxvin as (vs' & b & hvs'); subst.
        inv hvt. eauto. }
      destruct ht' as [ts' ht']; subst; inv hfvt.
      assert (hsnd :
               Forall2 val_typ
                 (map snd vs) (map snd (P4String.clear_AList_tags ts))).
      { unfold AList.all_values in H3.
        rewrite Forall2_conj in H3.
        destruct H3 as [hfst hsnd].
        rewrite Forall2_map_both with (f:=snd) in hsnd.
        assumption. }
      assert (hupdate: exists uvs, update_union_member vs x vs0 b = Some uvs).
      { unfold update_union_member.
        pose proof havoc_headers_ex
          (match b with
           | Some true => fun _ : option bool => Some false
           | _ => id
           end) _ H1 as h.
        destruct h as [vs' hvs'].
        rewrite hvs'.
        pose proof havoc_headers_all_values_val_typ
          _ _ _ _ hvs' H3 as h.
        pose proof AListUtil.all_values_keys_eq _ _ _ _ _ _ _ h as hfst.
        pose proof AList.get_some_in_fst _ _ _ hget as hinfst.
        destruct hinfst as (kx & hkx & hkxin).
        symmetry in hkx; unfold "==="in hkx; subst.
        rewrite <- hfst in hkxin.
        apply AList.in_fst_get_some in hkxin as [vorig hget_vorig].
        apply AList.get_some_set
          with (v2:=ValBaseHeader vs0 b)
          in hget_vorig as hset; eauto. }
      destruct hupdate as [uvs huvs]. eauto.
  Qed.

  Lemma update_bitstring_length : forall {A : Type} (bits₁ bits₂ : list A) lo hi,
      (lo <= hi < List.length bits₁)%nat ->
      List.length bits₂ = (hi - lo + 1)%nat ->
      List.length (update_bitstring bits₁ lo hi bits₂) = List.length bits₁.
  Proof.
    intros A bits; induction bits as [| a bits ih];
      intros bts lo hi hbits hbts; cbn in *; auto.
    destruct lo as [| lo]; destruct hi as [| hi]; cbn in *.
    - destruct bts as [| b bts]; cbn in *; try discriminate.
      injection hbts as hbts.
      destruct bts; cbn in *; discriminate || reflexivity.
    - destruct bts as [| b bts]; cbn in *; try discriminate.
      injection hbts as hbts. f_equal.
      rewrite ih by lia. reflexivity.
    - reflexivity.
    - f_equal. rewrite ih by lia. reflexivity.
  Qed.
  
  Local Hint Constructors exec_write : core.
  
  Lemma exec_write_ex :
    forall (T: @Target _ expr) (ge : @genv_typ tags_t) st (Γ : gamma_var) lv v (t : @P4Type tags_t),
      gamma_var_domain Γ st ->
      gamma_var_val_typ_real_norm Γ st ge ->
      Γ ⊢ₗ lv \: t -> ⊢ᵥ v \: t ->
      exists st', exec_write st lv v st'.
  Proof.
    intros T ge st G lv v t hdom hG hlvt hvt.
    generalize dependent v.
    induction hlvt; intros v hvt.
    - exists (update_val_by_loc st l v).
      constructor; reflexivity.
    - assert (hsv: exists sv, exec_read st lv sv) by eauto using exec_read_ex.
      destruct hsv as [sv hsv].
      assert (hsvt: ⊢ᵥ sv \: τ) by eauto using exec_read_preserves_typ.
      pose proof update_member_ex _ _ _ _ _ _ H1 H2 hvt hsvt as hupdate.
      destruct hupdate as [sv' hsv'].
      pose proof update_member_preserves_typ
        _ _ _ _ _ _ _ hsv' H1 H2 hvt hsvt as hsv't.
      pose proof IHhlvt _ hsv't as IH.
      destruct IH as [st' hst'].
      eexists; eauto.
    - inv hvt.
      pose proof exec_read_ex _ _ _ _ _ _ hdom hG hlvt as hread.
      destruct hread as [sv hsv].
      pose proof exec_read_preserves_typ _ _ _ _ _ _ _ hG hsv hlvt as hsvt.
      inv hsvt.
      assert (hlen_nat : (N.to_nat lo <= N.to_nat hi < List.length v)%nat) by lia.
      apply f_equal with (f:= N.to_nat) in H2.
      autorewrite with core in H2.
      replace (N.to_nat (hi - lo + 1)%N)
        with (N.to_nat hi - N.to_nat lo + 1)%nat in H2 by lia.
      pose proof update_bitstring_length _ _ _ _ hlen_nat H2 as hupdate.
      pose proof @typ_bit _ tags_t (update_bitstring v (N.to_nat lo) (N.to_nat hi) v0) as hbit.
      rewrite hupdate in hbit.
      pose proof IHhlvt _ hbit as [st' hst']. eauto.
    - pose proof exec_read_ex _ _ _ _ _ _ hdom hG hlvt as [sv hread].
      pose proof exec_read_preserves_typ _ _ _ _ _ _ _ hG hread hlvt as hsvt.
      inv hsvt.
      assert
        (hstk:
          ⊢ᵥ ValBaseStack (update_stack_header vs z v) n0
            \: TypArray τ (N.of_nat (List.length vs))).
      { unfold update_stack_header.
        pose proof Zlength_upd_Znth _ z vs v as hlen.
        apply f_equal with (f:=Z.to_nat) in hlen.
        do 2 rewrite ZtoNat_Zlength in hlen.
        rewrite <- hlen.
        constructor; lia || eauto using Forall_upd_Znth. }
      apply IHhlvt in hstk as [st' IH]. eauto.
  Qed.

  Lemma exec_write_preservation :
    forall (T: @Target _ expr) (ge : @genv_typ tags_t) st st' (Γ : gamma_var) lv v (t : @P4Type tags_t),
      gamma_var_domain Γ st ->
      gamma_var_val_typ_real_norm Γ st ge ->
      exec_write st lv v st' ->
      Γ ⊢ₗ lv \: t -> ⊢ᵥ v \: t ->
      gamma_var_domain Γ st' /\ gamma_var_val_typ_real_norm Γ st' ge.
  Proof.
    intros T ge st st' G lv sv t hdom hG hwrite.
    generalize dependent t.
    induction hwrite; intros t hlvt hsvt; inv hlvt.
    - split.
      + unfold gamma_var_domain in *.
        intros l t' htyp_of.
        unfold update_val_by_loc,update_memory.
        destruct st as [st extn]; cbn in *.
        destruct loc as [loc | loc]; cbn in *; try discriminate.
        destruct l as [l | l]; cbn in *; try discriminate.
        destruct (list_eq_dec string_dec l loc) as [hlloc | hlloc]; subst.
        * pose proof PathMap.get_set_same loc rhs st as h.
          unfold PathMap.get,FuncAsMap.get in *. rewrite h. eauto.
        * specialize hdom with (LInstance l) t'; cbn in hdom.
          pose proof PathMap.get_set_diff l loc rhs st hlloc as h.
          unfold PathMap.get,FuncAsMap.get in *.
          rewrite h. eauto.
      + unfold gamma_var_val_typ_real_norm in *.
        intros l t' v htyp_of hloc_to_sval.
        unfold update_val_by_loc,update_memory in hloc_to_sval.
        destruct st as [st extn]; cbn in *.
        destruct loc as [loc | loc]; cbn in *; try discriminate.
        destruct l as [l | l]; cbn in *; try discriminate.
        destruct (list_eq_dec string_dec l loc) as [hlloc | hlloc]; subst.
        * rewrite H1 in htyp_of. some_inv.
          pose proof PathMap.get_set_same loc rhs st as h.
          unfold PathMap.get,FuncAsMap.get in *. rewrite h in hloc_to_sval.
          some_inv. assumption.
        * pose proof PathMap.get_set_diff l loc rhs st hlloc as h.
          specialize hG with (LInstance l) t' v as H. cbn in H.
          unfold PathMap.get,FuncAsMap.get in *.
          rewrite h in hloc_to_sval. auto.
    - pose proof IHhwrite hdom hG as ih; clear IHhwrite.
      rename hsvt into hrhst.
      pose proof exec_read_preserves_typ
        _ _ _ _ _ _ _ hG H H8 as hsvt.
      pose proof update_member_preserves_typ
        _ _ _ _ _ _ _ H0 H5 H6 hrhst hsvt as hsv't. eauto.
    - rename hsvt into hbits'.
      pose proof exec_read_preserves_typ
        _ _ _ _ _ _ _ hG H H9 as hsvt.
      specialize IHhwrite with (t:=TypBit w).
      inv hsvt. inv hbits'.
      apply IHhwrite; auto; clear IHhwrite.
      rewrite <- update_bitstring_length with
        (bits₂ := bits') (lo := N.to_nat lo) (hi := N.to_nat hi) by lia.
      constructor.
    - rename hsvt into hbits'.
      pose proof exec_read_preserves_typ
        _ _ _ _ _ _ _ hG H H9 as hsvt.
      specialize IHhwrite with (t:=TypBit w).
      inv hsvt. (* TODO: lval_typ needs to allow Int for slice arguments. *)
    - rename hsvt into hrhst.
      pose proof exec_read_preserves_typ
        _ _ _ _ _ _ _ hG H H5 as hsvt. inv hsvt.
      eapply IHhwrite; eauto.
      unfold update_stack_header.
      pose proof Zlength_upd_Znth _ idx headers rhs as hlen.
      apply f_equal with (f:=Z.to_nat) in hlen.
      do 2 rewrite ZtoNat_Zlength in hlen.
      rewrite <- hlen.
      constructor; lia || eauto using Forall_upd_Znth.
  Qed.
End Lemmas.
