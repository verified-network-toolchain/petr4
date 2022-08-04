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
              try rewrite rev_length,P4Arith.length_to_lbool'; cbn;
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
                  | |- ⊢ᵥ ValBaseBit (?l ++ ?r) \: TypBit (N.of_nat (length ?r + length ?l))
                    => rewrite PeanoNat.Nat.add_comm; rewrite <- app_length
                  | |- ⊢ᵥ ValBaseInt (?l ++ ?r) \: TypInt (N.of_nat (length ?r + length ?l))
                    => rewrite PeanoNat.Nat.add_comm; rewrite <- app_length
                  end;
              repeat if_destruct;
              try match_some_inv; try some_inv; auto;
                try bitint_length_rewrite;
                unfold P4Arith.to_lbool;
                try rewrite rev_length,P4Arith.length_to_lbool'; cbn;
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
      repeat match_some_inv; repeat some_inv; eauto.
    - rewrite map_pat_both in Heqo.
      rewrite <- Forall2_sequence_iff in Heqo.
      rewrite <- ForallMap.Forall2_map_l in Heqo.
      rewrite Forall2_destr_pair_eq in Heqo.
      destruct Heqo as [h_fst h_snd].
      constructor; eauto.
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
      rewrite Forall2_forall_nth_error in *.
      autorewrite with core in *.
      clear H h_fst.
      destruct H0 as [hlen_ts_xts hc_ts_xts].
      destruct H1 as [_ ih_ts_xts].
      destruct Heqo0 as [hlen_ts_l0 hreal_ts_l0].
      destruct h_snd as [hlen_xts_l hreal_xts_l].
      split; try lia.
      intros n t1 t2 hnl0t1 hnlt2.
      assert (hnts: exists t, nth_error ts n = Some t).
      { apply nth_error_exists.
        rewrite hlen_ts_l0; eauto. }
      destruct hnts as [t hntst].
      assert (hnxts: exists T, nth_error (map snd xts) n = Some T).
      { apply nth_error_exists.
        autorewrite with core.
        rewrite hlen_xts_l.
        rewrite <- map_length with (f:=snd); eauto. }
      destruct hnxts as [T hnxtsT]. eauto.
    - rewrite map_pat_both in Heqo,Heqo0.
      rewrite <- Forall2_sequence_iff in Heqo,Heqo0.
      rewrite <- ForallMap.Forall2_map_l in Heqo,Heqo0.
      rewrite Forall2_destr_pair_eq in Heqo,Heqo0.
      destruct Heqo as [h_fst_yts_l h_snd_yts_l].
      destruct Heqo0 as [h_fst_xts_l0 h_snd_xts_l0].
      constructor; eauto.
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
      clear h_fst_xts_l0 h_fst_yts_l h_fst_yts_l H H0.
      rewrite Forall2_forall_nth_error in *.
      destruct h_snd_xts_yts as [h_len_xts_yts h_xts_yts].
      destruct ih_xts_yts as [_ ih_xts_yts].
      destruct h_snd_xts_l0 as [h_len_xts_l0 h_xts_l0].
      destruct h_snd_yts_l as [h_len_yts_l h_yts_l].
      autorewrite with core in *.
      symmetry in h_len_xts_l0.
      split; try (do 2 etransitivity; eauto; assumption).
      intros n u v hnl0u hnlv.
      assert (hx: exists x, nth_error (map snd xts) n = Some x).
      { apply nth_error_exists.
        autorewrite with core.
        rewrite <- h_len_xts_l0.
        rewrite <- map_length with (f:=snd); eauto. }
      destruct hx as [x hx].
      assert (hy: exists y, nth_error (map snd yts) n = Some y).
      { apply nth_error_exists.
        autorewrite with core.
        rewrite h_len_yts_l.
        rewrite <- map_length with (f:=snd); eauto. }
      destruct hy as [y hy]. eauto.
    - (* TODO: factor out to lemma. *) admit.
    - (* TODO: factor out to lemma. *) admit.
    - (* TODO: factor out to lemma. *) admit.
    - (* TODO: factor out to lemma. *) admit.
    - constructor. (* TODO: finish. *)
  Admitted.
      
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
    - rewrite H in heval. cbn in heval.
      match_some_inv; some_inv.
      constructor; auto. clear H.
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
    - rewrite H0 in heval.
      destruct (AList.key_unique vs) eqn:h_unique_vs;
        cbn in *; try discriminate.
      assert (hlen: Datatypes.length yts = Datatypes.length vs).
      { apply Forall2_length in H6, H1.
        unfold P4String.clear_AList_tags in *.
        rewrite map_length in *.
        symmetry; etransitivity; eauto. }
      rewrite hlen in heval.
      autorewrite with core in heval.
      cbn in heval. match_some_inv; some_inv.
      constructor; auto.
      clear hlen h_unique_vs H H0 H4 b.
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
    - (* TODO: factor out lemma. *) admit.
    - (* TODO: factor out lemma. *) admit.
    - (* TODO: factor out lemma. *) admit.
    - (* TODO: factor out lemma. *) admit.
    - match_some_inv; some_inv.
      constructor.
      generalize dependent ts1;
        generalize dependent l;
        generalize dependent vs.
      induction ts2 as [| T TS ih];
        intros [| v vs] [| V VS] h [| t ts] hc ihc hvt;
        inv hc; inv ihc; inv hvt;
        repeat match_some_inv; some_inv; eauto.
  Admitted.
                
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
    - destruct bits as [| [] []];
        cbn in *; try discriminate; eauto; lia.
    - rewrite H2; cbn;
        assert
          (lem: exists vs2,
              (fix fields_of_val_tuple l1 l2 :=
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
                 end) xts vs = Some vs2);
        [ clear H2;
          generalize dependent ts;
          generalize dependent vs;
          induction xts as [| [x t] xts ih];
          intros [| v vs] [| T TS] hvsTS IH hTSxts;
          inv hvsTS; inv IH; inv hTSxts; cbn in *; eauto;
          apply H3 in H5 as [v2 hv2]; rewrite hv2;
          pose proof ih _ _ H4 H6 H8 as [vs2 hvs2];
          rewrite hvs2; eauto
        | destruct lem as [vs2 lem];
          rewrite lem; eauto ]; assumption.
    - (* factor out to helper lemma. *) admit.
    - assert
        (lem: exists vs2,
            (fix values_of_val_tuple l1 l2 :=
               match l1 with
               | [] => match l2 with
                      | [] => Some []
                      | _ :: _ => None
                      end
               | t :: l1' =>
                   match l2 with
                   | [] => None
                   | oldv :: l2' =>
                       match Ops.eval_cast t oldv with
                       | Some newv =>
                           match values_of_val_tuple l1' l2' with
                           | Some l3 => Some (newv :: l3)
                           | None => None
                           end
                       | None => None
                       end
                   end
               end) ts₂ vs = Some vs2).
      { generalize dependent ts;
          generalize dependent vs.
        induction ts₂ as [| t ts ihts];
          intros [| v vs] [| T TS] hvsTS ihvsTS htsTS;
          inv hvsTS; inv ihvsTS; inv htsTS; eauto.
        apply H3 in H5 as [v2 hv2]; rewrite hv2.
        pose proof ihts _ _ H4 H6 H8 as [vs2 hvs2].
        rewrite hvs2; eauto. }
      destruct lem as [vs2 lem]; rewrite lem; eauto.
    - rewrite H4. unfold AList.all_values in H0, H5, H1.
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
      clear H H3 H4 hlen_yts_vs ih_vs_ts.
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
      assert
        (lem: exists Vs,
            (fix fields_of_val_record
               (l1 : list (P4String.t tags_t * typ)) (l2 : list (ident * ValueBase)) {struct l1} :
              option (list (ident * ValueBase)) :=
               match l1 with
               | [] => Some []
               | (k, t) :: l1' =>
                   match AList.get l2 (P4String.str k) with
                   | Some oldv =>
                       match Ops.eval_cast t oldv with
                       | Some newv =>
                           match fields_of_val_record l1'
                                   (AListUtil.remove_first (P4String.str k) l2) with
                           | Some l3 => Some ((P4String.str k, newv) :: l3)
                           | None => None
                           end
                       | None => None
                       end
                   | None => None
                   end
               end) yts vs = Some Vs).
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
    - (* TODO: factor out helper lemma. *) admit.
    - (* TODO: factor out helper lemma. *) admit.
    - (* TODO: factor out helper lemma. *) admit.
  Admitted.
    
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
End Lemmas.
