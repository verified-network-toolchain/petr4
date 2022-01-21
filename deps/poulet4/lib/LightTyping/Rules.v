Require Export Poulet4.LightTyping.Lemmas Poulet4.Ops.

(** * P4light Typing Rules of Inference *)

Section Soundness.
  Context {tags_t : Type}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation block := (@Block tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := string.
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  Open Scope monad_scope.
  
  Local Hint Unfold expr_types : core.
  Local Hint Constructors exec_expr : core.
  Local Hint Constructors val_typ : core.
  Local Hint Constructors exec_val : core.
  Local Hint Constructors P4Type_ok : core.
  Local Hint Constructors is_expr_typ : core.
  Local Hint Resolve ok_get_real_type_ex : core.
  Local Hint Resolve is_expr_typ_normᵗ_impl : core.
  Local Hint Resolve val_typ_is_expr_typ : core.

  Variables (this : path) (Δ : list string).
  
  Section ExprTyping.
    Variable (Γ : @gamma_expr tags_t).

    Ltac solve_ex :=
      match goal with
      | |- exists rt, Some ?t = Some rt /\ _
        => exists t; cbn; eauto
      end.
    
    Ltac soundtac :=
      autounfold with *;
      intros Tgt rob ge st Hdlta Hrob Hg Hok Hise Hgrt;
      split; eauto;
      try (intros v Hrn; inversion Hrn; subst; cbn; try solve_ex).
  
    Lemma bool_sound : forall tag b dir,
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpBool b) TypBool dir ≀ this.
    Proof.
      intros; soundtac.
    Qed.
  
    Lemma arbitrary_int_sound : forall tag i z dir,
        Δ ~ Γ ⊢ₑ
          MkExpression
          tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir ≀ this.
    Proof.
      intros; soundtac.
    Qed.
    
    Lemma unsigned_int_sound : forall tag i z w dir,
        Δ ~ Γ ⊢ₑ
          MkExpression tag
          (ExpInt
             (P4Int.Build_t _ i z (Some (w,false))))
          (TypBit w) dir ≀ this.
    Proof.
      intros tag i z w dir; soundtac; split; auto.
      replace w with (N.of_nat (length (P4Arith.to_loptbool w z))) at 2; auto.
      unfold P4Arith.to_loptbool, P4Arith.to_lbool.
      rewrite map_length, rev_length, P4Arith.length_to_lbool'; cbn; lia.
    Qed.
    
    Lemma signed_int_sound : forall tag i z w dir,
        Δ ~ Γ ⊢ₑ
          MkExpression
          tag
          (ExpInt (P4Int.Build_t _ i z (Some (w,true))))
          (TypInt w) dir ≀ this.
    Proof.
      intros tag i z w dir; soundtac; split; auto.
      replace w with (N.of_nat (length (P4Arith.to_loptbool w z))) at 2; auto.
      unfold P4Arith.to_loptbool, P4Arith.to_lbool.
      rewrite map_length, rev_length, P4Arith.length_to_lbool'; cbn; lia.
    Qed.
    
    Lemma string_sound : forall tag s dir,
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpString s) TypString dir ≀ this.
    Proof.
      intros; soundtac.
    Qed.
    
    Lemma name_sound : forall tag x loc t dir,
        is_directional dir = true ->
        typ_of_loc_var loc Γ = Some t ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpName x loc) t dir ≀ this.
    Proof.
      intros i x l t d Hd Hgt; soundtac.
      - unfold gamma_expr_prop, gamma_var_prop, gamma_var_domain in Hg.
        destruct Hg as [[Hg _] _].
        assert (Hv : exists v, loc_to_sval l st = Some v).
        { destruct (loc_to_sval l st) as [v |] eqn:Hv; eauto.
          rewrite <- Hg, Hgt in Hv; discriminate. }
        destruct Hv; eauto.
      - unfold gamma_expr_prop, gamma_var_prop, gamma_var_val_typ in Hg.
        destruct Hg as [[_ Hg] _]; eauto.
      - rewrite Hd in H7; discriminate.
    Qed.

    Lemma constant_sound : forall tag x loc t dir,
        is_directional dir = false ->
        typ_of_loc_const this loc Γ = Some t ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpName x loc) t dir ≀ this.
    Proof.
      intros i x l t d Hd Hgt; soundtac.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_domain in Hg.
        destruct Hg as (_ & Hg & _).
        assert (Hv : exists v, loc_to_sval_const ge this l = Some v).
        { destruct (loc_to_sval_const ge this l) as [v |] eqn:Hv; eauto.
          rewrite <- Hg, Hgt in Hv; discriminate. }
        destruct Hv; eauto.
      - rewrite Hd in H7; discriminate.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_val_typ in Hg.
        destruct Hg as (_ & _ & Hg); eauto.
    Qed.
    
    Lemma array_access_sound : forall tag arry idx ts dir n,
        0 < N.to_nat n ->
        typ_of_expr arry = TypArray (TypHeader ts) n ->
        typ_of_expr idx  = TypBit n ->
        Δ ~ Γ ⊢ₑ arry ≀ this ->
        Δ ~ Γ ⊢ₑ idx ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpArrayAccess arry idx) (TypHeader ts) dir ≀ this.
    Proof.
      intros i e1 e2 ts d n Hn Ht1 Ht2 He1 He2;
        autounfold with * in *.
      intros Tgt rob ge st Hdelta Hrob Hg Hok Hise Hgrt; simpl in *.
      rewrite Ht1, Ht2 in *.
      pose proof He1 Tgt rob ge st Hdelta Hrob Hg as [[v1 Hev1] He1']; clear He1; auto.
      pose proof He2 Tgt rob ge st Hdelta Hrob Hg as [[v2 Hev2] He2']; clear He2; auto.
      split.
      - assert (Hv2': exists v2', sval_to_val rob v2 v2')
          by eauto using exec_val_exists.
        pose proof He1' v1 Hev1 as (r1 & Hr1 & Hv1).
        pose proof He2' v2 Hev2 as (r2 & Hr2 & Hv2).
        clear He1' He2'. cbn in *; inversion Hr2; subst; clear Hr2; cbn in *.
        unfold option_bind, option_ret in *.
        destruct (sequence (map (fun '(x, t) => get_real_type ge t >>| pair x) ts))
          as [rs |] eqn:Hrs;
          unfold ">>|",">>=" in *;
          unfold option_monad_inst, option_monad in *;
          unfold mret, mbind, option_bind, option_ret in *;
          unfold option_monad_inst, option_monad in *;
          rewrite Hrs in Hr1; try discriminate.
        inversion Hr1; subst; clear Hr1; cbn in *.
        assert (Hhrs: get_real_type ge (TypHeader ts) = Some (TypHeader rs)).
        { cbn in *.
          unfold ">>|",">>=" in *;
          unfold option_monad_inst, option_monad in *;
          unfold mret, mbind, option_bind, option_ret in *;
          unfold option_monad_inst, option_monad in *;
          rewrite Hrs; reflexivity. }
        destruct Hv2' as [v2' Hv2'].
        inversion Hv1; inversion Hv2; inversion Hv2';
          subst; try discriminate.
        rename v into bs; inversion H6; subst; clear H6.
        assert
          (Hz: exists z, array_access_idx_to_z (ValBaseBit lb') = Some z)
          by (simpl; eauto); destruct Hz as [z Hz].
        epose proof delta_genv_prop_ok_typ_nil as Hnil;
          unfold delta_genv_prop_ok_typ_nil_def in Hnil.
        assert (Hrtok : [] ⊢ok (TypHeader rs)) by eauto.
        assert (Huninit : exists v, uninit_sval_of_typ None (TypHeader rs) = Some v)
          by eauto using is_expr_typ_uninit_sval_of_typ.
        destruct Huninit as [v Hv]; eauto.
      - clear v1 v2 Hev1 Hev2.
        intros v Hev; inversion Hev; subst.
        apply He1' in H10 as (r1 & Hr1 & Hv1); clear He1'.
        apply He2' in H4 as (r2 & Hr2 & Hv2); clear He2'.
        rewrite H11.
        unfold get_real_type in Hr1, H11;
          fold (@get_real_type tags_t) in Hr1, H11.
        rewrite H11 in Hr1.
        cbv in Hr1; inversion Hr1; subst; clear Hr1 H11.
        cbn in *; inversion Hr2; subst; clear Hr2.
        inversion Hv1; subst.
        eexists; split; eauto; cbn in *.
        unfold Znth.
        destruct (ZArith_dec.Z_lt_dec idxz Z0) as [Hidxz | Hidxz].
        + pose proof uninit_sval_of_typ_val_typ rtyp as H.
          eapply H; eauto.
          apply val_typ_is_expr_typ in Hv1 as Hv1'.
          inversion Hv1'; subst; auto.
        + rewrite <- nth_default_eq.
          unfold nth_default.
          destruct (nth_error headers (BinInt.Z.to_nat idxz)) as [v |] eqn:Hv.
          * inversion Hv1; subst.
            rewrite Forall_forall in H6.
            eauto using nth_error_In.
          * pose proof uninit_sval_of_typ_val_typ rtyp as H.
            eapply H; eauto.
            apply val_typ_is_expr_typ in Hv1 as Hv1'.
            inversion Hv1'; subst; auto.
    Qed.

    Lemma bigstring_access_sound : forall tag bits lo hi dir w,
        (lo <= hi < w)%N ->
        typ_of_expr bits = TypBit w ->
        Δ ~ Γ ⊢ₑ bits ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpBitStringAccess bits lo hi)
          (TypBit (hi - lo + 1)%N) dir ≀ this.
    Proof.
      intros i e lo hi d w Hlwh Ht He.
      autounfold with * in *.
      intros T rob ge st Hdlta Hrob Hg Hok Hise Hgrt.
      rewrite Ht in *; cbn in *.
      pose proof He T rob ge st Hdlta Hrob Hg as [[v Hev] He']; clear He; auto.
      split.
      - apply He' in Hev as Hv';
          destruct Hv' as (rt & Hrt & Hv);
          inversion Hv; inversion Hrt; clear Hrt; subst; cbn in *; try discriminate.
        rename v0 into bits. inversion H1; clear H1; subst.
        exists (ValBaseBit (bitstring_slice bits (N.to_nat lo) (N.to_nat hi))).
        eapply exec_expr_bitstring_access with (wn := length bits); eauto; lia.
      - clear v Hev; intros v Hrn; inversion Hrn; subst; simpl.
        solve_ex; split; auto.
        rename H8 into He; rename H9 into Hsval; rename H12 into Hlhw.
        replace (hi - lo + 1)%N
          with (N.of_nat (length (bitstring_slice bitsbl (N.to_nat lo) (N.to_nat hi)))); auto.
        apply He' in He as (r & Hr & Hv); inversion Hr; subst; clear Hr; cbn in *.
        inversion Hv; subst; cbn in *.
        inversion Hsval; subst; clear Hsval.
        apply bitstring_slice_length in Hlhw; lia.
    Qed.
  
    Lemma list_sound : forall tag es dir,
        Forall (fun e => Δ ~ Γ ⊢ₑ e ≀ this) es ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpList es)
          (TypTuple (map typ_of_expr es)) dir ≀ this.
    Proof.
      intros i es d Hes. autounfold with * in *.
      intros Tgt rob ge st Hrob Hg Hok.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (T := Tgt)
          (read_one_bit:=rob) (ge:=ge) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Hg as Hes;
        simpl in Hes; clear Hes'.
      simpl in *; inversion Hok;
        rename H0 into Hτs; rename H into Hτs_eq.
      rewrite <- Forall_forall in Hes.
      (*rewrite Forall_map in Hτs.
      unfold Basics.compose in *.
      pose proof Forall_impl_Forall _ _ _ _ Hes Hτs as Hq.
      apply Forall_and_inv in Hq as [Hrnes Htyps]; split.
      - clear Htyps.
        rewrite Forall_exists_factor in Hrnes.
        destruct Hrnes as [vs Hvs]; eauto.
      - clear Hrnes; intros v Hrn; simpl.
        inversion Hrn; subst; clear Hrn.
        rename H6 into Hesvs.
        rewrite Forall_forall in Htyps.
        apply forall_Forall2 with (bs := vs) in Htyps;
          eauto using Forall2_length.
        apply Forall2_impl with
            (R := run_expr ge rob this st)
            (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Htyps; auto.
        rewrite Forall2_flip, Forall2_map_r in Htyps; auto.
    Qed.*)
    Admitted.

    Lemma record_sound : forall tag es dir,
        Forall (fun e => Δ ~ Γ ⊢ₑ e ≀ this) (map snd es) ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpRecord es)
          (TypRecord (map (fun '(x,e) => (x,typ_of_expr e)) es)) dir ≀ this.
    Proof.
      intros i es d Hes.
      autounfold with * in *.
      intros Tgt rob ge st Hrob Hg Hok.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (T := Tgt)
          (read_one_bit:=rob) (ge:=ge) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Hg as Hes;
        simpl in Hes; clear Hes'.
      simpl in *; inversion Hok;
        rename H0 into Hτs; rename H into Hτs_eq.
      rewrite <- Forall_forall in Hes.
      pose proof Forall_map
           (P4Type_ok Δ) snd
           (map (fun '(x, e) => (x, typ_of_expr e)) es)
        as Hfm.
      unfold Basics.compose in Hfm.
      (*rewrite <- Hfm in Hτs; clear Hfm.
      rewrite map_snd_map in Hτs.
      rewrite Forall_map in Hτs.
      unfold Basics.compose in *.
      pose proof Forall_impl_Forall _ _ _ _ Hes Hτs as Hq.
      apply Forall_and_inv in Hq as [Hrns Htyps]; split.
      - clear Htyps.
        rewrite Forall_exists_factor in Hrns.
        destruct Hrns as [vs Hvs].
        rewrite AList.Forall2_all_values
          with (ks := map fst es) in Hvs.
        + rewrite combine_map_fst_snd in Hvs; eauto. admit.
        + repeat rewrite map_length; reflexivity.
        + rewrite map_length, <- map_length with (f := snd).
          eauto using Forall2_length.
      - clear Hrns; intros v Hrns.
        inversion Hrns; subst.
        rename H6 into Heskvs.
        rewrite <- combine_map_fst_snd with (l := es)   in Heskvs.
        rewrite <- combine_map_fst_snd with (l := kvs') in Heskvs.
        apply AList.all_values_keys_eq in Heskvs as Hmf.
        repeat rewrite combine_map_fst_snd in Hmf.
        rewrite <- Hmf in Heskvs.*)
    (*rewrite <- AList.Forall2_all_values in Heskvs.
      + constructor; unfold AList.all_values;
        rewrite Forall2_conj; split.
        * rewrite Forall2_map_both, Forall2_eq,
          map_fst_map, map_id; auto.
        * rewrite Forall2_map_both.
          rewrite map_snd_map.
          assert (Hl : length es = length kvs').
          { rewrite <- map_length with (f := fst) (l := es).
            rewrite <- map_length with (f := fst) (l := kvs'), Hmf.
            reflexivity. }
          rewrite <- map_length with (f := snd) (l := es) in Hl.
          rewrite <- map_length with (f := snd) (l := kvs') in Hl.
          pose proof forall_Forall2 _ _ _ _ Htyps (map snd kvs') Hl as Hff2.
          apply Forall2_impl with
              (R := run_expr ge rob this st)
              (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Hff2; auto.
          rewrite Forall2_flip,Forall2_map_r in Hff2; assumption.
      + repeat rewrite map_length; reflexivity.
      + rewrite Hmf; repeat rewrite map_length; reflexivity.
  Qed.*)
    Admitted.

    Local Hint Unfold read_detbit : core.
    Local Hint Unfold sval_to_val : core.
    Local Hint Unfold val_to_sval : core.
    
    Lemma val_to_sval_ex : forall v,
        val_to_sval v (ValueBaseMap Some v).
    Proof.
      autounfold with *; intro v.
      induction v using (custom_ValueBase_ind bool); simpl; eauto.
      - constructor.
        rewrite <- Forall2_map_r, Forall2_Forall, Forall_forall.
        reflexivity.
      - constructor.
        rewrite <- Forall2_map_r, Forall2_Forall, Forall_forall.
        reflexivity.
      - constructor.
        rewrite <- Forall2_map_r, Forall2_Forall, Forall_forall.
        reflexivity.
      - constructor.
        rewrite <- Forall2_map_r, Forall2_Forall.
        assumption.
      - constructor. unfold AList.all_values.
        rewrite <- Forall2_map_r, Forall2_Forall.
        rewrite Forall_snd in H.
        apply Forall_and; rewrite Forall_forall in *;
          intros [? ?]; firstorder.
      - constructor; auto. unfold AList.all_values.
        rewrite <- Forall2_map_r, Forall2_Forall.
        rewrite Forall_snd in H.
        apply Forall_and; rewrite Forall_forall in *;
          intros [? ?]; firstorder.
      - constructor. unfold AList.all_values.
        rewrite <- Forall2_map_r, Forall2_Forall.
        rewrite Forall_snd in H.
        apply Forall_and; rewrite Forall_forall in *;
          intros [? ?]; firstorder.
      - constructor.
        rewrite <- Forall2_map_r, Forall2_Forall.
        assumption.
    Qed.

    Local Hint Resolve val_to_sval_ex : core.
    
    Lemma eval_unary_op_preserves_typ : forall o v v' (t t' : typ),
        unary_type o t t' ->
        Ops.eval_unary_op o v = Some v' ->
        ⊢ᵥ v \: t -> ⊢ᵥ v' \: t'.
    Proof.
      intros o v v' t t' Hut Heval Hvt;
        inversion Hut; subst;
          inversion Hvt; subst;
            try (inversion Heval; subst; auto; assumption).
      - unfold Ops.eval_unary_op in Heval.
        destruct (P4Arith.BitArith.from_lbool v0)
          as [w' n'] eqn:Heqfromlbool.
        injection Heval as Hv'. rewrite <- Hv'.
        inversion H; subst; clear H.
    (** TODO: need helper lemma about
        [P4Arith.to_lbool] and [P4Arith.BitArith.bit_not]. *)
    Admitted.
  
    Lemma unary_op_sound : forall tag o e t dir,
        unary_type o (typ_of_expr e) t ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpUnaryOp o e) t dir ≀ this.
    Proof.
      intros i o e t d Hut He.
      autounfold with * in *; intros Tgt rob ge st Hrob Hg Hok.
      specialize He with Tgt rob ge st.
      simpl in *.
      apply unary_type_eq in Hut as Hut_eq.
      rewrite Hut_eq in He.
      (*pose proof He Hrob Hg Hok as [[v Hev] Hvt]; clear He; split.
      - apply Hvt in Hev as Hv; clear Hvt.
        assert (exists v', sval_to_val rob v v')
          by eauto using exec_val_exists.
        destruct H as [v' Hv'].
        assert (exists v''', Ops.eval_unary_op o v' = Some v''').
        (* Maybe try to factor this out?
           Lemma exists_eval_unary_op : forall o v,
           exists v', Ops.eval_unary_op o v = Some v'. *)
        { destruct (Ops.eval_unary_op o v') as [v'' |] eqn:Heqop; eauto.
          inversion Hut; subst; try inv_numeric; try inv_numeric_width;
            match goal with
            | H: _ = typ_of_expr ?e,
                 Hv: val_typ _ ?v (typ_of_expr ?e),
                     Hv': sval_to_val _ ?v _
              |- _ => rewrite <- H in *; inversion Hv; inversion Hv'; subst
            end; simpl in *; try discriminate. }
        firstorder eauto. admit.
      - clear v Hev; intros v Hev.
        inversion Hev; subst; simpl in *.
        pose proof Hvt _ H7 as Hargsv.
        pose proof
             (@exec_val_preserves_typ
                tags_t _ _ _ _ _ H8 (ge_senum ge)) as Hevpt.
        assert (Hgsb : exists gsb,
                   FuncAsMap.related
                     (AList.all_values (exec_val rob))
                     (ge_senum ge) gsb).
        { admit. }
        destruct Hgsb as [gsb Hgsb].
        pose proof Hevpt _ Hgsb _ Hargsv as Hargv.
        assert (Hv0: val_typ gsb v0 (typ_of_expr e))
          by eauto using eval_unary_op_preserves_typ.
        assert (Hgsb' :
                  FuncAsMap.related
                    (AList.all_values val_to_sval)
                    gsb (ge_senum ge)).
        { (* TODO:
             Need assumption
             [read_one_bit_inverse rob read_detbit]. *)
          admit. }
        eauto using exec_val_preserves_typ.*)
    Admitted.

    Lemma binary_op_sound : forall tag o t e1 e2 dir,
        binary_type o (typ_of_expr e1) (typ_of_expr e2) t ->
        Δ ~ Γ ⊢ₑ e1 ≀ this ->
        Δ ~ Γ ⊢ₑ e2 ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpBinaryOp o (e1,e2)) t dir ≀ this.
    Proof.
    Admitted.
  
    Lemma cast_sound : forall tag e t dir,
        cast_type (typ_of_expr e) t ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpCast t e) t dir ≀ this.
    Proof.
    Admitted.

    Lemma enum_member_sound : forall tag tname member ename members dir,
        (* TODO: need [ge] of [genv].
           name_to_type ge tname = Some (TypEnum ename None members) ->*)
        List.In member members ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpTypeMember tname member)
          (TypEnum ename None members) dir ≀ this.
    Proof.
      intros tag X M E mems dir Hmem.
      intros Tgt rob ge st Hdlta Hrob Hg Hok Hise Hgrt; cbn in *; split.
      - exists (ValBaseEnumField (P4String.str E) (P4String.str M)).
        econstructor; eauto.
        (* Need [X] to be bound in [Δ], [In X Δ]. *)
        inversion Hok; subst. inversion H0; clear H0; subst.
        unfold delta_genv_prop in Hdlta.
        rewrite Forall_forall in Hdlta.
        (* It is not enough to know
           whether or not [X] is bound in [Δ], [In X Δ].
           applying [Hdlta] only gives that
           [exists r', get X ge = Some r' /\ [] ⊢ok r'].
           [r'] Must be further constrained somehow...
           It would be helpful if [X] was just substitued with
           [TypEnum E None mems] by this point in the evaluation.
           If [ExpTypeMember : P4Type -> P4String -> ExpressionPreT],
           then either I could require it in this lemma's statement,
           or in the definition of typing in [Typing.v]
           I could perform a substitution using [genv_type],
           which I've been implicitly doing already. *)
        unfold gamma_expr_prop in Hg.
        admit. (* Need some assumption for this? *)
        admit.
      - intros v Hrn.
        (*Search (exec_expr _ _ _ _ (MkExpression _ (ExpTypeMember _ _) _ _)). *)
        inversion Hrn; subst; solve_ex; split; auto.
        + admit.
        + admit. (* this case should not exist...*)
    Admitted.

    Lemma senum_member_sound : forall tag tname member ename t members dir,
        (*name_to_type ge tname = Some (TypEnum ename (Some etyp) members) ->
          IdentMap.get ename (ge_senum ge) = Some fields ->*)
        List.In member members ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpTypeMember tname member)
          (TypEnum ename (Some t) members) dir ≀ this.
    Proof.
    Admitted.

    Lemma error_member_sound : forall tag err dir,
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpErrorMember err) TypError dir ≀ this.
    Proof.
      soundtac.
    Qed.

    Local Hint Resolve member_get_member_ex : core.
    Local Hint Resolve get_member_types : core.
    
    Lemma other_member_sound : forall tag e x ts t dir,
        member_type ts (typ_of_expr e) ->
        AList.get ts x = Some t ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpExpressionMember e x) t dir ≀ this.
    Proof.
      (* TODO: maybe need an [⊢ok] for all syntax forms of p4light...yikes!
         For now I may be able to get away with just these assumptions. *)
      intros i e x ts t dir Hmem Hts He.
      assert (Htoeok : Δ ⊢ok typ_of_expr e) by admit.
      assert (Htoeise : is_expr_typ (typ_of_expr e)) by admit.
      intros Tgt rob ge st Hdlta Hrob Hg Hok Hise Hgrt.
      pose proof He Tgt rob ge st Hdlta Hrob Hg Htoeok Htoeise Hgrt as [[v Hev] Hv].
      cbn in *; split.
      - assert (Hget: exists v', get_member v (P4String.str x) v').
        { apply Hv in Hev as (r & Hr & Hvr).
          pose proof get_real_member_type _ _ _ _ Hr Hmem as [rs Hmemrs].
          (*assert (Hwah :
                    sequence (map (fun '(x,t) => get_real_type ge t >>| pair x) ts)
                    = Some rs) by admit.
          rewrite <- Forall2_sequence_iff in Hwah.
          unfold ">>|",">>=",
          option_monad_inst,option_monad,
          option_bind,option_ret,mret
            in Hwah.*)
          apply member_type_normᵗ in Hmemrs.
          assert (Hlem3' : exists r',
                     AList.get (map (fun '(x, t) => (x, normᵗ t)) rs) x = Some r').
          { clear Hv Hdlta Hg Hgrt Hok Hrob st Hise v Hvr Htoeise Htoeok
                  i Hmem He dir rob this Δ Γ.
            remember (typ_of_expr e) as te eqn:Heqte; clear Heqte.
            exists (normᵗ r). admit. }
          destruct Hlem3' as [r' Hr']; eauto. }
        destruct Hget as [v' Hv'].
        exists v'; eapply exec_expr_other_member; eauto.
      - clear v Hev; intros v Hev. inversion Hev; subst.
        apply Hv in H7 as (r & Hr & Hvr).
        pose proof ok_get_real_type_ex _ _ Hok _ Hdlta as [r' Hr'].
        exists r'; split; auto.
        pose proof get_real_member_type _ _ _ _ Hr Hmem as [rs Hmemrs].
        apply member_type_normᵗ in Hmemrs.
        assert (Hlem3' :
                  AList.get (map (fun '(x, t) => (x, normᵗ t)) rs) x = Some (normᵗ r')) by admit.
        eauto.
    Admitted.

    Lemma array_size_sound : forall tag e x dir t w,
        (* P4Arith.BitArith.bound 32 w -> *)
        (w < 2 ^ 32)%N ->
        typ_of_expr e = TypArray t w ->
        P4String.str x = "size"%string ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpExpressionMember e x) (TypBit 32) dir ≀ this.
    Proof.
    Admitted.

    Lemma array_last_index_sound : forall tag e x dir t w,
        typ_of_expr e = TypArray t w ->
        P4String.str x = "lastIndex"%string ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression
          tag (ExpExpressionMember e x) t dir ≀ this.
    Proof.
    Admitted.

    Lemma ternary_sound : forall tag e₁ e₂ e₃ t dir,
        typ_of_expr e₁ = TypBool ->
        typ_of_expr e₂ = typ_of_expr e₃ ->
        typ_of_expr e₂ = t ->
        Δ ~ Γ ⊢ₑ e₁ ≀ this ->
        Δ ~ Γ ⊢ₑ e₂ ≀ this ->
        Δ ~ Γ ⊢ₑ e₃ ≀ this ->
        Δ ~ Γ ⊢ₑ MkExpression tag (ExpTernary e₁ e₂ e₃) t dir ≀ this.
    Proof.
    Admitted.
  End ExprTyping.

  Local Hint Constructors exec_stmt : core.
  Local Hint Constructors exec_block : core.
  
  Section StmtTyping.
    Variable (Γ : @gamma_stmt tags_t).
    
    Lemma assign_sound : forall tag e₁ e₂,
        typ_of_expr e₁ = typ_of_expr e₂ ->
        lexpr_ok e₁ ->
        Δ ~ Γ ⊢ₑ e₁ ≀ this ->
        Δ ~ Γ ⊢ₑ e₂ ≀ this \/ Δ ~ Γ ⊢ᵪ e₂ ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement
          tag (StatAssignment e₁ e₂) StmUnit ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma cond_sound : forall tag e s₁ s₂ Γ₁,
        typ_of_expr e = TypBool ->
        Δ ~ Γ ⊢ₑ e ≀ this ->
        Δ ~ Γ ⊢ₛ s₁ ⊣ Γ₁ ≀ this ->
        predopt (fun s₂ => exists Γ₂, Δ ~ Γ ⊢ₛ s₂ ⊣ Γ₂ ≀ this) s₂ ->
        Δ ~ Γ ⊢ₛ MkStatement
          tag (StatConditional e s₁ s₂)
          (match s₂ with
           | None    => typ_of_stmt s₁
           | Some s₂ => lub_StmType (typ_of_stmt s₁) (typ_of_stmt s₂)
           end) ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma exit_sound : forall tag,
        Δ ~ Γ ⊢ₛ MkStatement tag StatExit StmVoid ⊣ Γ ≀ this.
    Proof.
      unfold stmt_types; intros; split; eauto.
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.

    Lemma return_sound : forall tag e,
        predopt (fun e => Δ ~ Γ ⊢ₑ e ≀ this) e ->
        Δ ~ Γ ⊢ₛ MkStatement tag (StatReturn e) StmVoid ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma empty_sound : forall tag,
        Δ ~ Γ ⊢ₛ MkStatement tag StatEmpty StmUnit ⊣ Γ ≀ this.
    Proof.
      unfold stmt_types; intros; split; eauto.
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.
    
    Lemma block_sound : forall Γ' tag blk t,
        Block_StmTypes blk t ->
        Δ ~ Γ ⊢ᵦ blk ⊣ Γ' ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement tag (StatBlock blk) t ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma method_call_sound : forall `{dummy : Inhabitant tags_t} tag e τs es,
        Δ ~ Γ ⊢ᵪ MkExpression dummy_tags
          (ExpFunctionCall e τs es)
          TypVoid Directionless ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement tag
          (StatMethodCall e τs es) StmUnit ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma direct_application_sound : forall `{dummy : Inhabitant tags_t} tag τ es,
        Δ ~ Γ ⊢ₑ MkExpression dummy_tags
          (ExpFunctionCall
             (direct_application_expression τ)
             nil (map Some es)) TypVoid Directionless ≀ this ->
        Δ ~ Γ ⊢ₛ MkStatement tag
          (StatDirectApplication τ es) StmUnit ⊣ Γ ≀ this.
    Proof.
    Admitted.

    Lemma stat_variable_sound : forall tag τ x e l,
        predopt
          (fun e =>
             typ_of_expr e = τ /\
             (Δ ~ Γ ⊢ₑ e ≀ this \/ Δ ~ Γ ⊢ᵪ e ≀ this)) e ->
        Δ ~ Γ ⊢ₛ MkStatement
          tag (StatVariable τ x e l) StmUnit
          ⊣ bind_typ_gamma_stmt l τ Γ ≀ this.
    Proof.
    Admitted.
  End StmtTyping.
End Soundness.
