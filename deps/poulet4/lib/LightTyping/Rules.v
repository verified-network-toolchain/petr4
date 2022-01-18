Require Export Poulet4.LightTyping.Lemmas Poulet4.Ops.

(** * P4light Typing Rules of Inference *)

Section Soundness.
  Create HintDb option_monad.
  Local Hint Unfold option_ret        : option_monad.
  Local Hint Unfold option_bind       : option_monad.
  Local Hint Unfold option_monad_inst : option_monad.
  Local Hint Unfold mret  : option_monad.
  Local Hint Unfold mbind : option_monad.

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

  Context `{T : @Target tags_t expr}.
  Variables (ge : genv) (this : path) (Δ : list string).
  
  Section ExprTyping.
    Variable (Γ : @gamma_expr tags_t).

    Ltac solve_ex :=
      match goal with
      | |- exists rt, Some ?t = Some rt /\ _
        => exists t; cbn; eauto
      end.
    
    Ltac soundtac :=
      autounfold with *;
      intros Hgrt Hdlta Hok Hise rob st Hrob Hg;
      inversion Hok; subst; inversion Hise; subst;
      split; eauto;
      try (intros v Hrn; inversion Hrn; subst; cbn; try solve_ex);
      cbn in *.
  
    Theorem bool_sound : forall tag b dir,
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpBool b) TypBool dir.
    Proof.
      intros; soundtac.
    Qed.
  
    Theorem arbitrary_int_sound : forall tag i z dir,
        (ge,this,Δ,Γ)
          ⊢ₑ
          MkExpression
          tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir.
    Proof.
      intros; soundtac.
    Qed.
    
    Theorem unsigned_int_sound : forall tag i z w dir,
        (ge,this,Δ,Γ)
          ⊢ₑ
          MkExpression tag
          (ExpInt
             (P4Int.Build_t _ i z (Some (w,false))))
          (TypBit w) dir.
    Proof.
      intros tag i z w dir; soundtac; split; auto.
      replace w with (N.of_nat (length (P4Arith.to_loptbool w z))) at 2; auto.
      unfold P4Arith.to_loptbool, P4Arith.to_lbool.
      rewrite map_length, rev_length, P4Arith.length_to_lbool'; cbn; lia.
    Qed.
    
    Theorem signed_int_sound : forall tag i z w dir,
        (ge,this,Δ,Γ)
          ⊢ₑ
          MkExpression
          tag
          (ExpInt (P4Int.Build_t _ i z (Some (w,true))))
          (TypInt w) dir.
    Proof.
      intros tag i z w dir; soundtac; split; auto.
      replace w with (N.of_nat (length (P4Arith.to_loptbool w z))) at 2; auto.
      unfold P4Arith.to_loptbool, P4Arith.to_lbool.
      rewrite map_length, rev_length, P4Arith.length_to_lbool'; cbn; lia.
    Qed.
    
    Theorem string_sound : forall tag s dir,
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpString s) TypString dir.
    Proof.
      intros; soundtac.
    Qed.
    
    Theorem name_sound : forall tag x loc t dir,
        is_directional dir = true ->
        typ_of_loc_var loc Γ = Some t ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpName x loc) t dir.
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
      - rewrite Hd in H11; discriminate.
    Qed.

    Theorem constant_sound : forall tag x loc t dir,
        is_directional dir = false ->
        typ_of_loc_const this loc Γ = Some t ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpName x loc) t dir.
    Proof.
      intros i x l t d Hd Hgt; soundtac.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_domain in Hg.
        destruct Hg as (_ & Hg & _).
        assert (Hv : exists v, loc_to_sval_const ge this l = Some v).
        { destruct (loc_to_sval_const ge this l) as [v |] eqn:Hv; eauto.
          rewrite <- Hg, Hgt in Hv; discriminate. }
        destruct Hv; eauto.
      - rewrite Hd in H11; discriminate.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_val_typ in Hg.
        destruct Hg as (_ & _ & Hg); eauto.
    Qed.
    
    Theorem array_access_sound : forall tag arry idx ts dir n,
        0 < N.to_nat n ->
        typ_of_expr arry = TypArray (TypHeader ts) n ->
        typ_of_expr idx  = TypBit n ->
        (ge,this,Δ,Γ) ⊢ₑ arry ->
        (ge,this,Δ,Γ) ⊢ₑ idx ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpArrayAccess arry idx) (TypHeader ts) dir.
    Proof.
      intros i e1 e2 ts d n Hn Ht1 Ht2 He1 He2;
        autounfold with * in *.
      intros Hgrt Hdelta Hok Hise rob st Hrob Hg; simpl in *.
      inversion Hok; subst. inversion H4; subst.
      rename H1 into Hokts; rename H4 into Hoke1e2;
        rename H2 into Hoke1; rename H3 into Hoke2.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hists; rename H4 into Hisacc;
        rename H2 into Hise1; rename H3 into Hise2.
      rewrite Ht1, Ht2 in *.
      pose proof He1 Hgrt Hdelta as [[v1 Hev1] He1']; clear He1; eauto.
      pose proof He2 Hgrt Hdelta as [[v2 Hev2] He2']; clear He2; eauto.
      split.
      - assert (Hv2': exists v2', sval_to_val rob v2 v2')
          by eauto using exec_val_exists.
        pose proof He1' v1 Hev1 as (r1 & Hr1 & Hv1).
        pose proof He2' v2 Hev2 as (r2 & Hr2 & Hv2).
        clear He1' He2'. cbn in *; inversion Hr2; subst; clear Hr2; cbn in *.
        autounfold with option_monad in *.
        destruct (sequence (map (fun '(x, t) => get_real_type ge t >>| pair x) ts))
          as [rs |] eqn:Hrs;
          unfold ">>|",">>=" in *;
          autounfold with option_monad in *;
          rewrite Hrs in Hr1; try discriminate.
        inversion Hr1; subst; clear Hr1; cbn in *.
        assert (Hhrs: get_real_type ge (TypHeader ts) = Some (TypHeader rs)).
        { cbn in *.
          unfold ">>|",">>=" in *;
            autounfold with option_monad in *;
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

    Theorem bigstring_access_sound : forall tag bits lo hi dir w,
        (lo <= hi < w)%N ->
        typ_of_expr bits = TypBit w ->
        (ge,this,Δ,Γ) ⊢ₑ bits ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpBitStringAccess bits lo hi)
          (TypBit (hi - lo + 1)%N) dir.
    Proof.
      intros i e lo hi d w Hlwh Ht He.
      autounfold with * in *.
      intros Hgrt Hdelta Hok Hise rob st Hrob Hg.
      inversion Hok; subst; inversion H4; subst.
      rename H1 into Hokbit; rename H4 into Hokacc; rename H0 into Hoke.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hisbit; rename H4 into Hisacc;
        rename H0 into Hisee.
      rewrite Ht in *; cbn in *.
      pose proof He Hgrt Hdelta as [[v Hev] He']; clear He; eauto.
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
          with (N.of_nat
                  (length (bitstring_slice bitsbl (N.to_nat lo) (N.to_nat hi)))); auto.
        apply He' in He as (r & Hr & Hv); inversion Hr; subst; clear Hr; cbn in *.
        inversion Hv; subst; cbn in *.
        inversion Hsval; subst; clear Hsval.
        apply bitstring_slice_length in Hlhw; lia.
    Qed.
  
    Theorem list_sound : forall tag es dir,
        Forall (fun e => (ge,this,Δ,Γ) ⊢ₑ e) es ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpList es)
                      (TypTuple (map typ_of_expr es)) dir.
    Proof.
      intros i es d Hes. autounfold with * in *; cbn in *.
      intros Hgrt Hged Hok Hise rob st Hrob Hg.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hgrt as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Hged as Hes;
        simpl in Hes; clear Hes'.
      pose proof (fun a inaes oka ise => Hes a inaes oka ise Hrob Hg) as Hduh; clear Hes.
      rewrite <- Forall_forall in Hduh.
      inversion Hok; subst; inversion H1; subst; inversion H4; subst.
      rename H1 into Hoktup; rename H4 into Hoklist;
        rename H0 into Hoktoees; rename H2 into Hokes.
      inversion Hise; subst; inversion H1; subst; inversion H4; subst.
      rename H1 into Hisettup; rename H4 into Hispees;
        rename H0 into Hisetes; rename H2 into Hisees.
      rewrite Forall_map in Hisetes.
      unfold Basics.compose in *.
      pose proof Forall_impl_Forall _ _ _ _ Hduh Hokes as Hq; clear Hduh Hokes; cbn in *.
      pose proof Forall_impl_Forall _ _ _ _ Hq Hisees as Hp; clear Hq Hisees; cbn in *.
      apply Forall_and_inv in Hp as [Hrnes Htyps]; split.
      - clear Htyps.
        rewrite Forall_exists_factor in Hrnes.
        destruct Hrnes as [vs Hvs]; eauto.
      - clear Hrnes; intros v Hrn; simpl.
        inversion Hrn; subst; clear Hrn.
        rename H6 into Hesvs.
        rewrite Forall_forall in Htyps.
        apply forall_Forall2 with (bs := vs) in Htyps;
          eauto using Forall2_length.
        pose proof Forall2_impl _ _ _ _ _ _ Htyps Hesvs as H; clear Htyps Hesvs.
        rewrite Forall2_flip in H.
        rewrite Forall2_map_r with
            (R := fun v t => exists r, get_real_type ge t = Some r /\ ⊢ᵥ v \: normᵗ r)
            (f := typ_of_expr) in H.
        apply Forall2_ex_factor in H as [rs Hrs].
        rewrite Forall3_permute_12, Forall3_conj_sep in Hrs.
        destruct Hrs as [Hesrs Hvsrs].
        rewrite Forall2_map_l with
            (R := fun ro r => ro = Some r) (f := get_real_type ge) in Hesrs.
        rewrite Forall2_sequence_iff in Hesrs.
        rewrite Forall2_map_r with (f:=normᵗ) in Hvsrs.
        rewrite Hesrs; autounfold with option_monad; cbn;
          solve_ex; split; auto.
    Qed.

    Hint Rewrite map_length : core.
    Local Hint Resolve Forall2_length : core.
    
    Theorem record_sound : forall tag es dir,
        Forall (fun e => (ge,this,Δ,Γ) ⊢ₑ e) (map snd es) ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpRecord es)
          (TypRecord (map (fun '(x,e) => (x,typ_of_expr e)) es)) dir.
    Proof.
      intros i es d Hes.
      autounfold with * in *; cbn in *.
      intros Hgrt Hged Hok Hise rob st Hrob Hg.
      inversion Hok; subst; inversion H1; subst; inversion H4; subst.
      rename H1 into Htokrec; rename H4 into Heokrec;
        rename H0 into Htokes; rename H2 into Heokes.
      inversion Hise; subst; inversion H1; subst; inversion H4; subst.
      unfold Basics.compose in *.
      rename H1 into Hisetrec; rename H4 into Hispe;
        rename H0 into Hisetes; rename H2 into Hisees.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (st:=st).
      pose proof (fun e HInnes Hok Hise =>
                    Hes e HInnes Hgrt Hged Hok Hise Hrob Hg)
        as H; clear Hes; rename H into Hes.
      rewrite <- Forall_forall,Forall_map in Hes.
      unfold Basics.compose in Hes; cbn in Hes.
      pose proof Forall_impl_Forall _ _ _ _ Hes Heokes as H; clear Hes Heokes.
      pose proof Forall_impl_Forall _ _ _ _ H Hisees as Hes; clear H Hisees.
      apply Forall_and_inv in Hes as [Hrnes Htyps]; split.
      - clear Htyps.
        rewrite Forall_exists_factor in Hrnes.
        destruct Hrnes as [vs Hvs].
        exists (ValBaseStruct (combine (map P4String.str (map fst es)) vs)).
        constructor. unfold AList.all_values, P4String.clear_AList_tags.
        rewrite Forall2_conj,
        Forall2_map_both with (f:=fst) (g:=fst),Forall2_map_both with (f:=snd) (g:=snd).
        rewrite map_snd_combine by (autorewrite with core; eauto).
        rewrite map_fst_combine by (autorewrite with core; eauto).
        rewrite Forall2_eq,map_fst_map,map_snd_map,map_id;split;auto.
        rewrite <- Forall2_map_l; assumption.
      - clear Hrnes.
        intros v Hev; inversion Hev; subst.
        rename kvs' into xvs; rename H6 into Hxvs.
        unfold AList.all_values,P4String.clear_AList_tags in Hxvs.
        rewrite Forall2_conj in Hxvs.
        destruct Hxvs as [Hfsteq Hxvs].
        rewrite Forall2_map_both,Forall2_eq,map_fst_map in Hfsteq.
        rewrite map_pat_both, <- Forall2_map_l in Hxvs; cbn in *.
        rewrite Forall_forall in Htyps.
        apply forall_Forall2 with (bs := map snd xvs) in Htyps;
          autorewrite with core; eauto.
        rewrite <- Forall2_map_r in Htyps.
        pose proof Forall2_impl _ _ _ _ _ _ Htyps Hxvs as H; clear Htyps Hxvs.
        apply Forall2_ex_factor in H as [rs Hrs].
        rewrite Forall3_conj_sep in Hrs.
        destruct Hrs as [Hesrs Hxvsrs].
        rewrite Forall2_map_l with
            (R:=fun e t => get_real_type ge (typ_of_expr e) = Some t)
            (f:=snd) in Hesrs.
        rewrite Forall2_map_l with
            (R:=fun t r => get_real_type ge t = Some r)
            (f:=typ_of_expr) in Hesrs.
        rewrite Forall2_map_l with
            (R:=fun ro r => ro = Some r) (f:=get_real_type ge) in Hesrs.
        rewrite Forall2_sequence_iff in Hesrs.
        rewrite map_pat_combine,map_id.
        pose proof @map_bind_pair _ option_monad_inst as Hmbp.
        unfold ">>|",">>=",mbind,mret in Hmbp.
        autounfold with option_monad in *.
        rewrite Hmbp; clear Hmbp.
        exists (TypRecord (combine (map fst es) rs)); cbn; split.
        + clear xvs Δ Γ this i d rob st Hged Hok Hise Hrob
                Hg Htokrec Heokrec Htokes Hev Hfsteq Hxvsrs.
          clear Hgrt Hisetrec Hispe Hisetes.
          generalize dependent rs.
          induction es as [| [x e] es IHes];
            intros [| r rs] Hrs; cbn in *; try discriminate;
              try specialize IHes with rs;
              repeat match_some_inv; some_inv; try reflexivity.
          intuition; match_some_inv; some_inv; reflexivity.
        + constructor.
          unfold AList.all_values,P4String.clear_AList_tags.
          rewrite Forall2_conj,
          Forall2_map_both with (f:=fst) (g:=fst),Forall2_map_both with (f:=snd) (g:=snd).
          repeat rewrite map_fst_map.
          repeat rewrite map_snd_map.
          repeat rewrite map_id.
          rewrite map_fst_combine by
              (apply sequence_length in Hesrs; autorewrite with core in *; auto).
          rewrite map_snd_combine by
              (apply sequence_length in Hesrs; autorewrite with core in *; auto).
          rewrite Forall2_eq, <- Forall2_map_both; auto.
    Qed.
    
    Local Hint Resolve val_to_sval_ex : core.
    Local Hint Resolve exec_val_preserves_typ : core.
    Local Hint Resolve eval_unary_op_preserves_typ : core.
    
    Theorem unary_op_sound : forall tag o e t dir,
        unary_type o (typ_of_expr e) t ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpUnaryOp o e) t dir.
    Proof.
      intros i o e t d Hut He; autounfold with * in *; cbn in *.
      intros Hgrt Hdelta Hok Hise rob st Hrob Hg.
      inversion Hok; subst; inversion H4; subst.
      rename H1 into Hokt; rename H4 into Hokuop; rename H0 into Hoke.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hiset; rename H4 into Hispe; rename H0 into Hisee.
      pose proof He Hgrt Hdelta Hoke Hisee _ _ Hrob Hg as [[v Hev] Hvt].
      apply unary_type_eq in Hut as Hut_eq; subst t.
      clear He Hgrt Hdelta Hoke Hisee; split.
      - assert (exists v', sval_to_val rob v v') by eauto using exec_val_exists.
        destruct H as [v' Hv'].
        apply Hvt in Hev as Hev'.
        destruct Hev' as (r & Hr & Hvr).
        pose proof exec_val_preserves_typ _ _ _ Hv' _ Hvr as Hv'r.
        assert (Hutr: unary_type o r r).
        { inversion Hut; subst;
            try inv_numeric; try inv_numeric_width;
              try match goal with
                  | H: _ = typ_of_expr _ |- _ => rewrite <- H in *
                  end; cbn in *; try some_inv; auto. }
        assert (Hutr_normᵗ: unary_type o (normᵗ r) (normᵗ r)).
        { inversion Hutr; subst;
            try inv_numeric;
            try inv_numeric_width;
            cbn; auto. }
        assert (exists v''', Ops.eval_unary_op o v' = Some v''').
        { destruct (Ops.eval_unary_op o v') as [v'' |] eqn:Heqop; eauto.
          inversion Hutr_normᵗ; subst;
            try inv_numeric; try inv_numeric_width;
              inversion Hv'r; subst; cbn in *; try discriminate;
                try match goal with
                    | H1: _ = ?a, H2: _ = ?a |- _ => rewrite <- H1 in H2; clear H1
                    end;
                try discriminate. }
        destruct H as [v'' Hv'']; eauto.
      - clear v Hev; intros v Hev.
        inversion Hev; subst; simpl in *.
        pose proof Hvt _ H7 as (r & Hr & Hvr); clear Hvt H7.
        pose proof exec_val_preserves_typ _ _ _ H8 _ Hvr as Hargvr; clear H8 Hvr.
        assert (Hr_eq : typ_of_expr e = r /\ r = normᵗ r).
        { inversion Hut; subst; try inv_numeric; try inv_numeric_width;
            try match goal with
                | H: _ = typ_of_expr _ |- _ => rewrite <- H in *
                end; cbn in *; try some_inv; auto. }
        destruct Hr_eq as [Het Hrr]; subst r.
        rewrite Hrr in Hut; eauto.
    Qed.

    Local Hint Resolve eval_binary_op_preserves_typ : core.
    Local Hint Resolve binary_type_get_real_type : core.
    Local Hint Resolve binary_type_normᵗ : core.
    
    Theorem binary_op_sound : forall tag o t e1 e2 dir,
        binary_type o (typ_of_expr e1) (typ_of_expr e2) t ->
        (ge,this,Δ,Γ) ⊢ₑ e1 ->
        (ge,this,Δ,Γ) ⊢ₑ e2 ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpBinaryOp o (e1,e2)) t dir.
    Proof.
      intros i o t e1 e2 d Hbt He1 He2.
      autounfold with * in *; cbn in *.
      intros Hgrt Hged Hok His rob st Hrob Hgst.
      inversion Hok; subst; inversion H4; subst.
      rename H1 into Hokt; rename H4 into Heokb;
        rename H2 into Hoke1; rename H5 into Hoke2.
      inversion His; subst; inversion H4; subst.
      rename H1 into Hiset; rename H4 into Hispe;
        rename H2 into Hisee1; rename H5 into Hisee2.
      pose proof He1 Hgrt Hged Hoke1 Hisee1 _ _ Hrob Hgst as [[v1 Hev1] Hvt1].
      pose proof He2 Hgrt Hged Hoke2 Hisee2 _ _ Hrob Hgst as [[v2 Hev2] Hvt2].
      clear He1 He2 Hgrt Hged Hoke1 Hoke2 Hisee1 Hisee2 Hgst; split.
      - apply Hvt1 in Hev1 as Hev1'; destruct Hev1' as (r1 & Hr1 & Hvr1); clear Hvt1.
        apply Hvt2 in Hev2 as Hev2'; destruct Hev2' as (r2 & Hr2 & Hvr2); clear Hvt2.
        (*Check exec_expr_binary_op.*)
        assert (Hv1': exists v1', sval_to_val rob v1 v1') by eauto using exec_val_exists.
        assert (Hv2': exists v2', sval_to_val rob v2 v2') by eauto using exec_val_exists.
        destruct Hv1' as [v1' Hv1']; destruct Hv2' as [v2' Hv2'].
        assert (Hvr1': ⊢ᵥ v1' \: normᵗ r1) by eauto.
        assert (Hvr2': ⊢ᵥ v2' \: normᵗ r2) by eauto.
        admit.
      - clear v1 v2 Hev1 Hev2; intros v Hev; inversion Hev; subst.
        apply Hvt1 in H7 as (r1 & Hr1 & Hvr1); clear Hvt1.
        apply Hvt2 in H9 as (r2 & Hr2 & Hvr2); clear Hvt2.
        assert (Hlargvr1: ⊢ᵥ largv \: normᵗ r1) by eauto using exec_val_preserves_typ.
        assert (Hrargvr2: ⊢ᵥ rargv \: normᵗ r2) by eauto using exec_val_preserves_typ.
        assert (Hr : exists r, get_real_type ge t = Some r /\ binary_type o r1 r2 r)
          by eauto using binary_type_get_real_type.
        destruct Hr as (r & Hr & Hbr); eauto 6.
    Admitted.
  
    Theorem cast_sound : forall tag e t dir,
        cast_type (typ_of_expr e) t ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpCast t e) t dir.
    Proof.
    Admitted.

    Theorem enum_member_sound : forall tag X M E mems dir,
        IdentMap.get (P4String.str X) (ge_typ ge) = Some (TypEnum E None mems) ->
        List.In M mems ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpTypeMember X M)
          (TypEnum E None mems) dir.
    Proof.
      intros tag X M E mems dir Hget Hmem.
      intros Hgrt Hdlta Hok Hise rob st Hrob Hg; cbn in *; split; eauto.
      intros v Hrn.
      inversion Hrn; subst; solve_ex; split; auto.
      - rewrite Hget in H7; some_inv; auto.
      - rewrite Hget in H7; some_inv.
    Qed.

    (*Theorem senum_member_sound :
      forall tag X M E t (mems : list (P4String.t tags_t * Sval)) dir,
        IdentMap.get (P4String.str X) (ge_typ ge) = Some (TypEnum E (Some t) (map fst mems)) ->
        (*IdentMap.get (P4String.str E) (ge_senum ge) = Some mems ->*)
        List.In M (map fst mems) ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpTypeMember X M)
          (TypEnum E (Some t) (map fst mems)) dir.
    Proof.
      intros i X M E t mems dir HM.
      intros Hgrt Hdlta Hok Hise rob st Hrob Hg; cbn in *.
      inversion Hok; subst; inversion H1; subst;
        inversion H4; subst; inversion H0; subst.
      rename H1 into Hokenumt; rename H4 into HokXM;
        rename H0 into Hoksomet; rename H2 into HinX; rename H3 into Hokt.
      inversion Hise; subst; inversion H1; subst.
      rename H1 into Hisetenum; rename H4 into Hispe; rename H0 into Hiset. split.
      - 
      Admitted.*)

    Theorem error_member_sound : forall tag err dir,
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpErrorMember err) TypError dir.
    Proof.
      intros tag err dir; soundtac.
    Qed.

    Local Hint Resolve member_get_member_ex : core.
    Local Hint Resolve get_member_types : core.
    
    Theorem other_member_sound : forall tag e x ts t dir,
        member_type ts (typ_of_expr e) ->
        AList.get ts x = Some t ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpExpressionMember e x) t dir.
    Proof.
      intros i e x ts t dir Hmem Hts He.
      intros Hgrt Hdlta Hok Hise rob st Hrob Hg; cbn in *.
      inversion Hok; subst; inversion H4; subst.
      rename H4 into Hokmem; rename H0 into Htoeok; rename H1 into Hokt.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hist; rename H4 into Hismem; rename H0 into Hise'.
      pose proof He Hgrt Hdlta as [[v Hev] Hv]; eauto.
      split.
      - assert (Hget: exists v', get_member v (P4String.str x) v').
        { apply Hv in Hev as (r & Hr & Hvr).
          pose proof get_real_member_type _ _ _ _ Hr Hmem as [rs Hmemrs].
          apply member_type_normᵗ in Hmemrs as Hmemrs_norm.
          assert (Hlem3' : exists r',
                     AList.get (map (fun '(x, t) => (x, normᵗ t)) rs) x = Some r').
          { clear i dir Γ Δ He Hdlta Hok
                  Hg Hokt Hokmem Htoeok v Hvr Hise
                  rob Hrob Hgrt Hv st.
            pose proof member_type_get_real_type
                 _ _ _ _ _
                 Hmem Hmemrs Hr as Hlem.
            apply f_equal with
                (f := option_map (map (fun '(x,t) => (x,normᵗ t)))) in Hlem.
            cbn in Hlem.
            rewrite option_map_lift_monad,sequence_map in Hlem.
            repeat rewrite map_pat_both in Hlem.
            rewrite map_map in Hlem.
            clear e Hmem Hismem Hise' Hist Hr r Hmemrs Hmemrs_norm.
            unfold option_map,option_bind,option_ret in Hlem.
            unfold ">>|",">>=",mbind,mret,option_monad_inst,
            option_bind,option_ret in *.
            generalize dependent t; generalize dependent rs.
            induction ts as [| [y t] ts IHts];
              intros [| [z r] rs] Hrs t' Hxt';
              cbn in *; try discriminate;
                repeat match_some_inv; repeat some_inv.
            inversion H0; subst.
            pose proof P4String.equiv_reflect x z as Hxz.
            inversion Hxz; subst.
            + rewrite AList.get_eq_cons by assumption; eauto.
            + rewrite AList.get_neq_cons in Hxt' by assumption.
              rewrite AList.get_neq_cons by assumption; eauto. }
          destruct Hlem3' as [r' Hr']; eauto. }
        destruct Hget as [v' Hv'].
        exists v'; eapply exec_expr_other_member; eauto.
      - clear v Hev; intros v Hev. inversion Hev; subst.
        apply Hv in H7 as (r & Hr & Hvr); clear Hv.
        pose proof ok_get_real_type_ex _ _ Hokt _ Hdlta as [r' Hr'].
        exists r'; split; auto.
        pose proof get_real_member_type _ _ _ _ Hr Hmem as [rs Hmemrs].
        pose proof member_type_get_real_type
               _ _ _ _ _
               Hmem Hmemrs Hr as Hlem.
        apply member_type_normᵗ in Hmemrs.
        apply f_equal with
            (f := option_map (map (fun '(x,t) => (x,normᵗ t)))) in Hlem.
        cbn in Hlem.
        rewrite option_map_lift_monad,sequence_map in Hlem.
        repeat rewrite map_pat_both in Hlem.
        rewrite map_map in Hlem.
        unfold option_map,option_bind,option_ret in Hlem.
        assert (Hlem3' :
                  AList.get (map (fun '(x, t) => (x, normᵗ t)) rs) x = Some (normᵗ r')).
        { clear H8 Hvr Hev v Hist Htoeok
                Hismem Hise' Hg rob Hrob st Hise Hok Hdlta Hgrt He
                Hokt Hokmem dir Δ Γ i e Hmem Hr r Hmemrs.
          unfold ">>|",">>=",mbind,mret,option_monad_inst,
          option_bind,option_ret in *.
          generalize dependent r'; generalize dependent t.
          generalize dependent rs.
          induction ts as [| [y t] ts IHts];
            intros [| [z r] rs] Hrs t' Hxt' r' Ht'r';
            cbn in *; try discriminate;
              repeat match_some_inv; repeat some_inv.
          inversion H0; subst.
          pose proof P4String.equiv_reflect x z as Hxz.
          inversion Hxz; subst.
          + rewrite AList.get_eq_cons in Hxt' by assumption; some_inv.
            rewrite AList.get_eq_cons by assumption.
            rewrite Heqo2 in Ht'r'; some_inv; reflexivity.
          + rewrite AList.get_neq_cons in Hxt' by assumption.
            rewrite AList.get_neq_cons by assumption; eauto. }
        eauto.
    Qed.

    Theorem array_size_sound : forall tag e x dir t w,
        (* P4Arith.BitArith.bound 32 w -> *)
        (w < 2 ^ 32)%N ->
        typ_of_expr e = TypArray t w ->
        P4String.str x = "size"%string ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpExpressionMember e x) (TypBit 32) dir.
    Proof.
    Admitted.

    Theorem array_last_index_sound : forall tag e x dir t w,
        typ_of_expr e = TypArray t w ->
        P4String.str x = "lastIndex"%string ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpExpressionMember e x) t dir.
    Proof.
    Admitted.

    Theorem ternary_sound : forall tag e₁ e₂ e₃ t dir,
        typ_of_expr e₁ = TypBool ->
        typ_of_expr e₂ = typ_of_expr e₃ ->
        typ_of_expr e₂ = t ->
        (ge,this,Δ,Γ) ⊢ₑ e₁ ->
        (ge,this,Δ,Γ) ⊢ₑ e₂ ->
        (ge,this,Δ,Γ) ⊢ₑ e₃ ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpTernary e₁ e₂ e₃) t dir.
    Proof.
    Admitted.
  End ExprTyping.

  Local Hint Constructors exec_stmt : core.
  Local Hint Constructors exec_block : core.
  
  Section StmtTyping.
    Variable (Γ : @gamma_stmt tags_t).
    
    Theorem assign_sound : forall tag e₁ e₂,
        typ_of_expr e₁ = typ_of_expr e₂ ->
        lexpr_ok e₁ ->
        (ge,this,Δ,Γ) ⊢ₑ e₁->
        (ge,this,Δ,Γ) ⊢ₑ e₂ \/ (ge,this,Δ,Γ) ⊢ᵪ e₂ ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatAssignment e₁ e₂) StmUnit ⊣ Γ.
    Proof.
    Admitted.

    Theorem cond_sound : forall tag e s₁ s₂ Γ₁,
        typ_of_expr e = TypBool ->
        (ge,this,Δ,Γ) ⊢ₑ e->
        (ge,this,Δ,Γ) ⊢ₛ s₁ ⊣ Γ₁ ->
        predopt (fun s₂ => exists Γ₂, (ge,this,Δ,Γ) ⊢ₛ s₂ ⊣ Γ₂) s₂ ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatConditional e s₁ s₂)
          (match s₂ with
           | None    => typ_of_stmt s₁
           | Some s₂ => lub_StmType (typ_of_stmt s₁) (typ_of_stmt s₂)
           end) ⊣ Γ.
    Proof.
    Admitted.

    Theorem exit_sound : forall tag,
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag StatExit StmVoid ⊣ Γ.
    Proof.
      unfold stmt_types; intros; split; eauto.
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.

    Theorem return_sound : forall tag e,
        predopt (fun e => (ge,this,Δ,Γ) ⊢ₑ e) e ->
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag (StatReturn e) StmVoid ⊣ Γ.
    Proof.
    Admitted.

    Theorem empty_sound : forall tag,
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag StatEmpty StmUnit ⊣ Γ.
    Proof.
      unfold stmt_types; intros; split; eauto.
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.
    
    Theorem block_sound : forall Γ' tag blk t,
        Block_StmTypes blk t ->
        (ge,this,Δ,Γ) ⊢ᵦ blk ⊣ Γ' ->
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag (StatBlock blk) t ⊣ Γ.
    Proof.
    Admitted.

    Theorem method_call_sound : forall `{dummy : Inhabitant tags_t} tag e τs es,
        (ge,this,Δ,Γ)
          ⊢ᵪ MkExpression dummy_tags
          (ExpFunctionCall e τs es)
          TypVoid Directionless ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement tag
          (StatMethodCall e τs es) StmUnit ⊣ Γ.
    Proof.
    Admitted.

    Theorem direct_application_sound : forall `{dummy : Inhabitant tags_t} tag τ es,
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression dummy_tags
          (ExpFunctionCall
             (direct_application_expression τ)
             nil (map Some es)) TypVoid Directionless ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement tag
          (StatDirectApplication τ es) StmUnit ⊣ Γ.
    Proof.
    Admitted.

    Theorem stat_variable_sound : forall tag τ x e l,
        predopt
          (fun e =>
             typ_of_expr e = τ /\
             ((ge,this,Δ,Γ) ⊢ₑ e \/ (ge,this,Δ,Γ) ⊢ᵪ e)) e ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatVariable τ x e l) StmUnit
          ⊣ bind_typ_gamma_stmt l τ Γ.
    Proof.
    Admitted.
  End StmtTyping.
End Soundness.
