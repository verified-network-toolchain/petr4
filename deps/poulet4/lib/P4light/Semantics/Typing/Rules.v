From Poulet4.P4light Require Export
     Semantics.Typing.Lemmas Semantics.Ops Semantics.Typing.CTK.

(** * P4light Typing Rules of Inference *)

(** Inference rules for the p4light types system
    given as theorems for progress & preservation. *)

Section Soundness.
  Create HintDb option_monad.
  Local Hint Unfold option_bind       : option_monad.
  Local Hint Unfold option_monad_inst : option_monad.
  Local Hint Unfold mret  : option_monad.
  Local Hint Unfold mbind : option_monad.
  Local Hint Resolve exec_val_exists : core.
  Local Hint Resolve val_to_sval_ex : core.
  Local Hint Resolve exec_val_preserves_typ : core.

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
  Local Hint Constructors exec_expr_det : core.
  Local Hint Constructors exec_lexpr : core.
  Local Hint Constructors val_typ : core.
  Local Hint Constructors lval_typ : core.
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
      autounfold with *; cbn in *;
      intros Hgrt Hdlta Hgok Hok Hise rob st Hrobsome Hrob Hg;
      inversion Hok; subst; inversion Hise; subst;
      split; [| split]; eauto;
      try match goal with
          | |- lexpr_ok _ -> _ => intros Hlv; inv Hlv; contradiction
          end;
      try (intros v Hrn; inversion Hrn; subst; cbn; try solve_ex);
      cbn in *.

    Theorem bool_sound : forall tag b dir,
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpBool b) TypBool dir.
    Proof using.
      intros; soundtac.
    Qed.

    Theorem arbitrary_int_sound : forall tag i z dir,
        (ge,this,Δ,Γ)
          ⊢ₑ
          MkExpression
          tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir.
    Proof using.
      intros; soundtac.
    Qed.

    Theorem unsigned_int_sound : forall tag i z w dir,
        (ge,this,Δ,Γ)
          ⊢ₑ
          MkExpression tag
          (ExpInt
             (P4Int.Build_t _ i z (Some (w,false))))
          (TypBit w) dir.
    Proof using.
      intros tag i z w dir; soundtac; split; auto.
      replace w
        with (N.of_nat (length (P4Arith.to_loptbool w z))) at 2; auto.
      unfold P4Arith.to_loptbool, P4Arith.to_lbool.
      rewrite map_length, length_to_lbool'; cbn; lia.
    Qed.

    Theorem signed_int_sound : forall tag i z w dir,
        (ge,this,Δ,Γ)
          ⊢ₑ
          MkExpression
          tag
          (ExpInt (P4Int.Build_t _ i z (Some (w,true))))
          (TypInt w) dir.
    Proof using.
      intros tag i z w dir; soundtac; split; auto.
      replace w
        with (N.of_nat (length (P4Arith.to_loptbool w z))) at 2; auto.
      unfold P4Arith.to_loptbool, P4Arith.to_lbool.
      rewrite map_length, P4Arith.length_to_lbool'; cbn; lia.
    Qed.

    Theorem string_sound : forall tag s dir,
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpString s) TypString dir.
    Proof using.
      intros; soundtac.
    Qed.

    Theorem name_sound : forall tag x loc t dir,
        is_directional dir = true ->
        typ_of_loc_var loc (var_gamma Γ) = Some t ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpName x loc) t dir.
    Proof using.
      intros i x l t d Hd Hgt; soundtac.
      - unfold gamma_expr_prop, gamma_var_prop, gamma_var_domain in Hg.
        destruct Hg as [[Hg _] _].
        apply Hg in Hgt as [sv Hsv]; eauto.
      - unfold gamma_expr_prop, gamma_var_prop, gamma_var_val_typ in Hg.
        destruct Hg as [[_ Hg] _]; eauto.
      - rewrite Hd in H11; discriminate.
      - intros Hlv; split; eauto.
        unfold gamma_expr_prop, gamma_var_prop,
        gamma_var_val_typ,gamma_var_domain in Hg.
        destruct Hg as [[Hdg Hg] _].
        apply Hdg in Hgt as Hsv.
        destruct Hsv as [sv Hsv].
        intros lv s Helv; inv Helv.
        pose proof Hg _ _ _ Hgt Hsv as (r & Hr & Hvr).
        destruct Γ as [Γv Γc] eqn:HeqΓ; cbn in *.
        eexists; repeat split; eauto.
        constructor.
        destruct l as [l | l]; cbn in *; try discriminate.
        rewrite FuncAsMap.get_map_map.
        unfold PathMap.get in Hgt.
        rewrite Hgt; cbn. unfold try_get_real_type.
        rewrite Hr; reflexivity.
    Qed.

    Theorem constant_sound : forall tag x loc t,
        typ_of_loc_const this loc Γ = Some t ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression tag (ExpName x loc) t Directionless.
    Proof using.
      intros i x l t Hgt; soundtac; try discriminate.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_domain in Hg.
        destruct Hg as (_ & Hg & _).
        apply Hg in Hgt as [v Hv].
        apply f_equal with (f:=option_map eval_val_to_sval) in Hv.
        eauto.
      - unfold gamma_expr_prop, gamma_const_prop, gamma_const_val_typ in Hg.
        destruct Hg as (_ & _ & Hg); eauto.
    Qed.

    Theorem array_access_sound : forall tag arry idx ts dir n,
        (0 < N.to_nat n)%nat ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ arry \: TypArray (TypHeader ts) n ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ idx  \: TypBit n ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpArrayAccess arry idx) (TypHeader ts) dir.
    Proof using.
      intros i e1 e2 ts d n Hn [He1 Ht1] [He2 Ht2];
        autounfold with * in *.
      intros Hgrt Hdelta Hgok Hok Hise rob st Hrobsome Hrob Hg; simpl in *.
      inversion Hok; subst. inversion H4; subst.
      rename H1 into Hokts; rename H4 into Hoke1e2;
        rename H2 into Hoke1; rename H3 into Hoke2.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hists; rename H4 into Hisacc;
        rename H2 into Hise1; rename H3 into Hise2.
      rewrite <- Ht1, <- Ht2 in *.
      pose proof He1 Hgrt Hdelta
        as [[v1 Hev1] [He1' Helv1]]; clear He1; eauto.
      pose proof He2 Hgrt Hdelta
        as [[v2 Hev2] [He2' _]]; clear He2; eauto.
      split; [| split].
      - clear Helv1.
        assert (Hv2': exists v2', sval_to_val rob v2 v2')
          by eauto using exec_val_exists.
        pose proof He1' v1 Hev1 as (r1 & Hr1 & Hv1).
        pose proof He2' v2 Hev2 as (r2 & Hr2 & Hv2).
        clear He1' He2'.
        cbn in *; inversion Hr2; subst; clear Hr2; cbn in *.
        autounfold with option_monad in *.
        destruct
          (sequence
             (map (fun '(x, t) => get_real_type ge t >>| pair x) ts))
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
        assert (Huninit :
                  exists v, uninit_sval_of_typ None (TypHeader rs) = Some v)
          by eauto using is_expr_typ_uninit_sval_of_typ.
        destruct Huninit as [v Hv]; eauto.
      - clear v1 v2 Hev1 Hev2 Helv1.
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
          destruct (nth_error
                      headers
                      (BinInt.Z.to_nat idxz)) as [v |] eqn:Hv.
          * inversion Hv1; subst.
            rewrite Forall_forall in H6.
            eauto using nth_error_In.
          * pose proof uninit_sval_of_typ_val_typ rtyp as H.
            eapply H; eauto.
            apply val_typ_is_expr_typ in Hv1 as Hv1'.
            inversion Hv1'; subst; auto.
      - intros Hlv; inv Hlv; rename H0 into Hleoke1.
        pose proof Helv1 Hleoke1 as [(lv1 & s1 & Hlv1) Helv1'];
          clear Helv1 Hleoke1; split.
        + apply He1' in Hev1 as Hev1'; clear He1'.
          destruct Hev1' as (r1 & Hr1 & Hvr1).
          cbn in Hr1. autounfold with option_monad in *.
          repeat match_some_inv; repeat some_inv.
          cbn in Hvr1; inversion Hvr1; subst.
          assert (Hsv1: exists v1, sval_to_val rob (ValBaseStack vs n0) v1)
            by eauto using exec_val_exists.
          destruct Hsv1 as [v1 Hsv1].
          inversion Hsv1; subst.
          assert (Hxed1:
                    exec_expr_det
                      ge rob this st e1 (ValBaseStack lv' n0)) by eauto.
          rename v2 into sv2.
          assert (Hsv2: exists v2, sval_to_val rob sv2 v2)
            by eauto using exec_val_exists.
          destruct Hsv2 as [v2 Hsv2].
          assert (Hxed2: exec_expr_det ge rob this st e2 v2) by eauto.
          apply He2' in Hev2 as (r2 & Hr2 & Hvr2);
            clear He2'; cbn in *; some_inv; cbn in *; inv Hvr2.
          inversion Hsv2; subst.
          assert (Hz: exists z, array_access_idx_to_z (ValBaseBit lb') = Some z)
            by (cbn; eauto).
          destruct Hz as [z Hz]; eauto.
        + clear lv1 s1 Hlv1; intros lv1 s1 Helv1; inv Helv1.
          apply Helv1' in H8 as Hlvt.
          destruct Γ as [Γv Γc] eqn:HeqΓ; cbn in *.
          destruct Hlvt as (r & hr & hlvr).
          unfold option_bind at 1 in hr.
          match_some_inv; some_inv.
          eexists; split; eauto.
          cbn in hlvr.
          econstructor; eauto.
          inv H10.
          apply He2' in H as (r2 & Hr2 & Hvr2); some_inv; cbn in *.
          inv Hvr2; inv H0; cbn in *; some_inv.
          apply BitArith.lbool_to_val_lower; lia.
    Qed.

    Theorem bigstring_access_sound : forall tag bits lo hi dir w,
        (lo <= hi < w)%N ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ bits \: TypBit w ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpBitStringAccess bits lo hi)
          (TypBit (hi - lo + 1)%N) dir.
    Proof using.
      intros i e lo hi d w Hlwh [He Ht].
      autounfold with * in *.
      intros Hgrt Hdelta Hgok Hok Hise rob st Hrobsome Hrob Hg.
      inversion Hok; subst; inversion H4; subst.
      rename H1 into Hokbit; rename H4 into Hokacc; rename H0 into Hoke.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hisbit; rename H4 into Hisacc;
        rename H0 into Hisee.
      rewrite <- Ht in *; cbn in *.
      pose proof He Hgrt Hdelta as [[v Hev] [He' Helv]]; clear He; eauto.
      split; [| split].
      - clear Helv.
        apply He' in Hev as Hv';
          destruct Hv' as (rt & Hrt & Hv);
          inversion Hv; inversion Hrt; clear Hrt;
            subst; cbn in *; try discriminate.
        rename v0 into bits. inversion H1; clear H1; subst.
        exists (ValBaseBit (bitstring_slice bits (N.to_nat lo) (N.to_nat hi))).
        eapply exec_expr_bitstring_access with
            (wn := length bits); eauto; lia.
      - clear v Hev Helv; intros v Hrn; inversion Hrn; subst; simpl.
        solve_ex; split; auto.
        rename H8 into He; rename H9 into Hsval; rename H12 into Hlhw.
        replace (hi - lo + 1)%N
          with (N.of_nat
                  (length
                     (bitstring_slice
                        bitsbl (N.to_nat lo) (N.to_nat hi)))); auto.
        apply He' in He as (r & Hr & Hv);
          inversion Hr; subst; clear Hr; cbn in *.
        inversion Hv; subst; cbn in *.
        inversion Hsval; subst; clear Hsval.
        apply bitstring_slice_length in Hlhw; lia.
      - intros Hlv; inv Hlv.
        apply Helv in H0 as [(lv & s & Hlvs) Helv']; clear Helv; split.
        + apply Helv' in Hlvs as Hlvw.
          rename v into sv.
          assert (Hsv: exists v, sval_to_val rob sv v)
            by eauto using exec_val_exists.
          destruct Hsv as [v Hsv].
          assert (Hxd: exec_expr_det ge rob this st e v) by eauto.
          exists (ValLeftBitAccess lv hi lo),s.
          apply He' in Hev as (r & Hr & Hvr); cbn in *.
          assert (Hbits: exists bits ws, sval_to_bits_width v = Some (bits,ws)).
          { inv Hr; cbn in *; inv Hvr.
            inv Hsv; cbn in *; eauto. }
          destruct Hbits as (bits & ws & Hbit).
          econstructor; eauto.
          inv Hr; cbn in *; inv Hvr.
          inv Hsv; cbn in *; some_inv.
          apply Forall2_length in H0; lia.
        + clear v Hev lv s Hlvs; intros lv s Hlvs; inv Hlvs; inv H10.
          apply He' in H as (r & Hr & Hsvr); clear He'; cbn in *; some_inv.
          cbn in *; inv Hsvr; inv H0; cbn in *; some_inv.
          apply Helv' in H9 as Hlvt.
          apply Forall2_length in H1.
          rewrite H1 in Hlvt.
          destruct Hlvt as (r & hr & hlvr).
          injection hr as hr; subst. cbn in *.
          eexists; split; eauto.
          econstructor; eauto.
    Qed.

    Theorem list_sound : forall tag es dir,
        Forall (fun e => (ge,this,Δ,Γ) ⊢ₑ e) es ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpList es)
                      (TypTuple (map typ_of_expr es)) dir.
    Proof using.
      intros i es d Hes. autounfold with * in *; cbn in *.
      intros Hgrt Hged Hgok Hok Hise rob st Hrobsome Hrob Hg.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hgrt as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Hged as Hes;
        simpl in Hes; clear Hes'.
      pose proof
           (fun a inaes oka ise =>
              Hes a inaes Hgok oka ise Hrobsome Hrob Hg) as Hduh; clear Hes.
      rewrite <- Forall_forall in Hduh.
      inversion Hok; subst; inversion H1; subst; inversion H4; subst.
      rename H1 into Hoktup; rename H4 into Hoklist;
        rename H0 into Hoktoees; rename H2 into Hokes.
      inversion Hise; subst; inversion H1; subst; inversion H4; subst.
      rename H1 into Hisettup; rename H4 into Hispees;
        rename H0 into Hisetes; rename H2 into Hisees.
      rewrite Forall_map in Hisetes.
      unfold Basics.compose in *.
      pose proof Forall_impl_Forall
           _ _ _ _ Hduh Hokes as Hq; clear Hduh Hokes; cbn in *.
      pose proof Forall_impl_Forall
           _ _ _ _ Hq Hisees as Hp; clear Hq Hisees; cbn in *.
      apply Forall_and_inv in Hp as [Hrnes Htyps].
      apply Forall_and_inv in Htyps as [Htyps _].
      split; [| split].
      - clear Htyps.
        rewrite Forall_exists_factor in Hrnes.
        destruct Hrnes as [vs Hvs]; eauto.
      - clear Hrnes; intros v Hrn; simpl.
        inversion Hrn; subst; clear Hrn.
        rename H6 into Hesvs.
        rewrite Forall_forall in Htyps.
        apply forall_Forall2 with (bs := vs) in Htyps;
          eauto using Forall2_length.
        pose proof Forall2_impl
             _ _ _ _ _ _ Htyps Hesvs as H; clear Htyps Hesvs.
        rewrite Forall2_flip in H.
        rewrite Forall2_map_r with
            (R := fun v t => exists r, get_real_type ge t = Some r /\ ⊢ᵥ v \: normᵗ r)
            (f := typ_of_expr) in H.
        apply Forall2_ex_factor in H as [rs Hrs].
        rewrite Forall3_permute_12, Forall3_conj_sep in Hrs.
        destruct Hrs as [Hesrs Hvsrs].
        rewrite ForallMap.Forall2_map_l with
            (R := fun ro r => ro = Some r) (f := get_real_type ge) in Hesrs.
        rewrite Forall2_sequence_iff in Hesrs.
        rewrite Forall2_map_r with (f:=normᵗ) in Hvsrs.
        rewrite Hesrs; autounfold with option_monad; cbn;
          solve_ex; split; auto.
      - intros H; inv H.
    Qed.

    Hint Rewrite map_length : core.
    Local Hint Resolve Forall2_length : core.

    Theorem record_sound : forall tag es dir,
        Forall (fun e => (ge,this,Δ,Γ) ⊢ₑ e) (map snd es) ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpRecord es)
          (TypRecord (map (fun '(x,e) => (x,typ_of_expr e)) es)) dir.
    Proof using.
      intros i es d Hes.
      autounfold with * in *; cbn in *.
      intros Hgrt Hged Hgok Hok Hise rob st Hrobsome Hrob Hg.
      inversion Hok; subst; inversion H1; subst; inversion H4; subst.
      rename H1 into Htokrec; rename H4 into Heokrec;
        rename H0 into Htokes; rename H2 into Heokes.
      inversion Hise; subst; inversion H1; subst; inversion H4; subst.
      unfold Basics.compose in *.
      rename H1 into Hisetrec; rename H4 into Hispe;
        rename H0 into Utoees; rename H2 into Hisetes;
          rename H3 into Ues; rename H5 into Hisees.
      rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (st:=st).
      pose proof (fun e HInnes Hok Hise =>
                    Hes e HInnes Hgrt Hged Hgok Hok Hise Hrobsome Hrob Hg)
        as H; clear Hes; rename H into Hes.
      rewrite <- Forall_forall,Forall_map in Hes.
      unfold Basics.compose in Hes; cbn in Hes.
      pose proof Forall_impl_Forall
           _ _ _ _ Hes Heokes as H; clear Hes Heokes.
      pose proof Forall_impl_Forall
           _ _ _ _ H Hisees as Hes; clear H Hisees.
      apply Forall_and_inv in Hes as [Hrnes Htyps].
      apply Forall_and_inv in Htyps as [Htyps _]; split; [| split].
      - clear Htyps.
        rewrite Forall_exists_factor in Hrnes.
        destruct Hrnes as [vs Hvs].
        exists (ValBaseStruct (combine (map P4String.str (map fst es)) vs)).
        constructor. unfold AList.all_values, P4String.clear_AList_tags.
        rewrite Forall2_conj,
        Forall2_map_both with
            (f:=fst) (g:=fst),Forall2_map_both with (f:=snd) (g:=snd).
        rewrite map_snd_combine by (autorewrite with core; eauto).
        rewrite map_fst_combine by (autorewrite with core; eauto).
        rewrite Forall2_eq,map_fst_map,map_snd_map,map_id;split;auto.
        rewrite <- ForallMap.Forall2_map_l; assumption.
      - clear Hrnes.
        intros v Hev; inversion Hev; subst.
        rename kvs' into xvs; rename H6 into Hxvs.
        unfold AList.all_values,P4String.clear_AList_tags in Hxvs.
        rewrite Forall2_conj in Hxvs.
        destruct Hxvs as [Hfsteq Hxvs].
        rewrite Forall2_map_both,Forall2_eq,map_fst_map in Hfsteq.
        rewrite map_pat_both, <- ForallMap.Forall2_map_l in Hxvs; cbn in *.
        rewrite Forall_forall in Htyps.
        apply forall_Forall2 with (bs := map snd xvs) in Htyps;
          autorewrite with core; eauto.
        rewrite <- Forall2_map_r in Htyps.
        pose proof Forall2_impl
             _ _ _ _ _ _ Htyps Hxvs as H; clear Htyps Hxvs.
        apply Forall2_ex_factor in H as [rs Hrs].
        rewrite Forall3_conj_sep in Hrs.
        destruct Hrs as [Hesrs Hxvsrs].
        rewrite ForallMap.Forall2_map_l with
            (R:=fun e t => get_real_type ge (typ_of_expr e) = Some t)
            (f:=snd) in Hesrs.
        rewrite ForallMap.Forall2_map_l with
            (R:=fun t r => get_real_type ge t = Some r)
            (f:=typ_of_expr) in Hesrs.
        rewrite ForallMap.Forall2_map_l with
            (R:=fun ro r => ro = Some r) (f:=get_real_type ge) in Hesrs.
        rewrite Forall2_sequence_iff in Hesrs.
        rewrite map_pat_combine,map_id.
        pose proof @map_bind_pair _ option_monad_inst as Hmbp.
        unfold ">>|",">>=",mbind,mret in Hmbp.
        autounfold with option_monad in *.
        rewrite Hmbp; clear Hmbp.
        exists (TypRecord (combine (map fst es) rs)); cbn; split.
        + clear xvs Δ Γ this i d rob st Hged Hok Hise Hrob Hrobsome Hgok
                Hg Htokrec Heokrec Htokes Hev Hfsteq Hxvsrs.
          clear Hgrt Hisetrec Hispe Hisetes Utoees Ues.
          generalize dependent rs.
          induction es as [| [x e] es IHes];
            intros [| r rs] Hrs; cbn in *; try discriminate;
              try specialize IHes with rs;
              repeat match_some_inv; some_inv; try reflexivity.
          intuition; match_some_inv; some_inv; reflexivity.
        + constructor.
          * rewrite <- Forall2_sequence_iff in Hesrs.
            repeat rewrite <- ForallMap.Forall2_map_l in Hesrs.
            clear - Utoees Hesrs.
            pose proof @AListUtil.key_unique_map_values as H'.
            unfold AListUtil.map_values in H'.
            rewrite H' in Utoees; rewrite H'; clear H'.
            rewrite AListUtil.key_unique_combine
              by eauto using Forall2_length.
            assumption.
          *  unfold AList.all_values,P4String.clear_AList_tags.
             rewrite Forall2_conj,
             Forall2_map_both
               with (f:=fst) (g:=fst),
                    Forall2_map_both with (f:=snd) (g:=snd).
             repeat rewrite map_fst_map.
             repeat rewrite map_snd_map.
             repeat rewrite map_id.
             rewrite map_fst_combine by
                 (apply sequence_length in Hesrs;
                  autorewrite with core in *; auto).
             rewrite map_snd_combine by
                 (apply sequence_length in Hesrs;
                  autorewrite with core in *; auto).
             rewrite Forall2_eq, <- Forall2_map_both; auto.
      - intros H; inv H.
    Qed.

    Local Hint Resolve eval_unary_op_preserves_typ : core.

    Theorem unary_op_sound : forall tag o e t dir,
        unary_type o (typ_of_expr e) t ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpUnaryOp o e) t dir.
    Proof using.
      intros i o e t d Hut He; autounfold with * in *; cbn in *.
      intros Hgrt Hdelta Hgok Hok Hise rob st Hrobsome Hrob Hg.
      inversion Hok; subst; inversion H4; subst.
      rename H1 into Hokt; rename H4 into Hokuop; rename H0 into Hoke.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hiset; rename H4 into Hispe; rename H0 into Hisee.
      pose proof He
           Hgrt Hdelta Hgok Hoke Hisee _ _ Hrobsome Hrob Hg
        as [[v Hev] [Hvt _]].
      apply unary_type_eq in Hut as Hut_eq; subst t.
      clear He Hgrt Hdelta Hoke Hisee; split; [| split].
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
                    | H1: _ = ?a, H2: _ = ?a
                      |- _ => rewrite <- H1 in H2; clear H1
                    end;
                try discriminate. }
        destruct H as [v'' Hv'']; eauto.
      - clear v Hev; intros v Hev.
        inversion Hev; subst; simpl in *.
        pose proof Hvt _ H7 as (r & Hr & Hvr); clear Hvt H7.
        pose proof exec_val_preserves_typ
             _ _ _ H8 _ Hvr as Hargvr; clear H8 Hvr.
        assert (Hr_eq : typ_of_expr e = r /\ r = normᵗ r).
        { inversion Hut; subst; try inv_numeric; try inv_numeric_width;
            try match goal with
                | H: _ = typ_of_expr _ |- _ => rewrite <- H in *
                end; cbn in *; try some_inv; auto. }
        destruct Hr_eq as [Het Hrr]; subst r.
        rewrite Hrr in Hut; eauto.
      - intro H; inv H.
    Qed.

    Local Hint Resolve eval_binary_op_preserves_typ : core.
    Local Hint Resolve binary_type_get_real_type : core.
    Local Hint Resolve binary_type_normᵗ : core.

    Definition binary_op_ctk_cases
               (o : OpBin) (e₁ e₂ : @Expression tags_t) : Prop :=
    match o with
    | Div
    | Mod => (exists bits,
                ⟨ this, ge_const ge, e₂ ⟩ ⇝ ValBaseBit bits /\
                (0 < snd (BitArith.from_lbool bits))%Z) \/
            exists z₁ z₂,
              ⟨ this, ge_const ge, e₁ ⟩ ⇝ ValBaseInteger (Zpos z₁) /\
              ⟨ this, ge_const ge, e₂ ⟩ ⇝ ValBaseInteger (Zpos z₂)
    | Shl
    | Shr => exists v,
            ⟨ this, ge_const ge, e₂ ⟩ ⇝ v /\
            match v with
            | ValBaseBit _
            | ValBaseInteger (Z0 | Zpos _) => True
            | _ => False
            end
    | _ => True
    end.

    Theorem binary_op_sound : forall tag o t e1 e2 dir,
        binary_op_ctk_cases o e1 e2 ->
        binary_type o (typ_of_expr e1) (typ_of_expr e2) t ->
        (ge,this,Δ,Γ) ⊢ₑ e1 ->
        (ge,this,Δ,Γ) ⊢ₑ e2 ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpBinaryOp o e1 e2) t dir.
    Proof using.
      intros i o t e1 e2 d Hctk Hbt He1 He2.
      autounfold with * in *; cbn in *.
      intros Hgrt Hged Hgok Hok His rob st Hrobsome Hrob Hgst.
      inversion Hok; subst; inversion H4; subst.
      rename H1 into Hokt; rename H4 into Heokb;
        rename H2 into Hoke1; rename H5 into Hoke2.
      inversion His; subst; inversion H4; subst.
      rename H1 into Hiset; rename H4 into Hispe;
        rename H2 into Hisee1; rename H5 into Hisee2.
      pose proof He1
           Hgrt Hged Hgok Hoke1 Hisee1 _ _ Hrobsome Hrob Hgst
        as [[v1 Hev1] [Hvt1 _]].
      pose proof He2
           Hgrt Hged Hgok Hoke2 Hisee2 _ _ Hrobsome Hrob Hgst
        as [[v2 Hev2] [Hvt2 _]].
      clear He1 He2 Hgrt Hged Hoke1 Hoke2 Hisee1 Hisee2 Hgst;
        split; [| split].
      - apply Hvt1 in Hev1 as Hev1';
          destruct Hev1' as (r1 & Hr1 & Hvr1); clear Hvt1.
        apply Hvt2 in Hev2 as Hev2';
          destruct Hev2' as (r2 & Hr2 & Hvr2); clear Hvt2.
        assert (Hv1': exists v1', sval_to_val rob v1 v1')
          by eauto using exec_val_exists.
        assert (Hv2': exists v2', sval_to_val rob v2 v2')
          by eauto using exec_val_exists.
        destruct Hv1' as [v1' Hv1']; destruct Hv2' as [v2' Hv2'].
        assert (Hvr1': ⊢ᵥ v1' \: normᵗ r1) by eauto.
        assert (Hvr2': ⊢ᵥ v2' \: normᵗ r2) by eauto.
        pose proof binary_type_get_real_type
             _ _ _ _ _ _ _ Hbt Hr1 Hr2 as (r & Hr & Hbr).
        apply binary_type_normᵗ in Hbr.
        assert (Hctk': binary_op_ctk_cases' o v1' v2').
        { unfold binary_op_ctk_cases in Hctk.
          destruct ge as [gf gt gs gi Σ ee] eqn:Heqge; cbn in *.
          clear d Hok His.
          assert (Hrob' : forall b b', rob (Some b) b' -> b = b') by firstorder.
          destruct o; cbn in *; trivial;
            try (destruct Hctk as
                    [(bits & He2 & Hbits) | (z1 & z2 & Hz1 & Hz2)];
                 [ assert (Heqv2: v2 = ValueBaseMap Some (ValBaseBit bits))
                   by eauto using CTK_exec_expr_agree; subst;
                   inv Hv2'; cbn in *;
                   match goal with
                   | H: Forall2 rob (map Some _) _
                     |- _ => rewrite <- ForallMap.Forall2_map_l,Forall2_forall in H;
                           destruct H as [Hlen HF2];
                           pose proof
                                (conj
                                   Hlen
                                   (fun u v Huv =>
                                      Hrob' u v (HF2 u v Huv))) as H';
                           rewrite <- Forall2_forall,Forall2_eq in H';
                           subst;
                           destruct v1' as
                               [| | [| |] | | | | | | | | | | | | |];
                           try assumption
                   end
                 | assert (Heqv1:
                             v1 =
                             ValueBaseMap
                               Some
                               (ValBaseInteger (Z.pos z1)))
                   by eauto using CTK_exec_expr_agree; subst;
                   assert (Heqv2:
                             v2 =
                             ValueBaseMap
                               Some (ValBaseInteger (Z.pos z2)))
                     by eauto using CTK_exec_expr_agree; subst;
                   inv Hv1'; inv Hv2'; trivial ]);
            try (destruct Hctk as (v & Hctkv & Hv);
                 assert (Heqv2: v2 = ValueBaseMap Some v)
                   by eauto using CTK_exec_expr_agree; subst;
                 rewrite sval_to_val_eval_val_to_sval_iff in Hv2';
                 subst; assumption). }
        assert (Hv: exists v, Ops.eval_binary_op o v1' v2' = Some v)
          by eauto using eval_binary_op_ex.
        destruct Hv as [v Hv].
        assert (Hv': exists v', val_to_sval v v') by eauto; eauto.
      - clear v1 v2 Hev1 Hev2; intros v Hev; inversion Hev; subst.
        apply Hvt1 in H7 as (r1 & Hr1 & Hvr1); clear Hvt1.
        apply Hvt2 in H9 as (r2 & Hr2 & Hvr2); clear Hvt2.
        assert (Hlargvr1: ⊢ᵥ largv \: normᵗ r1)
          by eauto.
        assert (Hrargvr2: ⊢ᵥ rargv \: normᵗ r2)
          by eauto.
        assert (Hr :
                  exists r, get_real_type ge t = Some r /\
                       binary_type o r1 r2 r)
          by eauto using binary_type_get_real_type.
        destruct Hr as (r & Hr & Hbr); eauto 6.
      - intros H; inv H.
    Qed.

    Ltac solve_ex' :=
      match goal with
      | |- exists rt, Some ?t = Some rt
        => exists t; cbn; eauto
      end.

    Theorem cast_sound : forall tag e t dir,
        cast_type (typ_of_expr e) t ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpCast t e) t dir.
    Proof using.
      intros i e t dir Hcast He.
      intros Hgrt Hdlta Hgok Hok Hise rob st Hrobsome Hrob Hg; cbn in *.
      inversion Hok; subst. inversion H4; subst.
      rename H4 into Hokcast; rename H3 into Htoeok; rename H1 into Hokt. clear H2.
      inversion Hise; subst. inversion H4; subst.
      rename H1 into Hist; rename H4 into Hiscast; rename H3 into Hise'. clear H2.
      pose proof He Hgrt Hdlta as [[sv Hesv] [Hsv Helsv]]; eauto.
      split; [| split].
      - clear Helsv. destruct (Hsv _ Hesv) as [rt [Hreal Hsvrt]].
        destruct (exec_val_exists _ Hrob sv) as [v Hexec].
        pose proof ok_get_real_type_ex _ _ Hokt _ Hdlta as [r hr].
        assert (heval_cast: exists newv, eval_cast r v = Some newv).
        { pose proof exec_val_preserves_typ
            _ _ _ Hexec _ Hsvrt as Hvrt.
          assert (hcast : cast_type rt r) by eauto using get_real_cast_type.
          assert (hcast_norm : cast_type (normᵗ rt) (normᵗ r))
            by auto using cast_type_normᵗ.
          replace r with (normᵗ r)
            by eauto using cast_type_normᵗ_same.
          eauto using eval_cast_ex. }
        firstorder eauto.
      - clear dependent sv. clear Helsv.
        intros sv hesv. inv hesv.
        apply Hsv in H6 as (r & hgetr & holdvr).
        assert (hcast : cast_type r real_typ) by
          eauto using get_real_cast_type.
        assert (hcast_norm : cast_type (normᵗ r) (normᵗ real_typ)) by
          eauto using cast_type_normᵗ.
        replace real_typ with (normᵗ real_typ) in H10
          by eauto using cast_type_normᵗ_same.
        assert (hnewvr: ⊢ᵥ newv \: normᵗ real_typ)
          by eauto using eval_cast_types. eauto.
      - intros Hlv; inv Hlv; contradiction.
    Qed.

    Theorem enum_member_sound : forall tag X M E mems dir,
        IdentMap.get (P4String.str X) (ge_typ ge) =
        Some (TypEnum E None mems) ->
        List.In (P4String.str M) (List.map P4String.str mems) ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression
          tag (ExpTypeMember X M)
          (TypEnum E None mems) dir.
    Proof using.
      intros tag X M E mems dir Hget Hmem.
      soundtac; split; auto; inv Hrn.
      - rewrite Hget in H7; some_inv; auto.
      - rewrite Hget in H11; some_inv.
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
    Proof using.
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
    Proof using.
      intros tag err dir; soundtac.
    Qed.

    Local Hint Resolve member_get_member_ex : core.
    Local Hint Resolve get_member_types : core.

    Theorem other_member_sound : forall tag e x ts t dir,
        P4String.str x <> "size"%string ->
        P4String.str x <> "lastIndex"%string ->
        (P4String.str x =? "next")%string = false ->
        member_type ts (typ_of_expr e) ->
        AList.get ts x = Some t ->
        (ge,this,Δ,Γ) ⊢ₑ e ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpExpressionMember e x) t dir.
    Proof using.
      intros i e x ts t dir hsize hlstdx Hnxt Hmem Hts He.
      intros Hgrt Hdlta Hgok Hok Hise rob st Hrobsome Hrob Hg; cbn in *.
      inversion Hok; subst; inversion H4; subst.
      rename H4 into Hokmem; rename H0 into Htoeok; rename H1 into Hokt.
      inversion Hise; subst; inversion H4; subst.
      rename H1 into Hist; rename H4 into Hismem; rename H0 into Hise'.
      pose proof He Hgrt Hdlta as [[v Hev] [Hv Helv]]; eauto.
      split; [| split].
      - clear Helv.
        assert (Hget: exists v', get_member v (P4String.str x) v').
        { apply Hv in Hev as (r & Hr & Hvr).
          pose proof get_real_member_type _ _ _ _ Hr Hmem as [rs Hmemrs].
          apply member_type_normᵗ in Hmemrs as Hmemrs_norm.
          assert (Hlem3' : exists r',
                     AList.get
                       (map (fun '(x, t) => (x, normᵗ t)) rs)
                       x = Some r').
          { clear i dir Γ Δ He Hdlta Hok Hrobsome
                  Hg Hokt Hokmem Htoeok v Hvr Hise Hgok
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
            unfold option_map,option_bind in Hlem.
            unfold ">>|",">>=",mbind,mret,option_monad_inst,
            option_bind in *.
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
          destruct Hlem3' as [r' Hr'].
          rewrite P4String.get_clear_AList_tags in Hr'; eauto. }
        destruct Hget as [v' Hv'].
        exists v'; eapply exec_expr_other_member; eauto.
      - clear v Hev Helv; intros v Hev. inversion Hev; subst.
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
        unfold option_map,option_bind in Hlem.
        assert (Hlem3' :
                  AList.get
                    (map (fun '(x, t) => (x, normᵗ t)) rs)
                    x =
                  Some (normᵗ r')).
        { clear H8 Hvr Hev v Hist Htoeok Hrobsome Hgok
                Hismem Hise' Hg rob Hrob st Hise Hok Hdlta Hgrt He
                Hokt Hokmem dir Δ Γ i e Hmem Hr r Hmemrs.
          unfold ">>|",">>=",mbind,mret,option_monad_inst,
          option_bind in *.
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
        rewrite P4String.get_clear_AList_tags in Hlem3'; eauto.
      - intros Hlv; inv Hlv.
        apply Helv in H6 as [(lv & s & Hlvs) Helv']; clear Helv; split; eauto.
        clear lv v s Hlvs Hev.
        intros lv s Hlvs; inv Hlvs;
          try (rewrite H10 in Hnxt; discriminate).
        apply Helv' in H11 as Hlvt.
        rewrite P4String.get_clear_AList_tags in Hts.
        destruct Hlvt as (r & hr & hlvr).
        pose proof get_real_member_type _ _ _ _ hr Hmem as [rs hrs].
        pose proof member_type_get_real_type _ _ _ _ _ Hmem hrs hr as hseq.
        assert (hrt: exists rt,
                   get_real_type ge t = Some rt /\
                     AList.get (P4String.clear_AList_tags rs) (P4String.str x) = Some rt).
        { clear dependent e. clear dependent Γ. clear dependent rob.
          clear dependent Δ. clear dependent s. clear dependent i.
          clear dependent dir. clear dependent st. clear dependent lv0.
          clear dependent r. clear dependent this.
          clear hsize hlstdx Hgrt Hist H2 H5 Hnxt H10.
          destruct x as [ix x]; cbn in*. clear ix.
          generalize dependent t; generalize dependent rs.
          induction ts as [| [[iy y] t] ts ih]; intros [| [[iz z] r] rs] hrs ty hty;
            cbn in *; try discriminate.
          - unfold option_bind at 1 2 in hrs.
            repeat match_some_inv; some_inv.
            unfold option_bind at 1 in hrs.
            match_some_inv.
          - unfold option_bind at 1 2 in hrs.
            repeat match_some_inv; some_inv.
            unfold option_bind at 1 in hrs.
            match_some_inv; some_inv.
            destruct (string_dec z x) as [hzx | hzx]; subst.
            + rewrite AList.get_eq_cons in hty by intuition; some_inv.
              rewrite AList.get_eq_cons by intuition.
              eauto.
            + rewrite AList.get_neq_cons in hty by firstorder.
              rewrite AList.get_neq_cons by firstorder.
              eauto. }
        destruct hrt as (rt & hrt & hxrt).
        exists rt; split; auto.
        apply typ_left_member with (τ:=normᵗ r) (τs:=AListUtil.map_values normᵗ rs); auto.
        + rewrite <- P4String.get_clear_AList_tags in *.
          rewrite AListUtil.get_map_values. rewrite hxrt; reflexivity.
        + unfold AListUtil.map_values. auto using member_type_normᵗ.
    Qed.

    Theorem array_size_sound : forall tag e x dir t w,
        (* P4Arith.BitArith.bound 32 w -> *)
        (* (w < 2 ^ 32)%N -> *)
        P4String.str x = "size"%string ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ e \: TypArray t w ->
        (ge,this,Δ,Γ)
          ⊢ₑ MkExpression tag (ExpExpressionMember e x) (TypBit 32) dir.
    Proof using.
      intros i e x dir t w Hstr [He Htyp].
      intros Hgrt Hdlta Hgok Hok Hise rob st Hrobsome Hrob Hg; cbn in *.
      inversion Hok; subst. inversion H4; subst.
      rename H4 into Hokmem; rename H0 into Htoeok; rename H1 into Hokt.
      inversion Hise; subst. inversion H4; subst.
      rename H1 into Hist; rename H4 into Hismem; rename H0 into Hise'.
      pose proof He Hgrt Hdlta as [[v Hev] [Hv Helv]]; eauto.
      split; [| split].
      - clear Helv.
        assert (Hget: exists v', get_member v (P4String.str x) v').
        { rewrite Hstr. apply Hv in Hev as (r & Hr & Hvr). rewrite <- Htyp in Hr. cbn in Hr.
          destruct (get_real_type ge t); simpl in Hr; inversion Hr. subst r. clear Hr.
          cbn in Hvr. inversion Hvr; subst. eexists. apply get_member_stack_size. }
        destruct Hget as [v' Hv']. exists v'; eapply exec_expr_other_member; eauto.
      - clear v Hev Helv; intros v Hev. inversion Hev; subst.
        exists (TypBit 32); split; auto. rewrite Hstr in H8.
        apply Hv in H7 as (r & Hr & Hvr); clear Hv. rewrite <- Htyp in Hr. cbn in Hr.
        destruct (get_real_type ge t); simpl in Hr; inversion Hr. subst r. clear Hr.
        cbn in Hvr. inversion Hvr; subst. inversion H8. constructor.
      - intros Hlv; inv Hlv; contradiction.
    Qed.

    Theorem array_last_index_sound : forall tag e x dir t w,
        P4String.str x = "lastIndex"%string ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ e \: TypArray t w ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpExpressionMember e x) (TypBit 32) dir.
    Proof using.
      intros i e x dir t w Hstr [He Htyp].
      intros Hgrt Hdlta Hgok Hok Hise rob st Hrobsome Hrob Hg; cbn in *.
      inversion Hok; subst. inversion H4; subst.
      rename H4 into Hokmem; rename H0 into Htoeok; rename H1 into Hokt.
      inversion Hise; subst. inversion H4; subst.
      rename H1 into Hist; rename H4 into Hismem; rename H0 into Hise'.
      pose proof He Hgrt Hdlta as [[v Hev] [Hv Helv]]; eauto.
      split; [| split].
      - clear Helv.
        assert (Hget: exists v', get_member v (P4String.str x) v').
        { rewrite Hstr. apply Hv in Hev as (r & Hr & Hvr). rewrite <- Htyp in Hr. cbn in Hr.
          destruct (get_real_type ge t) eqn:?S; simpl in Hr; inversion Hr. subst r. clear Hr.
          cbn in Hvr. inversion Hvr; subst.
          exists (if (n =? 0)%N then ValBaseBit (repeat None 32)
             else ValBaseBit (to_loptbool 32 (Z.of_N (n - 1)))).
          apply get_member_stack_last_index with (tags_t := tags_t).
          destruct (n =? 0)%N; reflexivity. }
        destruct Hget as [v' Hv']. exists v'; eapply exec_expr_other_member; eauto.
      - clear v Hev Helv; intros v Hev. exists (TypBit 32). split; auto.
        inversion Hev; subst. rewrite Hstr in H8.
        apply Hv in H7 as (r & Hr & Hvr); clear Hv. rewrite <- Htyp in Hr. cbn in Hr.
        destruct (get_real_type ge t) eqn:?S; simpl in Hr; inversion Hr. subst r. clear Hr.
        cbn in Hvr. inversion Hvr; subst. inversion H8; subst.
        destruct (n =? 0)%N.
        + simpl in H0. inv H0. constructor.
        + subst v. constructor.
      - intros Hlv; inv Hlv; contradiction.
    Qed.

    Theorem ternary_sound : forall tag e₁ e₂ e₃ t dir,
        (ge,this,Δ,Γ) ᵗ⊢ₑ e₁ \: TypBool ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ e₂ \: t ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ e₃ \: t ->
        (ge,this,Δ,Γ) ⊢ₑ MkExpression tag (ExpTernary e₁ e₂ e₃) t dir.
    Proof using.
      intros i e1 e2 e3 t d [He1 Ht1] [He2 Ht2] [He3 Ht3].
      autounfold with * in *; cbn in *.
      intros Hge Hged Hgok Hok Hise rob st Hrob Hreads Hgst.
      inv Hok; inv Hise. inv H4; inv H6.
      eapply He1 in H5 as [[sv1 Hesv1] [Hxe1 _]]; eauto; clear He1.
      eapply He2 in H7 as [[sv2 Hesv2] [Hxe2 _]]; eauto; clear He2.
      eapply He3 in H8 as [[sv3 Hesv3] [Hxe3 _]]; eauto; clear He3.
      split; [| split].
      - apply Hxe1 in Hesv1 as Hxe1'; clear Hxe1.
        destruct Hxe1' as (r1 & Hr1 & Hvr1).
        rewrite <- Ht1 in Hr1; cbn in *; some_inv.
        cbn in *; inv Hvr1.
        rename b into ob.
        assert (Hv1: exists v1, sval_to_val rob (ValBaseBool ob) v1)
          by eauto using exec_val_exists.
        destruct Hv1 as [v1 Hv1]; inversion Hv1; subst; rename b' into b.
        exists (if b then sv2 else sv3).
        econstructor; eauto.
        destruct b; auto.
      - clear dependent sv1. clear dependent sv2.
        clear dependent sv3.
        intros v Hev; inv Hev; inv H14.
        apply Hxe1 in H13 as (r1 & Hr1 & Hsvr1).
        rewrite <- Ht1 in Hr1; cbn in *; some_inv; cbn in *.
        destruct b.
        + firstorder.
        + rewrite Ht3; firstorder.
      - intros Hlv; inv Hlv.
    Qed.
  End ExprTyping.

  Local Hint Constructors exec_stmt : core.
  Local Hint Constructors exec_block : core.
  Local Hint Constructors exec_write : core.
  Local Hint Constructors exec_read : core.
  Local Hint Unfold stmt_types : core.
  Local Hint Resolve sub_gamma_expr_refl : core.
  Local Hint Resolve gamma_stmt_prop_sub_gamma : core.
  Local Hint Resolve gamma_var_domain_impl_real_norm : core.
  Local Hint Resolve gamma_real_norm_impl_var_domain : core.
  Local Hint Resolve gamma_var_val_type_impl_real_norm : core.
  Local Hint Resolve gamma_real_norm_impl_var_val_type : core.
  Local Hint Resolve exec_write_ex : core.
  Local Hint Resolve exec_write_preservation : core.
  Local Hint Resolve ValueBaseMap_preserves_type : core.

  Section StmtTyping.
    Context `{dummy : Inhabitant tags_t}.
    Variable (Γ : @gamma_stmt tags_t).

    Theorem assign_sound_expr : forall tag e₁ e₂,
        typ_of_expr e₁ = typ_of_expr e₂ ->
        lexpr_ok e₁ ->
        is_expr e₂ ->
        (ge,this,Δ,Γ) ⊢ₑ e₁ ->
        (ge,this,Δ,Γ) ⊢ₑ e₂ ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatAssignment e₁ e₂) StmUnit ⊣ Γ.
    Proof using.
      cbn. intros i e1 e2 Hte1e2 Hlvoke1 Hisexpr2 He1 He2.
      autounfold with * in *.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hread Hgst.
      split; auto.
      unfold gamma_stmt_prop in Hgst.
      destruct Hgst as [Hgste Hgstf].
      inv Hoks; inv Hiss; inv H0; inv H1.
      rename H3 into Hoke1; rename H4 into Hoke2;
        rename H2 into Hise1; rename H5 into Hise2.
      pose proof He1 Hge Hged Hgok Hoke1 Hise1 _ _ Hrob Hread Hgste as Het1; clear He1.
      destruct Het1 as [[sv1 Hev1] [He1 He1lv]].
      pose proof He1lv Hlvoke1 as [(lv1 & s1 & Helvs1) Helv1]; clear He1lv.
      pose proof He2 Hge Hged Hgok Hoke2 Hisexpr2 _ _ Hrob Hread Hgste as Het2; clear He2.
      destruct Het2 as [[sv2 Hev2] [He2 _]]; split.
      - assert (Hsv2: exists v2, sval_to_val rob sv2 v2)
          by eauto using exec_val_exists.
        destruct Hsv2 as [v2 Hsv2].
        assert (Hxd2: exec_expr_det ge rob this st e2 v2) by eauto.
        destruct (is_continue s1) eqn:Hiscont.
        + assert (Hst': exists st', exec_write st lv1 (ValueBaseMap Some v2) st').
          { pose proof He2 _ Hev2 as (r2 & hr2 & hsvr2).
            pose proof exec_val_preserves_typ
              _ _ _ Hsv2 _ hsvr2 as hvrt2.
            pose proof Helv1 _ _ Helvs1 as (r & hr & hlvr).
            rewrite Hte1e2, hr2 in hr; some_inv.
            replace (fun x : typ => normᵗ (try_get_real_type ge x)) with
              (normᵗ ∘ try_get_real_type ge) in hlvr by reflexivity.
            unfold gamma_expr_ok, gamma_expr_prop,gamma_var_prop in *.
            destruct Γ as [[Gv Gc] Gf Gext]. cbn in *.
            destruct Hgok as [hgok _].
            destruct Hgste as [[hGdom hG] _].
            assert (gamma_var_domain
                      (FuncAsMap.map_map (normᵗ ∘ try_get_real_type ge) Gv) st)
              as hGdom' by eauto.
            assert (gamma_var_val_typ_real_norm
                      (FuncAsMap.map_map (normᵗ ∘ try_get_real_type ge) Gv) st ge)
              as hGrn by eauto.
            eapply exec_write_ex; eauto. }
          destruct Hst' as [st' Hst']; exists st', s1.
          eapply exec_stmt_assign; eauto.
          rewrite Hiscont; assumption.
        + exists st, s1; eapply exec_stmt_assign; eauto.
          rewrite Hiscont; reflexivity.
      - clear dependent sv1; clear dependent sv2;
          clear dependent lv1; clear s1.
        intros st' sig Hxs; inversion Hxs; subst.
        + unfold gamma_stmt_prop; split; try assumption.
          unfold gamma_expr_prop in *.
          destruct Hgste as [Hgstvar Hgstconst];
            split; try assumption. inv H5.
          destruct (is_continue sig) eqn:?H; [| subst; assumption].
          pose proof He2 _ H as (r2 & hr2 & hsvr2).
          pose proof Helv1 _ _  H8 as (r1 & hr1 & hlvr1).
          rewrite Hte1e2,hr2 in hr1. some_inv.
          assert (⊢ᵥ v \: normᵗ r1) by eauto.
          assert (hsvr1: ⊢ᵥ sv \: normᵗ r1) by eauto.
          replace (fun x : typ => normᵗ (try_get_real_type ge x)) with
            (normᵗ ∘ try_get_real_type ge) in hlvr1 by reflexivity.
          unfold gamma_expr_ok, gamma_expr_prop,gamma_var_prop in *.
          destruct Γ as [[Gv Gc] Gf Gext]. cbn in *.
          destruct Hgok as [hgok _].
          destruct Hgstvar as [hGdom hG].
          assert (gamma_var_domain
                    (FuncAsMap.map_map (normᵗ ∘ try_get_real_type ge) Gv) st)
            as hGdom' by eauto.
          assert (gamma_var_val_typ_real_norm
                    (FuncAsMap.map_map (normᵗ ∘ try_get_real_type ge) Gv) st ge)
            as hGrn by eauto.
          pose proof exec_write_preservation
            _ (ge_typ ge) _ _ _ _ _ _ hGdom' hGrn H10 hlvr1 hsvr1
            as [hdomst' hGst']. eauto.
        + inv Hisexpr2. inv H7; inv H0.
    Qed.

    Theorem assign_sound_call : forall tag e₁ e₂,
        typ_of_expr e₁ = typ_of_expr e₂ ->
        lexpr_ok e₁ ->
        is_call e₂ ->
        (ge,this,Δ,Γ) ⊢ₑ e₁ ->
        (ge,this,Δ,Γ) ⊢ᵪ e₂ ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatAssignment e₁ e₂) StmUnit ⊣ Γ.
    Proof using.
      cbn. intros i e1 e2 Hte1e2 Hlvoke1 Hiscalle2 He1 He2.
      autounfold with * in *.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hread Hgst.
      split; auto.
      inv Hoks; inv Hiss; inv H0; inv H1.
      rename H3 into Hoke1; rename H4 into Hoke2;
        rename H2 into Hise1; rename H5 into Hise2.
      unfold call_types in He2.
      pose proof He1 Hge Hged Hgok Hoke1 Hise1 _ _ Hrob Hread (proj1 Hgst) as Het1; clear He1.
      destruct Het1 as [[sv1 Hev1] [He1 He1lv]].
      pose proof He1lv Hlvoke1 as [(lv1 & s1 & Helvs1) Helv1]; clear He1lv.
      pose proof He2 Hge Hged Hgok Hoke2 Hiscalle2 _ st Hrob Hread Hgst as Het2; clear He2.
      destruct Het2 as ((st' & sig & he2) & het2). split.
      - destruct (Helv1 _ _ Helvs1) as (r1 & hr1 & hlvr1); clear Helv1.
        admit.
      - clear dependent lv1. clear dependent sv1. clear s1.
        clear dependent st'. clear sig.
        intros st' sig hxs. inv hxs.
        + inv Hiscalle2. inv H. inv H5. inv H.
        + if_destruct.
    Admitted.

    Theorem cond_sound : forall tag e s₁ s₂ Γ₁,
        (ge,this,Δ,Γ) ᵗ⊢ₑ e \: TypBool ->
        (ge,this,Δ,Γ) ⊢ₛ s₁ ⊣ Γ₁ ->
        predop (fun s₂ => exists Γ₂, (ge,this,Δ,Γ) ⊢ₛ s₂ ⊣ Γ₂) s₂ ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatConditional e s₁ s₂)
          (match s₂ with
           | None    => typ_of_stmt s₁
           | Some s₂ => lub_StmType (typ_of_stmt s₁) (typ_of_stmt s₂)
           end) ⊣ Γ.
    Proof using.
      cbn. intros i e s1 s2 Γ₁ [He Het] Hs1 Hs2.
      autounfold with * in *.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hread Hgst.
      split; auto.
      inv Hoks; inv Hiss. inv H0; inv H1.
      pose proof He Hge Hged Hgok H4 H3 _ _ Hrob Hread (proj1 Hgst)
        as [[sv Hesv] [He' _]]; clear He H4 H3.
      pose proof Hs1 Hge Hged Hgok H5 H7 _ _ Hrob Hread Hgst
        as [HΓ₁ [(st1 & sig1 & Hxs1) Hs1']]; clear Hs1 H5 H7.
      assert (Hv: exists v, sval_to_val rob sv v)
        by eauto using exec_val_exists.
      destruct Hv as [v Hv].
      assert (Hxed: exec_expr_det ge rob this st e v) by eauto.
      rewrite <- Het in He'; cbn in He'.
      apply He' in Hesv as (r & Hr & Hsvr).
      some_inv; cbn in Hsvr; inv Hsvr; inv Hv.
      destruct s2 as [s2 |]; inv Hs2; inv H6; inv H8.
      - destruct H1 as [Γ₂ Hs2].
        pose proof Hs2 Hge Hged Hgok H2 H3 _ st Hrob Hread Hgst
          as [HΓ₂ [(st2 & sig2 & Hxs2) Hs2']]; clear Hs2 H2 H3.
        split.
        + destruct b'; eauto.
        + clear dependent st1. clear dependent st2.
          clear dependent b'. clear b sig1 sig2.
          intros st' sig Hxs. inv Hxs.
          destruct b; eauto.
      - split.
        + destruct b'; eauto.
          exists st,SContinue. econstructor; eauto; cbn.
          unfold empty_statement; auto.
        + clear dependent st1. clear dependent b'. clear b sig1.
          intros st' sig Hxs; inv Hxs.
          inv H7. inv H0. destruct b; eauto.
          inv H8; assumption.
    Qed.

    Theorem exit_sound : forall tag,
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag StatExit StmVoid ⊣ Γ.
    Proof using.
      unfold stmt_types; intros; repeat (split; [eauto; assumption |]).
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.

    Theorem return_sound : forall tag e,
        predop (fun e => (ge,this,Δ,Γ) ⊢ₑ e) e ->
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag (StatReturn e) StmVoid ⊣ Γ.
    Proof using.
      cbn. intros i e He.
      autounfold with * in *.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hreads Hgst.
      split; auto.
      destruct e as [e |]; inv He; cbn in *.
      - inv Hoks; inv Hiss. inv H1; inv H2. inv H3; inv H1.
        pose proof H0 Hge Hged Hgok H2 H3 _ _ Hrob Hreads (proj1 Hgst)
          as [[sv Hesv] [He _]]; clear H0; split.
        + eauto using exec_stmt_return_some.
          assert (Hv: exists v, sval_to_val rob sv v)
            by eauto using exec_val_exists.
          destruct Hv as [v Hv]; eauto.
        + clear dependent sv.
          intros st' sig Hxs; inv Hxs; assumption.
      - split; eauto.
        intros st' sig Hxs; inv Hxs; assumption.
    Qed.

    Theorem empty_sound : forall tag,
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag StatEmpty StmUnit ⊣ Γ.
    Proof using.
      unfold stmt_types; intros; repeat (split; [eauto; assumption |]).
      intros ? ? Hrn; inversion Hrn; subst; eauto.
    Qed.

    Theorem block_sound : forall Γ' tag blk t,
        Block_StmTypes blk t ->
        (ge,this,Δ,Γ) ⊢ᵦ blk ⊣ Γ' ->
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag (StatBlock blk) t ⊣ Γ.
    Proof using.
      intros Γ' tag blk t Hblk. revert dependent Γ'.
      induction Hblk; intros Γ' Hsblk Hge Hged Hgok Hoks Hiss rob st Hrob Hreads Hgsp;
        simpl in *; split; auto.
      - split.
        + do 2 eexists. do 2 constructor.
        + intros st' sig Hempty. inv Hempty. inv H6. auto.
      - inv Hoks. inv H1. inv Hiss. inv H1.
        specialize (Hsblk Hge Hged Hgok H0 H2 _ _ Hrob Hreads Hgsp).
        destruct Hsblk as [Hsge [Hsub [[st' [sig Hpro]] Hpre]]]. inv Hpro. split.
        + do 2 eexists. constructor. econstructor; eauto.
        + intros st'1 sig Hstmt. inv Hstmt. apply Hpre in H10.
          eapply gamma_stmt_prop_sub_gamma; eauto.
      - inv Hoks. inv H1. inv Hiss. inv H1.
        specialize (Hsblk Hge Hged Hgok H2 H3 _ _ Hrob Hreads Hgsp).
        destruct Hsblk as [Hsge [Hsub [[st' [sig Hpro]] Hpre]]]. inv Hpro. split.
        + do 2 eexists. constructor. econstructor; eauto.
        + intros st'1 sig Hstmt. inv Hstmt. apply Hpre in H11.
          eapply gamma_stmt_prop_sub_gamma; eauto.
    Qed.

    Theorem method_call_sound : forall tag e τs es,
        (ge,this,Δ,Γ)
          ⊢ᵪ MkExpression dummy_tags
          (ExpFunctionCall e τs es)
          TypVoid Directionless ->
        (ge,this,Δ,Γ) ⊢ₛ MkStatement tag (StatMethodCall e τs es) StmUnit ⊣ Γ.
    Proof using.
      intros tag e τs es Hcall.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hreads Hgsp. cbn [fst snd] in *.
      split; auto.
      assert (Δ ⊢okᵉ MkExpression dummy_tags (ExpFunctionCall e τs es) TypVoid Directionless)
        as hokcall.
      { inv Hoks. inv H0. repeat constructor; auto. }
      assert (is_call (MkExpression dummy_tags (ExpFunctionCall e τs es)
                         TypVoid Directionless)) as hiscall.
      { constructor. inv Hiss. inv H0. constructor; auto. }
      specialize (Hcall Hge Hged Hgok
                    hokcall hiscall rob st Hrob Hreads Hgsp).
      destruct Hcall as [[st' [sig Hpro]] Hpre]. split.
      - exists st', (force_continue_signal sig). econstructor. 1: apply Hpro. auto.
      - intros st'0 sig0 H1. inv H1. apply Hpre in H9. auto.
    Qed.

    Theorem direct_application_sound : forall tag τ τ' es,
        (ge,this,Δ,Γ)
          ⊢ᵪ MkExpression dummy_tags
          (ExpFunctionCall
             (direct_application_expression τ τ')
             nil es) TypVoid Directionless ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement tag
          (StatDirectApplication τ τ' es) StmUnit ⊣ Γ.
    Proof using.
      intros tag τ τ' es Hcall.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hreads Hgsp.
      cbn [fst snd] in *. split; auto.
      assert (Δ ⊢okᵉ MkExpression dummy_tags
                (ExpFunctionCall (direct_application_expression τ τ') [] es)
                TypVoid Directionless). {
        inv Hoks. inv H0. repeat constructor; auto. }
      assert (is_call
                (MkExpression dummy_tags
                   (ExpFunctionCall (direct_application_expression τ τ') [] es)
                   TypVoid Directionless)). {
        inv Hiss. inv H1. repeat constructor; auto. }
      specialize (Hcall Hge Hged Hgok H H0 rob st Hrob Hreads Hgsp).
      destruct Hcall as [[st' [sig Hpro]] Hpre]. split.
      - exists st', (force_continue_signal sig). econstructor. 1: apply Hpro. auto.
      - intros st'0 sig0 H1. inv H1. apply Hpre in H11. auto.
    Qed.

    Theorem stat_variable_init_sound : forall tag τ x l,
        PathMap.get (get_loc_path l) (var_gamma Γ) = None ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatVariable τ x None l) StmUnit
          ⊣ bind_typ_gamma_stmt l τ Γ.
    Proof using.
      cbn. intros i t x l Hl.
      autounfold with * in *.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hread Hgst.
      split; auto using bind_typ_gamma_stmt_sub_gamma.
      inv Hoks; inv Hiss. inv H0; inv H1. inv H7; inv H6.
      split.
      - assert (Hr: exists r, get_real_type ge t = Some r).
        { epose proof ok_get_real_type_ex as Hogre.
          unfold ok_get_real_type_ex_def in Hogre; eauto. }
        destruct Hr as [r Hr].
        assert (Huninit: exists sv, uninit_sval_of_typ (Some false) r = Some sv).
        { apply is_expr_typ_uninit_sval_of_typ; eauto.
          epose proof delta_genv_prop_ok_typ_nil as Hdgok.
          unfold delta_genv_prop_ok_typ_nil_def in Hdgok; eauto. }
        firstorder eauto.
      - intros st' sig Hxs; inv Hxs; inv H12.
        unfold gamma_stmt_prop in *.
        destruct Γ as [Γₑ gf] eqn:HeqΓ; cbn in *; split.
        + unfold gamma_expr_prop in *.
          destruct Hgst as [[Hvar Hconst] _].
          destruct Γₑ as [Γᵥ Γᵪ]; cbn in *; split; try assumption.
          clear Hconst. unfold gamma_var_prop in *.
          destruct Hvar as [Hdom Hvart]. split.
          * clear Hvart; unfold gamma_var_domain in *.
            intros l' t' Hlt'.
            unfold update_val_by_loc in *.
            specialize Hdom with (l:=l') (t:=t').
            destruct l' as [l' | l']; cbn in *; try discriminate.
            destruct st as [st ext].
            destruct l as [l | l];
              unfold update_memory,get_memory,get_loc_path,
              bind_var_typ in *; cbn in Hlt';
              pose proof list_eq_dec string_dec l' l as Hl'l;
              destruct Hl'l as [Hl'l | Hl'l]; subst;
              try rewrite PathMap.get_set_same in Hlt';
              try rewrite PathMap.get_set_same; eauto;
              try some_inv; cbn;
              try rewrite PathMap.get_set_diff in Hlt' by assumption;
              try rewrite PathMap.get_set_diff by assumption; eauto.
          * clear Hdom; unfold gamma_var_val_typ in *.
            intros l' t' sv' Hlt' Hlsv'.
            unfold update_val_by_loc in *.
            specialize Hvart with (l:=l') (t:=t') (v:=sv').
            destruct l' as [l' | l']; cbn in *; try discriminate.
            destruct st as [st ext].
            destruct l as [l | l];
              unfold update_memory,get_memory,get_loc_path,
              bind_var_typ in *; cbn in Hlt';
              pose proof list_eq_dec string_dec l' l as Hl'l;
              destruct Hl'l as [Hl'l | Hl'l]; subst;
              try rewrite PathMap.get_set_same in Hlt';
              try  rewrite PathMap.get_set_same in Hlsv';
              try rewrite PathMap.get_set_diff in Hlt' by assumption;
              try rewrite PathMap.get_set_diff in Hlsv' by assumption;
              cbn in *; unfold ok in *;
              repeat some_inv;
              eauto 6 using uninit_sval_of_typ_val_typ.
        + destruct Hgst as [HΓₑ [Hgfdom Hgft]].
          unfold gamma_func_prop in *; split; auto.
    Qed.

    Theorem stat_variable_sound : forall tag τ x e l,
        PathMap.get (get_loc_path l) (var_gamma Γ) = None ->
        (ge,this,Δ,Γ) ᵗ⊢ₑ e \: τ ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatVariable τ x (Some e) l) StmUnit
          ⊣ bind_typ_gamma_stmt l τ Γ.
    Proof using.
      cbn. intros i t x e l Hl He.
      autounfold with * in *.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hread Hgst.
      split; auto using bind_typ_gamma_stmt_sub_gamma.
      inv Hoks; inv Hiss. inv H0; inv H1.
      inv H6; inv H7. destruct He as [Het Het_eq].
      - pose proof Het Hge Hged Hgok H0 H1 _ _ Hrob Hread (proj1 Hgst)
          as [[sv Hesv] [He' _]]; clear Het H0 H1. split.
        + assert (Hv: exists v, sval_to_val rob sv v)
              by eauto using exec_val_exists.
            destruct Hv as [v Hv].
            assert (Hsv': exists sv', val_to_sval v sv') by eauto.
            destruct Hsv' as [sv' Hsv']; eauto 6.
        + intros st' sig Hxs; inv Hxs.
          * clear dependent sv. inv H13; inv H11.
            apply He' in H as (r & Hr & Hsvr); clear He'.
            assert (Hvr: ⊢ᵥ v \: normᵗ r) by eauto.
            assert (Hsvnr: ⊢ᵥ sv0 \: normᵗ r) by eauto.
            unfold gamma_stmt_prop in *.
            destruct Γ as [Γₑ gf]; cbn in *.
            destruct Hgst as [Hgst Hgf]; split; try assumption.
            destruct Γₑ as [Γᵥ Γᵪ]; cbn in *.
            unfold gamma_expr_prop in *; cbn.
            destruct Hgst as [Hvar Hconst]; split; try assumption.
            unfold gamma_var_prop in *.
            destruct Hvar as [Hdom Hvart]; split; cbn in *.
            -- unfold gamma_var_domain in *.
               intros l' t' Hlt'.
               unfold update_val_by_loc in *.
               specialize Hdom with (l:=l') (t:=t').
               destruct l' as [l' | l']; cbn in *; try discriminate.
               destruct st as [st ext].
               destruct l as [l | l];
                 unfold update_memory,get_memory,get_loc_path,
                 bind_var_typ in *; cbn in Hlt';
                 pose proof list_eq_dec string_dec l' l as Hl'l;
                 destruct Hl'l as [Hl'l | Hl'l]; subst;
                 try rewrite PathMap.get_set_same in Hlt';
                 try rewrite PathMap.get_set_same; eauto;
                 try some_inv; cbn;
                 try rewrite PathMap.get_set_diff in Hlt' by assumption;
                 try rewrite PathMap.get_set_diff by assumption; eauto.
            -- clear Hdom; unfold gamma_var_val_typ in *.
               intros l' t' sv' Hlt' Hlsv'.
               unfold update_val_by_loc in *.
               specialize Hvart with (l:=l') (t:=t') (v:=sv').
               destruct l' as [l' | l']; cbn in *; try discriminate.
               destruct st as [st ext].
               destruct l as [l | l];
                 unfold update_memory,get_memory,get_loc_path,
                 bind_var_typ in *; cbn in Hlt';
                 pose proof list_eq_dec string_dec l' l as Hl'l;
                 destruct Hl'l as [Hl'l | Hl'l]; subst;
                 try rewrite PathMap.get_set_same in Hlt';
                 try rewrite PathMap.get_set_same in Hlsv';
                 try rewrite PathMap.get_set_diff in Hlt' by assumption;
                 try rewrite PathMap.get_set_diff in Hlsv' by assumption;
                 cbn in *; unfold ok in *;
                 repeat some_inv; eauto.
          * eapply exec_expr_call_False in H11; eauto. contradiction.
    Qed.

    Theorem stat_variable_sound_call : forall tag τ x e l,
        PathMap.get (get_loc_path l) (var_gamma Γ) = None ->
        typ_of_expr e = τ -> (ge,this,Δ,Γ) ⊢ᵪ e ->
        (ge,this,Δ,Γ)
          ⊢ₛ MkStatement
          tag (StatVariable τ x (Some e) l) StmUnit
          ⊣ bind_typ_gamma_stmt l τ Γ.
    Proof using.
      cbn. intros i t x e l Hl He.
      autounfold with * in *.
      intros Hge Hged Hgok Hoks Hiss rob st Hrob Hread Hgst.
      split; auto using bind_typ_gamma_stmt_sub_gamma.
      inv Hoks; inv Hiss.
    Admitted.
  End StmtTyping.
End Soundness.
