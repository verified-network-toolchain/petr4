From Poulet4 Require Export P4light.Semantics.Semantics
     P4light.Semantics.Typing.Utility P4light.Syntax.Value.

(** * Typing of p4light Values. *)

(** Predicate that a
    [read_one_bit] relation
    is productive. *)
Definition read_one_bit_reads
           {U V : Type}
           (read_one_bit : U -> V -> Prop) : Prop :=
  forall u, exists v, read_one_bit u v.

(** Value typing. *)
Reserved Notation "'⊢ᵥ' v '\:' t" (at level 80, no associativity).

(** There's a 1-to-1 correspondence
    between values & types. *)
Inductive val_typ
          {A tags_t : Type}
  : @ValueBase A -> @P4Type tags_t -> Prop :=
| typ_bool : forall b,
    ⊢ᵥ ValBaseBool b \: TypBool
| typ_integer : forall v,
    ⊢ᵥ ValBaseInteger v \: TypInteger
| typ_bit : forall v,
    ⊢ᵥ ValBaseBit v \: TypBit (N.of_nat (length v))
| typ_int : forall v,
    ⊢ᵥ ValBaseInt v \: TypInt (N.of_nat (length v))
| typ_varbit : forall n v,
    length v <= N.to_nat n ->
    ⊢ᵥ ValBaseVarbit n v \: TypVarBit n
| typ_string : forall s,
    ⊢ᵥ ValBaseString s \: TypString
| typ_tuple : forall vs ts,
    Forall2 val_typ vs ts ->
    ⊢ᵥ ValBaseTuple vs \: TypTuple ts
| typ_error : forall err,
    ⊢ᵥ ValBaseError err \: TypError
| typ_struct : forall vs ts,
    AList.key_unique ts = true ->
    AList.all_values val_typ vs (P4String.clear_AList_tags ts) ->
    ⊢ᵥ ValBaseStruct vs \: TypStruct ts
| typ_header : forall b vs ts,
    AList.key_unique ts = true ->
    AList.all_values val_typ vs (P4String.clear_AList_tags ts) ->
    ⊢ᵥ ValBaseHeader vs b \: TypHeader ts
| typ_union : forall vs ts,
    AList.key_unique ts = true ->
    AList.all_values val_typ vs (P4String.clear_AList_tags ts) ->
    ⊢ᵥ ValBaseUnion vs \: TypHeaderUnion ts
| typ_array : forall n vs t,
    0 < length vs ->
    Forall (fun v => ⊢ᵥ v \: t) vs ->
    ⊢ᵥ ValBaseStack vs n \: TypArray t (N.of_nat (length vs))
| typ_enumfield : forall ename member members,
    List.In (P4String.str member) (List.map P4String.str members) ->
    ⊢ᵥ ValBaseEnumField (P4String.str ename) (@P4String.str tags_t member)
     \: TypEnum ename (inr members)
| typ_senumfield : forall ename v t,
    ⊢ᵥ v \: t ->
    ⊢ᵥ ValBaseSenumField (P4String.str ename) v \: TypEnum ename (inl t)
where "'⊢ᵥ' v '\:' t" := (val_typ v t) : type_scope.

(** Induction principle. *)
Section ValTypInd.
  Variables (A tags_t : Type).
  Notation V := (@ValueBase A).
  Notation typ := (@P4Type tags_t).
  Variable P : V -> typ -> Prop.

  Hypothesis HBool : forall b, P (ValBaseBool b) TypBool.
  Hypothesis HInteger : forall z, P (ValBaseInteger z) TypInteger.
  Hypothesis HBit : forall bits,
      P (ValBaseBit bits) (TypBit (N.of_nat (length bits))).
  Hypothesis HInt : forall bits,
      P (ValBaseInt bits) (TypInt (N.of_nat (length bits))).
  Hypothesis HVarbit : forall n bits,
      length bits <= N.to_nat n ->
      P (ValBaseVarbit n bits) (TypVarBit n).
  Hypothesis HString : forall s,
      P (ValBaseString s) TypString.
  Hypothesis HTuple : forall vs ts,
      Forall2 val_typ vs ts ->
      Forall2 P vs ts ->
      P (ValBaseTuple vs) (TypTuple ts).
  Hypothesis HError : forall err,
      P (ValBaseError err) TypError.
  Hypothesis HStruct : forall vs ts,
      AList.key_unique ts = true ->
      AList.all_values val_typ vs (P4String.clear_AList_tags ts) ->
      AList.all_values P vs (P4String.clear_AList_tags ts) ->
      P (ValBaseStruct vs) (TypStruct ts).
  Hypothesis HHeader : forall b vs ts,
      AList.key_unique ts = true ->
      AList.all_values val_typ vs (P4String.clear_AList_tags ts) ->
      AList.all_values P vs (P4String.clear_AList_tags ts) ->
      P (ValBaseHeader vs b) (TypHeader ts).
  Hypothesis HUnion : forall vs ts,
      AList.key_unique ts = true ->
      AList.all_values val_typ vs (P4String.clear_AList_tags ts) ->
      AList.all_values P vs (P4String.clear_AList_tags ts) ->
      P (ValBaseUnion vs) (TypHeaderUnion ts).
  Hypothesis HArray : forall n vs t,
      0 < length vs ->
      Forall (fun v => val_typ v t) vs ->
      Forall (fun v => P v t) vs ->
      P (ValBaseStack vs n) (TypArray t (N.of_nat (length vs))).
  Hypothesis HEnum : forall ename member members,
      List.In (P4String.str member) (List.map P4String.str members) ->
      P
        (ValBaseEnumField (P4String.str ename) (@P4String.str tags_t member))
        (TypEnum ename (inr members)).
  Hypothesis HSenum : forall ename v t,
      val_typ v t ->
      P v t ->
      P
        (ValBaseSenumField (P4String.str ename) v)
        (TypEnum ename (inl t)).
  
  Definition custom_val_typ_ind :
    forall (v : V) (t : typ), val_typ v t -> P v t :=
    fix vtind (v : V) (t : typ) (H : val_typ v t) : P v t :=
      let fix lind {vs : list V} {ts : list typ}
              (H : Forall2 val_typ vs ts)
          : Forall2 P vs ts :=
          match H with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Ht =>
            Forall2_cons _ _ (vtind _ _ Hh) (lind Ht)
          end in
      let fix alind
              {vs : AList.AList String.string V _}
              {ts : AList.AList String.string typ _}
              (H : AList.all_values val_typ vs ts)
          : AList.all_values P vs ts :=
          match H with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ (conj Hx Hh) Ht =>
            Forall2_cons _ _ (conj Hx (vtind _ _ Hh)) (alind Ht)
          end in
      let fix same_typ_ind {vs : list V} {t : typ}
              (H : Forall (fun v => val_typ v t) vs)
          : Forall (fun v => P v t) vs :=
          match H with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hh Ht =>
            Forall_cons _ (vtind _ _ Hh) (same_typ_ind Ht)
          end in
      match H with
      | typ_bool b => HBool b
      | typ_integer z => HInteger z
      | typ_bit bits => HBit bits
      | typ_int bits => HInt bits
      | typ_varbit _ _ H => HVarbit _ _ H
      | typ_string s => HString s
      | typ_tuple _ _ H => HTuple _ _ H (lind H)
      | typ_error err => HError err
      | typ_struct _ _ U H => HStruct _ _ U H (alind H)
      | typ_header b _ _ U H => HHeader b _ _ U H (alind H)
      | typ_union _ _ U H => HUnion _ _ U H (alind H)
      | typ_array n _ _ l H => HArray n _ _ l H (same_typ_ind H)
      | typ_enumfield x _ _ H => HEnum x _ _ H
      | typ_senumfield X _ _ Hv =>
        HSenum X _ _ Hv (vtind _ _ Hv)
      end.
End ValTypInd.

(** Results for relations & mappings between values. *)
Section RelTyp.
  Context {A B tags_t : Type}.
  Notation VA := (@ValueBase A).
  Notation VB := (@ValueBase B).
  Notation typ := (@P4Type tags_t).
  Local Hint Constructors val_typ : core.
    
  Section Map.
    Variable (f : A -> B).
      
    Lemma ValueBaseMap_preserves_type : forall v (t : typ),
        ⊢ᵥ v \: t ->
        ⊢ᵥ ValueBaseMap f v \: t.
    Proof.
      intros v t Hv;
        induction Hv using custom_val_typ_ind;
        simpl in *; auto;
          try match goal with
              | H: AList.all_values (fun v t => ⊢ᵥ ValueBaseMap f v \: t) ?vs _
                |- context [map (fun '(x,v) => (x,ValueBaseMap f v)) ?vs]
                => constructor; auto;
                    unfold AList.all_values in *;
                    rewrite Forall2_conj in *;
                    destruct H1 as [Hnames Hvts]; split;
                      [ clear Hvts;
                        rewrite Forall2_map_both in *;
                        rewrite map_fst_map, map_id
                      | clear Hnames;
                        rewrite Forall2_map_both, map_snd_map,
                        map_map, <- Forall2_map_both ]; assumption
              end;
          try match goal with
              | |- context [N.of_nat (length ?bits)]
                => replace (length bits)
                  with (length (map f bits))
                  by (rewrite map_length; reflexivity); auto; assumption
              end.
      - constructor; rewrite map_length; auto.
      - rewrite ForallMap.Forall2_map_l in H0; auto.
      - replace (length vs)
          with (length (map (ValueBaseMap f) vs)) in *
          by (rewrite map_length; reflexivity).
        constructor; auto.
        rewrite Forall_map.
        unfold Basics.compose.
        assumption.
    Qed.
  End Map.

  Section Rel.
    Variable (R : A -> B -> Prop).

    Local Hint Resolve Forall2_forall_impl_Forall2 : core.
    Local Hint Resolve Forall2_forall_specialize : core.
    Local Hint Resolve Forall2_impl : core.
    Local Hint Resolve in_combine_l : core.
    Local Hint Resolve nth_error_in_combine : core.
    Local Hint Resolve Forall2_length : core.
      
    Lemma exec_val_preserves_typ : forall va vb,
        exec_val R va vb ->
        forall t : typ, ⊢ᵥ va \: t -> ⊢ᵥ vb \: t.
    Proof.
      intros va vb Hev.
      induction Hev using custom_exec_val_ind;
        intros t Hvat; inversion Hvat; clear Hvat; subst; eauto;
          try match goal with
              | H: AList.all_values val_typ ?kvas (P4String.clear_AList_tags ?ts),
                   IH: AList.all_values
                         (fun va vb => forall t, ⊢ᵥ va \: t -> ⊢ᵥ vb \: t)
                         ?kvas ?kvbs
                |- _ => constructor; auto;
                        unfold AList.all_values in *;
                        rewrite Forall2_conj in *;
                        destruct IH as [Habkeys Habtyps];
                        destruct H as [Hakeys Hatyps];
                        rewrite Forall2_map_both in *;
                        pose proof Forall2_map_both
                             _ _ _ _ (fun va vb => forall t : typ, val_typ va t -> val_typ vb t)
                             snd snd kvas kvbs as H';
                        cbn in *; apply H' in Habtyps; clear H';
                          rewrite Forall2_eq in *;
                          rewrite <- Habkeys, Forall2_map_both;
                          split; eauto; assumption
              end;
          try match goal with
              | H: Forall2 _ ?la _
                |- context [N.of_nat (Datatypes.length ?la)]
                => apply Forall2_length in H; rewrite H; auto; assumption
              end.
      - apply Forall2_length in H; rewrite H in H3; auto.
      - apply Forall2_length in H.
        apply Forall2_length in H0 as Hlen; rewrite Hlen; clear Hlen.
        constructor; try lia.
        apply Forall2_forall_specialize with (t := t0) in H0.
        rewrite Forall_forall in *.
        rewrite Forall2_forall in H0.
        destruct H0 as [Hlen Hcomb].
        intros vb Hinvbs.
        apply In_nth_error in Hinvbs as Hnthvbs.
        destruct Hnthvbs as [n Hnthvbs].
        assert (Hnthvas: exists va, nth_error vas n = Some va).
        { apply ListUtil.nth_error_exists.
          rewrite Hlen, <- nth_error_Some, Hnthvbs; discriminate. }
        destruct Hnthvas as [va Hnthvas]. eauto 6.
    Qed.
    
    Local Hint Constructors exec_val : core.
    Hint Rewrite map_length : core.
      
    Lemma exec_val_exists :
      read_one_bit_reads R ->
      forall (va : VA), exists vb, exec_val R va vb.
    Proof.
      intros HR va.
      induction va using @custom_ValueBase_ind; eauto.
      - unfold read_one_bit_reads in HR.
        specialize HR with b. firstorder eauto.
      - unfold read_one_bit_reads in HR.
        assert (forall a, List.In a n -> exists b, R a b) by firstorder eauto.
        rewrite <- Forall_forall, Forall_exists_factor in H.
        firstorder eauto.
      - unfold read_one_bit_reads in HR.
        assert (forall a, List.In a z -> exists b, R a b) by firstorder eauto.
        rewrite <- Forall_forall, Forall_exists_factor in H.
        firstorder eauto.
      - unfold read_one_bit_reads in HR.
        assert (forall a, List.In a n -> exists b, R a b) by firstorder eauto.
        rewrite <- Forall_forall, Forall_exists_factor in H.
        firstorder eauto.
      - rewrite Forall_exists_factor in H.
        firstorder eauto.
      - rewrite Forall_snd, Forall_exists_factor in H.
        destruct H as [bs Hbs].
        exists (ValBaseStruct (combine (map fst vs) bs)).
        constructor. unfold AList.all_values.
        rewrite Forall2_conj.
        split; rewrite Forall2_map_both.
        + rewrite Forall2_eq.
          rewrite map_fst_combine;
            autorewrite with core; eauto.
        + rewrite ForallMap.Forall2_map_l in Hbs.
          rewrite map_snd_combine;
            autorewrite with core; eauto.
          apply Forall2_length in Hbs.
          autorewrite with core in *; assumption.
      - rewrite Forall_snd, Forall_exists_factor in H.
        destruct H as [bs Hbs].
        unfold read_one_bit_reads in HR.
        specialize HR with b; destruct HR as [bb HR].
        exists (ValBaseHeader (combine (map fst vs) bs) bb).
        constructor; auto. unfold AList.all_values.
        rewrite Forall2_conj.
        split; rewrite Forall2_map_both.
        + rewrite Forall2_eq.
          rewrite map_fst_combine;
            autorewrite with core; eauto.
        + rewrite ForallMap.Forall2_map_l in Hbs.
          rewrite map_snd_combine;
            autorewrite with core; eauto.
          apply Forall2_length in Hbs.
          autorewrite with core in *; assumption.
      - rewrite Forall_snd, Forall_exists_factor in H.
        destruct H as [bs Hbs].
        exists (ValBaseUnion (combine (map fst vs) bs)).
        constructor. unfold AList.all_values.
        rewrite Forall2_conj.
        split; rewrite Forall2_map_both.
        + rewrite Forall2_eq.
          rewrite map_fst_combine;
            autorewrite with core; eauto.
        + rewrite ForallMap.Forall2_map_l in Hbs.
          rewrite map_snd_combine;
            autorewrite with core; eauto.
          apply Forall2_length in Hbs.
          autorewrite with core in *; assumption.
      - rewrite Forall_exists_factor in H.
        firstorder eauto.
      - firstorder eauto.
    Qed.
  End Rel.
End RelTyp.

(** Utility. *)
Section Lemmas.
  Context {tags_t : Type}.
  Notation typ := (@P4Type tags_t).
                                 
  Local Hint Constructors val_typ : core.
    
  Lemma uninit_sval_of_typ_list_val_typ :
    forall b (ts : list typ) v,
      Forall is_expr_typ ts ->
      Forall
        (fun t => forall v,
             uninit_sval_of_typ b t = Some v -> val_typ v (normᵗ t))
        ts ->
      sequence (map (uninit_sval_of_typ b) ts) >>| ValBaseTuple = Some v ->
      val_typ v (TypTuple (map normᵗ ts)).
  Proof.
    intros b ts v Hts IHts Hob; cbn in *.
    unfold option_bind in *.
    destruct (sequence (map (uninit_sval_of_typ b) ts))
      as [vs |] eqn:Hvs; cbn in *; try discriminate; some_inv.
    rewrite <- Forall2_sequence_iff,
    <- ForallMap.Forall2_map_l, Forall2_flip in Hvs.
    constructor.
    apply Forall2_impl
      with (R := fun v t => uninit_sval_of_typ b t = Some v)
           (Q := val_typ).
    - rewrite Forall2_forall;
        rewrite Forall_forall in IHts;
        split;
        [ rewrite map_length; eauto using Forall2_length
        | intros u v HIn Hun;
          apply in_combine_r in HIn;
          rewrite in_map_iff in HIn;
          destruct HIn as (t' & ? & Ht'); subst;
          epose proof uninit_sval_of_typ_norm as Husotn;
          unfold uninit_sval_of_typ_norm_def in Husotn;
          rewrite Husotn in Hun; clear Husotn; eauto ].
    - pose proof ForallMap.Forall2_map_l
           _ _ _ (fun vo v => vo = Some v) (@uninit_sval_of_typ tags_t b) as H';
        cbn in H'; rewrite Forall2_flip, H';
          rewrite Forall2_flip, H' in Hvs; clear H';
            rewrite map_map;
            epose proof uninit_sval_of_typ_norm as H';
            unfold uninit_sval_of_typ_norm_def in H'.
      specialize H' with (b0 := b);
        rewrite map_ext with
            (f := fun x => uninit_sval_of_typ b (normᵗ x))
            (g := uninit_sval_of_typ b) by auto;
        assumption.
  Qed.
  Local Hint Resolve uninit_sval_of_typ_list_val_typ : core.

  Lemma uninit_sval_of_typ_alist_val_typ :
    forall b (xts : list (P4String.t tags_t * typ))
      (v : @ValueBase (option bool)),
      AList.key_unique xts = true ->
      Forall (fun xt => is_expr_typ (snd xt)) xts ->
      Forall (fun xt => forall v,
                  uninit_sval_of_typ b (snd xt) = Some v ->
                  val_typ v (normᵗ (snd xt))) xts ->
      (sequence (map (fun '({| P4String.str := x |}, t) =>
                        uninit_sval_of_typ b t >>| pair x) xts)
                >>| ValBaseStruct = Some v ->
       val_typ v (TypStruct (map (fun '(x,t) => (x, normᵗ t)) xts))) /\
      (sequence (map (fun '({| P4String.str := x |}, t) =>
                        uninit_sval_of_typ b t >>| pair x) xts)
                >>| (fun xvs => ValBaseHeader xvs b) = Some v ->
       val_typ v (TypHeader (map (fun '(x,t) => (x, normᵗ t)) xts))) /\
      (sequence (map (fun '({| P4String.str := x |}, t) =>
                        uninit_sval_of_typ b t >>| pair x) xts)
                >>| ValBaseUnion = Some v ->
       val_typ v (TypHeaderUnion (map (fun '(x,t) => (x, normᵗ t)) xts))).
  Proof.
    intros b xts v Uxts Hxts IHxts.
    repeat split; intro Hob;
      destruct
        (sequence
           (map
              (fun '({| P4String.str := x |}, t) =>
                 uninit_sval_of_typ b t >>| pair x)
              xts))
      as [xvs |] eqn:Hxvs; cbn in *;
        unfold option_bind in *;
        try discriminate; some_inv;
    econstructor;
      try (epose proof AListUtil.key_unique_map_values as Hmv;
           unfold AListUtil.map_values in Hmv; rewrite Hmv; clear Hmv; assumption);
    unfold AList.all_values;
      rewrite <- Forall2_sequence_iff in Hxvs;
      rewrite Forall2_conj;
    rewrite Forall2_map_both with (f:=fst) (g:=fst);
      rewrite Forall2_map_both with (f:=snd) (g:=snd);
      rewrite Forall2_eq;
    unfold P4String.clear_AList_tags;
      do 2 rewrite map_fst_map;
      do 2 rewrite map_snd_map;
      repeat rewrite map_id;
    rewrite <- ForallMap.Forall2_map_l in Hxvs;
    clear Hxts Uxts;
    generalize dependent xvs;
      induction xts as [| [[i x] t] xts IHxts'];
      intros [| [y v] yvs] H; cbn in *;
        inversion H;
        inversion IHxts; subst; auto;
          specialize IHxts' with yvs;
          match_some_inv; some_inv;
            cbn in *; firstorder; f_equal; auto.
  Qed.
  Local Hint Resolve uninit_sval_of_typ_alist_val_typ : core.
  Local Hint Resolve sublist.Forall_repeat : core.

  Ltac width_solve :=
    match goal with
    | |- context [repeat ?o (N.to_nat ?w)]
      => assert (Hw : w = N.of_nat (length (repeat o (N.to_nat w))))
        by (rewrite repeat_length; lia);
        rewrite Hw at 2; auto
    end.
  Local Hint Extern 0 => width_solve : core.
    
  Lemma uninit_sval_of_typ_val_typ : forall (t : typ) b v,
      is_expr_typ t ->
      uninit_sval_of_typ b t = Some v ->
      val_typ v (normᵗ t).
  Proof.
    intros t b v H; generalize dependent v.
    induction H using my_is_expr_typ_ind;
      intros v Huninit; cbn in *;
        try discriminate; try some_inv; eauto.
    - constructor; simpl; lia.
    - unfold option_bind in *.
      assert (H0n: (0 <? n)%N = true) by (rewrite N.ltb_lt; lia).
      rewrite H0n in *.
      destruct (uninit_sval_of_typ b t)
        as [v' |] eqn:Hv'; inversion Huninit; subst.
      width_solve. constructor; auto.
      rewrite repeat_length; auto.
    - eapply uninit_sval_of_typ_alist_val_typ in H0; firstorder eauto.
    - eapply uninit_sval_of_typ_alist_val_typ in H0;
        cbn in *; unfold option_bind in *; cbn in *;
          firstorder eauto.
    - eapply uninit_sval_of_typ_alist_val_typ in H0; firstorder eauto.
    - eapply uninit_sval_of_typ_alist_val_typ in H0; firstorder eauto.
    - destruct X as [iX X'] eqn:HX;
        destruct mems as [| [iM M] mems];
        cbn in *; try lia.
      revert HX; some_inv; intros HX.
      rewrite <- HX.
      apply f_equal with (f := P4String.str) in HX;
        cbn in *.
      rewrite <- HX.
      replace M with
          (P4String.str {| P4String.tags:=iM; P4String.str:=M |}) at 1
        by reflexivity. constructor; cbn; auto.
    - destruct X as [iX X'] eqn:HX; cbn in *.
      unfold option_map,option_bind in *.
      revert HX.
      destruct (uninit_sval_of_typ b t)
        as [v' |] eqn:Hut; cbn in *;
          try discriminate; some_inv.
        intros HX.
        replace X' with (P4String.str X) at 1 by (subst; auto).
        rewrite <- HX; auto.
  Qed.

  Local Hint Constructors is_expr_typ : core.
  Local Hint Resolve Forall2_only_r_Forall : core.
  Local Hint Unfold AList.all_values : core.
  Local Hint Unfold P4String.clear_AList_tags : core.
  Local Hint Unfold Basics.compose : core.

  Create HintDb rw1.
  Create HintDb rw2.
  Hint Rewrite Forall2_conj : rw1.
  Hint Rewrite map_pat_both : rw1.
  Hint Rewrite <- Forall2_map_r : rw2.
  Local Hint Constructors predop : core.

  Context {A : Type}.
  Notation VA := (@ValueBase A).
  
  Lemma val_typ_is_expr_typ : forall (v : VA) (t : typ),
      ⊢ᵥ v \: t -> is_expr_typ t.
  Proof.
    intros v t Hvt.
    induction Hvt using custom_val_typ_ind;
      autounfold with * in *;
      autorewrite with rw1 in *;
      autorewrite with rw2 in *;
      intuition; eauto.
    - destruct vs as [| v vs]; cbn in *; try lia.
      inversion H1; subst; constructor; auto; lia.
    - constructor; auto.
      destruct members; cbn in *; try contradiction; try lia.
  Qed.
End Lemmas.
