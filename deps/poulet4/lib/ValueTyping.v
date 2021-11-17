Require Export Poulet4.Semantics Poulet4.Typed Poulet4.Syntax
        Coq.Strings.String Coq.NArith.BinNat Coq.Lists.List
        Poulet4.Value Coq.micromega.Lia Poulet4.Utils.
Export ListNotations.
Require Poulet4.P4String.

(** Predicate that a
    [read_one_bit] relation
    is productive. *)
Definition read_one_bit_reads
           {U V : Type}
           (read_one_bit : U -> V -> Prop) : Prop :=
  forall u, exists v, read_one_bit u v.

(** Relation that a
    [read_one_bit] is an inverse
    with respect to [f]. *)
Definition read_one_bit_inverse
           {U V : Type}
           (read_one_bit : U -> V -> Prop) (f : V -> U -> Prop) : Prop :=
  forall u v, read_one_bit u v <-> f v u.

Section ExecValInd.
  Variables (tags_t A B : Type).
  Notation VA := (@ValueBase tags_t A).
  Notation VB := (@ValueBase tags_t B).
  Variables (R : A -> B -> Prop) (P : VA -> VB -> Prop).
  
  Hypothesis HNull : P ValBaseNull ValBaseNull.
  Hypothesis HBool : forall a b,
      R a b -> P (ValBaseBool a) (ValBaseBool b).
  Hypothesis HInteger : forall n, P (ValBaseInteger n) (ValBaseInteger n).
  Hypothesis HBit : forall la lb,
      Forall2 R la lb -> P (ValBaseBit la) (ValBaseBit lb).
  Hypothesis HInt : forall la lb,
      Forall2 R la lb -> P (ValBaseInt la) (ValBaseInt lb).
  Hypothesis HVarbit : forall max la lb,
      Forall2 R la lb -> P (ValBaseVarbit max la) (ValBaseVarbit max lb).
  Hypothesis HString : forall s, P (ValBaseString s) (ValBaseString s).
  Hypothesis HTuple : forall vas vbs,
      Forall2 (exec_val R) vas vbs ->
      Forall2 P vas vbs ->
      P (ValBaseTuple vas) (ValBaseTuple vbs).
  Hypothesis HRecord : forall kvas kvbs,
      AList.all_values (exec_val R) kvas kvbs ->
      AList.all_values P kvas kvbs ->
      P (ValBaseRecord kvas) (ValBaseRecord kvbs).
  Hypothesis HError : forall s, P (ValBaseError s) (ValBaseError s).
  Hypothesis HMatchkind : forall s, P (ValBaseMatchKind s) (ValBaseMatchKind s).
  Hypothesis HStruct : forall kvas kvbs,
      AList.all_values (exec_val R) kvas kvbs ->
      AList.all_values P kvas kvbs ->
      P (ValBaseStruct kvas) (ValBaseStruct kvbs).
  Hypothesis HHeader : forall a b kvas kvbs,
      R a b ->
      AList.all_values (exec_val R) kvas kvbs ->
      AList.all_values P kvas kvbs ->
      P (ValBaseHeader kvas a) (ValBaseHeader kvbs b).
  Hypothesis HUnion : forall kvas kvbs,
      AList.all_values (exec_val R) kvas kvbs ->
      AList.all_values P kvas kvbs ->
      P (ValBaseUnion kvas) (ValBaseUnion kvbs).
  Hypothesis HStack : forall vas vbs size next,
      Forall2 (exec_val R) vas vbs ->
      Forall2 P vas vbs ->
      P (ValBaseStack vas size next) (ValBaseStack vbs size next).
  Hypothesis HEnumField : forall type_name enum_name,
      P
        (ValBaseEnumField type_name enum_name)
        (ValBaseEnumField type_name enum_name).
  Hypothesis HSenumField : forall type_name enum_name va vb,
      exec_val R va vb -> P va vb ->
      P
        (ValBaseSenumField type_name enum_name va)
        (ValBaseSenumField type_name enum_name vb).
  
  Definition custom_exec_val_ind : forall va vb,
      exec_val R va vb -> P va vb :=
    fix evind va vb (H : exec_val R va vb) : P va vb :=
      let fix lind
              {vas} {vbs}
              (HForall2 : Forall2 (exec_val R) vas vbs)
          : Forall2 P vas vbs :=
          match HForall2 with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hhd Htl
            => Forall2_cons _ _ (evind _ _ Hhd) (lind Htl)
          end in
      let fix alind
              {kvas} {kvbs}
              (Hall_values : AList.all_values (exec_val R) kvas kvbs)
          : AList.all_values P kvas kvbs :=
          match Hall_values with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ (conj Hk Hhd) Htl
            => Forall2_cons _ _ (conj Hk (evind _ _ Hhd)) (alind Htl)
          end in
      match H with
      | exec_val_null _ => HNull
      | exec_val_bool _ _ _ r => HBool _ _ r
      | exec_val_integer _ n => HInteger n
      | exec_val_bit _ _ _ rs => HBit _ _ rs
      | exec_val_int _ _ _ rs => HInt _ _ rs
      | exec_val_varbit _ _ max _ rs => HVarbit _ max _ rs
      | exec_val_string _ s => HString s
      | exec_val_tuple _ _ _ evs => HTuple _ _ evs (lind evs)
      | exec_val_record _ _ _ evs => HRecord _ _ evs (alind evs)
      | exec_val_error _ s => HError s
      | exec_val_matchkind _ s => HMatchkind s
      | exec_val_struct _ _ _ evs => HStruct _ _ evs (alind evs)
      | exec_val_header _ _ _ _ _ r evs
        => HHeader _ _ _ _ r evs (alind evs)
      | exec_val_union _ _ _ evs => HUnion _ _ evs (alind evs)
      | exec_val_stack _ _ _ size next evs
        => HStack _ _ size next evs (lind evs)
      | exec_val_enum_field _ tn en => HEnumField tn en
      | exec_val_senum_field _ tn en _ _ ev
        => HSenumField tn en _ _ ev (evind _ _ ev)
      end.
End ExecValInd.

Section ValueTyping.
  Context {tags_t : Type}.

  Notation typ := (@P4Type tags_t).

  Section Val.
    Context {A : Type}.
    Notation V := (@ValueBase tags_t A).
    Notation senum_env := (@IdentMap.t tags_t (P4String.AList tags_t V)).
    
    (* TODO:
       What constraints do we need on:
       - fixed-width numeric types?
       - headers (unions & stacks)?
       - senum values: see comments below.
       - needs to be parameterized by bit type. *)

    Variable (gsenum : senum_env).

    Inductive val_typ : V -> typ -> Prop :=
    | typ_null :
        val_typ ValBaseNull TypVoid
    | typ_bool : forall b,
        val_typ (ValBaseBool b) TypBool
    | typ_integer : forall v,
        val_typ (ValBaseInteger v) TypInteger
    | typ_bit : forall v,
        val_typ (ValBaseBit v) (TypBit (N.of_nat (length v)))
    | typ_int : forall v,
        val_typ (ValBaseInt v) (TypInt (N.of_nat (length v)))
    | typ_varbit : forall n v,
        N.to_nat n < length v ->
        val_typ (ValBaseVarbit n v) (TypVarBit n)
    | typ_string : forall s,
        val_typ (ValBaseString s) TypString
    | typ_tuple : forall vs ts,
        Forall2 val_typ vs ts ->
        val_typ (ValBaseTuple vs) (TypTuple ts)
    | typ_record : forall vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseRecord vs) (TypRecord ts)
    | typ_error : forall err,
        val_typ (ValBaseError err) TypError
    | typ_matchkind : forall mk,
        val_typ (ValBaseMatchKind mk) TypMatchKind
    | typ_struct : forall vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseStruct vs) (TypStruct ts)
    | typ_header : forall b vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseHeader vs b) (TypHeader ts)
    | typ_union : forall vs ts,
        AList.all_values val_typ vs ts ->
        val_typ (ValBaseUnion vs) (TypHeaderUnion ts)
    | typ_stack : forall s n vs ts,
        length vs = N.to_nat s ->
        Forall (fun v => val_typ v (TypHeader ts)) vs ->
        val_typ (ValBaseStack vs s n) (TypArray (TypHeader ts) n)
    | typ_enumfield : forall ename member members,
        In member members ->
        val_typ
          (ValBaseEnumField ename member)
          (TypEnum ename None members)
    | typ_senumfield : forall ename member v t fields,
        IdentMap.get ename gsenum = Some fields ->
        AList.get fields member = Some v ->
        val_typ v t ->
        val_typ
          (ValBaseSenumField ename member v)
          (TypEnum ename (Some t) (List.map fst fields)).

    Section ValTypInd.
      Variable P : V -> typ -> Prop.

      Hypothesis HNull : P ValBaseNull TypVoid.
      Hypothesis HBool : forall b, P (ValBaseBool b) TypBool.
      Hypothesis HInteger : forall z, P (ValBaseInteger z) TypInteger.
      Hypothesis HBit : forall bits,
          P (ValBaseBit bits) (TypBit (N.of_nat (length bits))).
      Hypothesis HInt : forall bits,
          P (ValBaseInt bits) (TypInt (N.of_nat (length bits))).
      Hypothesis HVarbit : forall n bits,
          N.to_nat n < length bits ->
          P (ValBaseVarbit n bits) (TypVarBit n).
      Hypothesis HString : forall s,
          P (ValBaseString s) TypString.
      Hypothesis HTuple : forall vs ts,
          Forall2 val_typ vs ts ->
          Forall2 P vs ts ->
          P (ValBaseTuple vs) (TypTuple ts).
      Hypothesis HRecord : forall vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseRecord vs) (TypRecord ts).
      Hypothesis HError : forall err,
          P (ValBaseError err) TypError.
      Hypothesis HMatchkind : forall mk,
          P (ValBaseMatchKind mk) TypMatchKind.
      Hypothesis HStruct : forall vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseStruct vs) (TypStruct ts).
      Hypothesis HHeader : forall b vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseHeader vs b) (TypHeader ts).
      Hypothesis HUnion : forall vs ts,
          AList.all_values val_typ vs ts ->
          AList.all_values P vs ts ->
          P (ValBaseUnion vs) (TypHeaderUnion ts).
      Hypothesis HStack : forall s n vs ts,
          length vs = N.to_nat s ->
          Forall (fun v => val_typ v (TypHeader ts)) vs ->
          Forall (fun v => P v (TypHeader ts)) vs ->
          P (ValBaseStack vs s n) (TypArray (TypHeader ts) n).
      Hypothesis HEnum : forall ename member members,
          In member members ->
          P
            (ValBaseEnumField ename member)
            (TypEnum ename None members).
      Hypothesis HSenum : forall ename member v t fields,
          IdentMap.get ename gsenum = Some fields ->
          AList.get fields member = Some v ->
          val_typ v t ->
          P v t ->
          P
            (ValBaseSenumField ename member v)
            (TypEnum ename (Some t) (List.map fst fields)).

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
                  {vs : AList.AList (P4String.t _) V _}
                  {ts : AList.AList (P4String.t _) typ _}
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
          | typ_null => HNull
          | typ_bool b => HBool b
          | typ_integer z => HInteger z
          | typ_bit bits => HBit bits
          | typ_int bits => HInt bits
          | typ_varbit _ _ H => HVarbit _ _ H
          | typ_string s => HString s
          | typ_tuple _ _ H => HTuple _ _ H (lind H)
          | typ_record _ _ H => HRecord _ _ H (alind H)
          | typ_error err => HError err
          | typ_matchkind mk => HMatchkind mk
          | typ_struct _ _ H => HStruct _ _ H (alind H)
          | typ_header b _ _ H => HHeader b _ _ H (alind H)
          | typ_union _ _ H => HUnion _ _ H (alind H)
          | typ_stack _ n _ _ Hl H => HStack _ n _ _ Hl H (same_typ_ind H)
          | typ_enumfield x _ _ H => HEnum x _ _ H
          | typ_senumfield _ _ _ _ _ H1 H2 Hv =>
            HSenum _ _ _ _ _ H1 H2 Hv (vtind _ _ Hv)
          end.
    End ValTypInd.
  End Val.

  Section RelTyp.
    Context {A B : Type}.
    Notation VA := (@ValueBase tags_t A).
    Notation VB := (@ValueBase tags_t B).

    Local Hint Constructors val_typ : core.
    
    Section Map.
      Variable (f : A -> B).
      
      Lemma ValueBaseMap_preserves_type : forall gs v t,
          val_typ gs v t ->
          val_typ
            (FuncAsMap.map_map (AList.map_values (ValueBaseMap f)) gs)
            (ValueBaseMap f v) t.
      Proof.
        intros gs v t Hv;
          induction Hv using @custom_val_typ_ind;
          simpl in *; auto.
        - replace (length bits)
            with (length (map f bits))
            by (rewrite map_length; reflexivity); auto.
        - replace (length bits)
            with (length (map f bits))
            by (rewrite map_length; reflexivity); auto.
        - constructor; rewrite map_length; auto.
        - rewrite Forall2_map_l in H0; auto.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *;
            destruct H0 as [Hnames Hvts]; split.
          + clear Hvts.
            rewrite Forall2_map_both in *.
            rewrite map_fst_map, map_id.
            assumption.
          + clear Hnames.
            rewrite Forall2_map_both, map_snd_map,
            map_map, <- Forall2_map_both.
            assumption.
        - constructor.
          + rewrite map_length; assumption.
          + rewrite Forall_map.
            unfold Basics.compose.
            assumption.
        - replace (map fst fields) with
              (map fst (AList.map_values (ValueBaseMap f) fields)).
          constructor; auto.
          + unfold IdentMap.get,
            FuncAsMap.get, FuncAsMap.map_map in *.
            rewrite H; reflexivity.
          + rewrite AList.get_map_values, H0; reflexivity.
          + unfold AList.map_values.
            rewrite map_fst_map, map_id; reflexivity.
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
          forall gsa gsb,
            FuncAsMap.related
              (AList.all_values (exec_val R))
              gsa gsb ->
            forall t, val_typ gsa va t -> val_typ gsb vb t.
      Proof.
        intros va vb Hev gsa gsb Hgs.
        induction Hev using custom_exec_val_ind;
          intros t Hvat; inversion Hvat; clear Hvat; subst; eauto.
        - apply Forall2_length in H; rewrite H; auto.
        - apply Forall2_length in H; rewrite H; auto.
        - apply Forall2_length in H; rewrite H in H3; auto.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *.
          destruct H0 as [Habkeys Habtyps].
          destruct H2 as [Hakeys Hatyps].
          rewrite Forall2_map_both in *.
          pose proof Forall2_map_both
               _ _ _ _ (fun va vb => forall t, val_typ gsa va t -> val_typ gsb vb t)
               snd snd kvas kvbs as H';
            cbn in *; apply H' in Habtyps; clear H'.
          rewrite Forall2_eq in *; rewrite <- Habkeys.
          rewrite Forall2_map_both; split; eauto.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *.
          destruct H0 as [Habkeys Habtyps].
          destruct H2 as [Hakeys Hatyps].
          rewrite Forall2_map_both in *.
          pose proof Forall2_map_both
               _ _ _ _ (fun va vb => forall t, val_typ gsa va t -> val_typ gsb vb t)
               snd snd kvas kvbs as H';
            cbn in *; apply H' in Habtyps; clear H'.
          rewrite Forall2_eq in *; rewrite <- Habkeys.
          rewrite Forall2_map_both; split; eauto.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *.
          destruct H1 as [Habkeys Habtyps].
          destruct H5 as [Hakeys Hatyps].
          rewrite Forall2_map_both in *.
          pose proof Forall2_map_both
               _ _ _ _ (fun va vb => forall t, val_typ gsa va t -> val_typ gsb vb t)
               snd snd kvas kvbs as H';
            cbn in *; apply H' in Habtyps; clear H'.
          rewrite Forall2_eq in *; rewrite <- Habkeys.
          rewrite Forall2_map_both; split; eauto.
        - constructor.
          unfold AList.all_values in *.
          rewrite Forall2_conj in *.
          destruct H0 as [Habkeys Habtyps].
          destruct H2 as [Hakeys Hatyps].
          rewrite Forall2_map_both in *.
          pose proof Forall2_map_both
               _ _ _ _ (fun va vb => forall t, val_typ gsa va t -> val_typ gsb vb t)
               snd snd kvas kvbs as H';
            cbn in *; apply H' in Habtyps; clear H'.
          rewrite Forall2_eq in *; rewrite <- Habkeys.
          rewrite Forall2_map_both; split; eauto.
        - apply Forall2_length in H.
          constructor; try lia.
          apply Forall2_forall_specialize with (t := TypHeader ts) in H0.
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
        - unfold FuncAsMap.related, IdentMap.get in *.
          specialize Hgs with type_name.
          inversion Hgs; subst; unfold P4String.AList in *.
          + exfalso; clear Hev vb H H4 H5 R enum_name gsb Hgs IHHev t0 B.
            rewrite H2 in H0. discriminate.
          + rewrite H2 in H; inversion H; subst; clear H.
            apply AList.all_values_keys_eq in H1 as Hkeys.
            rewrite Hkeys. constructor; auto.
            (* need notion of equivalent types and values. *)
      Admitted.

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
          assert (forall a, In a n -> exists b, R a b) by firstorder eauto.
          rewrite <- Forall_forall, Forall_exists_factor in H.
          firstorder eauto.
        - unfold read_one_bit_reads in HR.
          assert (forall a, In a z -> exists b, R a b) by firstorder eauto.
          rewrite <- Forall_forall, Forall_exists_factor in H.
          firstorder eauto.
        - unfold read_one_bit_reads in HR.
          assert (forall a, In a n -> exists b, R a b) by firstorder eauto.
          rewrite <- Forall_forall, Forall_exists_factor in H.
          firstorder eauto.
        - rewrite Forall_exists_factor in H.
          firstorder eauto.
        - rewrite Forall_snd, Forall_exists_factor in H.
          destruct H as [bs Hbs].
          exists (ValBaseRecord (combine (map fst vs) bs)).
          constructor. unfold AList.all_values.
          rewrite Forall2_conj.
          split; rewrite Forall2_map_both.
          + rewrite Forall2_eq.
            rewrite map_fst_combine;
              autorewrite with core; eauto.
          + rewrite Forall2_map_l in Hbs.
            rewrite map_snd_combine;
              autorewrite with core; eauto.
            apply Forall2_length in Hbs.
            autorewrite with core in *; assumption.
        - rewrite Forall_snd, Forall_exists_factor in H.
          destruct H as [bs Hbs].
          exists (ValBaseStruct (combine (map fst vs) bs)).
          constructor. unfold AList.all_values.
          rewrite Forall2_conj.
          split; rewrite Forall2_map_both.
          + rewrite Forall2_eq.
            rewrite map_fst_combine;
              autorewrite with core; eauto.
          + rewrite Forall2_map_l in Hbs.
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
          + rewrite Forall2_map_l in Hbs.
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
          + rewrite Forall2_map_l in Hbs.
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
End ValueTyping.
