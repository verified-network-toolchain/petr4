Require Import Poulet4.Semantics Poulet4.Typed
        Poulet4.Syntax Coq.NArith.BinNat Coq.Lists.List
        Poulet4.Value Coq.micromega.Lia Poulet4.Utils.
Import ListNotations.
Require Import Poulet4.P4String.
Require Import Poulet4.AList.

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
  Notation VA := (@ValueBase A).
  Notation VB := (@ValueBase B).
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
    Notation V := (@ValueBase A).
    Notation senum_env := (@IdentMap.t tags_t (StringAList V)).

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
        AList.all_values val_typ vs (clear_AList_tags ts) ->
        val_typ (ValBaseRecord vs) (TypRecord ts)
    | typ_error : forall err,
        val_typ (ValBaseError err) TypError
    | typ_matchkind : forall mk,
        val_typ (ValBaseMatchKind mk) TypMatchKind
    | typ_struct : forall vs ts,
        AList.all_values val_typ vs (clear_AList_tags ts) ->
        val_typ (ValBaseStruct vs) (TypStruct ts)
    | typ_header : forall b vs ts,
        AList.all_values val_typ vs (clear_AList_tags ts) ->
        val_typ (ValBaseHeader vs b) (TypHeader ts)
    | typ_union : forall vs ts,
        AList.all_values val_typ vs (clear_AList_tags ts) ->
        val_typ (ValBaseUnion vs) (TypHeaderUnion ts)
    | typ_stack : forall s n vs ts,
        length vs = N.to_nat s ->
        Forall (fun v => val_typ v (TypHeader ts)) vs ->
        val_typ (ValBaseStack vs s n) (TypArray (TypHeader ts) n)
    | typ_enumfield : forall ename member members,
        In member members ->
        val_typ
          (ValBaseEnumField (str ename) (str member))
          (TypEnum ename None members)
    | typ_senumfield : forall ename member v t fields,
        IdentMap.get ename gsenum = Some (clear_AList_tags fields) ->
        AList.get (clear_AList_tags fields) member = Some v ->
        val_typ v t ->
        val_typ
          (ValBaseSenumField (str ename) member v)
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
          AList.all_values val_typ vs (clear_AList_tags ts) ->
          AList.all_values P vs (clear_AList_tags ts) ->
          P (ValBaseRecord vs) (TypRecord ts).
      Hypothesis HError : forall err,
          P (ValBaseError err) TypError.
      Hypothesis HMatchkind : forall mk,
          P (ValBaseMatchKind mk) TypMatchKind.
      Hypothesis HStruct : forall vs ts,
          AList.all_values val_typ vs (clear_AList_tags ts) ->
          AList.all_values P vs (clear_AList_tags ts) ->
          P (ValBaseStruct vs) (TypStruct ts).
      Hypothesis HHeader : forall b vs ts,
          AList.all_values val_typ vs (clear_AList_tags ts) ->
          AList.all_values P vs (clear_AList_tags ts) ->
          P (ValBaseHeader vs b) (TypHeader ts).
      Hypothesis HUnion : forall vs ts,
          AList.all_values val_typ vs (clear_AList_tags ts) ->
          AList.all_values P vs (clear_AList_tags ts) ->
          P (ValBaseUnion vs) (TypHeaderUnion ts).
      Hypothesis HStack : forall s n vs ts,
          length vs = N.to_nat s ->
          Forall (fun v => val_typ v (TypHeader ts)) vs ->
          Forall (fun v => P v (TypHeader ts)) vs ->
          P (ValBaseStack vs s n) (TypArray (TypHeader ts) n).
      Hypothesis HEnum : forall ename member members,
          In member members ->
          P
            (ValBaseEnumField (str ename) (str member))
            (TypEnum ename None members).
      Hypothesis HSenum : forall ename member v t fields,
          IdentMap.get ename gsenum = Some (clear_AList_tags fields) ->
          AList.get (clear_AList_tags fields) member = Some v ->
          val_typ v t ->
          P v t ->
          P
            (ValBaseSenumField (str ename) member v)
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
                  {vs : StringAList V}
                  {ts : AList.AList (P4String.t _) typ _}
                  (H : AList.all_values val_typ vs (clear_AList_tags ts))
              : AList.all_values P vs (clear_AList_tags ts) :=
              match H with
              | Forall2_nil _ => Forall2_nil _
              | Forall2_cons _ _ (conj Hx Hh) Ht =>
                Forall2_cons _ _ (conj Hx (vtind _ _ Hh)) (@alind Ht)
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
    
Section TypingDefs.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  (** Typing context. *)
  Definition gamma : Type := @PathMap.t tags_t typ.

  (** TODO: is this correct? *)
  Definition typ_of_loc (l : Locator) (g : gamma) : option typ :=
    match l with
    | LInstance p => PathMap.get p g
    | LGlobal   p => PathMap.get p g
    end.

  Context `{T : @Target tags_t expr}.

  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).

  Definition envs_same (g : gamma) (st : state) : Prop :=
    forall p : path, PathMap.get p g = None <-> PathMap.get p (fst st) = None.

  Lemma envs_same_some_l : forall g st p t,
      envs_same g st -> PathMap.get p g = Some t ->
      exists v, PathMap.get p (fst st) = Some v.
  Proof.
    intros g st p t H Hgt; unfold envs_same in H.
    destruct (PathMap.get p (fst st)) as [v |] eqn:Heq; eauto.
    rewrite <- H, Hgt in Heq; discriminate.
  Qed.

  Lemma envs_same_some_r : forall g st p v,
      envs_same g st -> PathMap.get p (fst st) = Some v ->
      exists t, PathMap.get p g = Some t.
  Proof.
    intros g st p v H Hgt; unfold envs_same in H.
    destruct (PathMap.get p g) as [? |] eqn:Heq; eauto.
    rewrite H,Hgt in Heq; discriminate.
  Qed.
  
  Definition envs_type (gsenum : genv_senum) (g : gamma) (st : state) : Prop :=
    forall (p : path) (t : typ) (v : Sval),
      PathMap.get p g = Some t ->
      PathMap.get p (fst st) = Some v -> val_typ gsenum v t.

  Definition typ_of_expr (e : expr) : typ :=
    match e with
    | MkExpression _ _ t _ => t
    end.
  (**[]*)
  
  (** Expression typing. *)
  Definition expr_types (g : gamma) (e : expr) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (p : path) (st : state),
      read_one_bit_reads read_one_bit ->
      envs_same g st -> envs_type ge g st ->
      (exists v, run_expr ge read_one_bit p st e v) /\
      forall v, run_expr ge read_one_bit p st e v ->
           val_typ (ge_senum ge) v (typ_of_expr e).
  (**[]*)

  (** Statement typing. *)
  Definition stmt_types (g g' : gamma) (s : stmt) : Prop :=
    forall (read_one_bit : option bool -> bool -> Prop)
      (ge : genv) (p : path) (st : state),
      read_one_bit_reads read_one_bit ->
      envs_same g st -> envs_type ge g st ->
      (exists st' sig, run_stmt ge read_one_bit p st s st' sig) /\
      forall st' sig, run_stmt ge read_one_bit p st s st' sig ->
                 envs_same g' st' /\ envs_type ge g' st'.
End TypingDefs.

Notation "Γ '⊢e' e"
  := (expr_types Γ e) (at level 80, no associativity) : type_scope.
Notation "Γ1 '⊢s' s ⊣ Γ2"
  := (stmt_types Γ1 Γ2 s) (at level 80, no associativity) : type_scope.

(* TODO. *)
Section Soundness.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation stmt := (@Statement tags_t).
  Notation signal := (@signal tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).

  Context `{T : @Target tags_t expr}.

  Notation run_expr := (@exec_expr tags_t dummy T).
  Notation run_stmt := (@exec_stmt tags_t dummy T).

  Variable (Γ : @gamma tags_t).

  Local Hint Unfold expr_types : core.
  Local Hint Constructors exec_expr : core.
  Local Hint Constructors val_typ : core.
  
  Ltac soundtac :=
    autounfold with *;
    intros rob ge p st Hrob Henvs Henvt;
    split; eauto;
    try (intros v Hrn; inversion Hrn; subst; cbn; eauto).
  
  Lemma bool_sound : forall tag b dir,
      Γ ⊢e MkExpression tag (ExpBool b) TypBool dir.
  Proof.
    intros; soundtac.
  Qed.
  
  Lemma arbitrary_int_sound : forall tag i z dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z None)) TypInteger dir.
  Proof.
    intros; soundtac.
  Qed.

  Lemma unsigned_int_sound : forall tag i z w dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z (Some (w,false)))) (TypBit w) dir.
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma signed_int_sound : forall tag i z w dir,
      Γ ⊢e
        MkExpression
        tag (ExpInt (P4Int.Build_t _ i z (Some (w,true)))) (TypInt w) dir.
  Proof.
    intros tag i z dir; soundtac.
    (* TODO: need some result about [P4Arith.to_loptbool]. *)
  Admitted.

  Lemma string_sound : forall tag s dir,
      Γ ⊢e MkExpression tag (ExpString s) TypString dir.
  Proof.
    intros; soundtac.
  Qed.

  Lemma name_sound : forall tag x loc t dir,
      typ_of_loc loc Γ = Some t ->
      Γ ⊢e MkExpression tag (ExpName x loc) t dir.
  Proof.
    intros i x l t d Hgt; soundtac.
    - destruct l as [lp | lp]; simpl in Hgt;
        eapply envs_same_some_l in Hgt as [v Hv]; eauto.
      exists v. constructor; simpl.
      (** TODO:
          1. Need type preservation to [eval_val_to_sval].
          2. Perhaps [envs_same] needs to include [genv]. *)
      admit.
    - destruct l as [lp | lp]; simpl in Hgt;
        simpl in *; eauto.
  Admitted.

  Lemma array_access_sound : forall tag arry idx ts dir n,
      typ_of_expr arry = TypArray (TypHeader ts) n ->
      typ_of_expr idx  = TypBit n ->
      Γ ⊢e arry ->
      Γ ⊢e idx ->
      Γ ⊢e MkExpression tag (ExpArrayAccess arry idx) (TypHeader ts) dir.
  Proof.
    intros i e1 e2 ts d n Ht1 Ht2 He1 He2;
      autounfold with * in *.
    intros rob ge p st Hrob Henvs Henvt.
    pose proof He1 rob ge p st Hrob Henvs Henvt as [[v1 Hev1] He1']; clear He1.
    pose proof He2 rob ge p st Hrob Henvs Henvt as [[v2 Hev2] He2']; clear He2.
    split.
    - pose proof He1' v1 Hev1 as Hv1.
      pose proof He2' v2 Hev2 as Hv2.
      rewrite Ht1 in Hv1; rewrite Ht2 in Hv2.
      inversion Hv1; inversion Hv2; subst.
      (* Need to know [N_of_value idx < n]. *) admit.
    - intros v' Haa; inversion Haa; clear Haa; subst; simpl.
      rename H4 into He2; rename H10 into He1;
        rename H7 into Hsval; rename H9 into Haa;
          rename H11 into Huninit.
      pose proof He1' _ He1 as Hv1.
      pose proof He2' _ He2 as Hv2.
      rewrite Ht1 in Hv1; rewrite Ht2 in Hv2.
      inversion Hv1; inversion Hv2; subst.
      (* Need result about [Znth_def]. *)
  Admitted.

  Lemma bigstring_access_sound : forall tag bits lo hi dir w,
      (lo <= hi < w)%N ->
      typ_of_expr bits = TypBit w ->
      Γ ⊢e bits ->
      Γ ⊢e MkExpression
        tag (ExpBitStringAccess bits lo hi)
        (TypBit (hi - lo + 1)%N) dir.
  Proof.
    intros i e lo hi d w Hlwh Ht He.
    autounfold with * in *.
    intros rob ge p st Hrob Henvs Henvt.
    pose proof He rob ge p st Hrob Henvs Henvt as [[v Hev] He']; clear He.
    split.
    - apply He' in Hev as Hv; rewrite Ht in Hv;
        inversion Hv; subst; rename v0 into bits.
      exists (ValBaseBit (bitstring_slice bits (N.to_nat lo) (N.to_nat hi))).
      eapply exec_expr_bitstring_access with (wn := length bits); eauto; lia.
    - clear v Hev. intros v Hrn; inversion Hrn; subst; simpl.
      rename H8 into He; rename H9 into Hsval; rename H12 into Hlhw.
      (* Need result about [bitstring_slice]. *) admit.
  Admitted.
  
  Lemma list_sound : forall tag es dir,
      Forall (fun e => Γ ⊢e e) es ->
      Γ ⊢e MkExpression tag (ExpList es)
        (TypTuple (map typ_of_expr es)) dir.
  Proof.
    intros i es d Hes. autounfold with * in *.
    intros rob ge p st Hrob Henvs Henvt.
    rewrite Forall_forall in Hes.
      specialize Hes with
          (read_one_bit:=rob) (ge:=ge) (p:=p) (st:=st).
      pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
        simpl in Hes'; clear Hes; rename Hes' into Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes Henvs as Hes';
        simpl in Hes'; clear Hes.
      pose proof reduce_inner_impl _ _ _ _ Hes' Henvt as Hes;
        simpl in Hes; clear Hes'.
      rewrite split_impl_conj in Hes.
      destruct Hes as [Hrnes Htyps]. split.
    - clear Htyps; rewrite <- Forall_forall in Hrnes.
      rewrite Forall_exists_factor in Hrnes.
      destruct Hrnes as [vs Hvs]; eauto.
    - clear Hrnes; intros v Hrn; simpl.
      inversion Hrn; subst; clear Hrn.
      rename H6 into Hesvs.
      apply forall_Forall2 with (bs := vs) in Htyps;
        eauto using Forall2_length.
      apply Forall2_impl with
          (R := run_expr ge rob p st)
          (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Htyps; auto.
      rewrite Forall2_flip, Forall2_map_r in Htyps; auto.
  Qed.
  
  Lemma record_sound : forall tag es dir,
      Forall (fun e => Γ ⊢e e) (map snd es) ->
      Γ ⊢e
        MkExpression
        tag (ExpRecord es)
        (TypRecord (map (fun '(x,e) => (x,typ_of_expr e)) es)) dir.
  Proof.
    intros i es d Hes.
    autounfold with * in *.
    intros rob ge p st Hrob Henvs Henvt.
    rewrite Forall_forall in Hes.
    specialize Hes with
        (read_one_bit:=rob) (ge:=ge) (p:=p) (st:=st).
    pose proof reduce_inner_impl _ _ _ _ Hes Hrob as Hes';
        simpl in Hes'; clear Hes; rename Hes' into Hes.
    pose proof reduce_inner_impl _ _ _ _ Hes Henvs as Hes';
      simpl in Hes'; clear Hes.
    pose proof reduce_inner_impl _ _ _ _ Hes' Henvt as Hes;
      simpl in Hes; clear Hes'.
    rewrite split_impl_conj in Hes.
    destruct Hes as [Hrns Htyps]. split.
    - clear Htyps. rewrite <- Forall_forall in Hrns.
      rewrite Forall_exists_factor in Hrns.
      destruct Hrns as [vs Hvs].
      rewrite AList.Forall2_all_values
        with (ks := map fst es) in Hvs.
      + rewrite combine_map_fst_snd in Hvs; eauto.
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
      rewrite <- Hmf in Heskvs.
      rewrite <- AList.Forall2_all_values in Heskvs.
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
              (R := run_expr ge rob p st)
              (Q := fun e v => val_typ (ge_senum ge) v (typ_of_expr e)) in Hff2; auto.
          rewrite Forall2_flip,Forall2_map_r in Hff2; assumption.
      + repeat rewrite map_length; reflexivity.
      + rewrite Hmf; repeat rewrite map_length; reflexivity.
  Qed.

  (** Evidence for a type being a numeric of a given width. *)
  Inductive numeric_width (w : N) : typ -> Prop :=
  | numeric_width_bit : numeric_width w (TypBit w)
  | numeric_width_int : numeric_width w (TypInt w).

  Ltac inv_numeric_width :=
    match goal with
    | H: numeric_width _ _ |- _ => inversion H; subst
    end.
  
  (** Evidence for a type being numeric. *)
  Inductive numeric : typ -> Prop :=
  | NumericFixed (w : N) τ :
      numeric_width w τ -> numeric τ
  | NumericArbitrary :
      numeric TypInteger.

  Ltac inv_numeric :=
    match goal with
    | H: numeric _ |- _ => inversion H; subst; try inv_numeric_width
    end.

  (** Evidence a unary operation is valid for a type. *)
  Inductive unary_type : OpUni -> typ -> typ -> Prop :=
  | UTNot :
      unary_type Not TypBool TypBool
  | UTBitNot w τ :
      numeric_width w τ -> unary_type BitNot τ τ
  | UTUMinus τ :
      numeric τ -> unary_type UMinus τ τ.

  Local Hint Constructors exec_val : core.
  Local Hint Unfold read_detbit : core.
  Local Hint Unfold sval_to_val : core.
  Local Hint Unfold val_to_sval : core.
  
  Lemma val_to_sval_ex : forall v,
      @val_to_sval tags_t v (ValueBaseMap Some v).
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

  Lemma unary_type_eq : forall o t t', unary_type o t t' -> t = t'.
  Proof.
    intros ? ? ? H; inversion H; subst; auto.
  Qed.

  Lemma eval_unary_op_preserves_typ : forall o v v' g t t',
      unary_type o t t' ->
      Ops.Ops.eval_unary_op o v = Some v' ->
      val_typ g v t -> val_typ g v' t'.
  Proof.
    intros o v v' g t t' Hut Heval Hvt;
      inversion Hut; subst;
        inversion Hvt; subst;
          try (inversion Heval; subst; auto; assumption).
    - unfold Ops.Ops.eval_unary_op in Heval.
      destruct (P4Arith.BitArith.from_lbool v0)
        as [w' n'] eqn:Heqfromlbool.
      injection Heval as Hv'. rewrite <- Hv'.
      inversion H; subst; clear H.
      (** TODO: need helper lemma about
          [P4Arith.to_lbool] and [P4Arith.BitArith.bit_not]. *)
  Admitted.
  
  Lemma unary_op_sound : forall tag o e t dir,
      unary_type o (typ_of_expr e) t ->
      Γ ⊢e e ->
      Γ ⊢e MkExpression tag (ExpUnaryOp o e) t dir.
  Proof.
    intros i o e t d Hut He.
    autounfold with * in *;
      intros rob ge p st Hrob Henvs Henvt.
    specialize He with rob ge p st.
    pose proof He Hrob Henvs Henvt as [[v Hev] Hvt]; clear He; split.
    - apply Hvt in Hev as Hv; clear Hvt.
      assert (exists v', sval_to_val rob v v')
        by eauto using exec_val_exists.
      destruct H as [v' Hv'].
      assert (exists v''', Ops.Ops.eval_unary_op o v' = Some v''').
      (* Maybe try to factor this out?
        Lemma exists_eval_unary_op : forall o v,
          exists v', Ops.Ops.eval_unary_op o v = Some v'. *)
      { destruct (Ops.Ops.eval_unary_op o v') as [v'' |] eqn:Heqop; eauto.
        inversion Hut; subst; try inv_numeric; try inv_numeric_width;
          match goal with
          | H: _ = typ_of_expr ?e,
               Hv: val_typ _ ?v (typ_of_expr ?e),
                   Hv': sval_to_val _ ?v _
            |- _ => rewrite <- H in *; inversion Hv; inversion Hv'; subst
          end; simpl in *; try discriminate. }
      firstorder eauto.
    - clear v Hev; intros v Hev.
      inversion Hev; subst; simpl in *.
      pose proof Hvt _ H7 as Hargsv.
      assert (typ_of_expr e = t) by eauto using unary_type_eq.
      rewrite H in *. clear e Hvt Hev H7 H.
      pose proof exec_val_preserves_typ
           _ _ _ H8 (ge_senum ge) as Hevpt.
      assert (Hgsb : exists gsb,
                 FuncAsMap.related
                   (AList.all_values (exec_val rob))
                   (ge_senum ge) gsb).
      { admit. }
      destruct Hgsb as [gsb Hgsb].
      pose proof Hevpt _ Hgsb _ Hargsv as Hargv.
      assert (Hv0: val_typ gsb v0 t)
        by eauto using eval_unary_op_preserves_typ.
      assert (Hgsb' :
                FuncAsMap.related
                  (AList.all_values val_to_sval)
                  gsb (ge_senum ge)).
      { (* TODO:
           Need assumption
           [read_one_bit_inverse rob read_detbit]. *)
        admit. }
      eauto using exec_val_preserves_typ.
  Admitted.

  (** Evidence a binary operation is valid for given types. *)
  Variant binary_type : OpBin -> typ -> typ -> typ -> Prop :=
  | BTPlusPlusBit w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypBit w1) t2 (TypBit (w1 + w2)%N)
  | BTPlusPlusInt w1 w2 t2 :
      numeric_width w2 t2 ->
      binary_type PlusPlus (TypInt w1) t2 (TypInt (w1 + w2)%N)
  | BTShl w1 t1 t2 :
      numeric_width w1 t1 -> numeric t2 ->
      binary_type Shl t1 t2 t1
  | BTShrBit w1 w2 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 (TypBit w2) t1
  | BTShlInteger w1 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 TypInteger t1
  | BTShrInteger w1 t1 :
      numeric_width w1 t1 ->
      binary_type Shr t1 TypInteger t1
  | BTEq t :
      binary_type Eq t t TypBool
  | BTNotEq t :
      binary_type NotEq t t TypBool
  | BTPlus t :
      numeric t ->
      binary_type Plus t t t
  | BTMinus t :
      numeric t ->
      binary_type Minus t t t
  | BTMul t :
      numeric t ->
      binary_type Mul t t t
  | BTDiv t :
      numeric t ->
      binary_type Div t t t
  | BTMod t :
      numeric t ->
      binary_type Mod t t t
  | BTLe t :
      numeric t ->
      binary_type Le t t TypBool
  | BTGe t :
      numeric t ->
      binary_type Ge t t TypBool
  | BTLt t :
      numeric t ->
      binary_type Lt t t TypBool
  | BTGt t :
      numeric t ->
      binary_type Gt t t TypBool
  | BTPlusSat w t :
      numeric_width w t ->
      binary_type PlusSat t t t
  | BTMinusSat w t :
      numeric_width w t ->
      binary_type MinusSat t t t
  | BTBitAnd w t :
      numeric_width w t ->
      binary_type BitAnd t t t
  | BTBitOr w t :
      numeric_width w t ->
      binary_type BitOr t t t
  | BTBitXor w t :
      numeric_width w t ->
      binary_type BitXor t t t
  | BTAnd :
      binary_type And TypBool TypBool TypBool
  | BTOr :
      binary_type Or TypBool TypBool TypBool.

  Lemma binary_op_sound : forall tag o t e1 e2 dir,
      binary_type o (typ_of_expr e1) (typ_of_expr e2) t ->
      Γ ⊢e e1 -> Γ ⊢e e2 ->
      Γ ⊢e MkExpression tag (ExpBinaryOp o (e1,e2)) t dir.
  Proof.
  Admitted.

  Inductive cast_type : typ -> typ -> Prop :=
  | CTBool w :
      cast_type (TypBit w) TypBool
  | CTBit t w :
      match t with
      | TypBool
      | TypBit _
      | TypInt _
      | TypInteger
      | TypEnum _ (Some (TypBit _)) _ => True
      | _ => False
      end ->
      cast_type t (TypBit w)
  | CTInt t w :
      match t with
      | TypBool
      | TypBit _
      | TypInt _
      | TypInteger
      | TypEnum _ (Some (TypInt _)) _ => True
      | _ => False
      end ->
      cast_type t (TypInt w)
  | CTEnum t1 t2 enum fields :
      match t1, t2 with
      | TypBit _, TypBit _
      | TypInt _, TypInt _
      | TypEnum _ (Some (TypBit _)) _, TypBit _
      | TypEnum _ (Some (TypInt _)) _, TypInt _ => True
      | _, _ => False
      end ->
      cast_type t1 (TypEnum enum (Some t2) fields)
  | CTNewType x t t' :
      cast_type t t' ->
      cast_type t (TypNewType x t')
  | CTStructOfTuple ts xts :
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      cast_type (TypTuple ts) (TypStruct xts)
  | CTStructOfRecord xts xts' :
      AList.all_values cast_type xts xts' ->
      cast_type (TypRecord xts) (TypStruct xts')
  | CTHeaderOfTuple ts xts :
      Forall2 (fun t xt => cast_type t (snd xt)) ts xts ->
      cast_type (TypTuple ts) (TypHeader xts)
  | CTHeaderOfRecord xts xts' :
      AList.all_values cast_type xts xts' ->
      cast_type (TypRecord xts) (TypHeader xts')
  | CTTuple ts ts' :
      Forall2 cast_type ts ts' ->
      cast_type (TypTuple ts) (TypTuple ts').
  
  Lemma cast_sound : forall tag e t dir,
      cast_type (typ_of_expr e) t ->
      Γ ⊢e e ->
      Γ ⊢e MkExpression tag (ExpCast t e) t dir.
  Proof.
  Admitted.

  Lemma enum_sound : forall tag tname member ename members dir,
      (* TODO: need [ge] of [genv].
         name_to_type ge tname = Some (TypEnum ename None members) ->*)
      In member members ->
      Γ ⊢e MkExpression tag (ExpTypeMember tname member) (TypEnum ename None members) dir.
  Proof.
  Admitted.

  Lemma senum_sound : forall tag tname member ename t members dir,
      (*name_to_type ge tname = Some (TypEnum ename (Some etyp) members) ->
      IdentMap.get ename (ge_senum ge) = Some fields ->*)
      In member members ->
      Γ ⊢e MkExpression tag (ExpTypeMember tname member) (TypEnum ename (Some t) members) dir.
  Proof.
  Admitted.
End Soundness.
