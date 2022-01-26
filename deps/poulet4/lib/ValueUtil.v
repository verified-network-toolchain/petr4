Require Import Coq.Strings.String Coq.ZArith.ZArith Coq.Lists.List.
Require Import Poulet4.Value Poulet4.Typed Poulet4.P4String
               Poulet4.SyntaxUtil Poulet4.AList VST.zlist.Zlist.
Require Import Poulet4.P4Notations Poulet4.Monads.Monad Poulet4.Monads.Option
        Poulet4.ForallMap.
Import ListNotations.

Section ValueUtil.
  Context {tags_t: Type}.
  Notation Val := (@ValueBase bool).
  Notation Sval := (@ValueBase (option bool)).

  Inductive read_ndetbit : option bool -> bool -> Prop :=
  | read_none : forall b, read_ndetbit None b
  | read_some : forall b, read_ndetbit (Some b) b.

  Inductive strict_read_ndetbit : option bool -> bool -> Prop :=
    | strict_read_some : forall b, strict_read_ndetbit (Some b) b.

  Definition read_detbit (b : bool) (b': option bool) :=
    b' = Some b.

  Inductive exec_val {A B} (read_one_bit : A -> B -> Prop) :
                    @ValueBase A -> @ValueBase B -> Prop :=
    | exec_val_null : exec_val read_one_bit ValBaseNull ValBaseNull
    | exec_val_bool : forall b b',
                      read_one_bit b b' ->
                      exec_val read_one_bit (ValBaseBool b) (ValBaseBool b')
    | exec_val_integer : forall n,
                        exec_val read_one_bit (ValBaseInteger n) (ValBaseInteger n)
    | exec_val_bit : forall lb lb',
                    Forall2 read_one_bit lb lb' ->
                    exec_val read_one_bit (ValBaseBit lb) (ValBaseBit lb')
    | exec_val_int : forall lb lb',
                    Forall2 read_one_bit lb lb' ->
                    exec_val read_one_bit (ValBaseInt lb) (ValBaseInt lb')
    | exec_val_varbit : forall max lb lb',
                        Forall2 read_one_bit lb lb' ->
                        exec_val read_one_bit (ValBaseVarbit max lb) (ValBaseVarbit max lb')
    | exec_val_string : forall s,
                        exec_val read_one_bit (ValBaseString s) (ValBaseString s)
    | exec_val_tuple : forall lv lv',
                      Forall2 (exec_val read_one_bit) lv lv' ->
                      exec_val read_one_bit (ValBaseTuple lv) (ValBaseTuple lv')
    | exec_val_error: forall s,
                      exec_val read_one_bit (ValBaseError s) (ValBaseError s)
    | exec_val_matchkind: forall s,
                          exec_val read_one_bit (ValBaseMatchKind s) (ValBaseMatchKind s)
    | exec_val_struct : forall kvs kvs',
                        AList.all_values (exec_val read_one_bit) kvs kvs' ->
                        exec_val read_one_bit (ValBaseStruct kvs) (ValBaseStruct kvs')
    (* Invariant: when validity bit is None, kvs are also None. *)
    | exec_val_header : forall kvs kvs' b b',
                        read_one_bit b b' ->
                        AList.all_values (exec_val read_one_bit) kvs kvs' ->
                        exec_val read_one_bit (ValBaseHeader kvs b) (ValBaseHeader kvs' b')
    | exec_val_union : forall kvs kvs',
                      AList.all_values (exec_val read_one_bit) kvs kvs' ->
                      exec_val read_one_bit (ValBaseUnion kvs) (ValBaseUnion kvs')
    | exec_val_stack : forall lv lv' next,
                      Forall2 (exec_val read_one_bit) lv lv' ->
                      exec_val read_one_bit (ValBaseStack lv next) (ValBaseStack lv' next)
    | exec_val_enum_field : forall typ_name enum_name,
                            exec_val read_one_bit (ValBaseEnumField typ_name enum_name)
                                                  (ValBaseEnumField typ_name enum_name)
    | exec_val_senum_field : forall typ_name v v',
                            exec_val read_one_bit v v' ->
                            exec_val read_one_bit (ValBaseSenumField typ_name v)
                                                  (ValBaseSenumField typ_name v').

  Section ExecValInd.
    Variables (A B : Type).
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
    Hypothesis HStack : forall vas vbs next,
        Forall2 (exec_val R) vas vbs ->
        Forall2 P vas vbs ->
        P (ValBaseStack vas next) (ValBaseStack vbs next).
    Hypothesis HEnumField : forall type_name enum_name,
        P
          (ValBaseEnumField type_name enum_name)
          (ValBaseEnumField type_name enum_name).
    Hypothesis HSenumField : forall type_name va vb,
        exec_val R va vb -> P va vb ->
        P
          (ValBaseSenumField type_name va)
          (ValBaseSenumField type_name vb).

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
        | exec_val_error _ s => HError s
        | exec_val_matchkind _ s => HMatchkind s
        | exec_val_struct _ _ _ evs => HStruct _ _ evs (alind evs)
        | exec_val_header _ _ _ _ _ r evs
          => HHeader _ _ _ _ r evs (alind evs)
        | exec_val_union _ _ _ evs => HUnion _ _ evs (alind evs)
        | exec_val_stack _ _ _ next evs
          => HStack _ _ next evs (lind evs)
        | exec_val_enum_field _ tn en => HEnumField tn en
        | exec_val_senum_field _ tn _ _ ev
          => HSenumField tn _ _ ev (evind _ _ ev)
        end.
  End ExecValInd.

  Section LvalueInd.
    Notation LV := (@Value.ValueLvalue tags_t).
    Notation PLV := (@Value.ValuePreLvalue tags_t).

    Variables (PLval: LV -> Prop).
    Variables (PPreLval: PLV -> Prop).

    Hypothesis (HMkLval: forall plv typ,
                   PPreLval plv ->
                   PLval (Value.MkValueLvalue plv typ)).
    Hypothesis (HName: forall name loc,
                   PPreLval (Value.ValLeftName name loc)).
    Hypothesis (HMember: forall lv fname,
                   PLval lv ->
                   PPreLval (Value.ValLeftMember lv fname)).
    Hypothesis (HBitAccess: forall lv hi lo,
                   PLval lv ->
                   PPreLval (Value.ValLeftBitAccess lv hi lo)).
    Hypothesis (HArrayAccess: forall lv idx,
                   PLval lv ->
                   PPreLval (Value.ValLeftArrayAccess lv idx)).

    Hypothesis oops: forall A: Prop, A.

    Fixpoint lvalue_mut_ind (lv: LV) : PLval lv :=
      match lv with
      | Value.MkValueLvalue plv _ =>
        HMkLval _ _ (pre_lvalue_mut_ind plv)
      end
    with pre_lvalue_mut_ind (plv: PLV) : PPreLval plv :=
      match plv with
      | Value.ValLeftName _ _ =>
        HName _ _
      | Value.ValLeftMember lv _ =>
        HMember _ _ (lvalue_mut_ind lv)
      | Value.ValLeftBitAccess lv _ _ =>
        HBitAccess _ _ _ (lvalue_mut_ind lv)
      | Value.ValLeftArrayAccess lv _ =>
        HArrayAccess _ _ (lvalue_mut_ind lv)
      end.

  End LvalueInd.

  Definition sval_to_val (read_one_bit : option bool -> bool -> Prop) :=
    exec_val read_one_bit.

  Definition svals_to_vals (read_one_bit : option bool -> bool -> Prop) :=
    Forall2 (sval_to_val read_one_bit).

  Definition val_to_sval :=
    exec_val read_detbit.

  Definition vals_to_svals :=
    Forall2 val_to_sval.

  Definition eval_val_to_sval : Val -> Sval := ValueBaseMap Some.

  Fixpoint uninit_sval_of_typ
           (hvalid : option bool) (typ : @P4Type tags_t): option Sval :=
    match typ with
    | TypBool => Some (ValBaseBool None)
    | TypInt w => Some (ValBaseInt (repeat None (N.to_nat w)))
    | TypBit w => Some (ValBaseBit (repeat None (N.to_nat w)))
    | TypArray typ size =>
      if (0 <? size)%N then
        let^ sv := uninit_sval_of_typ hvalid typ in
        ValBaseStack (repeat sv (N.to_nat size)) 0
      else None
    | TypTuple typs
    | TypList typs =>
      sequence (List.map (uninit_sval_of_typ hvalid) typs) >>| ValBaseTuple
    | TypHeader fields =>
      let^ kvs :=
         sequence
           (List.map
              (fun '({| P4String.str := x |}, t) =>
                 uninit_sval_of_typ hvalid t >>| pair x)
              fields) in
      ValBaseHeader kvs hvalid
    | TypHeaderUnion fields =>
      sequence
        (List.map
           (fun '({| P4String.str := x |}, t) =>
              uninit_sval_of_typ hvalid t >>| pair x)
           fields) >>| ValBaseUnion
    | TypRecord fields
    | TypStruct fields =>
      sequence
        (List.map
           (fun '({| P4String.str := x |}, t) =>
              uninit_sval_of_typ hvalid t >>| pair x)
           fields) >>| ValBaseStruct
    | TypEnum tname None (mem :: _) =>
      Some (ValBaseEnumField (str tname) (str mem))
    | TypNewType _ typ' => uninit_sval_of_typ hvalid typ'
    (* TypTypeName should have been already resolved *)
    | TypTypeName _ => None
    (* Two possibilities for senum:
       1. Use the default values (similar to the enum type):
       For enum values with an underlying type the default value is 0. (7.3.)
       2. Use the underlying types's uninitialized values:
       Since an senum's underlying type is either bit or int, it can also be uninitialized
       by the underlying types.
       The current implementation follows the option 2.
       Rudy's note: attempt create a default [ValBaseSenumField]
       for type preservation proof. *)
    | TypEnum {| P4String.str := X |} (Some typ') _ =>
      uninit_sval_of_typ hvalid typ' >>| ValBaseSenumField X
    (* The P4Spec does not specify the unintialized values for the following types,
       so we use the default values for now. (7.3.)
       Note that this design choice makes the svals output from uninit_sval_of_typ different
       from uninit_sval_of_sval and val_to_sval. *)
    | TypVarBit w => Some (ValBaseVarbit w [])
    | TypInteger => Some (ValBaseInteger 0)
    | TypError => Some (ValBaseError "NoError")
    | _ => None
    end.
  (* Type without uninitialized svals:
      TypString: can be used only for compile-time constant string values (7.1.),
                  one cannot declare variables with a string type (7.1.5.),
                  so it cannot be uninitialized.
      TypVoid: It contains no values (7.1.1.).
      TypSet, TypMatchKind: They do not have default values (7.3.).
      TypControl, TypParser, TypExtern, TypFunction, TypAction,
      TypTable, TypPackage, TypSpecializedType, TypConstructor
  *)

  (* The definition of uninit_sval_of_sval follows val_to_sval instead of uninit_sval_of_typ.
    The discrepancies between uninit_sval_of_sval and uninit_sval_of_typ:
    1. ValBaseInteger, ValBaseVarbit, ValBaseError, ValBaseEnumField - different output sval
    2. ValBaseString, ValBaseMatchKind, ValBaseNull - not exist in uninit_sval_of_typ *)
  Fixpoint uninit_sval_of_sval (hvalid : option bool) (v : Sval): Sval :=
    match v with
    | ValBaseBool _ => ValBaseBool None
    | ValBaseBit bits => ValBaseBit (List.map (fun _ => None) bits)
    | ValBaseInt bits => ValBaseInt (List.map (fun _ => None) bits)
    (* May need change after clarifying the uninit sval of varbit *)
    | ValBaseVarbit max bits => ValBaseVarbit max (List.map (fun _ => None) bits)
    | ValBaseTuple vs => ValBaseTuple (List.map (uninit_sval_of_sval hvalid) vs)
    | ValBaseStruct kvs => ValBaseStruct (kv_map (uninit_sval_of_sval hvalid) kvs)
    | ValBaseHeader kvs is_valid => ValBaseHeader (kv_map (uninit_sval_of_sval hvalid) kvs) hvalid
    | ValBaseUnion kvs => ValBaseUnion (kv_map (uninit_sval_of_sval hvalid) kvs)
    | ValBaseStack vs next => ValBaseStack (List.map (uninit_sval_of_sval hvalid) vs) next
    | ValBaseSenumField typ_name v =>  ValBaseSenumField typ_name (uninit_sval_of_sval hvalid v)
    | _ => v
    end.

End ValueUtil.

Local Hint Unfold read_detbit : core.
Local Hint Unfold sval_to_val : core.
Local Hint Unfold val_to_sval : core.
Local Hint Constructors exec_val : core.
    
Lemma val_to_sval_ex : forall v,
    val_to_sval v (ValueBaseMap Some v).
Proof.
  autounfold with *; intro v.
  induction v using (custom_ValueBase_ind bool); simpl; eauto;
    try (constructor; rewrite <- Forall2_map_r, Forall2_Forall;
         (rewrite Forall_forall; reflexivity) || assumption);
    try (constructor; auto; unfold AList.all_values;
         rewrite <- Forall2_map_r, Forall2_Forall;
         rewrite Forall_snd in H;
         apply Forall_and; rewrite Forall_forall in *;
         intros [? ?]; firstorder).
Qed.

Lemma val_to_sval_iff:
  forall v1 v2, val_to_sval v1 v2 <-> eval_val_to_sval v1 = v2.
Proof.
  unfold eval_val_to_sval.
  intros; split; intros H; subst; eauto using val_to_sval_ex.
  unfold val_to_sval, read_detbit in H.
  induction H using custom_exec_val_ind; cbn in *; subst;
    try match goal with
        | H:Forall2 (fun b b' => b' = Some b) ?l _
          |- context [map Some ?l]
          => rewrite Forall2_flip in H;
              rewrite Forall2_map_r with
                  (f:=Some) (R:=eq) in H;
              rewrite Forall2_eq in H; subst
        | H: Forall2 (fun _ _ => ValueBaseMap Some _ = _) ?l _
          |- context [map (ValueBaseMap Some) ?l]
          => rewrite Forall2_map_l,Forall2_eq in H; subst
        | H:all_values (fun _ _ => ValueBaseMap Some _ = _) ?kvs _
          |- context [map (fun '(x,v) => (x,ValueBaseMap Some v)) ?kvs]
          => unfold all_values in H;
              rewrite Forall2_conj in H;
              destruct H as [Hfst Hsnd];
              rewrite Forall2_map_both,Forall2_eq in Hfst,Hsnd;
              rewrite <- map_map in Hsnd;
              rewrite map_pat_combine,map_id,
              Hfst,Hsnd,combine_map_fst_snd
        end; reflexivity.
Qed.

Lemma sval_to_val_eval_val_to_sval : forall (rob : option bool -> bool -> Prop) v,
    (forall b, rob (Some b) b) ->
    sval_to_val rob (eval_val_to_sval v) v.
Proof.
  intros rob v H; autounfold with *; unfold eval_val_to_sval.
  induction v using custom_ValueBase_ind; cbn; auto;
    try (constructor;
         rewrite <- Forall2_map_l,
         Forall2_Forall;
         assumption || (rewrite Forall_forall; auto); assumption);
    try  match goal with
         | H: Forall (fun '(_,v) => exec_val rob (ValueBaseMap Some v) v) ?vs
           |- context [map (fun '(x,v) => (x, ValueBaseMap Some v)) ?vs]
           => constructor; auto; unfold all_values;
               rewrite Forall2_conj;
               rewrite Forall2_map_both with (f:=fst) (g:=fst);
               rewrite Forall2_map_both with (f:=snd) (g:=snd);
               rewrite Forall2_eq,map_fst_map,map_snd_map,map_id,
               <- Forall2_map_l,Forall2_Forall;
               rewrite Forall_map; unfold Basics.compose;
                 rewrite Forall_snd in H; split; reflexivity || assumption
         end.
Qed.
