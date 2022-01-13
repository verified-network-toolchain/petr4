Require Import Coq.Strings.String Coq.ZArith.ZArith Coq.Lists.List.
Require Import Poulet4.Value Poulet4.Typed Poulet4.P4String
               Poulet4.SyntaxUtil Poulet4.AList VST.zlist.Zlist.
Require Import Poulet4.P4Notations Poulet4.Monads.Monad Poulet4.Monads.Option.
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

  Definition sval_to_val (read_one_bit : option bool -> bool -> Prop) := 
    exec_val read_one_bit.

  Definition svals_to_vals (read_one_bit : option bool -> bool -> Prop) :=
    Forall2 (exec_val read_one_bit).

  Definition val_to_sval := 
    exec_val read_detbit.

  Definition vals_to_svals := 
    Forall2 (exec_val read_detbit).

  Fixpoint eval_val_to_sval (val: Val): Sval :=
    let fix eval_val_to_svals (vl: list Val): list Sval :=
      match vl with
      | [] => []
      | s :: rest => eval_val_to_sval s :: eval_val_to_svals rest
      end in
    let fix val_to_avals (sl: StringAList Val): StringAList Sval :=
      match sl with
      | [] => []
      | (k, s) :: rest => (k, eval_val_to_sval s) :: val_to_avals rest
      end in
    match val with
    | ValBaseNull => ValBaseNull
    | ValBaseBool b => ValBaseBool (Some b)
    | ValBaseInteger z => ValBaseInteger z
    | ValBaseBit vl => ValBaseBit (map Some vl)
    | ValBaseInt vl => ValBaseInt (map Some vl)
    | ValBaseVarbit m vl => ValBaseVarbit m (map Some vl)
    | ValBaseString s => ValBaseString s
    | ValBaseTuple vl => ValBaseTuple (eval_val_to_svals vl)
    | ValBaseError s => ValBaseError s
    | ValBaseMatchKind s => ValBaseMatchKind s
    | ValBaseStruct rl => ValBaseStruct (val_to_avals rl)
    | ValBaseHeader rl b => ValBaseHeader (val_to_avals rl) (Some b)
    | ValBaseUnion rl => ValBaseUnion (val_to_avals rl)
    | ValBaseStack vl n => ValBaseStack (eval_val_to_svals vl) n
    | ValBaseEnumField t e => ValBaseEnumField t e
    | ValBaseSenumField t v => ValBaseSenumField t (eval_val_to_sval v)
    end.

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
