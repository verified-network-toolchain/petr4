Require Import Coq.Strings.String Coq.ZArith.ZArith Coq.Lists.List.
Require Import Poulet4.Value Poulet4.Typed Poulet4.P4String
               Poulet4.SyntaxUtil Poulet4.AList Poulet4.Sublist.
Require Import Poulet4.P4Notations.
Import ListNotations.

Section ValueUtil.
  Context {tags_t: Type} {inhabitant_tags_t : Inhabitant tags_t}.
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
    | exec_val_record : forall kvs kvs',
                        AList.all_values (exec_val read_one_bit) kvs kvs' ->
                        exec_val read_one_bit (ValBaseRecord kvs) (ValBaseRecord kvs')
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
    | exec_val_stack : forall lv lv' size next,
                      Forall2 (exec_val read_one_bit) lv lv' ->
                      exec_val read_one_bit (ValBaseStack lv size next) (ValBaseStack lv' size next)
    | exec_val_enum_field : forall typ_name enum_name,
                            exec_val read_one_bit (ValBaseEnumField typ_name enum_name) 
                                                  (ValBaseEnumField typ_name enum_name)
    | exec_val_senum_field : forall typ_name enum_name v v',
                            exec_val read_one_bit v v' ->
                            exec_val read_one_bit (ValBaseSenumField typ_name enum_name v) 
                                                  (ValBaseSenumField typ_name enum_name v')
    (*| exec_val_senum : forall kvs kvs',
                      AList.all_values (exec_val read_one_bit) kvs kvs' ->
                      exec_val read_one_bit (ValBaseSenum kvs) (ValBaseSenum kvs')*).

  Definition sval_to_val (read_one_bit : option bool -> bool -> Prop) := 
    exec_val read_one_bit.

  Definition svals_to_vals (read_one_bit : option bool -> bool -> Prop) :=
    Forall2 (exec_val read_one_bit).

  Definition val_to_sval := 
    exec_val read_detbit.

  Definition vals_to_svals := 
    Forall2 (exec_val read_detbit).

  Axiom eval_val_to_sval : Val -> Sval.

  Definition uninit_sval_of_typ (hvalid : option bool) (typ : @P4Type tags_t): option Sval :=
    let fix uninit_sval_of_typ' hvalid (typ : @P4Type tags_t) : option Sval :=
      match typ with
      | TypBool => Some (ValBaseBool None)
      | TypInt w => Some (ValBaseInt (Zrepeat None (Z.of_N w)))
      | TypBit w => Some (ValBaseBit (Zrepeat None (Z.of_N w)))
      | TypArray typ size =>
          match uninit_sval_of_typ' hvalid typ with
          | Some sv => Some (ValBaseStack (Zrepeat sv (Z.of_N size)) size 0)
          | None => None
          end
      | TypTuple typs
      | TypList typs => 
          match lift_option (List.map (uninit_sval_of_typ' hvalid) typs) with
          | Some svs => Some (ValBaseTuple svs)
          | None => None
          end
      | TypRecord fields =>
          match lift_option_kv (kv_map (uninit_sval_of_typ' hvalid) fields) with
          | Some kvs => Some (ValBaseRecord (P4String.clear_AList_tags kvs))
          | None => None
          end
      | TypHeader fields =>
          match lift_option_kv (kv_map (uninit_sval_of_typ' hvalid) fields) with
          | Some kvs => Some (ValBaseHeader (P4String.clear_AList_tags kvs) hvalid)
          | None => None
          end
      | TypHeaderUnion fields =>
          match lift_option_kv (kv_map (uninit_sval_of_typ' hvalid) fields) with
          | Some kvs => Some (ValBaseUnion (P4String.clear_AList_tags kvs))
          | None => None
          end
      | TypStruct fields =>
          match lift_option_kv (kv_map (uninit_sval_of_typ' hvalid) fields) with
          | Some kvs => Some (ValBaseStruct (P4String.clear_AList_tags kvs))
          | None => None
          end
      | TypNewType _ typ' => uninit_sval_of_typ' hvalid typ'
      (* TypTypeName should have been already resolved *)
      | TypTypeName _ => None
      (* Two possibilities for senum:
        1. Use the default values (similar to the enum type):
            For enum values with an underlying type the default value is 0. (7.3.)
        2. Use the underlying types's uninitialized values:
            Since an senum's underlying type is either bit or int, it can also be uninitialized
            by the underlying types.
        The current implementation follows the option 2. *)
      | TypEnum tname (Some typ') members => uninit_sval_of_typ' hvalid typ'
      (* The P4Spec does not specify the unintialized values for the following types,
        so we use the default values for now. (7.3.) 
        Note that this design choice makes the svals output from uninit_sval_of_typ different
        from uninit_sval_of_sval and val_to_sval. *)
      | TypVarBit w => Some (ValBaseVarbit w [])
      | TypInteger => Some (ValBaseInteger 0)
      | TypError => Some (ValBaseError "NoError")
      | TypEnum tname None members => 
          (* Empty members is a syntax error *)
          if (Nat.eqb (List.length members) 0) then None
          else Some (ValBaseEnumField (str tname) (str (List.hd !"" members)))
      | _ => None
      end
    in uninit_sval_of_typ' hvalid typ.
  (* Type without uninitialized svals:
      TypeString: can be used only for compile-time constant string values (7.1.),
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
    | ValBaseRecord kvs => ValBaseRecord (kv_map (uninit_sval_of_sval hvalid) kvs)
    | ValBaseStruct kvs => ValBaseStruct (kv_map (uninit_sval_of_sval hvalid) kvs)
    | ValBaseHeader kvs is_valid => ValBaseHeader (kv_map (uninit_sval_of_sval hvalid) kvs) hvalid
    | ValBaseUnion kvs => ValBaseUnion (kv_map (uninit_sval_of_sval hvalid) kvs)
    | ValBaseStack vs size next => ValBaseStack (List.map (uninit_sval_of_sval hvalid) vs) size next
    | ValBaseSenumField typ_name enum_name v =>  ValBaseSenumField typ_name enum_name (uninit_sval_of_sval hvalid v)
    (*| ValBaseSenum kvs => ValBaseSenum (kv_map (uninit_sval_of_sval hvalid) kvs)*)
    (* ValBaseNull, ValBaseInteger, ValBaseString, ValBaseError, ValBaseMatchKind, ValBaseEnumField*)
    | _ => v
    end.

End ValueUtil.