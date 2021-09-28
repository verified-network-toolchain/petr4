Require Import Poulet4.Semantics Poulet4.Typed
        Poulet4.Syntax Coq.NArith.BinNat
        Coq.Lists.List.
Import ListNotations.
Require Poulet4.P4String.

Section Typing.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).
  
  Definition gamma : Type := @PathMap.t tags_t typ.

  Context `{T : @Target tags_t (@Expression tags_t)}.

  (* TODO:
     What constraints do we need on:
     - fixed-width numeric types?
     - headers (unions & stacks)?
     - senum values: see comments below.
   *)
  Inductive val_typ (gsenum : genv_senum) : Sval -> typ -> Prop :=
  | typ_null : forall t, val_typ gsenum ValBaseNull t
  | typ_bool : forall b, val_typ gsenum (ValBaseBool b) TypBool
  | typ_integer : forall v, val_typ gsenum (ValBaseInteger v) TypInteger
  | typ_bit : forall v,
      val_typ gsenum (ValBaseBit v) (TypBit (N.of_nat (length v)))
  | typ_int : forall v,
      val_typ gsenum (ValBaseInt v) (TypInt (N.of_nat (length v)))
  | typ_varbit : forall n v,
      N.to_nat n < length v ->
      val_typ gsenum (ValBaseVarbit n v) (TypVarBit n)
  | typ_string : forall s,
      val_typ gsenum (ValBaseString s) TypString
  | typ_tuple : forall vs ts,
      Forall2 (val_typ gsenum) vs ts ->
      val_typ gsenum (ValBaseTuple vs) (TypTuple ts)
  | typ_record : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseRecord vs) (TypRecord ts)
  | typ_error : forall err,
      val_typ gsenum (ValBaseError err) TypError
  | typ_matchkind : forall mk,
      val_typ gsenum (ValBaseMatchKind mk) TypMatchKind
  | typ_struct : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseStruct vs) (TypStruct ts)
  | typ_header : forall b vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseHeader vs b) (TypHeader ts)
  | typ_union : forall vs ts,
      Forall2
        (fun xv xt =>
           P4String.equiv (fst xv) (fst xt) /\ val_typ gsenum (snd xv) (snd xt))
        vs ts ->
      val_typ gsenum (ValBaseUnion vs) (TypHeaderUnion ts)
  | typ_stack : forall s n vs ts,
      length vs = N.to_nat s ->
      Forall (fun v => val_typ gsenum v (TypHeader ts)) vs ->
      val_typ gsenum (ValBaseStack vs s n) (TypArray (TypHeader ts) n)
  | typ_enumfield : forall ename member members,
      In member members ->
      val_typ gsenum
              (ValBaseEnumField ename member)
              (TypEnum ename None members)
  | typ_senumfield : forall ename member v t fields,
      IdentMap.get ename gsenum = Some (ValBaseSenum fields) ->
      AList.get fields member = Some v ->
      val_typ gsenum v t ->
      val_typ gsenum
              (ValBaseSenumField ename member v)
              (TypEnum ename (Some t) (List.map fst fields))
  (* TODO: what is a [ValBaseSenum _], and what is its type?
     It seems to be something in [gsenum],
     but should it be a value? *)
  | typ_senum : forall fields ename t,
      IdentMap.get ename gsenum = Some (ValBaseSenum fields) ->
      Forall (fun xv => val_typ gsenum (snd xv) t) fields ->
      val_typ gsenum (ValBaseSenum fields) (TypEnum ename (Some t) (List.map fst fields)).

  Definition envs_same (g : gamma) (st : state) : Prop :=
    forall p : path, PathMap.get p g = None <-> PathMap.get p (fst st) = None.
  
  Definition envs_type (gsenum : genv_senum) (g : gamma) (st : state) : Prop :=
    forall (p : path) (t : typ) (v : Sval),
      PathMap.get p g = Some t ->
      PathMap.get p (fst st) = Some v -> val_typ gsenum v t.

  Notation run_expr := (@exec_expr tags_t dummy T).

  Definition typ_of_expr (e : expr) : typ :=
    match e with
    | MkExpression _ _ t _ => t
    end.
  (**[]*)

  (** Expression typing. *)
  Definition types (read_one_bit : option bool -> bool -> Prop)
             (p : path) (e : @Expression tags_t) : Prop :=
    forall (ge : genv) (g : gamma) (st : state),
      envs_same g st -> envs_type ge g st ->
      (exists v : Sval, run_expr ge read_one_bit p st e v) /\
      forall v : Sval, run_expr ge read_one_bit p st e v -> val_typ (ge_senum ge) v (typ_of_expr e).
  (**[]*)
End Typing.
