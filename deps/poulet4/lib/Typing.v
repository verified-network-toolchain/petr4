Require Import Poulet4.Semantics Poulet4.Typed Poulet4.Syntax.

Section Typing.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Notation typ := (@P4Type tags_t).
  Notation expr := (@Expression tags_t).
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).
  
  Definition gamma : Type := @PathMap.t tags_t typ.

  Context `{T : @Target tags_t (@Expression tags_t)}.

  (* TODO.
     Try to just use [genv_senum]. *)
  Inductive val_typ (gsenum : genv_senum) : Sval -> typ -> Prop :=
  | typ_null : forall t, val_typ gsenum ValBaseNull t
  | typ_bool : forall b, val_typ gsenum (ValBaseBool b) TypBool
  | typ_integer : forall v, val_typ gsenum (ValBaseInteger v) TypInteger
  | typ_senumfield : forall ename member v t fields,
      IdentMap.get ename gsenum = Some (ValBaseSenum fields) ->
      AList.get fields member = Some v ->
      val_typ gsenum v t ->
      val_typ gsenum (ValBaseSenumField ename member v) (TypEnum ename (Some t) (List.map fst fields)).

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
