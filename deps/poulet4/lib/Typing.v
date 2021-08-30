Require Import Poulet4.Semantics Poulet4.Typed Poulet4.Syntax.

(* TODOs:
   Typing [genv].
   Typing values [Sval].
*)

Section Typing.
  Context {tags_t : Type} {dummy : Inhabitant tags_t}.

  Let typ := @P4Type tags_t.
  Let expr := @Expression tags_t.
  Notation ident := (P4String.t tags_t).
  Notation path := (list ident).
  Notation Sval := (@ValueBase tags_t (option bool)).
  
  Definition gamma : Type := @PathMap.t tags_t typ.

  Context `{T : @Target tags_t (@Expression tags_t)}.

  (* TODO. *)
  Inductive val_typ : Sval -> typ -> Prop :=.

  Definition envs_same (g : gamma) (st : state) : Prop :=
    forall p : path, PathMap.get p g = None <-> PathMap.get p (fst st) = None.
  
  Definition envs_type (g : gamma) (st : state) : Prop :=
    forall (p : path) (t : typ) (v : Sval),
      PathMap.get p g = Some t ->
      PathMap.get p (fst st) = Some v -> val_typ v t.

  Let run_expr := @exec_expr tags_t dummy T.

  Definition typ_of_expr (e : expr) : typ :=
    match e with
    | MkExpression _ _ t _ => t
    end.
  (**[]*)
  
  Definition types (ge : genv) (read_one_bit : option bool -> bool -> Prop)
             (p : path) (e : @Expression tags_t) : Prop :=
    forall (g : gamma) (st : state),
      envs_same g st -> envs_type g st ->
      (exists v : Sval, run_expr ge read_one_bit p st e v) /\
      forall v : Sval, run_expr ge read_one_bit p st e v -> val_typ v (typ_of_expr e).
  (**[]*)
End Typing.
