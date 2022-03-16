Require Export
        Poulet4.Utils.Maps
        (*Poulet4.Syntax*)
        Coq.Strings.String.

(** * Parametric Locator PathMap Libary *)

(** A library for resolving &
    updating [PathMap.t] for both
    [Semantics.v] & [Typing.v]
    when a [Locator]'s path is needed. *)

Section LocatorMap.
    Notation path := (list string).
  
    (* TODO:
       This is a dummy data-type unused anywhere else
       & exists merely for demonstrative purposes.
       This [Locator] will be replaced with
       that of [Syntax.v] iff changes to
       [Syntax.v]'s [Locator] are approved.
       Otherwise it's likely this file will be deleted
       and remain unused for name resolution
       in [Semantics.v] & [Typing.v]. *)
    Variant Locator : Set :=
    | LVar      : path -> Locator (* local/member variables. *)
    | LInstance : path -> Locator (* local/member constants. *)
    | LGlobal   : path -> Locator (* global constants. *).
  
  Context {V : Type}.

  Notation pvmap := (PathMap.t V).

  Record loc_maps := {
    locals  : pvmap; (** [LVar] or [LInstance]. *)
    globals : pvmap; (** [LGlobal].   *) }.

  (** Local path. *)
  Variable this : path.
  
  Section Ops.
    (** [Locator] to lookup/update in store(s). *)
    Variable loc : Locator.

    (* TODO: how should [this] be used? *)
    Definition
      lookup_loc
      '({| locals:=lm; globals:=gm |} : loc_maps) : option V :=
      match loc with
      | LVar      p => PathMap.get p lm
      | LInstance p => PathMap.get p lm
      | LGlobal   p => PathMap.get (this ++ p) gm
      end.

    Definition
      update_loc
      (v : V) '({| locals:=lm; globals:=gm |} : loc_maps) : loc_maps :=
      match loc with
      | LVar      p => {| locals:=PathMap.set p v lm; globals:=gm |}
      | LInstance p => {| locals:=PathMap.set p v lm; globals:=gm |}
      | LGlobal   p => {| locals:=lm; globals:=PathMap.set (this ++ p) v gm |}
      end.
  End Ops.

  (* TODO: [lookup] & [write] for lvalues. *)
End LocatorMap.
