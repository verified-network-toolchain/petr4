Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require P4String.
Import ListNotations.

Module FuncAsMap.

  Section FuncAsMap.

    Context {key: Type}.
    Context {key_eqb: key -> key -> bool}.
    Context {value: Type}.

    Definition t := key -> option value.

    Definition empty: t := fun _ => None.
    Definition get: key -> t -> option value := fun k fmap => fmap k.
    Definition set: key -> value -> t -> t :=
      fun k v fmap x => if key_eqb x k then Some v else fmap x.
    
    Definition sets: list key -> list value -> t -> t :=
      fun kList vList fmap =>
        fold_left (fun fM kvPair => set (fst kvPair) (snd kvPair) fM)
                  (combine kList vList) fmap.
    
    Definition gets (kl: list key) (m: t): list (option value) :=
      map (fun k => get k m) kl.
    
  End FuncAsMap.

End FuncAsMap.

Module IdentMap.

Section IdentMap.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Context {A: Type}.

Definition t := @FuncAsMap.t ident A.
Definition empty : t := FuncAsMap.empty.
Definition get : ident -> t -> option A := FuncAsMap.get.
Definition set : ident -> A -> t -> t :=
  @FuncAsMap.set ident (@P4String.equivb tags_t) A.
Definition sets: list ident -> list A -> t -> t :=
  @FuncAsMap.sets ident (@P4String.equivb tags_t) A.
Definition gets: list ident -> t -> list (option A) := FuncAsMap.gets.

End IdentMap.

End IdentMap.

Definition list_eqb {A} (eqb : A -> A -> bool) al bl :=
  Nat.eqb (length al) (length bl) &&
  forallb (uncurry eqb) (combine al bl).

Definition path_equivb {tags_t: Type} :
  (list (P4String.t tags_t)) -> (list (P4String.t tags_t)) -> bool :=
  list_eqb (@P4String.equivb tags_t).

Module PathMap.

Section PathMap.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Context {A: Type}.

Definition t := @FuncAsMap.t path A.
Definition empty : t := FuncAsMap.empty.
Definition get : path -> t -> option A := FuncAsMap.get.
Definition set : path -> A -> t -> t :=
  @FuncAsMap.set path path_equivb A.
Definition sets : list path -> list A -> t -> t :=
  @FuncAsMap.sets path path_equivb A.
Definition gets: list path -> t -> list (option A) := FuncAsMap.gets.

End PathMap.

End PathMap.

Arguments IdentMap.t {_} _.
Arguments PathMap.t {_} _.
