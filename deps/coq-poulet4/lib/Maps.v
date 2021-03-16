Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require P4String.
Import ListNotations.

Module IdentMap.

Section IdentMap.

Context {tags_t: Type}.
Notation ident := (P4String.t tags_t).
Context {A: Type}.

Definition t := ident -> option A.

Definition empty : t := fun _ => None.
Definition get : ident -> t -> option A := fun id idMap => idMap id.
Definition set : ident -> A -> t -> t :=
  fun id value idMap x => if P4String.equivb x id then Some value else idMap x.

Definition sets: list ident -> list A -> t -> t :=
  fun idList valueList idMap =>
    fold_left (fun idM ivPair => set (fst ivPair) (snd ivPair) idM)
              (combine idList valueList) idMap.

Definition gets (kl : list ident) (m : t) : list (option A) :=
  map (fun k => get k m) kl.

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

Definition t := path -> option A.

Definition empty : t := fun _ => None.
Definition get : path -> t -> option A := fun p pM => pM p.
Definition set : path -> A -> t -> t :=
  fun p v pM x => if path_equivb x p then Some v else pM x.

Definition sets : list path -> list A -> t -> t :=
  fun pList vList pMap =>
    fold_left (fun idM ivPair => set (fst ivPair) (snd ivPair) idM)
              (combine pList vList) pMap.

Definition gets (kl : list path) (m : t) : list (option A) :=
  map (fun k => get k m) kl.

End PathMap.

End PathMap.

Arguments IdentMap.t {_} _.
Arguments PathMap.t {_} _.
