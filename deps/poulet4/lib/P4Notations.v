Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Poulet4.P4String.
Require Import Poulet4.Sublist.

(* Definition MkIdent {tags_t : Type} {tags_t_inhabitant : Inhabitant tags_t} (name : string) :=
  P4String.Build_t tags_t default name. *)

Notation "! s" := (P4String.Build_t _ _ s%string) (only printing, format "! s", at level 1, no associativity).
Notation "!! s" := (P4String.Build_t _ _ s%string) (only parsing, at level 1, no associativity).
Notation "! s" := (P4String.Build_t _ default s%string) (only parsing, at level 1, no associativity).

(* Definition MkPath {tags_t : Type} {tags_t_inhabitant : Inhabitant tags_t} (names : list string) :=
  map MkIdent names. *)

Notation "![ x ; .. ; y ]" := (cons (P4String.Build_t _ _ x%string) .. (cons (P4String.Build_t _ _ y%string) nil) .. )
    (only printing, format "![ x ;  .. ;  y ]", at level 1, no associativity).
Notation "!![ x ; .. ; y ]" := (cons (P4String.Build_t _ _ x%string) .. (cons (P4String.Build_t _ _ y%string) nil) .. )
    (only parsing, at level 1, no associativity).
Notation "![ x ; .. ; y ]" := (cons (P4String.Build_t _ default x%string) .. (cons (P4String.Build_t _ default y%string) nil) .. )
    (only parsing, at level 1, no associativity).
