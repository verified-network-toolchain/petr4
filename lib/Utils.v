Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Monads.Monad.
Require Import Monads.Option.

Open Scope monad.

Fixpoint assocUpdate {A: Type} (key: string) (val: A) (map: list (string * A)) : option (list (string * A)) :=
  match map with
  | (s, v) :: map' =>
    if String_as_OT.eq_dec s key
    then mret ((key, val) :: map')
    else let* map' := assocUpdate key val map' in
         mret ((s, v) :: map')
  | nil => None
  end.

Fixpoint rotateLeft {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements with
    | nil => None
    | header :: elements' =>
      rotateLeft (elements' ++ pad :: nil) count' pad
    end
  end.
  
Fixpoint rotateRight {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements  with
    | nil => None
    | header :: elements' =>
      rotateRight (pad :: (removelast elements)) count' pad
    end
  end.
