Require Import Coq.Lists.List.

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