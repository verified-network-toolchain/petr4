Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Monads.Monad.
Require Import Monads.Option.

Require Import BinPos.

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

Fixpoint rotateLeftNat {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements with
    | nil => None
    | header :: elements' =>
      rotateLeftNat (elements' ++ pad :: nil) count' pad
    end
  end.

Definition rotateLeftZ {A: Type} (elements: list A) (count: Z) (pad: A) : option (list A) :=
  match count with 
  | Zneg _ => None
  | Zpos count' => rotateLeftNat elements (Pos.to_nat count') pad
  | Z0 => rotateLeftNat elements 0 pad
  end.

  
Fixpoint rotateRightNat {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements  with
    | nil => None
    | header :: elements' =>
      rotateRightNat (pad :: (removelast elements)) count' pad
    end
  end.

Definition rotateRightZ {A: Type} (elements: list A) (count: Z) (pad: A) : option (list A) :=
  match count with 
  | Zneg _ => None
  | Zpos count' => rotateRightNat elements (Pos.to_nat count') pad
  | Z0 => rotateRightNat elements 0 pad
  end.

Definition listSliceZ {A: Type} (l: list A) (lo: Z) (hi: Z) : option (list A).
Admitted.

Fixpoint listSliceNat {A: Type} (l: list A) (lo: nat) (hi: nat) : option (list A) := 
  match (lo, hi) with
  | (0, 0)          => Some nil
  | (S _, 0)        => None
  | (0, S hi')      =>
    match l with
    | nil     => None
    | x :: xs => option_map (fun t => x :: t) (listSliceNat xs 0 hi')
    end
  | (S lo', S hi')  =>
    match l with
    | nil      => None
    | x :: xs => option_map (fun t => x :: t) (listSliceNat xs lo' hi')
    end
  end.

Definition indexZError {A} (xs: list A) (i: Z) : option A.
Admitted.

Fixpoint powTwo (w: nat) : Z :=
  match w with
  | 0     => 1
  | S w'  => Z.double (powTwo w')
  end.

(* Coq Bvectors are little-endian *)
Open Scope vector_scope.
Fixpoint of_bvector {w} (bits: Bvector w) : Z :=
  match bits with
  | [] => 0
  | (b :: bits') => Z.add (if b then 1 else 0) (Z.double (of_bvector bits'))
  end.
Close Scope vector_scope.
