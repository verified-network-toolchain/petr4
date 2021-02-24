Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.PArith.BinPos.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Monads.Monad.
Require Import Monads.Option.

Open Scope monad.

Fixpoint assoc_update {A: Type} (key: string) (val: A) (map: list (string * A)) : option (list (string * A)) :=
  match map with
  | (s, v) :: map' =>
    if String_as_OT.eq_dec s key
    then mret ((key, val) :: map')
    else let* map' := assoc_update key val map' in
         mret ((s, v) :: map')
  | nil => None
  end.

Fixpoint rotate_left_nat {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements with
    | nil => None
    | header :: elements' =>
      rotate_left_nat (elements' ++ pad :: nil) count' pad
    end
  end.

Definition rotate_left_z {A: Type} (elements: list A) (count: Z) (pad: A) : option (list A) :=
  match count with
  | Zneg _ => None
  | Zpos count' => rotate_left_nat elements (Pos.to_nat count') pad
  | Z0 => rotate_left_nat elements 0 pad
  end.


Fixpoint rotate_right_nat {A: Type} (elements: list A) (count: nat) (pad: A) : option (list A) :=
  match count with
  | 0 => Some elements
  | S count' =>
    match elements  with
    | nil => None
    | header :: elements' =>
      rotate_right_nat (pad :: (removelast elements)) count' pad
    end
  end.

Definition rotate_right_z {A: Type} (elements: list A) (count: Z) (pad: A) : option (list A) :=
  match count with
  | Zneg _ => None
  | Zpos count' => rotate_right_nat elements (Pos.to_nat count') pad
  | Z0 => rotate_right_nat elements 0 pad
  end.

Definition list_slice_z {A: Type} (l: list A) (lo: Z) (hi: Z) : option (list A).
Admitted.

Fixpoint list_slice_nat {A: Type} (l: list A) (lo: nat) (hi: nat) : option (list A) :=
  match (lo, hi) with
  | (0, 0)          => Some nil
  | (S _, 0)        => None
  | (0, S hi')      =>
    match l with
    | nil     => None
    | x :: xs => option_map (fun t => x :: t) (list_slice_nat xs 0 hi')
    end
  | (S lo', S hi')  =>
    match l with
    | nil      => None
    | x :: xs => list_slice_nat xs lo' hi'
    end
  end.

Definition index_z_error {A} (xs: list A) (i: Z) : option A.
Admitted.

Fixpoint truncate_bits (bits: positive) (count: nat) : N :=
  match count with
  | 0 => N0
  | S count' =>
    match bits with
    | xH => Npos xH
    | xO bits' =>
      match truncate_bits bits' count' with
      | N0 => N0
      | Npos rest => Npos (xO rest)
      end
    | xI bits' =>
      match truncate_bits bits' count' with
      | N0 => Npos xH
      | Npos rest => Npos (xI rest)
      end
    end
  end
.

Fixpoint glue_msb (bits: positive) :=
  match bits with
  | xH => xI xH
  | xO bits' => xO (glue_msb bits')
  | xI bits' => xI (glue_msb bits')
  end
.

Definition cast_bits_unsigned (bits: Z) (wold wnew: nat) : Z :=
  if Nat.eqb wold wnew then
    (* No difference in width; pass along old value. *)
    bits
  else if Nat.leb wold wnew then
    (* Strict widening. *)
    match bits with
    | Z0
    | Zpos _ =>
      bits
    | Zneg bits' =>
      (* Sign bit becomes part of the regular bits. *)
      Zpos (glue_msb bits')
    end
  else
    (* Strict truncation, i.e., wnew < wold. We can safely
       truncate without caring about the sign bit, because
       that is always discarded. *)
    match bits with
    | Z0 => Z0
    | Zpos bits'
    | Zneg bits' =>
      match truncate_bits bits' wnew with
      | N0 => Z0
      | Npos bits'' =>
        Zpos bits''
      end
    end
.

Fixpoint bits_length_positive (bits: positive) : nat :=
  match bits with
  | xH => 1
  | xO bits'
  | xI bits' =>
    1 + bits_length_positive bits'
  end
.

Definition bits_length_Z (bits: Z) : nat :=
  match bits with
  | Z0 => 0
  | Zpos bits' => bits_length_positive bits'
  | Zneg bits' => 1 + bits_length_positive bits'
  end
.

(* Coq Bvectors are little-endian *)
Open Scope vector_scope.
Fixpoint of_bvector {w} (bits: Bvector w) : Z :=
  match bits with
  | [] => 0
  | (b :: bits') => Z.add (if b then 1 else 0) (Z.double (of_bvector bits'))
  end.
Close Scope vector_scope.

Section list_rec.
  Context
    {A: Type}
    (PA: A -> Type)
    (PAList: list A -> Type)
    (HAListNil: PAList nil)
    (HAListCons: forall (a : A) (l: list A),
                 PA a -> PAList l -> PAList (a :: l))
  .

  Variable (rec: forall a: A, PA a).

  Fixpoint list_rec (l: list A) : PAList l :=
    match l with
    | nil => HAListNil
    | f :: l' =>
      HAListCons f l' (rec f) (list_rec l')
    end
  .
End list_rec.

Section option_rec.
  Context
    {A: Type}
    (PA: A -> Type)
    (PAOption: option A -> Type)
    (PAOptionNone: PAOption None)
    (PAOptionSome: forall a: A, PA a -> PAOption (Some a))
  .

  Variable (rec: forall a: A, PA a).

  Definition option_rec (o: option A) : PAOption o :=
    match o with
    | None => PAOptionNone
    | Some a => PAOptionSome a (rec a)
    end
  .
End option_rec.
