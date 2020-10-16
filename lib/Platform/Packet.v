Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinIntDef.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import Environment.
Require Import Value.
Require Import Utils.
Require Import Syntax.

Open Scope monad.

Definition packet_monad := @state_monad (list bool) exception.

Fixpoint readFirstBits (count: nat) : packet_monad (Bvector count) :=
  match count with
  | 0 => mret []%vector
  | S count' =>
    fun bits =>
      match bits with
      | nil => state_fail Internal bits
      | bit :: bits' =>
        match readFirstBits count' bits' with
        | (inr error, bits'') => state_fail error bits''
        | (inl rest, bits'') => state_return (bit :: rest)%vector bits''
        end
      end
  end.

Definition evalPacketExtractFixed (into: value) : packet_monad value :=
  match into with
  | ValBool _ =>
    let* vec := readFirstBits 1 in
    match vec with
    | (bit :: [])%vector => mret (ValBool bit)
    | _ => state_fail Internal
    end
  | ValFixedBit width _ =>
    let* vec := readFirstBits width in
    mret (ValFixedBit width vec)
  | ValFixedInt width _ =>
    let* vec := readFirstBits width in
    match vec with
    | (false :: rest)%vector => mret (ValFixedInt width (of_bvector rest))
    | (true :: rest)%vector =>
      let negated := Z.sub (powTwo width) (of_bvector rest) in
      mret (ValFixedInt width negated)
    | _ => state_fail Internal
    end
  | _ => state_fail Internal
  end.
