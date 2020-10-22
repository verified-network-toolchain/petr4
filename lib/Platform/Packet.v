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

Fixpoint read_first_bits (count: nat) : packet_monad (Bvector count) :=
  match count with
  | 0 => mret []%vector
  | S count' =>
    fun bits =>
      match bits with
      | nil => state_fail PacketTooShort bits
      | bit :: bits' =>
        match read_first_bits count' bits' with
        | (inr error, bits'') => state_fail error bits''
        | (inl rest, bits'') => state_return (bit :: rest)%vector bits''
        end
      end
  end.

Definition eval_packet_extract_fixed (into: value) : packet_monad value :=
  match into with
  | ValBool _ =>
    let* vec := read_first_bits 1 in
    match vec with
    | (bit :: [])%vector => mret (ValBool bit)
    | _ => state_fail Internal
    end
  | ValFixedBit width _ =>
    let* vec := read_first_bits width in
    mret (ValFixedBit width vec)
  | ValFixedInt width _ =>
    let* vec := read_first_bits width in
    match vec with
    | (false :: rest)%vector => mret (ValFixedInt width (of_bvector rest))
    | (true :: rest)%vector =>
      let negated := Z.sub (pow_two width) (of_bvector rest) in
      mret (ValFixedInt width negated)
    | _ => state_fail Internal
    end
  | _ => state_fail Internal
  end.
