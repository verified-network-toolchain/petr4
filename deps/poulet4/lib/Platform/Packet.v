Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinIntDef.

Require Import Monads.Monad.
Require Import Monads.State.

Require Import Environment.
Require Import Utils.
Require Import Syntax.
Require Import Typed.

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

Fixpoint eval_packet_extract_fixed (into: P4Type) : packet_monad Value :=
  match into with
  | TypBool =>
    let* vec := read_first_bits 1 in
    match vec with
    | (bit :: [])%vector => mret (ValBool bit)
    | _ => state_fail Internal
    end
  | TypBit width =>
    let* vec := read_first_bits width in
    mret (ValBit width vec)
  | TypInt width =>
    let* vec := read_first_bits width in
    mret (ValInt width vec)
  | TypRecord (MkRecordType field_types) =>
    let* field_vals := sequence (List.map eval_packet_extract_fixed_field field_types) in
    mret (ValRecord field_vals)
  | TypHeader (MkRecordType field_types) =>
    let* field_vals := sequence (List.map eval_packet_extract_fixed_field field_types) in
    mret (ValHeader field_vals true)
  | _ => state_fail Internal
  end

with eval_packet_extract_fixed_field (into_field: RecordFieldType) : packet_monad (string * Value) :=
  let '(MkRecordFieldType into_name into_type) := into_field in
  let* v := eval_packet_extract_fixed into_type in
  mret (into_name, v).
