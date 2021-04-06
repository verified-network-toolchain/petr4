Require Import Coq.Bool.Bvector.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinIntDef.

Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.

Require Import Poulet4.Environment.Environment.
Require Import Poulet4.Utils.
Require Import Poulet4.Syntax.
Require Import Poulet4.Typed.
Require Import Poulet4.Bitwise.

Open Scope monad.
Open Scope string_scope.

Section Packet.
  Context (tags_t: Type).
  Notation P4String := (P4String.t tags_t).
  Notation ValueBase := (@ValueBase tags_t).
  Notation P4Type := (@P4Type tags_t).
  Notation FieldType := (@FieldType tags_t).

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

  Definition convert_bits (width: nat) (bits: Bvector width) : Z :=
    Z.of_nat (to_nat (rev (Vector.to_list bits))).

  Fixpoint eval_packet_extract_fixed (into: P4Type) : packet_monad ValueBase :=
    match into with
    | TypBool =>
      let* vec := read_first_bits 1 in
      match vec with
      | (bit :: [])%vector => mret (ValBaseBool bit)
      | _ => state_fail Internal (* Does not happen -- vec has length exactly 1. *)
      end
    | TypBit width =>
      let* vec := read_first_bits width in
      mret (ValBaseBit width (convert_bits width vec))
    | TypInt width =>
      let* vec := read_first_bits width in
      mret (ValBaseInt width (convert_bits width vec))
    | TypRecord field_types =>
      let* field_vals := sequence (List.map eval_packet_extract_fixed_field field_types) in
      mret (ValBaseRecord field_vals)
    | TypHeader field_types =>
      let* field_vals := sequence (List.map eval_packet_extract_fixed_field field_types) in
      mret (ValBaseHeader field_vals true)
    | _ => state_fail (TypeError "Unsupported type passed to extract.")
    end

  with eval_packet_extract_fixed_field (into_field: FieldType) : packet_monad (P4String * ValueBase) :=
    let '(MkFieldType into_name into_type) := into_field in
    let* v := eval_packet_extract_fixed into_type in
    mret (into_name, v).


  Fixpoint parseable_type (type : P4Type) : bool :=
    match type with
    | TypRecord field_types
    | TypHeader field_types => fold_left andb (map parseable_ftype field_types) true
    | TypBool
    | TypBit _
    | TypInt _ => true
    | _ => false
    end
  with parseable_ftype (ftype: FieldType) : bool :=
    let '(MkFieldType _ x) := ftype in parseable_type x.



End Packet.
