Require Import Coq.Bool.Bvector.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.NArith.BinNat.

Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.State.

Require Import Poulet4.Environment.Environment.
Require Import Poulet4.Utils.
Require Import Poulet4.Value.
Require Import Poulet4.Typed.
Require Import Poulet4.Bitwise.
Require Import Poulet4.AList.

Open Scope monad.
Open Scope string_scope.

Section Packet.
  Context (bit: Type).
  Context (inject_bit: bool -> bit).
  Context (tags_t: Type).
  Notation P4String := (P4String.t tags_t).
  Notation ValueBase := (@ValueBase  bit).
  Notation P4Type := (@P4Type tags_t).

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
    let eval_packet_extract_fixed_field (into_field: P4String * P4Type) : packet_monad (string * ValueBase) :=
      let (into_name, into_type) := into_field in
      let* v := eval_packet_extract_fixed into_type in
        mret (P4String.str into_name, v) in
    match into with
    | TypBool =>
      let* vec := read_first_bits 1 in
      match vec with
      | (bit :: [])%vector => mret (ValBaseBool (inject_bit bit))
      | _ => state_fail Internal (* Does not happen -- vec has length exactly 1. *)
      end
    | TypBit width =>
      let* vec := read_first_bits (N.to_nat width) in
      mret (ValBaseBit (List.map inject_bit (Vector.to_list vec)))
    | TypInt width =>
      let* vec := read_first_bits (N.to_nat width) in
      mret (ValBaseInt (List.map inject_bit (Vector.to_list vec)))
    | TypStruct field_types
    | TypRecord field_types =>
      let* field_vals := sequence (List.map eval_packet_extract_fixed_field field_types) in
      mret (ValBaseStruct field_vals)
    | TypHeader field_types =>
      let* field_vals := sequence (List.map eval_packet_extract_fixed_field field_types) in
      mret (ValBaseHeader field_vals (inject_bit true))
    | _ => state_fail (TypeError "Unsupported type passed to extract.")
    end.


  Fixpoint parseable_type (type : P4Type) : bool :=
    let parseable_ftype (ftype: P4String * P4Type) : bool :=
      let (_, x) := ftype in 
        parseable_type x in
    match type with
    | TypRecord field_types
    | TypHeader field_types => fold_left andb (map parseable_ftype field_types) true
    | TypBool
    | TypBit _
    | TypInt _ => true
    | _ => false
    end.

End Packet.
