Require Import Coq.Strings.String.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Packet.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.Utils.AListUtil.

Section Extract.
Context {tags_t: Type} (* {inhabitant_tags_t : Inhabitant tags_t} *).
Notation Val := (@ValueBase bool).
Notation P4Type := (@P4Type tags_t).

Fixpoint extract (typ: P4Type) : Packet Val :=
  match typ with
  | TypBool =>
      let* b := extract_bit in
      mret (ValBaseBool b)
  | TypInt n =>
      let* bs := extract_bits (BinNatDef.N.to_nat n) in
      mret (ValBaseInt bs)
  | TypBit n =>
      let* bs := extract_bits (BinNatDef.N.to_nat n) in
      mret (ValBaseBit bs)
  | TypTuple ts =>
      let* vs := sequence (List.map extract ts) in
      mret (ValBaseTuple vs)
  | TypList ts =>
      let* vs := sequence (List.map extract ts) in
      mret (ValBaseTuple vs)
  | TypRecord fields =>
      let fields' := List.map (fun '(k, v) =>
                                 (k.(P4String.str), extract v))
                              fields in
      let* bits := asequence fields' in
      mret (ValBaseStruct bits)
  | TypHeader fields =>
      let fields' := List.map (fun '(k, v) =>
                                 (k.(P4String.str), extract v))
                              fields in
      let* bits := asequence fields' in
      mret (ValBaseHeader bits true)
  | TypStruct fields =>
      let fields' := List.map (fun '(k, v) =>
                                 (k.(P4String.str), extract v))
                              fields in
      let* bits := asequence fields' in
      mret (ValBaseStruct bits)
  | TypEnum name (Some t) fields =>
      let* v := extract t in
      mret (ValBaseSenumField String.EmptyString v)
  | _ => err (TypeError "Unsupported type passed to extract.")
  end.

Definition var_extract (typ: P4Type) (len: nat) : Packet Val :=
  match typ with
  | _ => mret ValBaseNull
  end.

End Extract.


