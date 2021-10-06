Require Import Coq.ZArith.BinInt.
Require Poulet4.Syntax.

Section ConstValue.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).

  Inductive Value :=
  | ValBool (_: bool)
  | ValInteger (_: Z)
  | ValBit (width: nat) (value: Z)
  | ValInt (width: nat) (value: Z)
  | ValString (_: P4String)
  | ValTuple (_: list Value)
  | ValRecord (_: P4String.AList tags_t Value)
  | ValError (_: P4String)
  | ValMatchKind (_: P4String)
  | ValStruct (fields: P4String.AList tags_t (Value))
  | ValHeader (fields: P4String.AList tags_t Value) (is_valid: bool)
  | ValEnumField (typ_name: P4String) (enum_name: P4String)
  | ValSenumField (typ_name: P4String) (enum_name: P4String) (value: Value)
  | ValSenum (_: P4String.AList tags_t Value).

End ConstValue.
