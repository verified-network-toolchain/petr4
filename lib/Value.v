Require Import String.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Module Import MStr := FMapList.Make(String_as_OT).

Inductive lvalue :=
  | LValName (var: string)
  | LValMember (base: lvalue) (member: string)
.

Inductive value :=
  | ValVoid
  | ValBool (b: bool)
  | ValInt (n: nat)
  | ValString (s: string)
  | ValArray (arr: list value)
  (* I would rather this was MStr.t value but that is not a strictly
  positive definition. The difference is that [Raw.t value] is
  basically list (string * value) while MStr.t value is a dependent
  record { raw: MStr.Raw.t; sorted: Sorted ...} which includes a proof
  that the list [raw] is sorted. *)
  | ValRecord (fs: MStr.Raw.t value)
  | ValBuiltinFunc (name: string) (obj: lvalue)
  | ValHeader (value: header)
  | ValHeaderStack (size: nat) (nextIndex: nat) (elements: list header)

with header := MkHeader (valid: bool) (fields: MStr.Raw.t value)
.