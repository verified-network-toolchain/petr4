Require Import Coq.Strings.String.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Bool.Bvector.

Module Import MStr := FMapList.Make(String_as_OT).

Inductive lvalue :=
  | LValName (var: string)
  | LValMember (base: lvalue) (member: string)
.

Inductive value :=
| ValVoid
| ValBool (b: bool)
| ValInt (n: nat)
| ValBit (width: nat) (value: Bvector width)
| ValVarbit (width: nat) (value: Bvector width)
| ValFixedInt (width: nat) (value: nat)
| ValSignedInt (n: Decimal.int)
| ValString (s: string)
| ValArray (arr: list value)
| ValError (msg: string)
(* I would rather this was MStr.t value but that is not a strictly
positive definition. The difference is that [Raw.t value] is
basically list (string * value) while MStr.t value is a dependent
record { raw: MStr.Raw.t; sorted: Sorted ...} which includes a proof
that the list [raw] is sorted. *)
| ValRecord (fs: MStr.Raw.t value)
| ValBuiltinFunc (name: string) (obj: lvalue)
| ValHeader (value: header)
| ValHeaderStack (size: nat) (nextIndex: nat) (elements: list header)

(* unused value types from the OCAML implementation

  | VStruct of
      { fields : (string * value) list; }
  | VUnion of
      { fields : (string * value) list; }
  | VEnumField of
      { typ_name : string;
        enum_name : string; }
  | VSenumField of
      { typ_name : string;
        enum_name : string;
        v : value; }
  | VSenum of (string * value) list *)

with header := MkHeader (valid: bool) (fields: MStr.Raw.t value)
.
