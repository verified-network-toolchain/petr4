Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq Require Import Numbers.BinNums Classes.EquivDec.

From Poulet4.P4light.Syntax Require P4String P4Int.


Section Syntax.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  
  Inductive surfaceTyp := 
  | TypBool
  | TypError
  | TypMatchKind
  | TypInteger
  | TypString
  | TypInt (width: N)
  | TypBit (width: N)
  | TypVarBit (width: N)
  | TypIdentifier (name: P4String)
  (* | TypSpecialized (base: surfaceTyp) (args: list surfaceType) *)
  | TypHeaderStack (typ: surfaceTyp) (size: N)
  | TypTuple (types: list surfaceTyp).

  Inductive declaredTyp :=
  | TypHeader (fields: P4String.AList tags_t surfaceTyp)
  | TypHeaderUnion
  | TypStruct
  | TypSerEnum
  | TypEnum
  | TypParser
  | TypControl
  | TypPackage.

  Inductive synthesizedTyp :=
  | TypFunction
  | TypSet
  | TypExtern
  | TypRecord
  | TypNewTyp
  | TypAction
  | TypConstructor
  | TypTable.

  Inductive typ :=
  | SurfaceTyp (typ: surfaceTyp)
  | DeclaredTyp (typ: declaredTyp) 
  | SynthesizedTyp (typ: synthesizedTyp).

  Inductive direction :=
  | In
  | Out
  | InOut
  | Directionless.

  Inductive Expression :=
  | ExpBool (b: Bool)
  | ExpString (s: P4String)
  | ExpInt (i: P4Int)
  | ExpSignedInt ().

End Syntax. 

