Require Export Coq.Lists.List.
Require Export Coq.NArith.NArith.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.

Require Export Poulet4.P4String.
Require Export Poulet4.P4Int.
Require Export Poulet4.Syntax.
Require Export Poulet4.Typed.
Require Import Poulet4.Sublist.

Notation stags := P4String.tags.
Notation itags := P4Int.tags.

Inductive Info := NoInfo.
Inductive Annotation := NoAnnotation.
Instance Inhabitant_Info : Inhabitant Info := NoInfo.
Instance Inhabitant_Annotation : Inhabitant Annotation := NoAnnotation.

