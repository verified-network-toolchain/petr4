Require Export Coq.Lists.List.
Require Export Coq.NArith.NArith.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
From Poulet4.P4light.Syntax Require Export
     P4String P4Int Typed.
Require Export Poulet4.P4light.Syntax.Syntax.
Require Import VST.zlist.Zlist.

Notation stags := P4String.tags.
Notation itags := P4Int.tags.

Inductive Info := NoInfo.
Inductive Annotation := NoAnnotation.
Instance Inhabitant_Info : Inhabitant Info := NoInfo.
Instance Inhabitant_Annotation : Inhabitant Annotation := NoAnnotation.
