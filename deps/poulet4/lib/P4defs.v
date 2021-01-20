Require Export Coq.Lists.List.
Require Export Coq.NArith.NArith.
Require Export Coq.ZArith.ZArith.
Require Export Strings.String.

Require Export Petr4.P4String.
Require Export Petr4.P4Int.
Require Export Petr4.Syntax.
Require Export Petr4.Typed.

Notation stags := P4String.tags.
Notation itags := P4Int.tags.

Inductive Info := NoInfo.
Inductive Annotation := NoAnnotation.

