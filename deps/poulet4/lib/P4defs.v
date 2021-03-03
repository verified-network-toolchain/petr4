Require Export Coq.Lists.List.
Require Export Coq.NArith.NArith.
Require Export Coq.ZArith.ZArith.
Require Export Strings.String.

Require Export P4String.
Require Export P4Int.
Require Export Syntax.
Require Export Typed.

Notation stags := P4String.tags.
Notation itags := P4Int.tags.

Inductive Info := NoInfo.
Inductive Annotation := NoAnnotation.

