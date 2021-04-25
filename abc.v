Require Import Poulet4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition u32 := DeclTypeDef NoInfo {| stags := NoInfo; str := "u32" |}
    (inl (TypBit 32)).

Definition Pt := DeclTypeDef NoInfo {| stags := NoInfo; str := "Pt" |}
    (inr (DeclStruct NoInfo {| stags := NoInfo; str := "Point" |}
              [(MkDeclarationField NoInfo (TypInt 32)
                    {| stags := NoInfo; str := "x" |});
               (MkDeclarationField NoInfo (TypInt 32)
                    {| stags := NoInfo; str := "y" |})])).

Definition Pot := DeclNewType NoInfo {| stags := NoInfo; str := "Pot" |}
    (inl (TypTypeName (BareName {| stags := NoInfo; str := "u32" |}))).

Definition Abc := DeclTypeDef NoInfo {| stags := NoInfo; str := "Abc" |}
    (inl (TypTypeName (BareName {| stags := NoInfo; str := "u32" |}))).

Definition Pot := DeclStruct NoInfo {| stags := NoInfo; str := "Pot" |}
    [(MkDeclarationField NoInfo (TypInt 32)
          {| stags := NoInfo; str := "z" |})].

Definition prog := Program [u32; Pt; Pot; Abc; Pot].


