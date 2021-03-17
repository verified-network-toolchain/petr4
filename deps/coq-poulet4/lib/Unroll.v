Require Import Syntax.
Require Import Monads.Monad.
Require Import Monads.Option.
Require Import Step.
Require Import Strings.String.
Require Import P4String.
Require Import Coq.Init.Nat.

Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.


Section Unroll.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Notation P4String := (P4String.t tags_t).
  Notation program := (@program tags_t).
  Notation Declaration := (@Declaration tags_t).
  Notation ParserState := (@ParserState tags_t).

  Definition unroll_parser (unrolls : nat) (states : list ParserState) : list ParserState :=
    states.

  Definition unroll_decl (unrolls : nat) (d : Declaration) : Declaration :=
    match d with
    | DeclParser t n tps ps cps ls ss =>
      DeclParser t n tps ps cps ls (unroll_parser unrolls ss)
    | _ => d end.
  
  Definition unroll_prog (unrolls : nat) (prog : program) : program :=
    match prog with
    | Program ds => Program (List.map (unroll_decl unrolls) ds) end.

End Unroll.
