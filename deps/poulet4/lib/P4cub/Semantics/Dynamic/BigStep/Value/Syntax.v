From Coq Require Import Bool.Bool ZArith.BinInt.
Require Export Poulet4.P4cub.Syntax.AST.
Import String.

Module Val.
  (** Values from expression evaluation. *)
  Inductive v : Set :=
  | Bool (b : bool)
  | Bit (width : N) (n : Z)
  | Int (width : positive) (n : Z)
  | Struct (fields : list v) (validity : option bool)
  | Error (err : option string).

  (** Lvalues. *)
  Inductive lv : Set :=
  | Var (x : nat)               (** Local variables. *)
  | Slice (arg : lv)
          (hi lo : positive)  (** Slice. *)
  | Member (arg : lv) (x : nat) (** Member access. *).

  (** Evaluated arguments. *)
  Definition argsv : Set := list (paramarg v lv).

  Module ValueNotations.
    Declare Scope value_scope.
    Delimit Scope value_scope with value.
    Coercion Bool : bool >-> v.
    Notation "w 'VW' n" := (Bit w n) (at level 0) : value_scope.
    Notation "w 'VS' n" := (Int w n) (at level 0) : value_scope.
  End ValueNotations.

  Module LValueNotations.
    Declare Scope lvalue_scope.
    Delimit Scope lvalue_scope with lvalue.
    Coercion Var : nat >-> lv.
    Notation "lval 'DOT' x"
      := (Member lval x)
           (at level 20, left associativity) : lvalue_scope.
  End LValueNotations.
End Val.
