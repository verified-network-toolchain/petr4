Require Import Coq.Bool.Bool Coq.ZArith.BinIntDef
        Coq.ZArith.BinInt Poulet4.P4Arith.
Require Export Poulet4.P4cub.Syntax.AST.
Module P := P4cub.
Import P.P4cubNotations.
Module E := P.Expr.
Module F := P.F.
Module PR := P.Parser.

(** Notation entries. *)
Declare Custom Entry p4value.
Declare Custom Entry p4lvalue.

Module Val.
(** Values from expression evaluation. *)
Inductive v : Type :=
| VBool (b : bool)
| VInt (w : positive) (n : Z)
| VBit (w : positive) (n : Z)
| VTuple (vs : list v)
| VStruct (fs : F.fs string v)
| VHeader (fs : F.fs string v) (validity : bool)
| VError (err : option string)
| VMatchKind (mk : P4cub.Expr.matchkind)
| VHeaderStack (ts : F.fs string E.t)
               (headers : list (bool * F.fs string v))
               (size : positive) (nextIndex : Z).
(**[]*)

(** Lvalues. *)
Inductive lv : Type :=
| LVVar (x : string)                 (* Local variables. *)
| LVMember (arg : lv) (x : string) (* Member access. *)
| LVAccess (stk : lv) (index : Z)       (* Header stack indexing. *).
(**[]*)

(** Evaluated arguments. *)
Definition argsv : Type := F.fs string (P4cub.paramarg v lv).

Module ValueNotations.
  Notation "'~{' val '}~'" := val (val custom p4value at level 99).
  Notation "( x )" := x (in custom p4value, x at level 99).
  Notation "x" := x (in custom p4value at level 0, x constr at level 0).
  Notation "'TRUE'" := (VBool true) (in custom p4value at level 0).
  Notation "'FALSE'" := (VBool false) (in custom p4value at level 0).
  Notation "'VBOOL' b" := (VBool b) (in custom p4value at level 0).
  Notation "w 'VW' n" := (VBit w n) (in custom p4value at level 0).
  Notation "w 'VS' n" := (VInt w n) (in custom p4value at level 0).
  Notation "'TUPLE' vs" := (VTuple vs) (in custom p4value at level 0).
  Notation "'STRUCT' { fs }" := (VStruct fs)
                               (in custom p4value at level 6,
                                   no associativity).
  Notation "'HDR' { fs } 'VALID' ':=' b" := (VHeader fs b)
                               (in custom p4value at level 6,
                                   no associativity).
  Notation "'ERROR' x" := (VError x) (in custom p4value at level 0).
  Notation "'MATCHKIND' mk"
    := (VMatchKind mk)
         (in custom p4value at level 0, mk custom p4matchkind).
  Notation "'STACK' vs : ts [ n ] 'NEXT' ':=' ni"
           := (VHeaderStack ts vs n ni)
                (in custom p4value at level 0, no associativity).
End ValueNotations.

Module LValueNotations.
  Notation "'l{' lval '}l'" := lval (lval custom p4lvalue at level 99).
  Notation "( x )" := x (in custom p4lvalue, x at level 99).
  Notation "x" := x (in custom p4lvalue at level 0, x constr at level 0).
  Notation "'VAR' x" := (LVVar x) (in custom p4lvalue at level 0).
  Notation "lval 'DOT' x"
    := (LVMember lval x) (in custom p4lvalue at level 1,
                             lval custom p4lvalue).
  Notation "lval [ n ]"
           := (LVAccess lval n) (in custom p4lvalue at level 1,
                                   lval custom p4lvalue).
End LValueNotations.
End Val.
