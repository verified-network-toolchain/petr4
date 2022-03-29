Require Import Coq.Bool.Bool Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Require Export Poulet4.P4cub.Syntax.AST.
Require Import Poulet4.P4cub.Syntax.CubNotations.
Import AllCubNotations.
Import String.

(** Notation entries. *)
Declare Custom Entry p4value.
Declare Custom Entry p4lvalue.

Module Val.
(** Values from expression evaluation. *)
Inductive v : Type :=
| VBool (b : bool)
| VInt (w : positive) (n : Z)
| VBit (w : N) (n : Z)
| VTuple (vs : list v)
| VStruct (fs : F.fs string v)
| VHeader (fs : F.fs string v) (validity : bool)
| VError (err : option string)
| VHeaderStack (ts : F.fs string Expr.t)
               (headers : list (bool * F.fs string v))
               (next_index : Z).
(**[]*)

(** Lvalues. *)
Inductive lv : Type :=
| LVVar (x : string)               (* Local variables. *)
| LVSlice (arg : lv)
          (hi lo : positive)       (* Slice. *)
| LVMember (arg : lv) (x : string) (* Member access. *)
| LVAccess (stk : lv) (index : Z)  (* Header stack indexing. *).
(**[]*)

(** Evaluated arguments. *)
Definition argsv : Type := F.fs string (paramarg v lv).

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
  Notation "'STACK' vs : ts 'NEXT' ':=' ni"
    := (VHeaderStack ts vs ni)
         (in custom p4value at level 0, no associativity).
End ValueNotations.

Module LValueNotations.
  Notation "'l{' lval '}l'" := lval (lval custom p4lvalue at level 99).
  Notation "( x )" := x (in custom p4lvalue, x at level 99).
  Notation "x" := x (in custom p4lvalue at level 0, x constr at level 0).
  Notation "'VAR' x" := (LVVar x) (in custom p4lvalue at level 0).
  Notation "'SLICE' lval [ hi : lo ]"
    := (LVSlice lval hi lo)
         (in custom p4lvalue at level 2,
             lval custom p4lvalue, left associativity).
  Notation "lval 'DOT' x"
    := (LVMember lval x) (in custom p4lvalue at level 1,
                             lval custom p4lvalue).
  Notation "'ACCESS' lval [ n ]"
           := (LVAccess lval n) (in custom p4lvalue at level 1,
                                   lval custom p4lvalue).
End LValueNotations.
End Val.
