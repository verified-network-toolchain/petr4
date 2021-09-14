Require Import Coq.Program.Basics.
Require Export Poulet4.P4cub.Syntax.AST.
Require Export Poulet4.P4Arith.
Require Export Poulet4.P4cub.Envn.
Require Export Poulet4.P4cub.BigStep.InstUtil.
Require Export Poulet4.P4cub.BigStep.BigStep.
Require Export Poulet4.P4cub.BigStep.Semantics.
Require Export Poulet4.P4cub.BigStep.Value.Value.
Require Export Poulet4.P4cub.Util.Result.
Require Import Coq.Arith.EqNat.
Require Import String.
Open Scope string_scope.

Require Import Poulet4.P4cub.Util.StringUtil.

Import Env.EnvNotations.

Import Result.
Import ResultNotations.

(** Compile to GCL *)
Module P := P4cub.
Module ST := P.Stmt.
Module CD := P.Control.ControlDecl.
Module E := P.Expr.
Module F := P.F.
Require Import Poulet4.P4cub.Inline.

Definition tags_t : Type := Inline.tags_t.

Module GCL.
  Inductive t {lvalue rvalue form : Type} : Type :=
  | GSkip (i : tags_t)
  | GAssign (type : E.t) (lhs : lvalue) (rhs : rvalue) (i : tags_t)
  | GSeq (g1 g2 : t)
  | GChoice (g1 g2 : t)
  | GAssume (phi : form)
  | GAssert (phi : form).

  Definition g_sequence {L R F : Type} (i : tags_t) : list (@t L R F) -> @t L R F :=
    fold_right GSeq (GSkip i).

  Module BitVec.
    Inductive bop :=
    | BVPlus (sat : bool) (signed : bool)
    | BVMinus (sat : bool) (signed : bool)
    | BVTimes (signed : bool)
    | BVConcat
    | BVShl (signed : bool)
    | BVShr (signed : bool)
    | BVAnd
    | BVOr
    | BVXor.

    Inductive uop :=
    | BVNeg
    | BVCast (i : nat)
    | BVSlice (hi lo : nat).

    Inductive t :=
    | BitVec (n : nat) (w : option nat) (i : tags_t)
    | Int (z : Z) (w : option nat) (i : tags_t)
    | BVVar (x : string) (w : nat) (i : tags_t)
    | BinOp (op : bop) (u v : t) (i : tags_t)
    | UnOp (op : uop) (v : t) (i : tags_t).

    Definition bit (w : nat) (n : nat) := BitVec n (Some w).
    Definition varbit (n : nat) := BitVec n None.
    Definition int (w : nat) (n : Z) := Int n (Some w).
    Definition integer (n : Z) := Int n None.

    Definition uadd := BinOp (BVPlus false false).
    Definition sadd := BinOp (BVPlus false true).
    Definition uadd_sat := BinOp (BVPlus true false).
    Definition sadd_sat := BinOp (BVPlus true true).

    Definition usub := BinOp (BVMinus false false).
    Definition ssub := BinOp (BVMinus false true).
    Definition usub_sat := BinOp (BVMinus true false).
    Definition ssub_sat := BinOp (BVMinus true true).

    Definition umul := BinOp (BVTimes false).
    Definition smul := BinOp (BVTimes true).

    Definition app := BinOp BVConcat.

    Definition ushl := BinOp (BVShl false).
    Definition sshl := BinOp (BVShl true).

    Definition ushr := BinOp (BVShr false).
    Definition sshr := BinOp (BVShr true).

    Definition band := BinOp BVAnd.
    Definition bor := BinOp BVOr.
    Definition bxor := BinOp BVXor.

  End BitVec.

  Inductive lbop := LOr
                  | LAnd
                  | LImp
                  | LIff.

  Inductive lcomp := LEq
                   | LLe (signed : bool)
                   | LLt (signed : bool)
                   | LGe (signed : bool)
                   | LGt (signed : bool)
                   | LNeq.

  Inductive form :=
  | LBool (b : bool) (i : tags_t)
  | LBop (op : lbop) (ϕ ψ : form) (i : tags_t)
  | LNot (ϕ : form) (i : tags_t)
  | LVar (x : string) (i : tags_t)
  | LComp (comp : lcomp) (bv1 bv2 : BitVec.t) (i : tags_t).

  Definition bveq := LComp LEq.
  Definition bvule := LComp (LLe false).
  Definition bvsle := LComp (LLe true).

  Definition bvult := LComp (LLt false).
  Definition bvslt := LComp (LLt true).

  Definition bvuge := LComp (LGe false).
  Definition bvsge := LComp (LGe true).

  Definition bvugt := LComp (LGt false).
  Definition bvsgt := LComp (LGt true).

  Definition bvne := LComp LNeq.

  Definition lor := LBop LOr.
  Definition land := LBop LAnd.
  Definition limp := LBop LImp.
  Definition liff := LBop LIff.

  Definition pos : (nat -> positive) := BinPos.Pos.of_nat.

  Definition is_true (x : string) (i : tags_t) : form :=
    bveq (BitVec.BVVar x 1 i) (BitVec.bit 1 1 i) i.

  Definition exit (i : tags_t) : form := is_true "exit" i.
  Definition etrue (i : tags_t) : E.e tags_t := E.EBool true i.
  Definition efalse (i : tags_t) : E.e tags_t := E.EBool false i.
  Definition ite {lvalue rvalue : Type} (guard_type : E.t) (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop E.Not guard_type guard i)) fls).
  Definition iteb {lvalue rvalue : Type} (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop E.Not E.TBool guard i)) fls).

  Definition isone (v : BitVec.t) (i :tags_t) : GCL.form :=
    bvule v (BitVec.bit 1 1 i) i.

End GCL.
