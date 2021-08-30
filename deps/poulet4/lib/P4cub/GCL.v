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
    | BVPlus
    | BVMinus
    | BVTimes
    | BVConcat
    | BVShl
    | BVShr
    | BVAnd
    | BVOr
    | BVXor.

    Inductive uop :=
    | BVNeg
    | BVCast (i : positive)
    | BVSlice (hi lo : positive).

    Inductive t :=
    | BitVec (n : positive) (w : positive) (i : tags_t)
    | BVVar (x : string) (w : positive) (i : tags_t)
    | BinOp (op : bop) (u v : t) (i : tags_t)
    | UnOp (op : uop) (v : t) (i : tags_t).

    Definition add := BinOp BVPlus.
    Definition sub := BinOp BVMinus.
    Definition mul := BinOp BVTimes.
    Definition app := BinOp BVConcat.
    Definition shl := BinOp BVShl.
    Definition shr := BinOp BVShr.
    Definition band := BinOp BVAnd.
    Definition bor := BinOp BVOr.
    Definition bxor := BinOp BVXor.

  End BitVec.

  Inductive lbop := | LOr | LAnd | LImp | LIff.
  Inductive lcomp := | LEq | LLe | LLt | LGe | LGt | LNeq.
  Inductive form :=
  | LBool (b : bool) (i : tags_t)
  | LBop (op : lbop) (ϕ ψ : form) (i : tags_t)
  | LNot (ϕ : form) (i : tags_t)
  | LVar (x : string) (i : tags_t)
  | LComp (comp : lcomp) (bv1 bv2 : BitVec.t) (i : tags_t)
  .

  Definition leq := LComp LEq.
  Definition lle := LComp LLe.
  Definition llt := LComp LLt.
  Definition lge := LComp LGe.
  Definition lgt := LComp LGt.
  Definition lne := LComp LNeq.

  Definition lor := LBop LOr.
  Definition land := LBop LAnd.
  Definition limp := LBop LImp.
  Definition liff := LBop LIff.

  Definition pos : (nat -> positive) := BinPos.Pos.of_nat.

  Definition is_true (x : string) (i : tags_t) : form :=
    LComp (LEq) (BitVec.BVVar x (pos 1) i) (BitVec.BitVec (pos 1) (pos 1) i) i.

  Definition exit (i : tags_t) : form := is_true "exit" i.
  Definition etrue (i : tags_t) : E.e tags_t := E.EBool true i.
  Definition efalse (i : tags_t) : E.e tags_t := E.EBool false i.
  Definition ite {lvalue rvalue : Type} (guard_type : E.t) (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop E.Not guard_type guard i)) fls).
  Definition iteb {lvalue rvalue : Type} (guard : E.e tags_t) (tru fls : @t lvalue rvalue (E.e tags_t)) (i : tags_t) : t :=
    GChoice (GSeq (GAssume guard) tru) (GSeq (GAssume (E.EUop E.Not E.TBool guard i)) fls).

  Definition isone (v : BitVec.t) (i :tags_t) : GCL.form :=
    leq v (BitVec.BitVec (pos 1) (pos 1) i) i.


End GCL.
