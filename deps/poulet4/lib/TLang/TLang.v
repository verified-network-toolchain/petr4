From Coq Require Import List ZArith String.
From Ceres Require Import Ceres.
From Poulet4 Require Import Monads.Monad.
From Poulet4 Require Monads.Result.
Module R := Result.
Import R.ResultNotations.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope sexp_scope.
From Poulet4 Require GCL.Inline.
Module E := AST.Expr.

(* This file defines the Coq version of the AST used in Egg for
   rewriting. See deps/table_opt/src/table_lang.rs for that.

   It's all smushed into one datatype, destroying KAT distinctions
   between binary expressions, variables, and commands. This is
   because egg needs everything to be terms over a signature with only
   1 sort. *)

Inductive tm : Type :=
| TBool (b : bool)
| TInt (width : N) (val : Z)
| TIf (e1 c1 c2 : tm)
| TAnd (e1 e2 : tm)
| TNot (e1 : tm)
| TSeq (c1 c2 : tm)
| TNop
| TSet (x e : tm)
| TEq (x1 x2 : tm)
| TVar (s: string)
.
(* These sexp serializers and deserializers were implemented using the
   Ceres library following this tutorial:
     https://lysxia.github.io/coq-ceres/Tutorial.html
 *)

Instance Serialize_tm : Serialize tm :=
  fix sz (t : tm) : sexp :=
    match t with
    | TBool b => to_sexp b
    | TInt w v => [Atom "int"; to_sexp w; to_sexp v]
    | TIf e1 c1 c2 => [Atom "if"; sz c1; sz c2]
    | TAnd e1 e2 => [Atom "and"; sz e1; sz e2]
    | TNot e1 => [Atom "not"; sz e1]
    | TSeq c1 c2 => [Atom "seq"; sz c1; sz c2]
    | TNop => Atom "nop"
    | TSet x c => [Atom "set"; sz x; sz c]
    | TEq x1 x2 => [Atom "eq"; sz x1; sz x2]
    | TVar x => [Atom "var"; to_sexp x]
    end.

Instance Deserialize_tm : Deserialize tm :=
  fix ds (l : loc) (e : sexp) : error + tm :=
    Deser.match_con
      "tm" [("nop", TNop)]
      [("if",  Deser.con3 TIf ds ds ds);
       ("and", Deser.con2 TAnd ds ds);
       ("not", Deser.con1 TNot ds);
       ("set", Deser.con2 TSet ds ds);
       ("eq",  Deser.con2 TEq ds ds);
       ("seq",  Deser.con2 TSeq ds ds);
       ("not", Deser.con1 TNot ds);
       ("var", Deser.con1_ TVar)]
      l e.

Section Optimizer.
  (* There's something that takes in a string (sexp) and produces a
     string (sexp). In extraction, filled in with a call to the
     table_opt Egg rewriter. *)
  Variable (ExternalOptimizer : string -> string).
  Variable (tags_t : Type).

  Definition tm_to_string (t : tm) : string :=
    to_string t.

  Definition tm_from_string (s : string) : R.result error tm :=
    R.from_sum (from_string s).

  Definition optimize_tm (t: tm) : R.result error tm :=
    tm_from_string (ExternalOptimizer (to_string t)).

  Fixpoint e_to_tm (e: E.e tags_t) : R.result string tm :=
    match e with
    | E.EBool b _     => mret (TBool b)
    | E.EBit w n _    => mret (TInt w n)
    | E.EInt w n _    => mret (TInt (Npos w) n)
    | E.EVar _ name _ => mret (TVar name)
    | _               => R.error "e_to_tm: unimplemented"
    end.

  Fixpoint t_to_tm (stmt: Inline.t tags_t) : R.result string tm :=
    match stmt with
    | Inline.ISkip _ i =>
        mret TNop
    | Inline.IVardecl _ type x i =>
        mret TNop
    | Inline.IAssign _ type lhs rhs i =>
        match lhs with
        | AST.Expr.EVar _ name _ =>
            let* rhs_tm := e_to_tm rhs in
            mret (TSet (TVar name) rhs_tm)
        | _ => mret TNop
        end
    | Inline.IConditional _ _ e s1 s2 _ =>
        let* t1 := t_to_tm s1 in
        let* t2 := t_to_tm s2 in
        let+ e := e_to_tm e in
        TIf e t1 t2
    | Inline.ISeq _ s1 s2 i =>
        let* t1 := t_to_tm s1 in
        let+ t2 := t_to_tm s2 in
        TSeq t1 t2
    | Inline.IBlock _ blk =>
        (* this breaks scope, so we need to require the original
           stmt to have unique variable names somehow.

           Better yet, statically allocate everything so that
           IBlocks do not appear at the statement level. *)
        t_to_tm blk
    | Inline.IReturnVoid _ _
    | Inline.IReturnFruit _ _ _ _
    | Inline.IExit _ _ =>
        (* Not sure what to do about return/etc in this setup.
           If I have ---[x>0]--[x:=2]--+--[x:=x+1]---
                          |            |
                          +----[ret]---+,
           then in P4 this is not the same as
                     ---[x>0]--[x:=2]--+--[x:=x+1]---
                          |
                          +----[ret]------[x:=x+1],
           but if ret is taken to be a primitive action, in KA,
           they're equal.
         *)
        R.error "t_to_tm: exit/return unimplemented"
    | Inline.IInvoke _ x keys actions i =>
        R.error "t_to_tm: table invocation unimplemented"
    | Inline.ISetValidity _ hdr val i =>
        R.error "t_to_tm: header validity unimplemented"
    | Inline.IHeaderStackOp _ hdr_stck_name typ op
                            size i =>
        R.error "t_to_tm: header stack ops unimplemented"
    | Inline.IExternMethodCall _ extn method args i =>
        R.error "t_to_tm: extern calls unimplemented"
    end.

  Fixpoint tm_to_t (e : tm) : R.result string (Inline.t tags_t).
  Admitted.

  Fixpoint tm_to_e (e : tm) : R.result string (Inline.t tags_t).
  Admitted.

  Definition optimize_inline_t (t: Inline.t tags_t) : R.result string (Inline.t tags_t) :=
    let* tprog := t_to_tm t in
    let* tprog_better := R.emap (fun x => "") (optimize_tm tprog) in
    tm_to_t tprog_better.

End Optimizer.
