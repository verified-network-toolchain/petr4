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

(* This p4int datatype should be (and probably is) defined somewhere
   else. In fact it should really be hidden behind an abstraction
   somehow so we can make decisions about extraction without having to
   also worry about proofs breaking. If that's
   possible. *)
Record p4int :=
  MkP4Int { iwidth : N;
            ivalue : Z }.

Instance Serialize_p4int : Serialize p4int :=
  fun i =>
    let '{| iwidth := iwidth; ivalue := ivalue |} := i in
    [Atom "p4int"; to_sexp iwidth; to_sexp ivalue].

Instance Deserialize_p4int : Deserialize p4int :=
  Deser.match_con
    "p4int" []
    [("p4int",  Deser.con2_ MkP4Int)].

Inductive tm : Type :=
| TBool (b : bool)
| TInt (i : p4int)
| TIf (e1 c1 c2 : tm)
| TAnd (e1 e2 : tm)
| TNot (e1 : tm)
| TSeq (c1 c2 : tm)
| TNop
| TSet (x : string) (e : tm)
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
    | TInt i => [Atom "int"; to_sexp i]
    | TIf e1 c1 c2 => [Atom "if"; sz c1; sz c2]
    | TAnd e1 e2 => [Atom "and"; sz e1; sz e2]
    | TNot e1 => [Atom "not"; sz e1]
    | TSeq c1 c2 => [Atom "seq"; sz c1; sz c2]
    | TNop => Atom "nop"
    | TSet x c => [Atom "set"; to_sexp x; sz c]
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
       ("set", Deser.con2 TSet _from_sexp ds);
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

  Fixpoint e_to_tm (e: Inline.E.e) : R.result string tm :=
    match e with
    | E.Bool b       => mret (TBool b)
    | E.Bit w n      => mret (TInt {|iwidth:=w; ivalue:=n|})
    | E.Int w n      => mret (TInt {|iwidth:=Npos w; ivalue:=n|})
    | E.Var _ name _ => mret (TVar name)
    | _              => R.error "e_to_tm: unimplemented"
    end.

  Fixpoint t_to_tm (stmt: Inline.t) : R.result string tm :=
    match stmt with
    | Inline.ISkip =>
        mret TNop
    | Inline.IVardecl type x =>
        mret TNop
    | Inline.IAssign type lhs rhs =>
        match lhs with
        | AST.Expr.Var _ name _ =>
            let* rhs_tm := e_to_tm rhs in
            mret (TSet name rhs_tm)
        | _ => mret TNop
        end
    | Inline.IConditional _ e s1 s2 =>
        let* t1 := t_to_tm s1 in
        let* t2 := t_to_tm s2 in
        let+ e := e_to_tm e in
        TIf e t1 t2
    | Inline.ISeq s1 s2 =>
        let* t1 := t_to_tm s1 in
        let+ t2 := t_to_tm s2 in
        TSeq t1 t2
    | Inline.IBlock blk =>
        (* this breaks scope, so we need to require the original
           stmt to have unique variable names somehow.

           Better yet, statically allocate everything so that
           IBlocks do not appear at the statement level. *)
        t_to_tm blk
    | Inline.IReturnVoid
    | Inline.IReturnFruit _ _
    | Inline.IExit =>
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
    | Inline.IInvoke x keys actions =>
        R.error "t_to_tm: table invocation unimplemented"
    | Inline.IExternMethodCall extn method args ret =>
        R.error "t_to_tm: extern calls unimplemented"
    end.

  Set Printing All.
  Fixpoint tm_to_t (e : tm) : R.result string Inline.t :=
    match e with
    | TIf e1 c1 c2 =>
        let* e1' := tm_to_e e1 in
        let* t1 := tm_to_t c1 in
        let+ t2 := tm_to_t c2 in
        Inline.IConditional E.TBool e1' t1 t2
    | TSeq c1 c2 =>
        let* t1 := tm_to_t c1 in
        let+ t2 := tm_to_t c2 in
        Inline.ISeq t1 t2
    | TNop => mret Inline.ISkip
    | TSet x e =>
        let+ e' := tm_to_e e in
        Inline.IAssign E.TBool (E.Var E.TBool x 0) e'
    | _ => Result.error "tm is not a command"
    end
    with tm_to_e (e : tm) : R.result string Inline.E.e :=
      match e with
      | TBool b => mret (Inline.E.Bool b)
      | TInt i => mret (E.Bit (iwidth i) (ivalue i))
      | TAnd e1 e2 =>
          let* e1' := tm_to_e e1 in
          let+ e2' := tm_to_e e2 in
          E.Bop E.TBool E.And e1' e2'
      | TNot e1 =>
          let+ e1' := tm_to_e e1 in
          E.Uop E.TBool E.Not e1'
      | TEq e1 e2 =>
          let* e1' := tm_to_e e1 in
          let+ e2' := tm_to_e e2 in
          E.Bop E.TBool E.Eq e1' e2'
      | TVar s => mret (Inline.E.Var E.TBool s 0)
      | _ => Result.error "tm is not an expression"
      end.

  Definition optimize_inline_t (t: Inline.t) : R.result string Inline.t :=
    let* tprog := t_to_tm t in
    let* tprog_better := R.emap (fun x => "") (optimize_tm tprog) in
    tm_to_t tprog_better.

End Optimizer.
