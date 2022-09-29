From Coq Require Import List ZArith String.
From Ceres Require Import Ceres.
From Poulet4 Require Import Monads.Monad.
From Poulet4 Require Monads.Result.
Module R := Result.

(* This file defines the Coq version of the AST used in Egg for
   rewriting. See deps/table_opt/src/table_lang.rs for that.

   It's all smushed into one datatype, destroying KAT distinctions
   between binary expressions, variables, and commands. This is
   because egg needs everything to be terms over a signature with only
   1 sort. *)

Inductive tm : Type :=
| TBool (b : bool)
| TIf (e1 c1 c2 : tm)
| TAnd (e1 e2 : tm)
| TNot (e1 : tm)
| TSet (x c : tm)
| TEq (x1 x2 : tm)
| TVar (s: string)
.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope sexp_scope.
(* These sexp serializers and deserializers were implemented using the
   Ceres library following this tutorial:
     https://lysxia.github.io/coq-ceres/Tutorial.html
 *)
Instance Serialize_tm : Serialize tm :=
  fix sz (t : tm) : sexp :=
    match t with
    | TBool b => to_sexp b
    | TIf e1 c1 c2 => List [Atom "if"; sz c1; sz c2]
    | TAnd e1 e2 => [Atom "and"; sz e1; sz e2]
    | TNot e1 => [Atom "not"; sz e1]
    | TSet x c => [Atom "set"; sz x; sz c]
    | TEq x1 x2 => [Atom "eq"; sz x1; sz x2]
    | TVar x => [Atom "var"; to_sexp x]
    end.

Instance Deserialize_tm : Deserialize tm :=
  fix ds (l : loc) (e : sexp) : error + tm :=
    Deser.match_con
      "tm" []
      [("if",  Deser.con3 TIf ds ds ds);
       ("and", Deser.con2 TAnd ds ds);
       ("not", Deser.con1 TNot ds);
       ("set", Deser.con2 TSet ds ds);
       ("eq",  Deser.con2 TEq ds ds);
       ("not", Deser.con1 TNot ds);
       ("var", Deser.con1_ TVar)]
      l e.

Section Optimizer.
  (* There's something that takes in a string (sexp) and produces a
     string (sexp). In extraction, filled in with a call to the
     table_opt Egg rewriter. *)
  Variable (ExternalOptimizer : string -> string).

  Definition to_string (t : tm) : string :=
    to_string t.

  Definition from_string (s : string) : R.result error tm :=
    R.from_sum (from_string s).

  Definition optimize (t: tm) : R.result error tm :=
    from_string (ExternalOptimizer (to_string t)).

End Optimizer.
