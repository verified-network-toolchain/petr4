Require Import
  Poulet4.Monads.Result
  Poulet4.P4cub.Syntax.Syntax
  Poulet4.P4cub.Syntax.CubNotations
  Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
  Poulet4.P4cub.Semantics.Dynamic.BigStep.ExprUtil.

Import
  Val.ValueNotations
  ExprNotations
  ParserNotations
  Val.LValueNotations
  ResultNotations
  StmtNotations
  String.

Variant error : Set :=
  | Unbound (name : string) (index : nat)
  | IllegalSlice (hi lo : positive) (v : Val.v)
  | IllegalCast 

Section Expr.
  Variable env : list Val.v.

  Definition interpret_var (name : string) (index : nat) :=
    from_opt (nth_error env index) (Unbound name index).

  Definition interpret_slice hi lo v :=
    from_opt (eval_slice hi lo v) (IllegalSlice hi lo v).

  Definition interpret_cast t v :=
    from_opt

  Fixpoint interpret_expr (e : Expr.e) : Result.result error Val.v :=
    match e with
    | Expr.Bool b => mret (Val.Bool b)
    | Expr.Bit w n => mret (Val.Bit w n)
    | Expr.Int w n => mret (Val.Int w n)
    | Expr.Var _ name index => interpret_var name index
    | Expr.Slice hi lo e => interpret_expr e >>= interpret_slice hi lo
    | Expr.Cast t e => interpret_expr e >>= interpret_slice t
    | _ => Error Foo
    end.

End Expr.