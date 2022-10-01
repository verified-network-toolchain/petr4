From Poulet4 Require Import
     P4light.Transformations.SimplExpr
     P4light.Transformations.InlineTypeDecl
     Utils.Util.OptionUtil
     AListUtil.
From Poulet4 Require Export
     P4light.Syntax.Syntax
     P4cub.Syntax.Syntax
     P4cub.Syntax.Substitution
     P4cub.Syntax.InferMemberTypes
     Monads.Option
     P4cub.Semantics.Dynamic.BigStep.InstUtil.
Require Import Coq.Lists.List.
Import AST Result Envn ResultNotations.

Require Import String.
Open Scope string_scope.

Section SubstExpr.

  Import Typed P4Int.

  (** AST tags *)
  Context {tags_t : Type}.
  
  (** Environment mapping identifiers to the value to be substituted, if any *)
  Variable env : string -> option (@Expression tags_t).

  Definition subst_name (d : @Expression tags_t) (x : @P4String.t tags_t) : @Expression tags_t :=
    let bound_value := env x.(P4String.str) in
    default d bound_value.

  Fixpoint subst_expr (e : @Expression tags_t) : @Expression tags_t :=
    let '(MkExpression i e_pre type dir) := e in
    (* Rewrap an expression with the existing tags and type *)
    let tag e_pre := MkExpression i e_pre type dir in
    let subst_exprs := List.map subst_expr in
    match e_pre with
    | ExpBool _ 
    | ExpInt _ 
    | ExpString _ 
    | ExpName (QualifiedName _ _) _
    | ExpTypeMember _ _
    | ExpErrorMember _
    | ExpDontCare => e
    | ExpName (BareName x) _ => subst_name e x
    | ExpArrayAccess array idx => tag (ExpArrayAccess (subst_expr array) idx)
    | ExpBitStringAccess bits lo hi => tag (ExpBitStringAccess (subst_expr bits) lo hi)
    | ExpList es => tag (ExpList (subst_exprs es))
    | ExpRecord entries => tag (ExpRecord (map_values subst_expr entries))
    | ExpUnaryOp op e => tag (ExpUnaryOp op (subst_expr e))
    | ExpBinaryOp op e1 e2 => tag (ExpBinaryOp op (subst_expr e1) (subst_expr e2))
    | ExpCast type e => tag (ExpCast type (subst_expr e))
    | ExpExpressionMember e name => tag (ExpExpressionMember (subst_expr e) name)
    | ExpTernary e1 e2 e3 => tag (ExpTernary (subst_expr e1) (subst_expr e2) (subst_expr e3))
    | ExpFunctionCall e types args =>
      let args' := List.map (option_map subst_expr) args in
      tag (ExpFunctionCall (subst_expr e) types args')
    | ExpNamelessInstantiation type args =>
      let args' := subst_exprs args in
      tag (ExpNamelessInstantiation type args')
    end.

End SubstExpr.
