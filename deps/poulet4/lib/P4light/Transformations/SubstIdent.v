From Poulet4 Require Import
     P4light.Transformations.SimplExpr
     P4light.Transformations.InlineTypeDecl
     Utils.Util.Utiliser
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

Section SubstIdent.

  (** AST tags *)
  Context {tags_t : Type}.

  Section SubstExpr.

    Import Typed P4Int.
    
    (** Environment mapping identifiers to the value to be substituted, if any *)
    Variable env : string -> option (@Expression tags_t).

    (** [subst_name d x] is the expression bound to [x] in [env], if any, or [d]
        if [x] is unbound in [env] *)
    Definition subst_name (d : @Expression tags_t) (x : @P4String.t tags_t) : @Expression tags_t :=
      let bound_value := env x.(P4String.str) in
      default d bound_value.

    (** [subst_expr e] is [e] with every identifier subsituted with the value it
        is bound to in [env] *)
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
      | ExpArrayAccess array idx =>
        let array' := subst_expr array in
        tag (ExpArrayAccess array' idx)
      | ExpBitStringAccess bits lo hi =>
        let bits' := subst_expr bits in
        tag (ExpBitStringAccess bits' lo hi)
      | ExpList es => tag (ExpList (subst_exprs es))
      | ExpRecord entries =>
        let entries' := map_values subst_expr entries in
        tag (ExpRecord entries')
      | ExpUnaryOp op e =>
        let e' := subst_expr e in
        tag (ExpUnaryOp op e')
      | ExpBinaryOp op e1 e2 =>
        let e1' := subst_expr e1 in
        let e2' := subst_expr e2 in
        tag (ExpBinaryOp op e1' e2')
      | ExpCast type e =>
        let e' := subst_expr e in
        tag (ExpCast type e')
      | ExpExpressionMember e name =>
        let e' := subst_expr e in
        tag (ExpExpressionMember e' name)
      | ExpTernary e1 e2 e3 =>
        let e1' := subst_expr e1 in
        let e2' := subst_expr e2 in
        let e3' := subst_expr e3 in
        tag (ExpTernary e1' e2' e3')
      | ExpFunctionCall e types args =>
        let e' := subst_expr e in
        let args' := List.map (option_map subst_expr) args in
        tag (ExpFunctionCall e' types args')
      | ExpNamelessInstantiation type args =>
        let args' := subst_exprs args in
        tag (ExpNamelessInstantiation type args')
      end.

  End SubstExpr.

  Definition env : Type := Env.t string (@Expression tags_t).

  Definition subst_decl (env : env) (decl : @Declaration tags_t) : option (@Declaration tags_t) :=
    None.

End SubstIdent.
