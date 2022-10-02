From Poulet4 Require Import
     P4light.Transformations.SimplExpr
     P4light.Transformations.InlineTypeDecl
     Utils.Util.Utiliser
     AListUtil
     Monads.State.Pure.
From Poulet4 Require Export
     P4light.Syntax.Syntax
     P4cub.Syntax.Syntax
     P4cub.Syntax.Substitution
     P4cub.Syntax.InferMemberTypes
     Monads.Option
     P4cub.Semantics.Dynamic.BigStep.InstUtil.
Require Import Coq.Lists.List.
Import AST Result Envn ResultNotations.
Import Typed P4Int.

Require Import String.
Open Scope string_scope.

Section SubstIdent.

  (** AST tags *)
  Context {tags_t : Type}.

  Definition Env : Type := Env.t string (@Expression tags_t).

  Section SubstExpr.
    
    (** Environment mapping identifiers to the value to be substituted, if any *)
    Variable env : Env.

    (** [subst_name d x] is the expression bound to [x] in [env], if any, or [d]
        if [x] is unbound in [env] *)
    Definition subst_name (d : @Expression tags_t) (x : @P4String.t tags_t) : @Expression tags_t :=
      let bound_value := Env.find x.(P4String.str) env in
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

  Definition update_env (stmt : @Statement tags_t) (env : Env) : Env :=
    let '(MkStatement _ stmt _) := stmt in
    match stmt with
    | StatVariable _ name _ _
    | StatConstant _ name _ _ => Env.remove name.(P4String.str) env
    | _ => env
    end.

  Fixpoint subst_stmt (env : Env) (stmt : @Statement tags_t) : @Statement tags_t :=
    let '(MkStatement tags stmt type) := stmt in
    MkStatement tags (subst_stmt_pre env stmt) type

  with subst_stmt_pre (env : Env) (stmt : @StatementPreT tags_t) : @StatementPreT tags_t :=
    let subst_expr := subst_expr env in
    let subst_expr_opt := option_map subst_expr in
    let subst_expr_opts :=  List.map subst_expr_opt in
    let subst_stmt := subst_stmt env in
    match stmt with
    | StatMethodCall fn types args =>
      StatMethodCall (subst_expr fn) types (subst_expr_opts args)
    | StatAssignment e1 e2 => StatAssignment (subst_expr e1) (subst_expr e2)
    | StatDirectApplication t1 t2 args =>
      StatDirectApplication t1 t2 (subst_expr_opts args)
    | StatConditional e s1 s2 =>
      StatConditional (subst_expr e) (subst_stmt s1) (option_map subst_stmt s2)
    | StatBlock block => StatBlock (subst_block env block)
    | StatExit | StatEmpty => stmt
    | StatReturn e => StatReturn (subst_expr_opt e)
    | StatSwitch e cases =>
      let cases' := List.map (subst_switch_case env) cases in
      StatSwitch (subst_expr e) cases'
    | StatConstant type name value loc =>
      StatConstant type name (subst_expr value) loc
    | StatVariable type name init loc =>
      StatVariable type name (subst_expr_opt init) loc
    | StatInstantiation type args name inits =>
      let args' := List.map subst_expr args in
      let inits' := List.map (subst_initializer env) inits in
      StatInstantiation type args' name inits'
    end

  with subst_block (env : Env) (block : Block) : Block :=
    match block with
    | BlockEmpty _ => block
    | BlockCons stmt stmts =>
      let stmt := subst_stmt env stmt in
      let env := update_env stmt env in
      BlockCons stmt (subst_block env stmts)
    end

  with subst_switch_case (env : Env) (case : StatementSwitchCase) : StatementSwitchCase :=
    match case with
    | StatSwCaseFallThrough _ _ => case
    | StatSwCaseAction tags label code =>
      let code' := subst_block env code in
      StatSwCaseAction tags label code'
    end

  with subst_initializer (env : Env) (init : Initializer) : Initializer :=
    match init with
    | InitFunction tags ret name types params body =>
      let body' := subst_block env body in
      InitFunction tags ret name types params body'
    | InitInstantiation tags types args name inits =>
      let args' := List.map (subst_expr env) args in
      let inits' := List.map (subst_initializer env) inits in
      InitInstantiation tags types args' name inits'
    end.

  Definition State : Type -> Type := State Env.

  (* (tags : tags_t)
  (type : @P4Type tags_t)
  (name : P4String)
  (e : @Expression tags_t) : State (@Declaration tags_t) := *)

  Definition subst_constant env tags type x e :=
    let e := subst_expr env e in
    let ident := x.(P4String.str) in
    modify_state (Env.bind ident e);;
    mret (DeclConstant tags type x e).

  (* Fixpoint subst_decl (decl : @Declaration tags_t) : State (@Declaration tags_t) :=
    let* state := get_state in
    let env x := Env.find x state in
    let subst_decls ds := eval_state (map_monad subst_decl ds) state in
    match decl with
    | DeclConstant tags type x e => subst_constant env tags type x e
    | DeclInstantiation tags type args name init =>
      let args' := List.map (subst_expr env) args in
      let init' := subst_decls init in
      mret (DeclInstantiation tags type args' name init')
    | DeclParser tags name types params cparams locals states =>
      let locals' := 
    | _ => mret decl
    end. *)

End SubstIdent.
