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

  Section ConstantEnv.
    
    (** Environment mapping identifiers to the value to be substituted, if any *)
    Variable env : Env.

    (** [subst_name d x] is the expression bound to [x] in [env], if any, or [d]
        if [x] is unbound in [env] *)
    Definition subst_name (d : @Expression tags_t) (x : @P4String.t tags_t) : @Expression tags_t :=
      let bound_value := Env.find x.(P4String.str) env in
      default d bound_value.

    Fixpoint subst_expr (e : @Expression tags_t) : @Expression tags_t :=
      let 'MkExpression i e_pre type dir := e in
      match e_pre with
      | ExpName (BareName x) _ => subst_name e x
      | _ =>
        let e_pre' := subst_expr_pre e_pre in
        MkExpression i e_pre' type dir
      end

    (** [subst_expr e] is [e] with every identifier subsituted with the value it
        is bound to in [env] *)
    with subst_expr_pre (e : @ExpressionPreT tags_t) : @ExpressionPreT tags_t :=
      let subst_exprs := List.map subst_expr in
      match e with
      | ExpBool _ 
      | ExpInt _ 
      | ExpString _ 
      | ExpName _ _
      | ExpTypeMember _ _
      | ExpErrorMember _
      | ExpDontCare => e
      | ExpArrayAccess array idx => ExpArrayAccess (subst_expr array) idx
      | ExpBitStringAccess bits lo hi =>
        ExpBitStringAccess (subst_expr bits) lo hi
      | ExpList es => ExpList (subst_exprs es)
      | ExpRecord entries => ExpRecord (map_values subst_expr entries)
      | ExpUnaryOp op e => ExpUnaryOp op (subst_expr e)
      | ExpBinaryOp op e1 e2 => ExpBinaryOp op (subst_expr e1) (subst_expr e2)
      | ExpCast type e => ExpCast type (subst_expr e)
      | ExpExpressionMember e name => ExpExpressionMember (subst_expr e) name
      | ExpTernary e1 e2 e3 =>
        ExpTernary (subst_expr e1) (subst_expr e2) (subst_expr e3)
      | ExpFunctionCall e types args =>
        let e' := subst_expr e in
        let args' := List.map (option_map subst_expr) args in
        ExpFunctionCall e' types args'
      | ExpNamelessInstantiation type args =>
        ExpNamelessInstantiation type (subst_exprs args)
      end.

    Definition subst_expr_opt := option_map subst_expr.

    Definition subst_expr_opts := List.map subst_expr_opt.

    Definition subst_exprs : list (@Expression tags_t) -> list (@Expression tags_t) :=
      List.map subst_expr.

    Definition subst_match_pre (match_pre : @MatchPreT tags_t) :  @MatchPreT tags_t :=
      match match_pre with
      | MatchDontCare => MatchDontCare
      | MatchMask e mask => MatchMask (subst_expr e) (subst_expr mask)
      | MatchRange lo hi => MatchRange (subst_expr lo) (subst_expr hi)
      | MatchCast type expr => MatchCast type (subst_expr expr)
      end.

    Definition subst_match (mtch : @Match tags_t) : @Match tags_t :=
      let 'MkMatch tags e type := mtch in
      MkMatch tags (subst_match_pre e) type.

    Definition subst_parser_case (case : @ParserCase tags_t) : @ParserCase tags_t :=
      let 'MkParserCase tags matches next := case in
      let matches' := List.map subst_match matches in
      MkParserCase tags matches' next.

    Definition subst_parser_transition (trans : @ParserTransition tags_t) : @ParserTransition tags_t :=
      match trans with
      | ParserDirect _ _ => trans
      | ParserSelect tags es cases =>
        let es' := subst_exprs es in
        let cases' := List.map subst_parser_case cases in
        ParserSelect tags es' cases'
      end.

    Definition subst_method_call fn types args :=
      StatMethodCall (subst_expr fn) types (subst_expr_opts args).

    Definition subst_assignment e1 e2 :=
      StatAssignment (subst_expr e1) (subst_expr e2).

    Definition subst_direct_application t1 t2 args :=
      StatDirectApplication t1 t2 (subst_expr_opts args).

    Definition subst_return e := StatReturn (subst_expr_opt e).

    Definition subst_constant_stmt type name value loc :=
      StatConstant type name (subst_expr value) loc.

    Definition subst_variable_stmt type name init loc :=
      StatVariable type name (subst_expr_opt init) loc.

  End ConstantEnv.

  Definition update_env (env : Env) (stmt : @Statement tags_t) : Env :=
    let '(MkStatement _ stmt _) := stmt in
    match stmt with
    | StatVariable _ name _ _
    | StatConstant _ name _ _ => Env.remove name.(P4String.str) env
    | _ => env
    end.

  Fixpoint subst_stmt (env : Env) (stmt : @Statement tags_t) : @Statement tags_t :=
    let 'MkStatement tags stmt type := stmt in
    MkStatement tags (subst_stmt_pre env stmt) type

  with subst_stmt_pre (env : Env) (stmt : @StatementPreT tags_t) : @StatementPreT tags_t :=
    let subst_expr := subst_expr env in
    let subst_stmt := subst_stmt env in
    match stmt with
    | StatMethodCall fn types args => subst_method_call env fn types args
    | StatAssignment e1 e2 => subst_assignment env e1 e2
    | StatDirectApplication t1 t2 args =>
      subst_direct_application env t1 t2 args
    | StatConditional e s1 s2 =>
      StatConditional (subst_expr e) (subst_stmt s1) (option_map subst_stmt s2)
    | StatBlock block => StatBlock (subst_block env block)
    | StatExit | StatEmpty => stmt
    | StatReturn e => subst_return env e
    | StatSwitch e cases =>
      let cases' := List.map (subst_switch_case env) cases in
      StatSwitch (subst_expr e) cases'
    | StatConstant type name value loc =>
      subst_constant_stmt env type name value loc
    | StatVariable type name init loc =>
      subst_variable_stmt env type name init loc
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
      let env := update_env env stmt in
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
      let args' := subst_exprs env args in
      let inits' := List.map (subst_initializer env) inits in
      InitInstantiation tags types args' name inits'
    end.

  Definition Statements : Type := list (@Statement tags_t).

  Definition subst_stmts_state : Statements -> State Env Statements :=
    map_monad
      ( fun stmt =>
          let* env := get_state in
          let stmt' := subst_stmt env stmt in
          put_state (update_env env stmt) ;;
          mret stmt'
      ).

  Definition subst_parser_state (env : Env) (state : @ParserState tags_t) : @ParserState tags_t :=
    let 'MkParserState tags name stmts trans := state in
    let stmts_state := subst_stmts_state stmts in
    let (stmts', env') := run_state stmts_state env in
    let trans' := subst_parser_transition env' trans in
    MkParserState tags name stmts' trans'.

  Definition subst_parser_states (env : Env) : list (@ParserState tags_t) -> list (@ParserState tags_t) :=
    List.map (subst_parser_state env).

  Definition update_toplevel_env (env : Env) (d : @Declaration tags_t) : Env :=
    match d with
    | DeclConstant _ _ x e => Env.bind x.(P4String.str) e env
    | _ => env
    end.

  (** Would be nice to declare this as mutually recursive with [subst_decl].
      Unfortuntely, this would not be structurally recursive. *)
  Section SubstDecls.

    Variable subst_decl : Env -> @Declaration tags_t -> @Declaration tags_t.

    (* Fixpoint subst_decls *)

    Definition Declarations := list (@Declaration tags_t).

    Definition subst_decls_state : Declarations -> State Env Declarations :=
      map_monad 
        ( fun decl =>
            let* env := get_state in
            let decl' := subst_decl env decl in
            put_state (update_toplevel_env env decl) ;;
            mret decl'
        ).

    Definition subst_decls (env : Env) (decls : Declarations) : Declarations :=
      eval_state (subst_decls_state decls) env.

    Definition subst_decls_env (env : Env) (decls : Declarations) : Declarations * Env :=
      run_state (subst_decls_state decls) env.

  End SubstDecls.

  Definition subst_function env tags ret name types params body :=
    let body' := subst_block env body in
    DeclFunction tags ret name types params body'.

  Definition subst_variable env tags type name init :=
    let init' := option_map (subst_expr env) init in
    DeclVariable tags type name init'.

  Definition subst_action env tags name dparams cparams body :=
    let body' := subst_block env body in
    DeclAction tags name dparams cparams body'.

  (* Definition subst_table env tags name key actions entries default size props := *)

  Fixpoint subst_decl (env : Env) (decl : @Declaration tags_t) : @Declaration tags_t :=
    let subst_decls := subst_decls subst_decl env in
    let subst_decls_env := subst_decls_env subst_decl env in
    match decl with
    | DeclConstant tags type name value =>
      DeclConstant tags type name (subst_expr env value)
    | DeclInstantiation tags type args name init =>
      let args' := subst_exprs env args in
      let init' := subst_decls init in
      DeclInstantiation tags type args' name init'
    | DeclParser tags name types params cparams locals states =>
      let (locals', env') := subst_decls_env locals in
      let states' := subst_parser_states env' states in
      DeclParser tags name types params cparams locals' states'
    | DeclControl tags name types params cparams locals apply =>
      let (locals', env') := subst_decls_env locals in
      let apply' := subst_block env' apply in
      DeclControl tags name types params cparams locals' apply'
    | DeclFunction tags ret name types params body =>
      subst_function env tags ret name types params body
    | DeclVariable tags type name init =>
      subst_variable env tags type name init
    | DeclExternFunction _ _ _ _ _
    | DeclValueSet _ _ _ _ => decl
    | DeclAction tags name dparams cparams body =>
      subst_action env tags name dparams cparams body
    | _ => decl
    end.

End SubstIdent.
