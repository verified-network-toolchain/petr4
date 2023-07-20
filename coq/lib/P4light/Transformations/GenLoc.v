Require Import Poulet4.P4light.Syntax.Syntax.
From Poulet4.P4light.Syntax Require Import Typed SyntaxUtil.
Require Import Poulet4.P4light.Transformations.SimplExpr.
Require Import Poulet4.Monads.ExceptionState.
Require Poulet4.Utils.NameGen.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.

Import Coq.Lists.List.ListNotations.

Open Scope monad.
Open Scope N_scope.

Definition N_to_string : forall (n: N), string := SimplExpr.N_to_string.

Section Transformer.

  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Variable default_tag: tags_t.

  (* The summarization step is necessary, at least for corner cases like this.
       apply {
         { int C; }
         C.apply();
       }
  *)
  Fixpoint summarize_stmtpt (tags: tags_t) (stmt: @StatementPreT tags_t) (typ: StmType):
        (list string) :=
    match stmt with
    | StatDirectApplication typ' _ args => []
    | StatBlock block => summarize_blk block
    | StatSwitch expr cases => concat (map summarize_ssc cases)
    | StatInstantiation typ' args name init => [P4String.str name]
    | _ => nil
    end
  with summarize_stmt (stmt: @Statement tags_t):
      (list string) :=
    match stmt with
    | MkStatement tags stmt typ => summarize_stmtpt tags stmt typ
    end
  with summarize_blk (blk: @Block tags_t): (list string) :=
    match blk with
    | BlockEmpty tag => nil
    | BlockCons stmt blk' => summarize_stmt stmt ++ summarize_blk blk'
    end
  with summarize_ssc (ssc: @StatementSwitchCase tags_t): (list string) :=
    match ssc with
    | StatSwCaseAction tags label code => summarize_blk code
    | StatSwCaseFallThrough _ _ => nil
    end.

  Definition state := NameGen.t.
  Definition exception := unit.
  Definition monad := @state_monad state exception.

  Definition error {T: Type}: monad T := state_fail tt.

  Definition use (n: string): monad unit :=
    fun env =>
      match NameGen.observe_dup env n with
      | None => (inr tt, env)
      | Some ret => (inl tt, ret)
      end.

  Definition use_dup (n: string): monad unit :=
    fun env =>
      match NameGen.observe_dup env n with
      | None => (inr tt, env)
      | Some ret => (inl tt, ret)
      end.

  Definition use_all (n: list string): monad unit :=
    fun env =>
      match NameGen.observe_all env n with
      | None => (inr tt, env)
      | Some ret => (inl tt, ret)
      end.

  (* In case of preformance issue, we can extract this function into native OCaml. *)
  Definition fresh (n: string): monad string :=
    let* env := get_state in
    let (n', env') := NameGen.freshen env n in
    put_state env';;
    mret n'.

  Definition env := IdentMap.t Locator.

  Definition clear_list (p: list (P4String.t tags_t)): list string :=
    map (@P4String.str tags_t) p.

  Definition name_to_loc (e: env) (n: @Typed.name tags_t) :=
    match n with
    | BareName name =>
        match IdentMap.get (P4String.str name) e with
        | Some loc => loc
        | None => LGlobal ["missing_" ++ name.(P4String.str)]%string
        end
    | QualifiedName path name =>
        LGlobal (clear_list (path ++ [name]))
    end.

  Fixpoint transform_ept (e: env) (tags: tags_t) (expr: @ExpressionPreT tags_t) (typ: P4Type) (dir: direction):
      @Expression tags_t :=
    match expr with
    | ExpBool b => MkExpression tags (ExpBool b) typ dir
    | ExpInt i => MkExpression tags (ExpInt i) typ dir
    | ExpString str => MkExpression tags (ExpString str) typ dir
    | ExpName name _ =>
      let loc := name_to_loc e name in
      MkExpression tags (ExpName name loc) typ dir
    | ExpArrayAccess array index =>
      let array' := transform_expr e array in
      let index' := transform_expr e index in
      MkExpression tags (ExpArrayAccess array' index') typ dir
    | ExpBitStringAccess bits lo hi =>
      let bits' := transform_expr e bits in
      MkExpression tags (ExpBitStringAccess bits' lo hi) typ dir
    | ExpList value =>
      let value' := map (transform_expr e) value in
      MkExpression tags (ExpList value') typ dir
    | ExpRecord entries =>
      let entries' := map (fun '(k, v) => (k, transform_expr e v)) entries in
      MkExpression tags (ExpRecord entries') typ dir
    | ExpUnaryOp op arg =>
      let arg' := transform_expr e arg in
      MkExpression tags (ExpUnaryOp op arg') typ dir
    | ExpBinaryOp op arg1 arg2 =>
      let arg1' := transform_expr e arg1 in
      let arg2' := transform_expr e arg2 in
      MkExpression tags (ExpBinaryOp op arg1' arg2') typ dir
    | ExpCast typ' expr =>
      let expr' := transform_expr e expr in
      MkExpression tags (ExpCast typ' expr') typ dir
    | ExpTypeMember typ' name =>
      MkExpression tags (ExpTypeMember typ' name) typ dir
    | ExpErrorMember mem =>
      MkExpression tags (ExpErrorMember mem) typ dir
    | ExpExpressionMember expr name =>
      let expr' := transform_expr e expr in
      MkExpression tags (ExpExpressionMember expr' name) typ dir
    | ExpTernary cond tru fls =>
      let cond' := transform_expr e cond in
      let tru' := transform_expr e tru in
      let fls' := transform_expr e fls in
      MkExpression tags (ExpTernary cond' tru' fls') typ dir
    | ExpFunctionCall func type_args args =>
      let func' := transform_expr e func in
      let args' := map (option_map (transform_expr e)) args in
      MkExpression tags (ExpFunctionCall func' type_args args') typ dir
    | ExpNamelessInstantiation typ' args =>
      let args := map (transform_expr e) args in
      MkExpression tags (ExpNamelessInstantiation typ' args) typ dir
    | ExpDontCare => MkExpression tags ExpDontCare typ dir
    end
  with transform_expr (e: env) (expr: @Expression tags_t): @Expression tags_t :=
    match expr with
    | MkExpression tags expr typ dir => transform_ept e tags expr typ dir
    end.

  Definition transform_exprs (e: env) (exprs: list (@Expression tags_t)): list (@Expression tags_t) :=
    map (transform_expr e) exprs.

  Definition transform_oexprs (e: env) (oexprs: list (option (@Expression tags_t))):
      list (option (@Expression tags_t)) :=
    map (option_map (transform_expr e)) oexprs.

  Section transform_stmt.
  Variable (LCurScope: list string -> Locator). (* LGlobal or LInstance *)

    Fixpoint transform_stmtpt (e: env) (ns: list string) (tags: tags_t) (stmt: @StatementPreT tags_t) (typ: StmType):
        monad (@Statement tags_t * env) :=
      match stmt with
      | StatMethodCall func type_args args =>
        let func' := transform_expr e func in
        let args' := transform_oexprs e args in
        mret (MkStatement tags (StatMethodCall func' type_args args') typ, e)
      | StatAssignment lhs rhs =>
        let lhs' := transform_expr e lhs in
        let rhs' := transform_expr e rhs in
        mret (MkStatement tags (StatAssignment lhs' rhs') typ, e)
      | StatDirectApplication typ' func_typ args =>
        mret (MkStatement tags (StatDirectApplication typ' func_typ (transform_oexprs e args)) typ, e)
      | StatConditional cond tru fls =>
        let cond' := transform_expr e cond in
        let* (tru', _) := transform_stmt e ns tru in
        let* fls' :=
          match fls with
          | Some fls => let* (fls', _) := transform_stmt e ns fls in mret (Some fls')
          | None => mret None
          end in
        mret (MkStatement tags (StatConditional cond' tru' fls') typ, e)
      | StatBlock block =>
        let* block' := transform_blk e ns block in
        mret (MkStatement tags (StatBlock block') typ, e)
      | StatExit => mret (MkStatement tags stmt typ, e)
      | StatEmpty => mret (MkStatement tags stmt typ, e)
      | StatReturn oexpr =>
        let oexpr' := option_map (transform_expr e) oexpr in
        mret (MkStatement tags (StatReturn oexpr') typ, e)
      | StatSwitch expr cases =>
        let expr' := transform_expr e expr in
        let* cases' := sequence (map (transform_ssc e ns) cases) in
        mret (MkStatement tags (StatSwitch expr' cases') typ, e)
      | StatConstant typ' name value _ =>
        let* name' := fresh (P4String.str name) in
        let loc := LCurScope (ns ++ [name']) in
        let e' := IdentMap.set (P4String.str name) loc e in
        mret (MkStatement tags (StatConstant typ' name value loc) typ, e')
      | StatVariable typ' name init _ =>
        let* name' :=  fresh (P4String.str name) in
        let init' := option_map (transform_expr e) init in
        let loc := LCurScope (ns ++ [name']) in
        let e' := IdentMap.set (P4String.str name) loc e in
        mret (MkStatement tags (StatVariable typ' name init' loc) typ, e')
      | StatInstantiation typ' args name init =>
        (* StatInstantiation is unsupported. *)
        let args' := transform_exprs e args in
        mret (MkStatement tags (StatInstantiation typ' args' name []) typ, e)
      end
    with transform_stmt (e: env) (ns: list string) (stmt: @Statement tags_t):
           monad (@Statement tags_t * env) :=
           match stmt with
           | MkStatement tags stmt typ => transform_stmtpt e ns tags stmt typ
           end
    with transform_blk (e: env) (ns: list string) (blk: @Block tags_t): monad (@Block tags_t) :=
           match blk with
           | BlockEmpty tag => mret (BlockEmpty tag)
           | BlockCons stmt blk0 =>
             let* (stmt', e') := transform_stmt e ns stmt in
             let* blk0' := transform_blk e' ns blk0 in
             mret (BlockCons stmt' blk0')
           end
    with transform_ssc (e: env) (ns: list string) (ssc: @StatementSwitchCase tags_t):
           monad (@StatementSwitchCase tags_t) :=
           match ssc with
           | StatSwCaseAction tags label code =>
             let* code' := transform_blk e ns code in
             mret (StatSwCaseAction tags label code')
           | StatSwCaseFallThrough _ _ => mret ssc
           end.

  End transform_stmt.

  Definition with_state {T} (st: state) (m: monad T) : monad T :=
    fun st' => let (res, _) := m st in (res, st').

  Definition with_empty_state {T} (m: monad T): monad T :=
    with_state NameGen.init m.

  Definition declare_params (LCurScope: list string -> Locator) (e: env) (ns: list string)
                            (params: list (@P4Parameter tags_t)): monad env :=
    let names := map get_param_name params in
    let env_add e (name : string) :=
      let loc := LCurScope (ns ++ [name]) in
      IdentMap.set name loc e in
    let e' := fold_left env_add names e in
    sequence (map use names);;
    mret e'.

  Definition transform_tblkey (e: env) (tk: @TableKey tags_t): @TableKey tags_t :=
    match tk with
    | MkTableKey tags key match_kind =>
      let key' := transform_expr e key in
      MkTableKey tags key' match_kind
    end.

  Definition transform_tpar (e: env) (tpar: @TablePreActionRef tags_t): @TablePreActionRef tags_t :=
    match tpar with
    | MkTablePreActionRef name args =>
      let name' :=
        (* Action names should only be global or directly under a control block. *)
        (* Here we abuse name to do the work of a locator. For global actions (LGlobal _),
          we write qualified name (.name) to indicate it is global. For local actions
          (LInstance _), we unqualified name (name). *)
        match name_to_loc e name with
        | LGlobal [name'] => QualifiedName [] (P4String.Build_t tags_t default_tag name')
        | LInstance [_] => name
        | _ => name (* This should never happen. *)
        end in
      let args' := map (option_map (transform_expr e)) args in
      MkTablePreActionRef name' args'
    end.

  Definition transform_tar (e: env) (tar: @TableActionRef tags_t): @TableActionRef tags_t :=
    match tar with
    | MkTableActionRef tags action typ =>
      let action' := transform_tpar e action in
      MkTableActionRef tags action' typ
    end.

  Definition transform_match (e: env) (mt: @Match tags_t): @Match tags_t :=
    match mt with
    | MkMatch tags expr typ =>
      match expr with
      | MatchDontCare => mt
      | MatchMask expr mask =>
        let expr' := transform_expr e expr in
        let mask' := transform_expr e mask in
        MkMatch tags (MatchMask expr' mask') typ
      | MatchRange lo hi =>
        let lo' := transform_expr e lo in
        let hi' := transform_expr e hi in
        MkMatch tags (MatchRange lo' hi') typ
      | MatchCast typ' expr =>
        let expr' := transform_expr e expr in
        MkMatch tags (MatchCast typ' expr') typ
      end
    end.

  Definition transform_psrcase (e: env) (pc: @ParserCase tags_t): @ParserCase tags_t :=
    match pc with
    | MkParserCase tags matches next =>
      let matches' := map (transform_match e) matches in
      MkParserCase tags matches next
    end.

  Definition transform_psrtrans (e: env) (pt: @ParserTransition tags_t): @ParserTransition tags_t :=
    match pt with
    | ParserDirect _ _ => pt
    | ParserSelect tags exprs cases =>
      let exprs' := transform_exprs e exprs in
      let cases' := map (transform_psrcase e) cases in
      ParserSelect tags exprs' cases'
    end.

  Definition transform_psrst (e: env) (ps: @ParserState tags_t): monad (@ParserState tags_t) :=
    match ps with
    | MkParserState tags name statements transition =>
      let* blk' := transform_blk LInstance e [] (list_statement_to_block default_tag statements) in
      let statements' := block_to_list_statement blk' in
      let transition' := transform_psrtrans e transition in
      mret (MkParserState tags name statements' transition')
    end.

  Definition transform_tblenty (e: env) (te: @TableEntry tags_t): @TableEntry tags_t :=
    match te with
    | MkTableEntry tags matches action =>
      let matches' := map (transform_match e) matches in
      let action' := transform_tar e action in
      MkTableEntry tags matches' action'
    end.

  Definition transform_tblprop (e: env) (tp: @TableProperty tags_t): @TableProperty tags_t :=
    match tp with
    | MkTableProperty tags const name value =>
      let value' := transform_expr e value in
      MkTableProperty tags const name value'
    end.

  (* Transform declarations except parsers, controls and instantiations. *)
  Definition transform_decl_base (LCurScope: list string -> Locator) (e: env) (decl: @Declaration tags_t):
      monad (@Declaration tags_t * env) :=
    match decl with
    | DeclConstant tags typ name value =>
      let* name' := fresh (P4String.str name) in
      let p4name' := {| P4String.str := name';
                        P4String.tags := P4String.tags name |} in
      let loc := LCurScope [name'] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclConstant tags typ p4name' value, e')
    | DeclFunction tags ret name type_params params body =>
      use (P4String.str name);;
      let inner_monad := (
        let* e' := declare_params LCurScope e [P4String.str name] params in
        let* body' := transform_blk LCurScope e' [P4String.str name] body in
        mret body'
      ) in
      let* body' := with_empty_state inner_monad in
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclFunction tags ret name type_params params body', e')
    | DeclExternFunction tags ret name type_params params =>
      use_dup (P4String.str name);;
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (decl, e')
    | DeclVariable tags typ name init =>
      let init' := option_map (transform_expr e) init in
      let* name' := fresh (P4String.str name) in
      let p4name' := {| P4String.str := name';
                        P4String.tags := P4String.tags name |} in
      let loc := LCurScope [name'] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclVariable tags typ p4name' init', e')
    | DeclValueSet tags typ size name =>
      use (P4String.str name);;
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclValueSet tags typ size name, e')
    | DeclAction tags name data_params ctrl_params body =>
      let inner_monad := (
        let* e' := declare_params LCurScope e [P4String.str name] data_params in
        let* e'' := declare_params LCurScope e' [P4String.str name] ctrl_params in
        let* body' := transform_blk LCurScope e'' [P4String.str name] body in
        mret body'
      ) in
      let* body' := with_empty_state inner_monad in
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclAction tags name data_params ctrl_params body', e')
    | DeclTable tags name key actions entries default_action size
            custom_properties =>
      let key' := map (transform_tblkey e) key in
      let actions' := map (transform_tar e) actions in
      let entries' := option_map (map (transform_tblenty e)) entries in
      let default_action' := option_map (transform_tar e) default_action in
      let custom_properties' := map (transform_tblprop e) custom_properties in
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclTable tags name key' actions' entries' default_action' size
            custom_properties', e')
    (* Maybe we should handle DeclError, DeclMatchKind, DeclEnum, DeclSerializableEnum, DeclExternObject,
        or some of them. *)
    | _ => mret (decl, e)
    end.

  Fixpoint transform_decls_base (LCurScope: list string -> Locator)
      (e: env) (decls: list (@Declaration tags_t)):
      monad (list (@Declaration tags_t) * env) :=
    match decls with
    | nil => mret (nil, e)
    | decl :: decls0 =>
      let* (decl', e') := transform_decl_base LCurScope e decl in
      let* (decls0', e'') := transform_decls_base LCurScope e' decls0 in
      mret (decl' :: decls0', e'')
    end.

  Fixpoint transform_decl (LCurScope: list string -> Locator) (e: env) (decl: @Declaration tags_t):
      monad (@Declaration tags_t * env) :=
    let transform_decls (LCurScope: list string -> Locator) (e: env) (decls : list (@Declaration tags_t)):
        monad (list (@Declaration tags_t) * env) :=
      Utils.list_rec
        (fun _ => env -> monad (@Declaration tags_t * env))
        (fun _ => env -> monad (list (@Declaration tags_t) * env))
        (fun e => mret (nil, e))
        (fun decl decls' res_decl res_decls' e =>
          let* (decl', e') := res_decl e in
          let* (decls'', e'') := res_decls' e' in
          mret (decl' :: decls'', e''))
        (fun decl e => transform_decl LCurScope e decl)
        decls
        e in
    match decl with
    | DeclParser tags name type_params params cparams locals states =>
      let inner_scope_monad := (
        let* e' := declare_params LInstance e nil params in
        let* e'' := declare_params LInstance e' nil cparams in
        let* (locals', e''') := transform_decls LInstance e'' locals in
        let used_list := concat
              (map (fun ps => summarize_blk (list_statement_to_block default_tag (get_parser_state_statements ps))) states) in
        use_all used_list;;
        let* states' := sequence (map (transform_psrst e''') states) in
        mret (locals', states')
      ) in
      let* (locals', states') := with_empty_state inner_scope_monad in
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclParser tags name type_params params cparams locals' states', e')
    | DeclControl tags name type_params params cparams locals apply =>
      let inner_scope_monad := (
        let* e' := declare_params LInstance e nil params in
        let* e'' := declare_params LInstance e' nil cparams in
        let* (locals', e''') := transform_decls LInstance e'' locals in
        (* If there is a direct application in the apply block, then there will not be a definition with
          the same name in local definitions because of shadowing. So there will not be any conflict. *)
        use_all (summarize_blk apply);;
        let* apply' := transform_blk LInstance e''' nil apply in
        mret (locals', apply')
      ) in
      let* (locals', apply') := with_empty_state inner_scope_monad in
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclControl tags name type_params params cparams locals' apply', e')
    | DeclInstantiation tags typ args name init =>
      let* (init', _) := transform_decls LCurScope e init in
      use (P4String.str name);;
      let loc := LCurScope [P4String.str name] in
      let e' := IdentMap.set (P4String.str name) loc e in
      mret (DeclInstantiation tags typ args name init', e')
    | _ => transform_decl_base LCurScope e decl
    end.

  Fixpoint transform_decls (LCurScope: list string -> Locator) (e: env) (decls: list (@Declaration tags_t)) :
      monad (list (@Declaration tags_t) * env) :=
    match decls with
    | nil => mret (nil, e)
    | decl :: decls' =>
      let* (decl', e') := transform_decl LCurScope e decl in
      let* (decls'', e'') := transform_decls LCurScope e' decls' in
      mret (decl' :: decls'', e'')
    end.

  Definition transform_prog (prog: @program tags_t): @program tags_t + exception :=
    match prog with
    | Program decls =>
      match transform_decls LGlobal IdentMap.empty decls NameGen.init with
      | (inl (decls', _), _) => inl (Program decls')
      | (inr ex, _) => inr ex
      end
    end.

End Transformer.
