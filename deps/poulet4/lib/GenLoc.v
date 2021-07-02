Require Import Poulet4.Syntax.
Require Import Typed.
Require Import SyntaxUtil.
Require Import SimplExpr.
Require Import Monads.Monad.
Require Import Monads.State.
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
        (list P4String) :=
    match stmt with
    | StatDirectApplication typ' args => [get_type_name typ']
    | StatBlock block => summarize_blk block
    | StatSwitch expr cases => concat (map summarize_ssc cases)
    | StatInstantiation typ' args name init => [name]
    | _ => nil
    end
  with summarize_stmt (stmt: @Statement tags_t):
      (list P4String) :=
    match stmt with
    | MkStatement tags stmt typ => summarize_stmtpt tags stmt typ
    end
  with summarize_blk (blk: @Block tags_t): (list P4String) :=
    match blk with
    | BlockEmpty tag => nil
    | BlockCons stmt blk' => summarize_stmt stmt ++ summarize_blk blk'
    end
  with summarize_ssc (ssc: @StatementSwitchCase tags_t): (list P4String) :=
    match ssc with
    | StatSwCaseAction tags label code => summarize_blk code
    | StatSwCaseFallThrough _ _ => nil
    end.

  Definition state := list P4String.
  Definition exception := unit.
  Definition monad := @state_monad state exception.

  Definition error {T: Type}: monad T := state_fail tt.

  Definition has {T: Type} (eqb: T -> T -> bool) (x: T) (l: list T): bool :=
    existsb (eqb x) l.

  Definition equivb: P4String -> P4String -> bool := @P4String.equivb tags_t.

  Definition is_used (n: P4String): monad bool :=
    let* used_list := get_state in
    mret (has equivb n used_list).

  Definition var_name (n: P4String) (cnt: N): P4String :=
    if cnt =? 0%N then n else
      let str := P4String.str n in P4String.Build_t _ default_tag (str ++ (N_to_string cnt))%string.

  Fixpoint fresh' (n: P4String) (cnt: N) (fuel: nat): monad P4String :=
    match fuel with
    | O => error
    | S fuel =>
        let n' := var_name n cnt in
        let* b := is_used n' in
        if b then fresh' n (cnt+1) fuel else mret n'
    end.

  Definition use (n: P4String): monad unit :=
    put_state (fun l => n :: l).

  (* In case of preformance issue, we can extract this function into native OCaml. *)
  Definition fresh (n: P4String): monad P4String :=
    let* used_list := get_state in
    let* n' := fresh' n 0 (1 + length used_list)%nat in
    let* _ := use n' in
    mret n'.

  Definition env := @IdentMap.t tags_t (@Locator tags_t).

  Definition name_to_loc (e: env) (n: @Typed.name tags_t) :=
    match n with
    | BareName name =>
        match IdentMap.get name e with
        | Some loc => loc
        | None => NoLocator
        end
    | QualifiedName path name =>
        LGlobal (path ++ [name])
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
      let entries' := map (transform_keyvalue e) entries in
      MkExpression tags (ExpRecord entries') typ dir
    | ExpUnaryOp op arg =>
      let arg' := transform_expr e arg in
      MkExpression tags (ExpUnaryOp op arg') typ dir
    | ExpBinaryOp op (arg1, arg2) =>
      let arg1' := transform_expr e arg1 in
      let arg2' := transform_expr e arg2 in
      MkExpression tags (ExpBinaryOp op (arg1', arg2')) typ dir
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
    | ExpMask expr mask =>
      let expr' := transform_expr e expr in
      let mask' := transform_expr e mask in
      MkExpression tags (ExpMask expr' mask') typ dir
    | ExpRange lo hi =>
      let lo' := transform_expr e lo in
      let hi' := transform_expr e hi in
      MkExpression tags (ExpRange lo' hi') typ dir
    end
  with transform_expr (e: env) (expr: @Expression tags_t): @Expression tags_t :=
    match expr with
    | MkExpression tags expr typ dir => transform_ept e tags expr typ dir
    end
  with transform_keyvalue (e: env) (kv: @KeyValue tags_t): @KeyValue tags_t :=
    match kv with
    | MkKeyValue tags key value =>
        MkKeyValue tags key (transform_expr e value)
    end.

  Definition transform_exprs (e: env) (exprs: list (@Expression tags_t)): list (@Expression tags_t) :=
    map (transform_expr e) exprs.

  Definition transform_oexprs (e: env) (oexprs: list (option (@Expression tags_t))):
      list (option (@Expression tags_t)) :=
    map (option_map (transform_expr e)) oexprs.

  Section transform_stmt.
  Variable (LCurScope: list P4String -> @Locator tags_t). (* LGlobal or LInstance *)

    Fixpoint transform_stmtpt (e: env) (ns: list P4String) (tags: tags_t) (stmt: @StatementPreT tags_t) (typ: StmType):
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
      | StatDirectApplication typ' args =>
        mret (MkStatement tags (StatDirectApplication typ' (transform_exprs e args)) typ, e)
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
        mret (MkStatement tags (StatReturn oexpr) typ, e)
      | StatSwitch expr cases =>
        let expr' := transform_expr e expr in
        let* cases' := sequence (map (transform_ssc e ns) cases) in
        mret (MkStatement tags (StatSwitch expr' cases') typ, e)
      | StatConstant typ' name value _ =>
        let* name' := fresh name in
        let loc := LCurScope (ns ++ [name']) in
        let e' := IdentMap.set name loc e in
        mret (MkStatement tags (StatConstant typ' name value loc) typ, e')
      | StatVariable typ' name init _ =>
        let* name' :=  fresh name in
        let init' := option_map (transform_expr e) init in
        let loc := LCurScope (ns ++ [name']) in
        let e' := IdentMap.set name loc e in
        mret (MkStatement tags (StatVariable typ' name init' loc) typ, e')
      | StatInstantiation typ' args name init =>
        let args' := transform_exprs e args in
        let* init' :=
          match init with
          | Some init => let* init' := transform_blk e ns init in mret (Some init')
          | None => mret None
          end in
        mret (MkStatement tags (StatInstantiation typ' args' name init') typ, e)
      end
    with transform_stmt (e: env) (ns: list P4String) (stmt: @Statement tags_t):
           monad (@Statement tags_t * env) :=
           match stmt with
           | MkStatement tags stmt typ => transform_stmtpt e ns tags stmt typ
           end
    with transform_blk (e: env) (ns: list P4String) (blk: @Block tags_t): monad (@Block tags_t) :=
           match blk with
           | BlockEmpty tag => mret (BlockEmpty tag)
           | BlockCons stmt blk0 =>
             let* (stmt', e') := transform_stmt e ns stmt in
             let* blk0' := transform_blk e' ns blk0 in
             mret (BlockCons stmt' blk0')
           end
    with transform_ssc (e: env) (ns: list P4String) (ssc: @StatementSwitchCase tags_t):
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
    with_state nil m.

  Definition declare_params (LCurScope: list P4String -> @Locator tags_t) (e: env) (ns: list P4String)
                            (params: list (@P4Parameter tags_t)): monad env :=
    let names := map get_param_name params in
    let env_add e name :=
      let loc := LCurScope (ns ++ [name]) in
      IdentMap.set name loc e in
    let e' := fold_left env_add names e in
    let* _ := sequence (map use names) in
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
        match name_to_loc e name with
        | LGlobal [name'] => QualifiedName [] name'
        | LInstance [_] => name
        | _ => name (* This should not happen. *)
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
      | MatchExpression expr =>
        let expr' := transform_expr e expr in
        MkMatch tags (MatchExpression expr') typ
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

  (* Transform declarations except parsers and controls. *)
  Definition transform_decl_base (LCurScope: list P4String -> @Locator tags_t) (e: env) (decl: @Declaration tags_t):
      monad (@Declaration tags_t * env) :=
    match decl with
    | DeclConstant tags typ name value =>
      let* _ := use name in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclConstant tags typ name value, e')
    | DeclInstantiation tags typ args name init =>
      let* _ := use name in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (decl, e')
    | DeclFunction tags ret name type_params params body =>
      let inner_monad := (
        let* e' := declare_params LCurScope e [name] params in
        let* body' := transform_blk LCurScope e' [name] body in
        mret body'
      ) in
      let* body' := with_empty_state inner_monad in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclFunction tags ret name type_params params body', e')
    | DeclExternFunction tags ret name type_params params =>
      let* _ := use name in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (decl, e')
    | DeclVariable tags typ name init =>
      let init' := option_map (transform_expr e) init in
      let* _ := use name in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclVariable tags typ name init', e')
    | DeclValueSet tags typ size name =>
      let size' := transform_expr e size in
      let* _ := use name in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclValueSet tags typ size' name, e')
    | DeclAction tags name data_params ctrl_params body =>
      let inner_monad := (
        let* e' := declare_params LCurScope e [name] data_params in
        let* e'' := declare_params LCurScope e [name] ctrl_params in
        let* body' := transform_blk LCurScope e'' [name] body in
        mret body'
      ) in
      let* body' := with_empty_state inner_monad in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclAction tags name data_params ctrl_params body', e')
    | DeclTable tags name key actions entries default_action size
            custom_properties =>
      let key' := map (transform_tblkey e) key in
      let actions' := map (transform_tar e) actions in
      let entries' := option_map (map (transform_tblenty e)) entries in
      let default_action' := option_map (transform_tar e) default_action in
      let custom_properties' := map (transform_tblprop e) custom_properties in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclTable tags name key' actions' entries' default_action' size
            custom_properties', e')
    (* Maybe we should handle DeclError, DeclMatchKind, DeclEnum, DeclSerializableEnum, DeclExternObject,
        or some of them. *)
    | _ => mret (decl, e)
    end.

  Fixpoint transform_decls_base (LCurScope: list P4String -> @Locator tags_t)
      (e: env) (decls: list (@Declaration tags_t)):
      monad (list (@Declaration tags_t) * env) :=
    match decls with
    | nil => mret (nil, e)
    | decl :: decls0 =>
      let* (decl', e') := transform_decl_base LCurScope e decl in
      let* (decls0', e'') := transform_decls_base LCurScope e' decls0 in
      mret (decl' :: decls0', e'')
    end.

  Definition transform_decl (LCurScope: list P4String -> @Locator tags_t) (e: env) (decl: @Declaration tags_t):
      monad (@Declaration tags_t * env) :=
    match decl with
    | DeclParser tags name type_params params cparams locals states =>
      let inner_scope_monad := (
        let* e' := declare_params LInstance e nil params in
        let* e'' := declare_params LInstance e' nil cparams in
        let* (locals', e''') := transform_decls_base LInstance e'' locals in
        let used_list := concat
              (map (fun ps => summarize_blk (list_statement_to_block default_tag (get_parser_state_statements ps))) states) in
        let* _ := put_state (fun l => used_list ++ l) in
        let* states' := sequence (map (transform_psrst e) states) in
        mret (locals', states')
      ) in
      let* (locals', states') := with_empty_state inner_scope_monad in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclParser tags name type_params params cparams locals' states', e')
    | DeclControl tags name type_params params cparams locals apply =>
      let inner_scope_monad := (
        let* e' := declare_params LInstance e nil params in
        let* e'' := declare_params LInstance e' nil cparams in
        let* (locals', e''') := transform_decls_base LInstance e'' locals in
        (* If there is a direct application in the apply block, then there will not be a definition with
          the same name in local definitions because of shadowing. So there will not be any conflict. *)
        let used_list := summarize_blk apply in
        let* _ := put_state (fun l => used_list ++ l) in
        let* apply' := transform_blk LInstance e''' nil apply in
        mret (locals', apply')
      ) in
      let* (locals', apply') := with_empty_state inner_scope_monad in
      let loc := LCurScope [name] in
      let e' := IdentMap.set name loc e in
      mret (DeclControl tags name type_params params cparams locals' apply', e')
    | _ => transform_decl_base LCurScope e decl
    end.

  Fixpoint transform_decls (LCurScope: list P4String -> @Locator tags_t) (e: env) (decls: list (@Declaration tags_t)):
      monad (list (@Declaration tags_t) * env) :=
    match decls with
    | nil => mret (nil, e)
    | decl :: decls' =>
      let* (decl', e') := transform_decl LCurScope e decl in
      let* (decls'', e'') := transform_decls LCurScope e decls' in
      mret (decl' :: decls'', e'')
    end.

  Definition transform_prog (prog: @program tags_t): @program tags_t + exception :=
    match prog with
    | Program decls =>
      match (transform_decls LGlobal IdentMap.empty decls) nil with
      | (inl (decls', _), _) => inl (Program decls')
      | (inr ex, _) => inr ex
      end
    end.

End Transformer.
