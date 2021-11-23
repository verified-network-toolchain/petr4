From Poulet4 Require Import Monads.Error
     P4cub.Syntax.AST P4cub.Syntax.Auxilary.
Require Poulet4.P4cub.Transformations.Lifting.VarNameGen.
Import ListNotations.

Open Scope list_scope.
Open Scope nat_scope.
Open Scope string_scope.

Section Statementize.
  Context {tags_t : Type}.
  Notation t := Expr.t.
  Notation ct := Expr.ct.
  Notation e := (Expr.e tags_t).
  Notation st := (Stmt.s tags_t).
  Notation td := (TopDecl.d tags_t).
  Inductive StatementizeError :=
  | IllformedCargs.

  Definition TransformExprList' 
             (TransformExpr : e -> VarNameGen.t -> (st * e * VarNameGen.t)) 
             (el : list e) (env: VarNameGen.t) (i: tags_t)
    : st * list e * VarNameGen.t := 
    List.fold_right
      (fun (expr: e)
         '((prev_stmt, prev_el, prev_env): (st * list e * VarNameGen.t))
       => let '(new_stmt, new_e, new_env) := TransformExpr expr prev_env in
         ((Stmt.SSeq new_stmt prev_stmt i, new_e :: prev_el), new_env))
      ((Stmt.SSkip i, []), env) el.

  Definition TransformFields'
             (TransformExpr : e -> VarNameGen.t -> (st * e * VarNameGen.t))
             (fs : Field.fs string e) (env: VarNameGen.t) (i: tags_t)
    : st * Field.fs string e * VarNameGen.t :=
    Field.fold 
      (fun (name : string) 
         '(expr : e)
         '((prev_stmt, prev_fs, prev_env): st * Field.fs string e * VarNameGen.t)
       => let '(new_stmt, new_expr, new_env):= TransformExpr expr prev_env in
         (Stmt.SSeq new_stmt prev_stmt i, (name,new_expr) :: prev_fs, new_env)
      ) fs ((Stmt.SSkip i, []), env).

  Definition decl_var_env
             (s : st) (expr : e) (env : VarNameGen.t) (i : tags_t)
    : st * e * VarNameGen.t :=
    let (var_name, env') := VarNameGen.new_var env in
    (Stmt.SSeq s (Stmt.SVardecl var_name (Right expr) i) i,
     Expr.EVar (t_of_e expr) var_name i, env').
  
  Fixpoint TransformExpr (expr : e) (env: VarNameGen.t) 
    : st * e * VarNameGen.t := 
    let TransformExprList := TransformExprList' TransformExpr in
    let TransformFields := TransformFields' TransformExpr in
    match expr with
    | Expr.EBool      _ i
    | Expr.EVar     _ _ i
    | Expr.EError     _ i
    | Expr.EMatchKind _ i => (Stmt.SSkip i, expr, env)
    | Expr.EExprMember ty mem arg i => 
      let '(arg_stmts, sel_arg, env') := TransformExpr arg env in
      (arg_stmts, Expr.EExprMember ty mem sel_arg i, env')
    | Expr.EBit _ _ i
    | Expr.EInt _ _ i =>
      decl_var_env (Stmt.SSkip i) expr env i
    | Expr.ESlice n hi lo i =>  
      let '(n_stmt, n', env_n) := TransformExpr n env in
      decl_var_env n_stmt (Expr.ESlice n' hi lo i) env_n i        
    | Expr.ECast type arg i =>
      let '(arg_stmt, arg', env_arg) := TransformExpr arg env in
      decl_var_env arg_stmt (Expr.ECast type arg' i) env_arg i
    | Expr.EUop rt op arg i => 
      let '(arg_stmt, arg', env_arg) := TransformExpr arg env in
      decl_var_env arg_stmt (Expr.EUop rt op arg' i) env_arg i
    | Expr.EBop rt op lhs rhs i => 
      let '(lhs_stmt, lhs', env_lhs) := TransformExpr lhs env in 
      let '(rhs_stmt, rhs', env_rhs) := TransformExpr rhs env_lhs in
      decl_var_env
        (Stmt.SSeq lhs_stmt rhs_stmt i)
        (Expr.EBop rt op lhs' rhs' i) env_rhs i
    | Expr.ETuple es i => 
      let '(es_stmt, es', env_es) := TransformExprList es env i in 
      decl_var_env es_stmt (Expr.ETuple es' i) env_es i
    | Expr.EStruct fields i =>
      let '(fs_stmt, fs', env_fs) := TransformFields fields env i in 
      decl_var_env fs_stmt (Expr.EStruct fs' i) env_fs i
    | Expr.EHeader fields valid i =>
      let '(fs_stmt, fs', env_fs) := TransformFields fields env i in 
      let '(valid_stmt, valid', env_valid) := TransformExpr valid env_fs in
      decl_var_env
        (Stmt.SSeq fs_stmt valid_stmt i)
        (Expr.EHeader fs' valid' i) env_valid i
    | Expr.EHeaderStack fields headers next_index i => 
      let '(hdrs_stmt, hdrs', env_hdrs) := TransformExprList headers env i in 
      decl_var_env
        hdrs_stmt
        (Expr.EHeaderStack fields hdrs' next_index i)
        env_hdrs i
    | Expr.EHeaderStackAccess ts stack index i =>
      let '(stack_stmt, stack', env_stack) := TransformExpr stack env in
      let val := Expr.EHeaderStackAccess ts stack' index i in 
      let stmt := stack_stmt in
      (stmt, val, env_stack)
    end.
  
  Fixpoint VerifyConstExpr (expr : e) : bool :=
    match expr with
    | Expr.EBool _ _
    | Expr.EBit _ _ _
    | Expr.EInt _ _ _ => true
    | Expr.ESlice n _ _ i =>  VerifyConstExpr n
    | Expr.ECast _ arg _ => VerifyConstExpr arg
    | Expr.EUop _ _ arg _ => VerifyConstExpr arg
    | Expr.EBop _ _ lhs rhs _ => andb (VerifyConstExpr lhs) (VerifyConstExpr rhs) 
    | _ => false
    (* | Expr.EVar type x i => false
       | Expr.EExprMember mem expr_type arg i => false
       | Expr.EError err i => false
       | Expr.EMatchKind mk i => false
       | Expr.ETuple es i => false
       | Expr.EStruct fields i => false
       | Expr.EHeader fields valid i => false
       | Expr.EHeaderStack fields headers size next_index i => false
       | Expr.EHeaderStackAccess stack index i => false *)
    end.
  
  Definition VerifyCArgs 
             (cargs: Expr.constructor_args tags_t)
    : bool :=
    Field.fold 
      (fun (name : string)
         (arg: Expr.constructor_arg tags_t)
         (cumulator : bool)
       => andb cumulator 
              match arg with
              | Expr.CAName _ => true
              | Expr.CAExpr expr => VerifyConstExpr expr 
              end
      ) cargs (true).
  
  Definition TranslateArgs (arguments : Expr.args tags_t) (env : VarNameGen.t) (i: tags_t)
    : st * Expr.args tags_t * VarNameGen.t :=
    Field.fold 
      (fun (name : string) 
         (arg: paramarg (Expr.e tags_t) (Expr.e tags_t))
         (cumulator: ((Stmt.s tags_t * (Expr.args tags_t) * VarNameGen.t)))
       =>  
         let '((prev_stmt, prev_args), prev_env) := cumulator in 
         let expr := match arg with
                     | PADirLess e
                     | PAIn e
                     | PAOut e
                     | PAInOut e => e
                     end in
         let '((new_stmt, new_expr), new_env):= TransformExpr expr prev_env in
         let new_stmt := Stmt.SSeq prev_stmt new_stmt i in
         let new_arg := match arg with 
                        | PADirLess _ => PAIn new_expr
                        | PAIn _ => PAIn new_expr
                        | PAOut _ => PAOut new_expr
                        | PAInOut _ => PAInOut new_expr
                        end in
         ((new_stmt, prev_args++[(name,new_arg)]), new_env)
      ) arguments ((Stmt.SSkip i, []), env).
  
  
  Definition TranslateArrowE
             '({|paramargs:=pas; rtrns:=returns|} : Expr.arrowE tags_t)
             (env : VarNameGen.t) (i: tags_t)
    : st * Expr.arrowE tags_t * VarNameGen.t :=
    let '(pas_stmt, pas', env_pas) := TranslateArgs pas env i in 
    let '(returns_stmt, returns', env_returns):= 
        match returns with
        | None => ((pas_stmt, None), env_pas)
        | Some expr => 
          let '(expr_stmt, expr', env_expr) := TransformExpr expr env_pas in
          (Stmt.SSeq pas_stmt expr_stmt i, Some expr', env_expr) 
        end in
    (returns_stmt, {|paramargs:=pas'; rtrns:=returns'|}, env_returns).
  
  Fixpoint TranslateStatement (stmt : st) (env: VarNameGen.t) 
    : st * VarNameGen.t := 
    match stmt with
    | Stmt.SHeaderStackOp _ _ _ _
    | Stmt.SSkip _
    | Stmt.SExit _
    | Stmt.SInvoke _ _
    | Stmt.SReturn None _
    | Stmt.SVardecl _ (Left _) _ => (stmt, env)
    | Stmt.SVardecl x (Right e) i =>
      let '(s,e',env') := TransformExpr e env in
      (Stmt.SSeq s (Stmt.SVardecl x (Right e') i) i, env')
    | Stmt.SAssign lhs rhs i => 
      let '(lhs_stmt, lhs', env_lhs) := TransformExpr lhs env in 
      let '(rhs_stmt, rhs', env_rhs) := TransformExpr rhs env_lhs in 
      let new_stmt := Stmt.SSeq lhs_stmt (Stmt.SSeq rhs_stmt (Stmt.SAssign lhs' rhs' i) i) i in 
      (new_stmt, env_rhs)
    | Stmt.SConditional guard tru_blk fls_blk i =>
      let '(guard_stmt, guard', env_guard) := TransformExpr guard env in
      let (tru_blk', env_tru) := TranslateStatement tru_blk env_guard in 
      let (fls_blk', env_fls) := TranslateStatement fls_blk env_tru in 
      let new_stmt :=
          Stmt.SSeq
            guard_stmt
            (Stmt.SConditional guard' tru_blk' fls_blk' i) i in
      (new_stmt, env) 
    | Stmt.SSeq s1 s2 i => 
      let (s1', env_s1) := TranslateStatement s1 env in 
      let (s2', env_s2) := TranslateStatement s2 env_s1 in 
      (Stmt.SSeq s1' s2' i, env_s2)
    | Stmt.SBlock block => 
      let (block', env_block) := TranslateStatement block env in
      (Stmt.SBlock block' , env_block)
    | Stmt.SExternMethodCall e f targs args i =>
      let '(stmt_args, args', env_args) := TranslateArrowE args env i in 
      (Stmt.SSeq stmt_args (Stmt.SExternMethodCall e f targs args' i) i, env_args)
    | Stmt.SFunCall f targs args i => 
      let '(stmt_args, args', env_args) := TranslateArrowE args env i in
      (Stmt.SSeq stmt_args (Stmt.SFunCall f targs args' i) i, env_args)
    | Stmt.SActCall f args i => 
      let '(stmt_args, args', env_args) := TranslateArgs args env i in
      (Stmt.SSeq stmt_args (Stmt.SActCall f args' i) i, env_args)
    | Stmt.SReturn (Some e) i => 
      let '(e_stmt, e', env_e) := TransformExpr e env in
      (Stmt.SSeq e_stmt (Stmt.SReturn (Some e') i) i, env_e)
    | Stmt.SApply x ext args i => 
      let '(stmt_args, args', env_args) := TranslateArgs args env i in 
      (Stmt.SSeq stmt_args (Stmt.SApply x ext args' i) i, env_args)
    | Stmt.SSetValidity hdr val i  => 
      let '(hdr_stmt, hdr', env_hdr) := TransformExpr hdr env in 
      (Stmt.SSeq hdr_stmt (Stmt.SSetValidity hdr' val i) i, env_hdr)
    end.  
  
  Definition TranslateCases'
             (TranslateParserExpr : Parser.e tags_t -> VarNameGen.t -> st * Parser.e tags_t * VarNameGen.t)
             (cases: Field.fs Parser.pat (Parser.e tags_t)) (env: VarNameGen.t) (i : tags_t)
    :Stmt.s tags_t * Field.fs Parser.pat (Parser.e tags_t) * VarNameGen.t :=
    Field.fold 
      (fun (pattern: Parser.pat) 
         (e: Parser.e tags_t) 
         (cumulator: Stmt.s tags_t * Field.fs Parser.pat (Parser.e tags_t) * VarNameGen.t)
       => let '(prev_stmt, prev_cases, prev_env) := cumulator in 
         let '(stmt_e, e', env_e) := TranslateParserExpr e prev_env in
         let new_stmt := Stmt.SSeq prev_stmt stmt_e i in 
         let new_cases := prev_cases ++ [(pattern, e')] in
         (new_stmt, new_cases, env_e) 
      ) cases ((Stmt.SSkip i, []), env).
  
  Fixpoint TranslateParserExpr (expr: Parser.e tags_t) (env : VarNameGen.t)
    : st * Parser.e tags_t * VarNameGen.t :=
    let TranslateCases := TranslateCases' TranslateParserExpr in 
    match expr with 
    | Parser.PGoto st i => 
      ((Stmt.SSkip i, Parser.PGoto st i), env)
    | Parser.PSelect exp default cases i => 
      let '(stmt_exp, exp', env_exp) := TransformExpr exp env in
      let '(stmt_default, default', env_default) := TranslateParserExpr default env_exp  in
      let '(stmt_cases, cases', env_cases) := TranslateCases cases env_default i in
      let new_stmt := Stmt.SSeq stmt_exp (Stmt.SSeq stmt_default stmt_cases i ) i in
      (new_stmt, Parser.PSelect exp' default' cases' i, env_cases)
    end.
  
  Definition ParserExprTags (expr: Parser.e tags_t) : tags_t :=
    match expr with
    | Parser.PGoto _ i
    | Parser.PSelect _ _ _ i =>  i
    end.
  
  Definition TranslateParserState 
             '({|Parser.stmt:=stmt; Parser.trans:=transition|}: Parser.state_block tags_t)
             (env : VarNameGen.t)
    : (Parser.state_block tags_t) * VarNameGen.t := 
    let (stmt', env_stmt) := TranslateStatement stmt env in
    let '(stmt_transition, transition', env_transition) := TranslateParserExpr transition env_stmt in
    let i := ParserExprTags transition in  
    let new_stmt := Stmt.SSeq stmt' stmt_transition i in 
    ({|Parser.stmt:=new_stmt; Parser.trans:=transition'|}, env_transition).
  
  
  Definition TranslateParserStates
             (states: Field.fs string (Parser.state_block tags_t))
             (env: VarNameGen.t)
    : Field.fs string (Parser.state_block tags_t) * VarNameGen.t := 
    Field.fold 
      (fun 
          (name: string)
          (parser_state: Parser.state_block tags_t)
          (cumulator: (Field.fs string (Parser.state_block tags_t) * VarNameGen.t))
        =>
          let (prev_states, env_prev) := cumulator in
          let (parser_state', env_state) := TranslateParserState parser_state env_prev in
          (prev_states ++ [(name, parser_state')], env_state)
      ) states ([],env).
  
  Definition TranslateTable
             '({|Control.table_key:=key;
                 Control.table_actions:=actions|} : Control.table tags_t)
             (env: VarNameGen.t) (i : tags_t)
    : st * Control.table tags_t * VarNameGen.t :=
    let '(stmt_key, key', env_key) := 
        List.fold_right 
          (fun '(e,mk) '(s',ky',env) =>
             let '(s, e', env') := TransformExpr e env in 
             (Stmt.SSeq s s' i, (e',mk) :: ky', env'))
          (Stmt.SSkip i, [], env) key in 
    (stmt_key, {|Control.table_key:=key'; Control.table_actions:=actions|}, env_key).
  
  Fixpoint TranslateControlDecl 
           (cd : Control.d tags_t) (env : VarNameGen.t)
    : st * Control.d tags_t * VarNameGen.t :=
    match cd with
    | Control.CDAction a signature body i =>
      let (body', env_body) := TranslateStatement body env in 
      (Stmt.SSkip i, Control.CDAction a signature body' i , env_body)
    | Control.CDTable t bdy i =>
      let '(table_init, bdy', env_bdy) := TranslateTable bdy env i in 
      (table_init, Control.CDTable t bdy' i, env_bdy)
    | Control.CDSeq d1 d2 i => 
      let '(st1, d1', env_d1) := TranslateControlDecl d1 env in 
      let '(st2, d2', env_d2) := TranslateControlDecl d2 env_d1 in 
      (Stmt.SSeq st1 st2 i, Control.CDSeq d1' d2' i, env_d2)
    end.
  

Fixpoint TranslateTopDecl
         (td : TopDecl.d tags_t) (env : VarNameGen.t)
  : @error_monad StatementizeError ((TopDecl.d tags_t) * VarNameGen.t) := 
  match td with 
  | TopDecl.TPInstantiate C x targs cargs i =>
    if (VerifyCArgs cargs) then
      error_ret (TopDecl.TPInstantiate C x targs cargs i, env)
    else (err IllformedCargs)
  | TopDecl.TPExtern e tparams cparams methods i => 
    error_ret (TopDecl.TPExtern e tparams cparams methods i, env)
              
  | TopDecl.TPControl c cparams eps params body apply_blk i =>
    let '(init_blk, body', env_body) := TranslateControlDecl body env in
    let (apply_blk', env_apply_blk) := TranslateStatement apply_blk env_body in
    error_ret (TopDecl.TPControl c cparams eps params body' (Stmt.SSeq init_blk apply_blk' i) i, env_apply_blk)
              
  | TopDecl.TPParser p cparams eps params start states i =>
    let (start', env_start) := TranslateParserState start env in
    let (states', env_states) := TranslateParserStates states env_start in
    error_ret (TopDecl.TPParser p cparams eps params start' states' i, env_states)
              
  | TopDecl.TPFunction f tparams signature body i =>
    let (body', env_body) := TranslateStatement body env in 
    error_ret (TopDecl.TPFunction f tparams signature body' i, env_body)
              
  | TopDecl.TPPackage p tparams cparams i => 
    error_ret (TopDecl.TPPackage p tparams cparams i, env)

  | TopDecl.TPSeq d1 d2 i => 
    let* (d1', env_d1) := TranslateTopDecl d1 env in
    let* (d2', env_d2) := TranslateTopDecl d2 env_d1 in 
    error_ret (TopDecl.TPSeq d1' d2' i, env_d2)
  end.

Definition TranslateProgram (program: TopDecl.d tags_t) 
  : @error_monad StatementizeError (TopDecl.d tags_t):=
  let* (p, e) := TranslateTopDecl program VarNameGen.new_env in
  error_ret p
.

End Statementize.
