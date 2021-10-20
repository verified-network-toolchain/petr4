Require Import Poulet4.P4cub.Syntax.AST.
Require Import Poulet4.Monads.Option.
Require Poulet4.P4sel.VarNameGen.
Require Import Field.
Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.


Section Statementize.
  Context (tags_t : Type).
  Notation t := P4cub.Expr.t.
  Notation ct := P4cub.Expr.ct.
  Notation e := (P4cub.Expr.e tags_t).
  Notation st := (P4cub.Stmt.s tags_t).
  Notation td := (P4cub.TopDecl.d tags_t).

Definition TransformExprList' 
  (TransformExpr : e -> VarNameGen.t -> (st * e * VarNameGen.t)) 
  (el : list e) (env: VarNameGen.t) (i: tags_t)
  : st * list e * VarNameGen.t := 
  List.fold_left 
  (fun (cumulator: (st * list e * VarNameGen.t)) (expr: e)
   => let '(prev_stmt, prev_el, prev_env) := cumulator in 
      let '(new_stmt, new_e, new_env) := TransformExpr expr prev_env in
      ((P4cub.Stmt.SSeq prev_stmt new_stmt i, prev_el ++ [new_e]), new_env) 
  ) el ((P4cub.Stmt.SSkip i, []), env).


Definition TransformFields' 
  (TransformExpr : e -> VarNameGen.t -> (st * e * VarNameGen.t))
  (fs : Field.fs string (t * e)) (env: VarNameGen.t) (i: tags_t)
  : st * Field.fs string (t * e) * VarNameGen.t :=
  Field.fold 
  (fun (name : string) 
      (field: t * e)
      (cumulator: st * Field.fs string (t * e) * VarNameGen.t)
  =>  
    let '(prev_stmt, prev_fs, prev_env) := cumulator in 
    let '(type, expr) := field in
    let '(new_stmt, new_expr, new_env):= TransformExpr expr prev_env in
    (P4cub.Stmt.SSeq prev_stmt new_stmt i, prev_fs++[(name,(type,new_expr))], new_env)
  ) fs ((P4cub.Stmt.SSkip i, []), env).

Fixpoint TransformExpr (expr : e) (env: VarNameGen.t) 
  : st * e * VarNameGen.t := 
  let TransformExprList := TransformExprList' TransformExpr in
  let TransformFields := TransformFields' TransformExpr in
  match expr with
  | P4cub.Expr.EBool b i => (P4cub.Stmt.SSkip i,P4cub.Expr.EBool b i, env)

  | P4cub.Expr.EVar type x i => (P4cub.Stmt.SSkip i, P4cub.Expr.EVar type x i, env)

  | P4cub.Expr.EExprMember mem expr_type arg i => 
    let '(arg_stmts, sel_arg, env') := TransformExpr arg env in
    (arg_stmts, P4cub.Expr.EExprMember mem expr_type sel_arg i, env')

  | P4cub.Expr.EError err i => (P4cub.Stmt.SSkip i, P4cub.Expr.EError err i, env)

  | P4cub.Expr.EMatchKind mk i => (P4cub.Stmt.SSkip i, P4cub.Expr.EMatchKind mk i, env)

  | P4cub.Expr.EBit width val i => 
    let type := P4cub.Expr.TBit width in 
    let (var_name, env') := VarNameGen.new_var env in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) expr i in 
    (P4cub.Stmt.SSeq declaration assign i, P4cub.Expr.EVar type var_name i, env')

  | P4cub.Expr.EInt width val i => 
    let type := P4cub.Expr.TInt width in 
    let (var_name, env') := VarNameGen.new_var env in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) expr i in 
    (P4cub.Stmt.SSeq declaration assign i, P4cub.Expr.EVar type var_name i, env')
  
  | P4cub.Expr.ESlice n τ hi lo i =>  
    let '(n_stmt, n', env_n) := TransformExpr n env in 
    let (var_name, env') := VarNameGen.new_var env_n in
    let declaration := P4cub.Stmt.SVardecl τ var_name i in
    let assign := P4cub.Stmt.SAssign τ (P4cub.Expr.EVar τ var_name i) (P4cub.Expr.ESlice n' τ hi lo i) i in 
    let stmt := P4cub.Stmt.SSeq n_stmt (P4cub.Stmt.SSeq declaration assign i) i in
    (stmt, P4cub.Expr.EVar τ var_name i, env')
  
  | P4cub.Expr.ECast type arg i =>
    let '(arg_stmt, arg', env_arg) := TransformExpr arg env in 
    let (var_name, env') := VarNameGen.new_var env_arg in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) (P4cub.Expr.ECast type arg' i) i in 
    let stmt := P4cub.Stmt.SSeq arg_stmt (P4cub.Stmt.SSeq declaration assign i) i in
    (stmt, P4cub.Expr.EVar type var_name i, env')

  | P4cub.Expr.EUop op type arg i => 
    let (arg_result, env_arg) := TransformExpr arg env in 
    let (var_name, env') := VarNameGen.new_var env_arg in
    let (arg_stmt, arg') := arg_result in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) (P4cub.Expr.EUop op type arg' i) i in 
    let stmt := P4cub.Stmt.SSeq arg_stmt (P4cub.Stmt.SSeq declaration assign i) i in
    (stmt, P4cub.Expr.EVar type var_name i, env')

  | P4cub.Expr.EBop op lhs_type rhs_type lhs rhs i => 
    let '(lhs_stmt, lhs', env_lhs) := TransformExpr lhs env in 
    let '(rhs_stmt, rhs', env_rhs) := TransformExpr rhs env_lhs in 
    let (var_name, env') := VarNameGen.new_var env_rhs in
    let dst_type := lhs_type in
    let declaration := P4cub.Stmt.SVardecl dst_type var_name i in
    let assign := P4cub.Stmt.SAssign dst_type (P4cub.Expr.EVar dst_type var_name i) (P4cub.Expr.EBop op lhs_type rhs_type lhs' rhs' i) i in 
    let stmt := P4cub.Stmt.SSeq lhs_stmt (P4cub.Stmt.SSeq rhs_stmt (P4cub.Stmt.SSeq declaration assign i) i) i in
    (stmt, P4cub.Expr.EVar dst_type var_name i, env')

  | P4cub.Expr.ETuple es i => (*TODO: get the correct type*)
    let type := P4cub.Expr.TBool in 
    let '(es_stmt, es', env_es) := TransformExprList es env i in 
    let (var_name, env') := VarNameGen.new_var env_es in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) (P4cub.Expr.ETuple es' i) i in 
    let stmt := P4cub.Stmt.SSeq es_stmt (P4cub.Stmt.SSeq declaration assign i) i in
    (stmt, P4cub.Expr.EVar type var_name i, env')

  | P4cub.Expr.EStruct fields i => (*TODO: get the correct type*)
    let type := P4cub.Expr.TBool in 
    let '(fs_stmt, fs', env_fs) := TransformFields fields env i in 
    let (var_name, env') := VarNameGen.new_var env_fs in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) (P4cub.Expr.EStruct fs' i) i in 
    let stmt := P4cub.Stmt.SSeq fs_stmt (P4cub.Stmt.SSeq declaration assign i) i in
    (stmt, P4cub.Expr.EVar type var_name i, env')

  | P4cub.Expr.EHeader fields valid i =>(*TODO: get the correct type*)
    let type := P4cub.Expr.TBool in 
    let '(fs_stmt, fs', env_fs) := TransformFields fields env i in 
    let '(valid_stmt, valid', env_valid) := TransformExpr valid env in
    let (var_name, env') := VarNameGen.new_var env_valid in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) (P4cub.Expr.EHeader fs' valid' i) i in 
    let stmt := P4cub.Stmt.SSeq fs_stmt (P4cub.Stmt.SSeq valid_stmt (P4cub.Stmt.SSeq declaration assign i) i) i in
    (stmt, P4cub.Expr.EVar type var_name i, env')

  | P4cub.Expr.EHeaderStack fields headers size next_index i => (*TODO: get the correct type*)
    let type := P4cub.Expr.TBool in 
    let '((hdrs_stmt, hdrs'), env_hdrs) := TransformExprList headers env i in 
    let (var_name, env') := VarNameGen.new_var env_hdrs in
    let declaration := P4cub.Stmt.SVardecl type var_name i in
    let assign := P4cub.Stmt.SAssign type (P4cub.Expr.EVar type var_name i) (P4cub.Expr.EHeaderStack fields hdrs' size next_index i) i in 
    let stmt := P4cub.Stmt.SSeq hdrs_stmt (P4cub.Stmt.SSeq declaration assign i) i in
    (stmt, P4cub.Expr.EVar type var_name i, env')

  | P4cub.Expr.EHeaderStackAccess stack index i =>(*TODO: get the correct type*) 
    let type := P4cub.Expr.TBool in 
    let '(stack_stmt, stack', env_stack) := TransformExpr stack env in
    let val := P4cub.Expr.EHeaderStackAccess stack' index i in 
    let stmt := stack_stmt in
    (stmt, val, env_stack)
  end.



Definition TranslateCArg 
  (carg: P4cub.Expr.constructor_arg tags_t) (env: VarNameGen.t) (i : tags_t)
  : st * P4cub.Expr.constructor_arg tags_t * VarNameGen.t :=
  match carg with 
  | P4cub.Expr.CAExpr expr => 
    let '(stmt_expr, expr', env_expr) := TransformExpr expr env in
    (stmt_expr, P4cub.Expr.CAExpr expr', env_expr)
  | P4cub.Expr.CAName x => (P4cub.Stmt.SSkip i, P4cub.Expr.CAName x, env)
  end.
Definition TranslateCArgs 
  (cargs: P4cub.Expr.constructor_args tags_t) (env: VarNameGen.t) (i: tags_t)
  : st * P4cub.Expr.constructor_args tags_t * VarNameGen.t :=
  Field.fold 
  (fun (name : string)
       (arg: P4cub.Expr.constructor_arg tags_t)
       (cumulator : (P4cub.Stmt.s tags_t) * (P4cub.Expr.constructor_args tags_t) * VarNameGen.t)
   => 
   let '(prev_stmt, prev_cargs, prev_env) := cumulator in 
   let '(arg_stmt, arg', arg_env) := TranslateCArg arg prev_env i in 
   let new_stmt := P4cub.Stmt.SSeq prev_stmt arg_stmt i in
   let new_cargs := prev_cargs ++ [(name,arg')] in
   (new_stmt, new_cargs, arg_env) 
  ) cargs (P4cub.Stmt.SSkip i, [], env).

Definition TranslateArgs (arguments : P4cub.Expr.args tags_t) (env : VarNameGen.t) (i: tags_t)
  : st * P4cub.Expr.args tags_t * VarNameGen.t :=
  Field.fold 
  (fun (name : string) 
       (arg: P4cub.paramarg (P4cub.Expr.t * P4cub.Expr.e tags_t) (P4cub.Expr.t * P4cub.Expr.e tags_t))
       (cumulator: ((P4cub.Stmt.s tags_t * (P4cub.Expr.args tags_t) * VarNameGen.t)))
      =>  
      let '((prev_stmt, prev_args), prev_env) := cumulator in 
      let (type, expr) := match arg with
        | P4cub.PADirLess (t, e)
        | P4cub.PAIn (t, e)
        | P4cub.PAOut (t, e)
        | P4cub.PAInOut (t, e) => (t, e)
        end in
      let '((new_stmt, new_expr), new_env):= TransformExpr expr prev_env in
      let new_stmt := P4cub.Stmt.SSeq prev_stmt new_stmt i in
      let new_arg := match arg with 
        | P4cub.PADirLess _ => P4cub.PAIn (type, new_expr)
        | P4cub.PAIn _ => P4cub.PAIn (type, new_expr)
        | P4cub.PAOut _ => P4cub.PAOut (type, new_expr)
        | P4cub.PAInOut _ => P4cub.PAInOut (type, new_expr) 
        end in
      ((new_stmt, prev_args++[(name,new_arg)]), new_env)
  ) arguments ((P4cub.Stmt.SSkip i, []), env).


Definition TranslateArrowE (arguments : P4cub.Expr.arrowE tags_t) (env : VarNameGen.t) (i: tags_t)
  : st * P4cub.Expr.arrowE tags_t * VarNameGen.t :=
  match arguments with 
  | P4cub.Arrow pas returns => 
    let '(pas_stmt, pas', env_pas) := TranslateArgs pas env i in 
    let '(returns_stmt, returns', env_returns):= 
      match returns with
      | None => ((pas_stmt, None), env_pas)
      | Some (type, expr) => 
        let '(expr_stmt, expr', env_expr) := TransformExpr expr env_pas in
        (P4cub.Stmt.SSeq pas_stmt expr_stmt i, Some (type, expr'), env_expr) 
      end in
    (returns_stmt, P4cub.Arrow pas' returns', env_returns)
  end.

Fixpoint TranslateStatement (stmt : st) (env: VarNameGen.t) 
  : st * VarNameGen.t := 
  match stmt with
  | P4cub.Stmt.SHeaderStackOp name op n i => (P4cub.Stmt.SHeaderStackOp name op n i, env)
  | P4cub.Stmt.SSkip i => (P4cub.Stmt.SSkip i, env)
  | P4cub.Stmt.SVardecl type x i => (P4cub.Stmt.SVardecl type x i, env)
  | P4cub.Stmt.SAssign type lhs rhs i => 
    let '(lhs_stmt, lhs', env_lhs) := TransformExpr lhs env in 
    let '(rhs_stmt, rhs', env_rhs) := TransformExpr rhs env_lhs in 
    let new_stmt := P4cub.Stmt.SSeq lhs_stmt (P4cub.Stmt.SSeq rhs_stmt (P4cub.Stmt.SAssign type lhs' rhs' i) i) i in 
    (new_stmt, env_rhs)
  | P4cub.Stmt.SConditional guard_type guard tru_blk fls_blk i =>
    let '(guard_stmt, guard', env_guard) := TransformExpr guard env in
    let (tru_blk', env_tru) := TranslateStatement tru_blk env_guard in 
    let (fls_blk', env_fls) := TranslateStatement fls_blk env_tru in 
    let new_stmt := P4cub.Stmt.SSeq guard_stmt (P4cub.Stmt.SConditional guard_type guard' tru_blk' fls_blk' i) i in
    (new_stmt, env) 
  | P4cub.Stmt.SSeq s1 s2 i => 
    let (s1', env_s1) := TranslateStatement s1 env in 
    let (s2', env_s2) := TranslateStatement s2 env_s1 in 
    (P4cub.Stmt.SSeq s1' s2' i, env_s2)
  | P4cub.Stmt.SBlock block => 
    let (block', env_block) := TranslateStatement block env in
    (P4cub.Stmt.SBlock block' , env_block)
  | P4cub.Stmt.SExternMethodCall e f targs args i =>
    let '(stmt_args, args', env_args) := TranslateArrowE args env i in 
    (P4cub.Stmt.SSeq stmt_args (P4cub.Stmt.SExternMethodCall e f targs args' i) i, env_args)
  | P4cub.Stmt.SFunCall f targs args i => 
    let '(stmt_args, args', env_args) := TranslateArrowE args env i in
    (P4cub.Stmt.SSeq stmt_args (P4cub.Stmt.SFunCall f targs args' i) i, env_args)
  | P4cub.Stmt.SActCall f args i => 
    let '(stmt_args, args', env_args) := TranslateArgs args env i in
    (P4cub.Stmt.SSeq stmt_args (P4cub.Stmt.SActCall f args' i) i, env_args)
  | P4cub.Stmt.SReturnVoid i => (P4cub.Stmt.SReturnVoid i, env)
  | P4cub.Stmt.SReturnFruit t e i => 
    let '(e_stmt, e', env_e) := TransformExpr e env in
    (P4cub.Stmt.SSeq e_stmt (P4cub.Stmt.SReturnFruit t e' i) i, env_e)
  | P4cub.Stmt.SExit i => (P4cub.Stmt.SExit i, env)
  | P4cub.Stmt.SInvoke x i => (P4cub.Stmt.SInvoke x i, env)
  | P4cub.Stmt.SApply x ext args i => 
    let '(stmt_args, args', env_args) := TranslateArgs args env i in 
    (P4cub.Stmt.SSeq stmt_args (P4cub.Stmt.SApply x ext args' i) i, env_args)
  | P4cub.Stmt.SSetValidity hdr val i  => 
    let '(hdr_stmt, hdr', env_hdr) := TransformExpr hdr env in 
    (P4cub.Stmt.SSeq hdr_stmt (P4cub.Stmt.SSetValidity hdr' val i) i, env_hdr)
  end.


Definition TranslateCases'
  (TranslateParserExpr : P4cub.Parser.e tags_t -> VarNameGen.t -> st * P4cub.Parser.e tags_t * VarNameGen.t)
  (cases: Field.fs P4cub.Parser.pat (P4cub.Parser.e tags_t)) (env: VarNameGen.t) (i : tags_t)
  :P4cub.Stmt.s tags_t * Field.fs P4cub.Parser.pat (P4cub.Parser.e tags_t) * VarNameGen.t :=
  Field.fold 
  (fun (pattern: P4cub.Parser.pat) 
       (e: P4cub.Parser.e tags_t) 
       (cumulator: P4cub.Stmt.s tags_t * Field.fs P4cub.Parser.pat (P4cub.Parser.e tags_t) * VarNameGen.t)
    => let '(prev_stmt, prev_cases, prev_env) := cumulator in 
       let '(stmt_e, e', env_e) := TranslateParserExpr e prev_env in
       let new_stmt := P4cub.Stmt.SSeq prev_stmt stmt_e i in 
       let new_cases := prev_cases ++ [(pattern, e')] in
       (new_stmt, new_cases, env_e) 
    ) cases ((P4cub.Stmt.SSkip i, []), env).

Fixpoint TranslateParserExpr (expr: P4cub.Parser.e tags_t) (env : VarNameGen.t)
  : st * P4cub.Parser.e tags_t * VarNameGen.t :=
  let TranslateCases := TranslateCases' TranslateParserExpr in 
  match expr with 
  | P4cub.Parser.PGoto st i => 
    ((P4cub.Stmt.SSkip i, P4cub.Parser.PGoto st i), env)
  | P4cub.Parser.PSelect exp default cases i => 
    let '(stmt_exp, exp', env_exp) := TransformExpr exp env in
    let '(stmt_default, default', env_default) := TranslateParserExpr default env_exp  in
    let '(stmt_cases, cases', env_cases) := TranslateCases cases env_default i in
    let new_stmt := P4cub.Stmt.SSeq stmt_exp (P4cub.Stmt.SSeq stmt_default stmt_cases i ) i in
    (new_stmt, P4cub.Parser.PSelect exp' default' cases' i, env_cases)
  end.
  

Definition ParserExprTags (expr: P4cub.Parser.e tags_t) : tags_t :=
  match expr with
  | P4cub.Parser.PGoto _ i
  | P4cub.Parser.PSelect _ _ _ i =>  i
  end.

Definition TranslateParserState 
  (parser_state: P4cub.Parser.state_block tags_t) (env : VarNameGen.t)
  : (P4cub.Parser.state_block tags_t) * VarNameGen.t := 
  match parser_state with 
  | P4cub.Parser.State stmt transition =>
    let (stmt', env_stmt) := TranslateStatement stmt env in
    let '(stmt_transition, transition', env_transition) := TranslateParserExpr transition env_stmt in
    let i := ParserExprTags transition in  
    let new_stmt := P4cub.Stmt.SSeq stmt' stmt_transition i in 
    (P4cub.Parser.State new_stmt transition', env_transition)
  end.
  

Definition TranslateParserStates
  (states: Field.fs string (P4cub.Parser.state_block tags_t))
  (env: VarNameGen.t)
  : Field.fs string (P4cub.Parser.state_block tags_t) * VarNameGen.t := 
  Field.fold 
    (fun 
      (name: string)
      (parser_state: P4cub.Parser.state_block tags_t)
      (cumulator: (Field.fs string (P4cub.Parser.state_block tags_t) * VarNameGen.t))
      =>
      let (prev_states, env_prev) := cumulator in
      let (parser_state', env_state) := TranslateParserState parser_state env_prev in
      (prev_states ++ [(name, parser_state')], env_state)
    ) states ([],env).

Definition TranslateTable
  (table : P4cub.Control.ControlDecl.table tags_t) (env: VarNameGen.t) (i : tags_t)
  : st * P4cub.Control.ControlDecl.table tags_t * VarNameGen.t :=
  match table with
  | P4cub.Control.ControlDecl.Table key actions =>
    let '(stmt_key, key', env_key) := 
      List.fold_left 
      (fun 
        (cumulator: (P4cub.Stmt.s tags_t) * list (P4cub.Expr.t * P4cub.Expr.e tags_t * P4cub.Expr.matchkind) * VarNameGen.t)
        (key : P4cub.Expr.t * P4cub.Expr.e tags_t * P4cub.Expr.matchkind)
        => let '(prev_stmt, prev_keys, prev_env) := cumulator in
          let '(type, expr, mk) := key in
          let '(expr_stmt, expr', env_expr) := TransformExpr expr prev_env in 
          let new_stmt := P4cub.Stmt.SSeq prev_stmt expr_stmt i in
          let new_keys := prev_keys ++ [(type, expr', mk)] in 
          (new_stmt, new_keys, env_expr)   
        )
        key (P4cub.Stmt.SSkip i, [], env)
      in 
      (stmt_key, P4cub.Control.ControlDecl.Table key' actions, env_key)
  end .


Fixpoint TranslateControlDecl 
  (cd : P4cub.Control.ControlDecl.d tags_t) (env : VarNameGen.t)
  : st * P4cub.Control.ControlDecl.d tags_t * VarNameGen.t :=
  match cd with
  | P4cub.Control.ControlDecl.CDAction a signature body i =>
    let (body', env_body) := TranslateStatement body env in 
    (P4cub.Stmt.SSkip i, P4cub.Control.ControlDecl.CDAction a signature body' i , env_body)
  | P4cub.Control.ControlDecl.CDTable t bdy i =>
    let '(table_init, bdy', env_bdy) := TranslateTable bdy env i in 
    (table_init, P4cub.Control.ControlDecl.CDTable t bdy' i, env_bdy)
  | P4cub.Control.ControlDecl.CDSeq d1 d2 i => 
    let '(st1, d1', env_d1) := TranslateControlDecl d1 env in 
    let '(st2, d2', env_d2) := TranslateControlDecl d2 env_d1 in 
    (P4cub.Stmt.SSeq st1 st2 i, P4cub.Control.ControlDecl.CDSeq d1' d2' i, env_d2)
  end.


Fixpoint TranslateTopDecl
  (td : P4cub.TopDecl.d tags_t) (env : VarNameGen.t)
  : (P4cub.TopDecl.d tags_t) * VarNameGen.t := 
  match td with 
  | P4cub.TopDecl.TPInstantiate C x targs cargs i => (*TODO: what to do with the statement here?*)
    let '(cargs_stmt, cargs', env_cargs) := TranslateCArgs cargs env i in
    (P4cub.TopDecl.TPInstantiate C x targs cargs' i, env_cargs)

  | P4cub.TopDecl.TPExtern e tparams cparams methods i => 
    (P4cub.TopDecl.TPExtern e tparams cparams methods i, env)

  | P4cub.TopDecl.TPControl c cparams eps params body apply_blk i =>
    let '(init_blk, body', env_body) := TranslateControlDecl body env in
    let (apply_blk', env_apply_blk) := TranslateStatement apply_blk env_body in
    (P4cub.TopDecl.TPControl c cparams eps params body' (P4cub.Stmt.SSeq init_blk apply_blk' i) i, env_apply_blk)

  | P4cub.TopDecl.TPParser p cparams eps params start states i =>
    let (start', env_start) := TranslateParserState start env in
    let (states', env_states) := TranslateParserStates states env_start in
    (P4cub.TopDecl.TPParser p cparams eps params start' states' i, env_states)

  | P4cub.TopDecl.TPFunction f tparams signature body i =>
    let (body', env_body) := TranslateStatement body env in 
    (P4cub.TopDecl.TPFunction f tparams signature body' i, env_body)

  | P4cub.TopDecl.TPPackage p tparams cparams i => 
    (P4cub.TopDecl.TPPackage p tparams cparams i, env)

  | P4cub.TopDecl.TPSeq d1 d2 i => 
    let (d1', env_d1) := TranslateTopDecl d1 env in
    let (d2', env_d2) := TranslateTopDecl d2 env_d1 in 
    (P4cub.TopDecl.TPSeq d1' d2' i, env_d2)
  end.

Definition TranslateProgram (program: P4cub.TopDecl.d tags_t) 
  : P4cub.TopDecl.d tags_t :=
  fst (TranslateTopDecl program VarNameGen.new_env).

End Statementize.
