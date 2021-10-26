Require Import Poulet4.P4cub.Syntax.AST.
Require Import Poulet4.Monads.Error.
Require Poulet4.P4sel.VarNameGen.
Require Import Field.
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
  (fs : Field.fs string (t * e)) (env: VarNameGen.t) (i: tags_t)
  : st * Field.fs string (t * e) * VarNameGen.t :=
  Field.fold 
  (fun (name : string) 
     '((type, expr): t * e)
     '((prev_stmt, prev_fs, prev_env): st * Field.fs string (t * e) * VarNameGen.t)
   => let '(new_stmt, new_expr, new_env):= TransformExpr expr prev_env in
     (Stmt.SSeq new_stmt prev_stmt i, (name,(type,new_expr)) :: prev_fs, new_env)
  ) fs ((Stmt.SSkip i, []), env).

Fixpoint TransformExpr (expr : e) (env: VarNameGen.t) 
  : st * e * VarNameGen.t := 
  let TransformExprList := TransformExprList' TransformExpr in
  let TransformFields := TransformFields' TransformExpr in
  match expr with
  | Expr.EBool b i => (Stmt.SSkip i,Expr.EBool b i, env)

  | Expr.EVar type x i => (Stmt.SSkip i, Expr.EVar type x i, env)

  | Expr.EExprMember mem expr_type arg i => 
    let '(arg_stmts, sel_arg, env') := TransformExpr arg env in
    (arg_stmts, Expr.EExprMember mem expr_type sel_arg i, env')

  | Expr.EError err i => (Stmt.SSkip i, Expr.EError err i, env)

  | Expr.EMatchKind mk i => (Stmt.SSkip i, Expr.EMatchKind mk i, env)

  | Expr.EBit width val i => 
    let type := Expr.TBit width in 
    let (var_name, env') := VarNameGen.new_var env in
    let declaration := Stmt.SVardecl type var_name i in
    let assign := Stmt.SAssign type (Expr.EVar type var_name i) expr i in 
    (Stmt.SSeq declaration assign i, Expr.EVar type var_name i, env')

  | Expr.EInt width val i => 
    let type := Expr.TInt width in 
    let (var_name, env') := VarNameGen.new_var env in
    let declaration := Stmt.SVardecl type var_name i in
    let assign := Stmt.SAssign type (Expr.EVar type var_name i) expr i in 
    (Stmt.SSeq declaration assign i, Expr.EVar type var_name i, env')
  
  | Expr.ESlice n τ hi lo i =>  
    let '(n_stmt, n', env_n) := TransformExpr n env in 
    let (var_name, env') := VarNameGen.new_var env_n in
    let declaration := Stmt.SVardecl τ var_name i in
    let assign := Stmt.SAssign τ (Expr.EVar τ var_name i) (Expr.ESlice n' τ hi lo i) i in 
    let stmt := Stmt.SSeq n_stmt (Stmt.SSeq declaration assign i) i in
    (stmt, Expr.EVar τ var_name i, env')
  
  | Expr.ECast type arg i =>
    let '(arg_stmt, arg', env_arg) := TransformExpr arg env in 
    let (var_name, env') := VarNameGen.new_var env_arg in
    let declaration := Stmt.SVardecl type var_name i in
    let assign :=
        Stmt.SAssign
          type (Expr.EVar type var_name i) (Expr.ECast type arg' i) i in 
    let stmt := Stmt.SSeq arg_stmt (Stmt.SSeq declaration assign i) i in
    (stmt, Expr.EVar type var_name i, env')

  | Expr.EUop op type arg i => 
    let '(arg_stmt, arg', env_arg) := TransformExpr arg env in 
    let (var_name, env') := VarNameGen.new_var env_arg in
    let declaration := Stmt.SVardecl type var_name i in
    let assign :=
        Stmt.SAssign
          type (Expr.EVar type var_name i) (Expr.EUop op type arg' i) i in 
    let stmt := Stmt.SSeq arg_stmt (Stmt.SSeq declaration assign i) i in
    (stmt, Expr.EVar type var_name i, env')

  | Expr.EBop op lhs_type rhs_type lhs rhs i => 
    let '(lhs_stmt, lhs', env_lhs) := TransformExpr lhs env in 
    let '(rhs_stmt, rhs', env_rhs) := TransformExpr rhs env_lhs in 
    let (var_name, env') := VarNameGen.new_var env_rhs in
    let dst_type := lhs_type in
    let declaration := Stmt.SVardecl dst_type var_name i in
    let assign := Stmt.SAssign dst_type (Expr.EVar dst_type var_name i) (Expr.EBop op lhs_type rhs_type lhs' rhs' i) i in 
    let stmt := Stmt.SSeq lhs_stmt (Stmt.SSeq rhs_stmt (Stmt.SSeq declaration assign i) i) i in
    (stmt, Expr.EVar dst_type var_name i, env')

  | Expr.ETuple es i => 
    let type := Expr.cub_type_of tags_t expr in 
    let '(es_stmt, es', env_es) := TransformExprList es env i in 
    let (var_name, env') := VarNameGen.new_var env_es in
    let declaration := Stmt.SVardecl type var_name i in
    let assign := Stmt.SAssign type (Expr.EVar type var_name i) (Expr.ETuple es' i) i in 
    let stmt := Stmt.SSeq es_stmt (Stmt.SSeq declaration assign i) i in
    (stmt, Expr.EVar type var_name i, env')

  | Expr.EStruct fields i => 
    let type := Expr.cub_type_of tags_t expr in 
    let '(fs_stmt, fs', env_fs) := TransformFields fields env i in 
    let (var_name, env') := VarNameGen.new_var env_fs in
    let declaration := Stmt.SVardecl type var_name i in
    let assign := Stmt.SAssign type (Expr.EVar type var_name i) (Expr.EStruct fs' i) i in 
    let stmt := Stmt.SSeq fs_stmt (Stmt.SSeq declaration assign i) i in
    (stmt, Expr.EVar type var_name i, env')

  | Expr.EHeader fields valid i =>
    let type := Expr.cub_type_of tags_t expr in 
    let '(fs_stmt, fs', env_fs) := TransformFields fields env i in 
    let '(valid_stmt, valid', env_valid) := TransformExpr valid env in
    let (var_name, env') := VarNameGen.new_var env_valid in
    let declaration := Stmt.SVardecl type var_name i in
    let assign := Stmt.SAssign type (Expr.EVar type var_name i) (Expr.EHeader fs' valid' i) i in 
    let stmt := Stmt.SSeq fs_stmt (Stmt.SSeq valid_stmt (Stmt.SSeq declaration assign i) i) i in
    (stmt, Expr.EVar type var_name i, env')

  | Expr.EHeaderStack fields headers size next_index i => 
    let type := Expr.cub_type_of tags_t expr in 
    let '((hdrs_stmt, hdrs'), env_hdrs) := TransformExprList headers env i in 
    let (var_name, env') := VarNameGen.new_var env_hdrs in
    let declaration := Stmt.SVardecl type var_name i in
    let assign := Stmt.SAssign type (Expr.EVar type var_name i) (Expr.EHeaderStack fields hdrs' size next_index i) i in 
    let stmt := Stmt.SSeq hdrs_stmt (Stmt.SSeq declaration assign i) i in
    (stmt, Expr.EVar type var_name i, env')

  | Expr.EHeaderStackAccess stack index i =>
    let type := Expr.cub_type_of tags_t expr in 
    let '(stack_stmt, stack', env_stack) := TransformExpr stack env in
    let val := Expr.EHeaderStackAccess stack' index i in 
    let stmt := stack_stmt in
    (stmt, val, env_stack)
  end.

Fixpoint VerifyConstExpr (expr : e) : bool :=
  match expr with
  | Expr.EBool b i => true
  | Expr.EBit width val i => true
  | Expr.EInt width val i => true
  | Expr.ESlice n τ hi lo i =>  VerifyConstExpr n
  | Expr.ECast type arg i => VerifyConstExpr arg
  | Expr.EUop op type arg i => VerifyConstExpr arg
  | Expr.EBop op lhs_type rhs_type lhs rhs i => andb (VerifyConstExpr lhs) (VerifyConstExpr rhs) 
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
       (arg: paramarg (Expr.t * Expr.e tags_t) (Expr.t * Expr.e tags_t))
       (cumulator: ((Stmt.s tags_t * (Expr.args tags_t) * VarNameGen.t)))
      =>  
      let '((prev_stmt, prev_args), prev_env) := cumulator in 
      let (type, expr) := match arg with
        | PADirLess (t, e)
        | PAIn (t, e)
        | PAOut (t, e)
        | PAInOut (t, e) => (t, e)
        end in
      let '((new_stmt, new_expr), new_env):= TransformExpr expr prev_env in
      let new_stmt := Stmt.SSeq prev_stmt new_stmt i in
      let new_arg := match arg with 
        | PADirLess _ => PAIn (type, new_expr)
        | PAIn _ => PAIn (type, new_expr)
        | PAOut _ => PAOut (type, new_expr)
        | PAInOut _ => PAInOut (type, new_expr) 
        end in
      ((new_stmt, prev_args++[(name,new_arg)]), new_env)
  ) arguments ((Stmt.SSkip i, []), env).


Definition TranslateArrowE (arguments : Expr.arrowE tags_t) (env : VarNameGen.t) (i: tags_t)
  : st * Expr.arrowE tags_t * VarNameGen.t :=
  match arguments with 
  | Arrow pas returns => 
    let '(pas_stmt, pas', env_pas) := TranslateArgs pas env i in 
    let '(returns_stmt, returns', env_returns):= 
      match returns with
      | None => ((pas_stmt, None), env_pas)
      | Some (type, expr) => 
        let '(expr_stmt, expr', env_expr) := TransformExpr expr env_pas in
        (Stmt.SSeq pas_stmt expr_stmt i, Some (type, expr'), env_expr) 
      end in
    (returns_stmt, Arrow pas' returns', env_returns)
  end.

Fixpoint TranslateStatement (stmt : st) (env: VarNameGen.t) 
  : st * VarNameGen.t := 
  match stmt with
  | Stmt.SHeaderStackOp name op n i => (Stmt.SHeaderStackOp name op n i, env)
  | Stmt.SSkip i => (Stmt.SSkip i, env)
  | Stmt.SVardecl type x i => (Stmt.SVardecl type x i, env)
  | Stmt.SAssign type lhs rhs i => 
    let '(lhs_stmt, lhs', env_lhs) := TransformExpr lhs env in 
    let '(rhs_stmt, rhs', env_rhs) := TransformExpr rhs env_lhs in 
    let new_stmt := Stmt.SSeq lhs_stmt (Stmt.SSeq rhs_stmt (Stmt.SAssign type lhs' rhs' i) i) i in 
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
  | Stmt.SReturnVoid i => (Stmt.SReturnVoid i, env)
  | Stmt.SReturnFruit t e i => 
    let '(e_stmt, e', env_e) := TransformExpr e env in
    (Stmt.SSeq e_stmt (Stmt.SReturnFruit t e' i) i, env_e)
  | Stmt.SExit i => (Stmt.SExit i, env)
  | Stmt.SInvoke x i => (Stmt.SInvoke x i, env)
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
  (parser_state: Parser.state_block tags_t) (env : VarNameGen.t)
  : (Parser.state_block tags_t) * VarNameGen.t := 
  match parser_state with 
  | Parser.State stmt transition =>
    let (stmt', env_stmt) := TranslateStatement stmt env in
    let '(stmt_transition, transition', env_transition) := TranslateParserExpr transition env_stmt in
    let i := ParserExprTags transition in  
    let new_stmt := Stmt.SSeq stmt' stmt_transition i in 
    (Parser.State new_stmt transition', env_transition)
  end.
  

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
  (table : Control.table tags_t) (env: VarNameGen.t) (i : tags_t)
  : st * Control.table tags_t * VarNameGen.t :=
  match table with
  | Control.Table key actions =>
    let '(stmt_key, key', env_key) := 
      List.fold_left 
      (fun 
        (cumulator: (Stmt.s tags_t) * list (Expr.t * Expr.e tags_t * Expr.matchkind) * VarNameGen.t)
        (key : Expr.t * Expr.e tags_t * Expr.matchkind)
        => let '(prev_stmt, prev_keys, prev_env) := cumulator in
          let '(type, expr, mk) := key in
          let '(expr_stmt, expr', env_expr) := TransformExpr expr prev_env in 
          let new_stmt := Stmt.SSeq prev_stmt expr_stmt i in
          let new_keys := prev_keys ++ [(type, expr', mk)] in 
          (new_stmt, new_keys, env_expr)   
        )
        key (Stmt.SSkip i, [], env)
      in 
      (stmt_key, Control.Table key' actions, env_key)
  end .


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
