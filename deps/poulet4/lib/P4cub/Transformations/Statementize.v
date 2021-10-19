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
  Context (tags_dummy: tags_t).
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
(* 
  | P4cub.Expr.EBop op lhs_type rhs_type lhs rhs i => 
    let (lhs_result, env_lhs) := TransformExpr lhs env in 
    let (lhs_stmt, lhs') := lhs_result in
    let (rhs_result, env_rhs) := TransformExpr rhs env_lhs in 
    let (rhs_stmt, rhs') := rhs_result in
    let (var_name, env') := VarNameGen.new_var env_rhs in
    let dst_type := lhs_type in (*the result type is always the same as lhs type*)
    let declaration := SelS.SVardecl dst_type var_name i in
    let assign := SelS.SBop dst_type op lhs' rhs' var_name i in 
    let stmt := SelS.SSeq lhs_stmt (SelS.SSeq rhs_stmt (SelS.SSeq declaration assign i) i) i in
    ( (stmt, SelE.EVar dst_type var_name i), env')

  | P4cub.Expr.ETuple es i =>
    let type := CubE.TBool in 
    let '((es_stmt, es'), env_es) := TranslateExprList es env i in 
    let (var_name, env') := VarNameGen.new_var env_es in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.STuple es' var_name i in 
    let stmt := SelS.SSeq es_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')

  | P4cub.Expr.EStruct fields i => 
    let type := CubE.TBool in 
    let '((fs_stmt, fs'), env_fs) := TranslateFields fields env i in 
    let (var_name, env') := VarNameGen.new_var env_fs in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SStruct fs' var_name i in 
    let stmt := SelS.SSeq fs_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')

  | P4cub.Expr.EHeader fields valid i =>
    let type := CubE.TBool in 
    let '((fs_stmt, fs'), env_fs) := TranslateFields fields env i in 
    let '((valid_stmt, valid'), env_valid) := TransformExpr valid env in
    let (var_name, env') := VarNameGen.new_var env_valid in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SHeader fs' var_name valid' i in 
    let stmt := SelS.SSeq fs_stmt (SelS.SSeq valid_stmt (SelS.SSeq declaration assign i) i) i in
    ( (stmt, SelE.EVar type var_name i), env')

  | P4cub.Expr.EHeaderStack fields headers size next_index i => 
    let type := CubE.TBool in 
    let '((hdrs_stmt, hdrs'), env_hdrs) := TranslateExprList headers env i in 
    let (var_name, env') := VarNameGen.new_var env_hdrs in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SHeaderStack fields hdrs' size next_index var_name i in 
    let stmt := SelS.SSeq hdrs_stmt (SelS.SSeq declaration assign i) i in
    ((stmt, SelE.EVar type var_name i), env')

  | P4cub.Expr.EHeaderStackAccess stack index i => 
    let type := CubE.TBool in 
    let '((stack_stmt, stack'), env_stack) := TransformExpr stack env in
    let val := SelE.EHeaderStackAccess stack' index i in 
    let stmt := stack_stmt in
    ( (stmt, val), env_stack) *)
  (*| CubE.EString s i => ((SelS.SSkip i,SelE.EString _ s i), env)
  | CubE.EEnum x m i => ((SelS.SSkip i, SelE.EEnum _ x m i), env)*)
  | _ => (P4cub.Stmt.SSkip tags_dummy, P4cub.Expr.EBool true tags_dummy, env)
  end.



Definition TranslateCArg 
(carg: P4cub.Expr.constructor_arg tags_t) (env: VarNameGen.t) (i : tags_t)
: st * P4cub.Expr.constructor_arg tags_t * VarNameGen.t.
  Admitted.
Definition TranslateCArgs 
(cargs: P4cub.Expr.constructor_args tags_t) (env: VarNameGen.t) (i: tags_t)
: st * P4cub.Expr.constructor_args tags_t * VarNameGen.t.
  Admitted.

Definition TranslateArgs (arguments : P4cub.Expr.args tags_t) (env : VarNameGen.t) (i: tags_t)
  : st * P4cub.Expr.args tags_t * VarNameGen.t.
  Admitted.

Definition TranslateArrowE (arguments : P4cub.Expr.arrowE tags_t) (env : VarNameGen.t) (i: tags_t)
  : st * P4cub.Expr.arrowE tags_t * VarNameGen.t.
  Admitted.

Fixpoint TranslateStatement (stmt : st) (env: VarNameGen.t) 
  : st * VarNameGen.t.
  Admitted.

Fixpoint TranslateParserExpr (expr: P4cub.Parser.e tags_t) (env : VarNameGen.t)
  : st * P4cub.Parser.e tags_t * VarNameGen.t.
  Admitted.
  

Definition ParserExprTags (expr: P4cub.Parser.e tags_t) : tags_t.
  Admitted.

Definition TranslateParserState 
  (parser_state: P4cub.Parser.state_block tags_t) (env : VarNameGen.t)
  : (P4cub.Parser.state_block tags_t) * VarNameGen.t := 
  match parser_state with 
  | P4cub.Parser.State stmt transition =>
    let (stmt', env_stmt) := TranslateStatement stmt env in
    let '((stmt_transition, transition'), env_transition) := TranslateParserExpr transition env_stmt in
    let i := ParserExprTags transition in  
    let new_stmt := P4cub.Stmt.SSeq stmt' stmt_transition i in 
    (P4cub.Parser.State new_stmt transition', env_transition)
  end.
  

Definition TranslateParserStates
  (states: Field.fs string (P4cub.Parser.state_block tags_t))
  (env: VarNameGen.t)
  : (Field.fs string (P4cub.Parser.state_block tags_t)) * VarNameGen.t := 
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
  : (P4cub.Control.ControlDecl.table tags_t) * VarNameGen.t.
  Admitted.


Fixpoint TranslateControlDecl 
  (cd : P4cub.Control.ControlDecl.d tags_t) (env : VarNameGen.t)
  : (P4cub.Control.ControlDecl.d tags_t) * VarNameGen.t.
  Admitted.


Fixpoint TranslateTopDecl
  (td : P4cub.TopDecl.d tags_t) (env : VarNameGen.t)
  : (P4cub.TopDecl.d tags_t) * VarNameGen.t.
  Admitted.

Definition TranslateProgram (program: P4cub.TopDecl.d tags_t) 
  : P4cub.TopDecl.d tags_t :=
  fst (TranslateTopDecl program VarNameGen.new_env).

End Statementize.
