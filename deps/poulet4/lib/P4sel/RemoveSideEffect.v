Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4sel.P4sel.
Require Import Poulet4.Monads.Option.
Require Poulet4.P4sel.VarNameGen.
Module Cub := P4cub.
Module F := Cub.F.
Module CubE := Cub.Expr.
Module CubS := Cub.Stmt.
Module CubPA := Cub.Parser.
Module CubCT := Cub.Control.ControlDecl.
Module CubTD := Cub.TopDecl.
Module Sel := P4sel.
Module SelE := Sel.Expr.
Module SelS := Sel.Stmt.
Module SelPA := Sel.Parser.
Module SelCT := Sel.Control.ControlDecl.
Module SelTD := Sel.TopDecl.
Section Translation.
  Context (tags_t : Type).

Fixpoint TranslateExpr (e : CubE.e tags_t) (env: VarNameGen.t) 
: (SelS.s tags_t * SelE.e tags_t) * VarNameGen.t := 
  let TranslateExprList (el : list (CubE.e tags_t)) (env: VarNameGen.t) (i: tags_t)
  : ((SelS.s tags_t * (list (SelE.e tags_t)))* VarNameGen.t) :=
    List.fold_left 
    (fun (cumulator: ((SelS.s tags_t * list (SelE.e tags_t))* VarNameGen.t))
         (expr: CubE.e tags_t)
    =>  let '((prev_stmt, prev_el), prev_env) := cumulator in 
        let '((new_stmt, new_e), new_env) := TranslateExpr expr prev_env in
        ((SelS.SSeq prev_stmt new_stmt i, prev_el ++ [new_e]), new_env) 
    ) el ((SelS.SSkip i, []), env)
  in
  let TranslateFields 
    (fs : F.fs string (CubE.t * (CubE.e tags_t)))
    (env: VarNameGen.t) 
    (i: tags_t)
  : ((SelS.s tags_t * 
    (F.fs string (CubE.t * (SelE.e tags_t)))) *
    VarNameGen.t) :=
    F.fold 
    (fun (name : string) 
        (field: CubE.t * (CubE.e tags_t))
        (cumulator: ((SelS.s tags_t * (F.fs string (CubE.t * (SelE.e tags_t)))) * VarNameGen.t))
    =>  
      let '((prev_stmt, prev_fs), prev_env) := cumulator in 
      let '(type, expr) := field in
      let '((new_stmt, new_expr), new_env):= TranslateExpr expr prev_env in
      ((SelS.SSeq prev_stmt new_stmt i, prev_fs++[(name,(type,new_expr))]), new_env)
    ) fs ((SelS.SSkip i, []), env)
  in  
  match e with
  | CubE.EBool b i => ((SelS.SSkip i,SelE.EBool b i), env)
  | CubE.EVar type x i => ((SelS.SSkip i, SelE.EVar type x i), env)
  | CubE.EExprMember mem expr_type arg i => 
    let (result, env') := TranslateExpr arg env in
    let (arg_stmts, sel_arg) := result in
    ((arg_stmts, SelE.EExprMember mem expr_type sel_arg i), env')
  | CubE.EError err i => ((SelS.SSkip i, SelE.EError err i), env)
  | CubE.EMatchKind mk i => ((SelS.SSkip i, SelE.EMatchKind mk i), env)
  | CubE.EBit width val i => 
    let type := CubE.TBit width in 
    let (var_name, env') := VarNameGen.new_var env in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SBitAssign type var_name width val i in 
    ((SelS.SSeq declaration assign i, SelE.EVar type var_name i), env')
  | CubE.EInt width val i => 
    let type := CubE.TInt width in 
    let (var_name, env') := VarNameGen.new_var env in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SIntAssign type var_name width val i in 
    ((SelS.SSeq declaration assign i, SelE.EVar type var_name i), env')
  
  | CubE.ESlice n τ hi lo i =>  
    let (n_result, env_n) := TranslateExpr n env in 
    let (var_name, env') := VarNameGen.new_var env_n in
    let (n_stmt, n') := n_result in
    let declaration := SelS.SVardecl τ var_name i in
    let assign := SelS.SSlice n' τ hi lo var_name i in 
    let stmt := SelS.SSeq n_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar τ var_name i), env')
  
  | CubE.ECast type arg i =>
    let (arg_result, env_arg) := TranslateExpr arg env in 
    let (var_name, env') := VarNameGen.new_var env_arg in
    let (arg_stmt, arg') := arg_result in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SCast type arg' var_name i in 
    let stmt := SelS.SSeq arg_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')
  | CubE.EUop op type arg i => 
    let (arg_result, env_arg) := TranslateExpr arg env in 
    let (var_name, env') := VarNameGen.new_var env_arg in
    let (arg_stmt, arg') := arg_result in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SUop type op arg' var_name i in 
    let stmt := SelS.SSeq arg_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')
  | CubE.EBop op lhs_type rhs_type lhs rhs i => 
    let (lhs_result, env_lhs) := TranslateExpr lhs env in 
    let (lhs_stmt, lhs') := lhs_result in
    let (rhs_result, env_rhs) := TranslateExpr rhs env_lhs in 
    let (rhs_stmt, rhs') := rhs_result in
    let (var_name, env') := VarNameGen.new_var env_rhs in
    let dst_type := lhs_type in (*the result type is always the same as lhs type*)
    let declaration := SelS.SVardecl dst_type var_name i in
    let assign := SelS.SBop dst_type op lhs' rhs' var_name i in 
    let stmt := SelS.SSeq lhs_stmt (SelS.SSeq rhs_stmt (SelS.SSeq declaration assign i) i) i in
    ( (stmt, SelE.EVar dst_type var_name i), env')
  | CubE.ETuple es i =>
    let type := CubE.TBool in 
    let '((es_stmt, es'), env_es) := TranslateExprList es env i in 
    let (var_name, env') := VarNameGen.new_var env_es in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.STuple es' var_name i in 
    let stmt := SelS.SSeq es_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')
  | CubE.EStruct fields i => 
    let type := CubE.TBool in 
    let '((fs_stmt, fs'), env_fs) := TranslateFields fields env i in 
    let (var_name, env') := VarNameGen.new_var env_fs in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SStruct fs' var_name i in 
    let stmt := SelS.SSeq fs_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')
  | CubE.EHeader fields valid i =>
    let type := CubE.TBool in 
    let '((fs_stmt, fs'), env_fs) := TranslateFields fields env i in 
    let '((valid_stmt, valid'), env_valid) := TranslateExpr valid env in
    let (var_name, env') := VarNameGen.new_var env_valid in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SHeader fs' var_name valid' i in 
    let stmt := SelS.SSeq fs_stmt (SelS.SSeq valid_stmt (SelS.SSeq declaration assign i) i) i in
    ( (stmt, SelE.EVar type var_name i), env')
  | CubE.EHeaderStack fields headers size next_index i => 
    let type := CubE.TBool in 
    let '((hdrs_stmt, hdrs'), env_hdrs) := TranslateExprList headers env i in 
    let (var_name, env') := VarNameGen.new_var env_hdrs in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SHeaderStack fields hdrs' size next_index var_name i in 
    let stmt := SelS.SSeq hdrs_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')
  | CubE.EHeaderStackAccess stack index i => 
    let type := CubE.TBool in 
    let '((stack_stmt, stack'), env_stack) := TranslateExpr stack env in
    let (var_name, env') := VarNameGen.new_var env_stack in
    let declaration := SelS.SVardecl type var_name i in
    let assign := SelS.SHeaderStackAccess stack' index var_name i in 
    let stmt := SelS.SSeq stack_stmt (SelS.SSeq declaration assign i) i in
    ( (stmt, SelE.EVar type var_name i), env')
  end.
Definition TranslateCArg 
(carg: CubE.constructor_arg tags_t) (env: VarNameGen.t) (i : tags_t)
: (SelS.s tags_t) * (SelE.constructor_arg tags_t )* VarNameGen.t :=
  match carg with 
  | CubE.CAExpr expr => 
    let '((stmt_expr, expr'), env_expr) := TranslateExpr expr env in
    (stmt_expr, SelE.CAExpr expr', env_expr)
  | CubE.CAName x => (SelS.SSkip i, SelE.CAName x, env)
  end
.

Definition TranslateCArgs 
(cargs: CubE.constructor_args tags_t) (env: VarNameGen.t) (i: tags_t)
: (SelS.s tags_t) * (SelE.constructor_args tags_t) * VarNameGen.t :=
  F.fold 
  (fun (name : string)
       (arg: CubE.constructor_arg tags_t)
       (cumulator : (SelS.s tags_t) * (SelE.constructor_args tags_t) * VarNameGen.t)
   => 
   let '(prev_stmt, prev_cargs, prev_env) := cumulator in 
   let '(arg_stmt, arg', arg_env) := TranslateCArg arg prev_env i in 
   let new_stmt := SelS.SSeq prev_stmt arg_stmt i in
   let new_cargs := prev_cargs ++ [(name,arg')] in
   (new_stmt, new_cargs, arg_env) 
  ) cargs (SelS.SSkip i, [], env).

Definition TranslateArgs (arguments : CubE.args tags_t) (env : VarNameGen.t) (i: tags_t)
  : ((SelS.s tags_t * SelE.args tags_t) * VarNameGen.t) := 
  F.fold 
  (fun (name : string) 
       (arg: Cub.paramarg (CubE.t * CubE.e tags_t) (CubE.t * CubE.e tags_t))
       (cumulator: ((SelS.s tags_t * (SelE.args tags_t) * VarNameGen.t)))
      =>  
      let '((prev_stmt, prev_args), prev_env) := cumulator in 
      let (type, expr) := match arg with
        | Cub.PAIn (t, e)
        | Cub.PAOut (t, e)
        | Cub.PAInOut (t, e) => (t, e)
        end in
      let '((new_stmt, new_expr), new_env):= TranslateExpr expr prev_env in
      let new_stmt := SelS.SSeq prev_stmt new_stmt i in
      let new_arg := match arg with 
        | Cub.PAIn _ => Cub.PAIn (type, new_expr)
        | Cub.PAOut _ => Cub.PAOut (type, new_expr)
        | Cub.PAInOut _ => Cub.PAInOut (type, new_expr) 
        end in
      ((new_stmt, prev_args++[(name,new_arg)]), new_env)
  ) arguments ((SelS.SSkip i, []), env).


Definition TranslateArrowE (arguments : CubE.arrowE tags_t) (env : VarNameGen.t) (i: tags_t)
  : ((SelS.s tags_t * SelE.arrowE tags_t) * VarNameGen.t) := 
  match arguments with 
  | Cub.Arrow pas returns => 
    let '((pas_stmt, pas'), env_pas) := TranslateArgs pas env i in 
    let '((returns_stmt, returns'), env_returns):= 
      match returns with
      | None => ((pas_stmt, None), env_pas)
      | Some (type, expr) => 
        let '((expr_stmt, expr'), env_expr) := TranslateExpr expr env_pas in
        ((SelS.SSeq pas_stmt expr_stmt i, Some (type, expr')), env_expr) 
      end in
    ((returns_stmt, Cub.Arrow pas' returns'), env_returns)
  end.

Fixpoint TranslateStatement (stmt : CubS.s tags_t) (env: VarNameGen.t) : (SelS.s tags_t) * VarNameGen.t := 
  match stmt with 
  | CubS.SSkip i => (SelS.SSkip i, env) 
  | CubS.SVardecl type x i => (SelS.SVardecl type x i, env)
  | CubS.SAssign type lhs rhs i => 
    let '((lhs_stmt, lhs'), env_lhs) := TranslateExpr lhs env in 
    let '((rhs_stmt, rhs'), env_rhs) := TranslateExpr rhs env_lhs in 
    let new_stmt := SelS.SSeq lhs_stmt (SelS.SSeq rhs_stmt (SelS.SAssign type lhs' rhs' i) i) i in 
    (new_stmt, env_rhs)
  | CubS.SConditional guard_type guard tru_blk fls_blk i =>
    let '((guard_stmt, guard'), env_guard) := TranslateExpr guard env in
    let (tru_blk', env_tru) := TranslateStatement tru_blk env_guard in 
    let (fls_blk', env_fls) := TranslateStatement fls_blk env_tru in 
    let new_stmt := SelS.SSeq guard_stmt (SelS.SConditional guard_type guard' tru_blk' fls_blk' i) i in
    (new_stmt, env) 
  | CubS.SSeq s1 s2 i => 
    let (s1', env_s1) := TranslateStatement s1 env in 
    let (s2', env_s2) := TranslateStatement s2 env_s1 in 
    (SelS.SSeq s1' s2' i, env_s2)
  | CubS.SBlock block => 
    let (block', env_block) := TranslateStatement block env in
    (SelS.SBlock block' , env_block)
  | CubS.SExternMethodCall e f args i =>
    let '((stmt_args, args'), env_args) := TranslateArrowE args env i in 
    (SelS.SSeq stmt_args (SelS.SExternMethodCall e f args' i) i, env_args)
  | CubS.SFunCall f args i => 
    let '((stmt_args, args'), env_args) := TranslateArrowE args env i in
    (SelS.SSeq stmt_args (SelS.SFunCall f args' i) i, env_args)
  | CubS.SActCall f args i => 
    let '((stmt_args, args'), env_args) := TranslateArgs args env i in
    (SelS.SSeq stmt_args (SelS.SActCall f args' i) i, env_args)
  | CubS.SReturnVoid i => (SelS.SReturnVoid i, env)
  | CubS.SReturnFruit t e i => 
    let '((e_stmt, e'), env_e) := TranslateExpr e env in
    (SelS.SSeq e_stmt (SelS.SReturnFruit t e' i) i, env_e)
  | CubS.SExit i => (SelS.SExit i, env)
  | CubS.SInvoke x i => (SelS.SInvoke x i, env)
  | CubS.SApply x args i => 
    let '((stmt_args, args'), env_args) := TranslateArgs args env i in 
    (SelS.SSeq stmt_args (SelS.SApply x args' i) i, env_args)
  end.


Fixpoint TranslateParserExpr
(expr: CubPA.e tags_t) (env : VarNameGen.t)
: (SelS.s tags_t * SelPA.e tags_t) * VarNameGen.t := 
  let TranslateCases (cases: F.fs CubPA.pat (CubPA.e tags_t)) (env: VarNameGen.t) (i : tags_t)
  :((SelS.s tags_t) * (F.fs CubPA.pat (SelPA.e tags_t))) * VarNameGen.t
  :=
    F.fold 
    (fun  (pattern: CubPA.pat) 
          (e: CubPA.e tags_t) 
          (cumulator: ((SelS.s tags_t) * (F.fs CubPA.pat (SelPA.e tags_t)))* VarNameGen.t)
     => let '((prev_stmt, prev_cases), prev_env) := cumulator in 
        let '((stmt_e, e'), env_e) := TranslateParserExpr e prev_env in
        let new_stmt := SelS.SSeq prev_stmt stmt_e i in 
        let new_cases := prev_cases ++ [(pattern, e')] in
        ((new_stmt, new_cases), env_e) 
     ) cases ((SelS.SSkip i, []), env)
  in 
  match expr with 
  | CubPA.PGoto st i => 
    ((SelS.SSkip i, SelPA.PGoto st i), env)
  | CubPA.PSelect exp default cases i => 
    let '((stmt_exp, exp'), env_exp) := TranslateExpr exp env in
    let '((stmt_default, default'), env_default) := TranslateParserExpr default env_exp  in
    let '((stmt_cases, cases'), env_cases) := TranslateCases cases env_default i in
    let new_stmt := SelS.SSeq stmt_exp (SelS.SSeq stmt_default stmt_cases i ) i in
    ((new_stmt, SelPA.PSelect exp' default' cases' i), env_cases)
  end.

Definition ParserExprTags (expr: CubPA.e tags_t) : tags_t := 
  match expr with
  | CubPA.PGoto _ i
  | CubPA.PSelect _ _ _ i =>  i
  end.

Definition TranslateParserState 
(state: CubPA.state_block tags_t) (env : VarNameGen.t)
: (SelPA.state_block tags_t) * VarNameGen.t := 
match state with 
| CubPA.State stmt transition =>
  let (stmt', env_stmt) := TranslateStatement stmt env in
  let '((stmt_transition, transition'), env_transition) := TranslateParserExpr transition env_stmt in
  let i := ParserExprTags transition in  
  let new_stmt := SelS.SSeq stmt' stmt_transition i in 
  (SelPA.State new_stmt transition', env_transition)
end.

Definition TranslateParserStates
(states: F.fs string (CubPA.state_block tags_t))
(env: VarNameGen.t)
: (F.fs string (SelPA.state_block tags_t)) * VarNameGen.t 
:= 
F.fold 
  (fun 
    (name: string)
    (state: CubPA.state_block tags_t)
    (cumulator: (F.fs string (SelPA.state_block tags_t) * VarNameGen.t))
    =>
    let (prev_states, env_prev) := cumulator in
    let (state', env_state) := TranslateParserState state env_prev in
    (prev_states ++ [(name,state')], env_state)
  ) states ([],env).

Definition TranslateTable
(table : CubCT.table tags_t) (env: VarNameGen.t) (i : tags_t)
: (SelCT.table tags_t) * VarNameGen.t :=
match table with
| CubCT.Table key actions =>
  let '(stmt_key, key', env_key) := 
    List.fold_left 
    (fun 
      (cumulator: (SelS.s tags_t) * list (CubE.t * SelE.e tags_t * CubE.matchkind) * VarNameGen.t)
      (key : CubE.t * CubE.e tags_t * CubE.matchkind)
      => let '(prev_stmt, prev_keys, prev_env) := cumulator in
        let '(type, expr, mk) := key in
        let '((expr_stmt, expr'), env_expr) := TranslateExpr expr prev_env in 
        let new_stmt := SelS.SSeq prev_stmt expr_stmt i in
        let new_keys := prev_keys ++ [(type, expr', mk)] in 
        (new_stmt, new_keys, env_expr)   
      )
      key (SelS.SSkip i, [], env)
    in 
    (SelCT.Table key' actions stmt_key, env_key)
end .


Fixpoint TranslateControlDecl 
(cd : CubCT.d tags_t) (env : VarNameGen.t)
: (SelCT.d tags_t) * VarNameGen.t :=
match cd with
| CubCT.CDAction a signature body i =>
  let (body', env_body) := TranslateStatement body env in 
  (SelCT.CDAction a signature body' i , env_body)
| CubCT.CDTable t bdy i =>
  let (bdy', env_bdy) := TranslateTable bdy env i in 
  (SelCT.CDTable t bdy' i, env_bdy)
| CubCT.CDSeq d1 d2 i => 
  let (d1', env_d1) := TranslateControlDecl d1 env in 
  let (d2', env_d2) := TranslateControlDecl d2 env_d1 in 
  (SelCT.CDSeq d1' d2' i, env_d2)
end.



Fixpoint TranslateTopDecl
(td : CubTD.d tags_t) (env : VarNameGen.t)
: (SelTD.d tags_t) * VarNameGen.t :=
match td with 
| CubTD.TPInstantiate C x cargs i => 
  let '(cargs_stmt, cargs', env_cargs) := TranslateCArgs cargs env i in
  (SelTD.TPInstantiate C x cargs' cargs_stmt i, env_cargs)
| CubTD.TPExtern e cparams methods i => 
  (SelTD.TPExtern e cparams methods i, env)
| CubTD.TPControl c cparams params body apply_blk i => 
  let (body', env_body) := TranslateControlDecl body env in
  let (apply_blk', env_apply_blk) := TranslateStatement apply_blk env_body in
  (SelTD.TPControl c cparams params body' apply_blk' i, env_apply_blk)
| CubTD.TPParser p cparams params start states i => 
  let (start', env_start) := TranslateParserState start env in
  let (states', env_states) := TranslateParserStates states env_start in
  (SelTD.TPParser p cparams params start' states' i, env_states)
| CubTD.TPFunction f signature body i =>
  let (body', env_body) := TranslateStatement body env in 
  (SelTD.TPFunction f signature body' i, env_body)
| CubTD.TPPackage p cparams i => 
  (SelTD.TPPackage p cparams i, env)
| CubTD.TPSeq d1 d2 i => 
  let (d1', env_d1) := TranslateTopDecl d1 env in
  let (d2', env_d2) := TranslateTopDecl d2 env_d1 in 
  (SelTD.TPSeq d1' d2' i, env_d2)
end.
Definition TranslateProgram (program: CubTD.d tags_t) : SelTD.d tags_t :=
  fst (TranslateTopDecl program VarNameGen.new_env).

End Translation.