Require Import Poulet4.P4cub.Syntax.Syntax.
Require Import Poulet4.P4sel.P4sel.
Require Import Poulet4.Monads.Option.
Require Poulet4.P4sel.VarNameGen.
Module Cub := P4cub.
Module F := Cub.F.
Module CubE := Cub.Expr.
Module CubS := Cub.Stmt.
Module CubPA := Cub.Parser.
Module CubCT := Cub.Control.
Module CubTD := Cub.TopDecl.
Module Sel := P4sel.
Module SelE := Sel.Expr.
Module SelS := Sel.Stmt.
Module SelPA := Sel.Parser.
Module SelCT := Sel.Control.
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
  | CubE.EHeaderStack fields headers size next_index i => ((SelS.SSkip i, SelE.EError None i), env)
  | CubE.EHeaderStackAccess stack index i => ((SelS.SSkip i, SelE.EError None i), env)
  end.
Definition TranslateProgram (program: CubTD.d tags_t) : SelTD.d tags_t.
 Admitted.

End Translation.