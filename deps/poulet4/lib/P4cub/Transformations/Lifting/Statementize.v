From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxilary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift.
Import ListNotations AllCubNotations.

Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.

(* TODO:
   To "statementize"/lift the new
   p4cub de Bruijn syntax, it will
   look something like:
   [lift_e : nat -> Expr.e -> list Expr.e * Expr.e].
   [lift_e n e]
   will shift all variables in [e] up by [n],
   and return a list of expressions
   that will be used to make
   a sequence of variable declarations.

   All lifted expressions like bitstrings
   will be replaced with a variable
   of index 0, which may need to
   be shifted up later.

   In the case of binary operations such as addition,
   it will look something like:
   [[[
   TransformExpr n (e1 + e2) =
   let (l1,e1') := TransformExpr n e1 in
   let (l2,e2') := TransformExpr (length l1 + n) e2 in
   (l1 ++ l2, shift (length l2) e1 + e2)
   ]]]
   Variables occursing in [e2] also
   need to be shifted up additionally
   by the number of new variables
   generated for [e1].
   Furthermore, [e1']'s variables
   will need to be shifted up
   by the number of variables
   generated for [e2]. *)

Fixpoint lift_e (up : nat) (e : Expr.e) {struct e}
  : list Expr.e * Expr.e :=
  let fix lift_e_list (up : nat) (es : list Expr.e)
    : list Expr.e * list Expr.e :=
    match es with
    | [] => ([],[])
    | e :: es
      => let '(le,e') := lift_e up e in
        let '(les,es') := lift_e_list (length le + up) es in
        (le ++ les, rename_e (plus $ length les) e :: es')
    end in
  match e with
  | Expr.Bool _
  | Expr.Error _ => ([], e)
  | Expr.Var t x => ([], Expr.Var t (up + x))
  | Expr.Member t x e
    => let '(inits, e) := lift_e up e in
      (inits, Expr.Member t x e)
  | Expr.Bit _ _
  | Expr.Int _ _ => ([e], Expr.Var (t_of_e e) 0)
  | Expr.Slice eₛ hi lo =>
      let '(inits, eₛ) := lift_e up eₛ in
      (Expr.Slice eₛ hi lo :: inits, Expr.Var (t_of_e e) 0)
  | Expr.Cast t e =>
      let '(inits, e) := lift_e up e in
      (Expr.Cast t e :: inits, Expr.Var t 0)
  | Expr.Uop t op e =>
      let '(inits, e) := lift_e up e in
      (Expr.Uop t op e :: inits, Expr.Var t 0)
  | Expr.Bop t op lhs rhs => 
      let '(ll, lhs) := lift_e up lhs in
      let '(lr, rhs) := lift_e (length ll + up) rhs in
      (Expr.Bop
         t op (rename_e (plus $ length lr) lhs) rhs
         :: lr ++ ll, Expr.Var t 0)
  | Expr.Struct es oe =>
      let '(les, es) := lift_e_list up es in
      match oe with
      | None
        => (Expr.Struct es None :: les, Expr.Var (t_of_e e) 0)
      | Some eₕ
        => let '(leₕ, eₕ) := lift_e (length les + up) eₕ in
          (Expr.Struct
             (map
                (rename_e $ plus $ length leₕ)
                es) $ Some eₕ
             :: leₕ ++ les, Expr.Var (t_of_e e) 0 )
      end
  end.

Fixpoint lift_e_list (up : nat) (es : list Expr.e)
  : list Expr.e * list Expr.e :=
    match es with
    | [] => ([],[])
    | e :: es
      => let '(le,e') := lift_e up e in
        let '(les,es') := lift_e_list (length le + up) es in
        (le ++ les, rename_e (plus $ length les) e :: es')
    end.

Definition lift_arg (up : nat) (arg : paramarg Expr.e Expr.e)
  : list Expr.e * paramarg Expr.e Expr.e :=
  match arg with
  | PAIn e =>
      let '(le, e) := lift_e up e in (le, PAIn e)
  | PAOut e =>
      let '(le, e) := lift_e up e in (le, PAOut e)
  | PAInOut e =>
      let '(le, e) := lift_e up e in (le, PAInOut e)
  end.

Fixpoint lift_args (up : nat) (es : Expr.args)
  : list Expr.e * Expr.args :=
    match es with
    | [] => ([],[])
    | e :: es
      => let '(le,e') := lift_arg up e in
        let '(les,es') := lift_args (length le + up) es in
        (le ++ les, rename_arg (plus $ length les) e :: es')
    end.

Definition lift_arrowE (up : nat)
           '({|paramargs:=args; rtrns:=oe|} : Expr.arrowE)
  : list Expr.e * Expr.arrowE :=
  let '(inits, args) := lift_args up args in
  match oe with
  | None => (inits, {|paramargs:=args;rtrns:=None|})
  | Some e
    => let '(le,e) := lift_e (length inits + up) e in
      (le ++ inits, {|paramargs:=args;rtrns:=Some e|})
  end.

Local Open Scope stmt_scope.

Definition lift_s (up : nat) (s : Stmt.s) : list Expr.e * Stmt.s :=
  match s with
  | Stmt.Invoke _ => ([],s)
  | e₁ `:= e₂
    => let '(le₁, e₁) := lift_e up e₁ in
      let '(le₂, e₂) := lift_e (length le₁ + up) e₂ in
      (le₂ ++ le₁, rename_e (plus $ length le₂) e₁ `:= e₂)
  | Stmt.FunCall f ts args
    => let '(inits, args) := lift_arrowE up args in
      (inits, Stmt.FunCall f ts args)
  | Stmt.ActCall f cargs dargs
    => let '(cs,cargs) := lift_e_list up cargs in
      let '(ds,dargs) := lift_args (length cs + up) dargs in
      (ds ++ cs, Stmt.ActCall f cargs dargs)
  | Stmt.MethodCall e f ts args
    => let '(inits, args) := lift_arrowE up args in
      (inits, Stmt.MethodCall e f ts args)  
  | Stmt.Apply x exts args => 
      let '(inits, args) := lift_args up args in
      (inits, Stmt.Apply x exts args)
  end.

Definition unwind_vars (es : list Expr.e) (b : Stmt.block) : Stmt.block :=
  List.fold_right (fun e => Stmt.Var $ inr e) b (List.rev es).

Fixpoint lift_block (up : nat) (b : Stmt.block) : Stmt.block :=
  match b with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Invoke _
  | Stmt.Return None => b
  | Stmt.Return (Some e) => 
      let '(le, e) := lift_e up e in
      unwind_vars le $ Stmt.Return e
    | Stmt.Vardecl _ (inl _) _ => (stmt, env)
    | Stmt.Vardecl x (inr e) i =>
      let '(s,e',env') := lift_e e env in
      (Stmt.Seq s (Stmt.Vardecl x (inr e') i) i, env')

      (new_stmt, env_rhs)
    | Stmt.Conditional guard tru_blk fls_blk i =>
      let '(guard_stmt, guard', env_guard) := lift_e guard env in
      let (tru_blk', env_tru) := TranslateStatement tru_blk env_guard in 
      let (fls_blk', env_fls) := TranslateStatement fls_blk env_tru in 
      let new_stmt :=
          Stmt.Seq
            guard_stmt
            (Stmt.Conditional guard' tru_blk' fls_blk' i) i in
      (new_stmt, env) 
    | Stmt.Seq s1 s2 i => 
      let (s1', env_s1) := TranslateStatement s1 env in 
      let (s2', env_s2) := TranslateStatement s2 env_s1 in 
      (Stmt.Seq s1' s2' i, env_s2)
    | Stmt.Block block => 
      let (block', env_block) := TranslateStatement block env in
      (Stmt.Block block' , env_block)

    | Stmt.SetValidity hdr val i  => 
      let '(hdr_stmt, hdr', env_hdr) := lift_e hdr env in 
      (Stmt.Seq hdr_stmt (Stmt.SetValidity hdr' val i) i, env_hdr)
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
         let new_stmt := Stmt.Seq prev_stmt stmt_e i in 
         let new_cases := prev_cases ++ [(pattern, e')] in
         (new_stmt, new_cases, env_e) 
      ) cases ((Stmt.Skip i, []), env).
  
  Fixpoint TranslateParserExpr (expr: Parser.e tags_t) (env : VarNameGen.t)
    : st * Parser.e tags_t * VarNameGen.t :=
    let TranslateCases := TranslateCases' TranslateParserExpr in 
    match expr with 
    | Parser.PGoto st i => 
      ((Stmt.Skip i, Parser.PGoto st i), env)
    | Parser.PSelect exp default cases i => 
      let '(stmt_exp, exp', env_exp) := lift_e exp env in
      let '(stmt_default, default', env_default) := TranslateParserExpr default env_exp  in
      let '(stmt_cases, cases', env_cases) := TranslateCases cases env_default i in
      let new_stmt := Stmt.Seq stmt_exp (Stmt.Seq stmt_default stmt_cases i ) i in
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
    let new_stmt := Stmt.Seq stmt' stmt_transition i in 
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
             let '(s, e', env') := lift_e e env in 
             (Stmt.Seq s s' i, (e',mk) :: ky', env'))
          (Stmt.Skip i, [], env) key in 
    (stmt_key, {|Control.table_key:=key'; Control.table_actions:=actions|}, env_key).
  
  Fixpoint TranslateControlDecl 
           (cd : Control.d tags_t) (env : VarNameGen.t)
    : st * Control.d tags_t * VarNameGen.t :=
    match cd with
    | Control.CDAction a signature body i =>
      let (body', env_body) := TranslateStatement body env in 
      (Stmt.Skip i, Control.CDAction a signature body' i , env_body)
    | Control.CDTable t bdy i =>
      let '(table_init, bdy', env_bdy) := TranslateTable bdy env i in 
      (table_init, Control.CDTable t bdy' i, env_bdy)
    | Control.CDSeq d1 d2 i => 
      let '(st1, d1', env_d1) := TranslateControlDecl d1 env in 
      let '(st2, d2', env_d2) := TranslateControlDecl d2 env_d1 in 
      (Stmt.Seq st1 st2 i, Control.CDSeq d1' d2' i, env_d2)
    end.
  

Fixpoint TranslateTopDecl
         (td : TopDecl.d tags_t) (env : VarNameGen.t)
  : TopDecl.d tags_t * VarNameGen.t := 
  match td with 
  | TopDecl.TPInstantiate C x targs cargs i =>
    (TopDecl.TPInstantiate C x targs cargs i, env)

  | TopDecl.TPExtern e tparams cparams methods i => 
    (TopDecl.TPExtern e tparams cparams methods i, env)
              
  | TopDecl.TPControl c cparams eps params body apply_blk i =>
    let '(init_blk, body', env_body) := TranslateControlDecl body env in
    let (apply_blk', env_apply_blk) := TranslateStatement apply_blk env_body in
    (TopDecl.TPControl c cparams eps params body' (Stmt.Seq init_blk apply_blk' i) i, env_apply_blk)
              
  | TopDecl.TPParser p cparams eps params start states i =>
    let (start', env_start) := TranslateParserState start env in
    let (states', env_states) := TranslateParserStates states env_start in
    (TopDecl.TPParser p cparams eps params start' states' i, env_states)
              
  | TopDecl.TPFunction f tparams signature body i =>
    let (body', env_body) := TranslateStatement body env in 
    (TopDecl.TPFunction f tparams signature body' i, env_body)
              
  | TopDecl.TPSeq d1 d2 i => 
    let (d1', env_d1) := TranslateTopDecl d1 env in
    let (d2', env_d2) := TranslateTopDecl d2 env_d1 in 
    (TopDecl.TPSeq d1' d2' i, env_d2)
  end.

Definition TranslateProgram (program: TopDecl.d tags_t) : TopDecl.d tags_t :=
  fst (TranslateTopDecl program VarNameGen.new_env)
.

End Statementize.
