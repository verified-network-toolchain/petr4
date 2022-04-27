From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxilary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift.
Import ListNotations AllCubNotations.

Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.

(** Idea for lift_e:
lift_e e = (l, e'), where e' is a lifted expression,
& l is a list of generated expressions.

Will want to show that
⟨ ϵ, e ⟩ ⇓ v →
lift_e e = (l, e') →
∃ vs, eval_decl_list ϵ l vs ∧ ⟨ vs ++ ϵ, e' ⟩ ⇓ v

lift up wWn = [wWn], `0
lift up true = [], true
lift up `n = [], `(up + n)
lift up e.x = l, e'.x
     lift up e = l, e'
lift up ~e = ~e' :: l, `0
     lift up e = l, e'
lift up e₁ + e₂ = shift (length l₂) e₁' + e₂' :: l₂ ++ l₁, `0
     lift up e₁ = l₁, e₁'
     lift up e₂ = l₂, e₂'


lift ~`5 + `6.x = [`0 + `6.x;~`5],`0 maybe `6 is messed up, needs to be up shifted?
lift ~`6.x = [], ~`6.x
lift ~`5 = [~`5],`0
lift `5 = [],`5

lift ~`1 + `0.x = [`0 + `0.x;~`1],`0   `0.x is messed up
lift ~`1 = [~`1],`0
want lift ~`1 + `0.x = [`0 + `1.x; ~`1], `0

*)

(** [lift_e up e = (l, e')],
    where e' is a lifted expression,
    & l is a list of lifted expressions. *)
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
  | Expr.Var τ x => ([], Expr.Var τ (up + x))
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
  | Expr.Struct es ob =>
      let '(les, es) := lift_e_list up es in
      (Expr.Struct es None :: les, Expr.Var (t_of_e e) 0)
  end.

(*
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

Local Close Scope stmt_scope.

Definition lift_trans (up : nat) (e : Parser.e)
  : list Expr.e * Parser.e :=
  match e with
  | Parser.Goto _ => ([],e)
  | Parser.Select e d cases
    => let '(le,e) := lift_e up e in
      (le, Parser.Select e d cases)
  end.

Definition unwind_vars (es : list Expr.e) : Stmt.block -> Stmt.block :=
  List.fold_left (fun b e => Stmt.Var (inr e) b) es.

Local Open Scope block_scope.

Fixpoint lift_block (up : nat) (b : Stmt.block) : Stmt.block :=
  match b with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Return None => b
  | Stmt.Return (Some e) => 
      let '(le, e) := lift_e up e in
      unwind_vars le $ Stmt.Return $ Some e
  | Stmt.Transition e =>
      let '(le, e) := lift_trans up e in
      unwind_vars le $ Stmt.Transition $ e
  | Stmt.Var (inl t) b => Stmt.Var (inl t) (lift_block up b)
  | Stmt.Var (inr e) b =>
      let '(le,e) := lift_e up e in
      unwind_vars
        le $ Stmt.Var (inr e)
        $ lift_block (length le + up) b
  | If e {` b₁ `} Else {` b₂ `} `; b =>
      let '(le,e) := lift_e up e in
      unwind_vars
        le $ If e {` lift_block (length le + up) b₁ `}
        Else {` lift_block (length le + up) b₂ `}
        `; lift_block (length le + up) b
  | s `; b =>
      let '(ls, s) := lift_s up s in
      unwind_vars ls (s `; lift_block (length ls + up) b)
  | Stmt.Block b₁ b₂
    => Stmt.Block (lift_block up b₁) $ lift_block up b₂
  end.

Local Close Scope block_scope.
*)
(* TODO: lifting controls & topdecls
   is only a total function
   starting with an up shift of [0].

Definition lift_control_decl (cd : Control.d) : Control.d :=
    match cd with
    | Control.Action a signature body i =>
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
. *)
