Require Import Coq.Strings.String.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift.
Import ListNotations AllCubNotations.

Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.

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
        (les ++ le, rename_e (plus $ length les) e' :: es')
    end in
  match e with
  | Expr.Bool _
  | Expr.Error _ => ([], e)
  | Expr.Var τ og x => ([], Expr.Var τ og (up + x))
  | Expr.Member t x e
    => let '(inits, e) := lift_e up e in
      (inits, Expr.Member t x e)
  | Expr.Bit _ _
  | Expr.Int _ _ => ([e], Expr.Var (t_of_e e) "" 0)
  | Expr.Slice hi lo eₛ =>
      let '(inits, eₛ) := lift_e up eₛ in
      (Expr.Slice hi lo eₛ :: inits, Expr.Var (t_of_e e) "" 0)
  | Expr.Cast t e =>
      let '(inits, e) := lift_e up e in
      (Expr.Cast t e :: inits, Expr.Var t "" 0)
  | Expr.Uop t op e =>
      let '(inits, e) := lift_e up e in
      (Expr.Uop t op e :: inits, Expr.Var t "" 0)
  | Expr.Bop t op lhs rhs => 
      let '(ll, lhs) := lift_e up lhs in
      let '(lr, rhs) := lift_e (length ll + up) rhs in
      (Expr.Bop
         t op (rename_e (plus $ length lr) lhs) rhs
         :: lr ++ ll, Expr.Var t "" 0)
  | Expr.Index t e1 e2 =>
      let '(l1, e1) := lift_e up e1 in
      let '(l2, e2) := lift_e (length l1 + up) e2 in
      (l2 ++ l1, Expr.Index t (rename_e (plus $ length l2) e1) e2)
  | Expr.Lists l es =>
      let '(les, es) := lift_e_list up es in
      (Expr.Lists l es :: les, Expr.Var (t_of_e e) "" 0)
  end.

Fixpoint lift_e_list (up : nat) (es : list Expr.e)
  : list Expr.e * list Expr.e :=
  match es with
  | [] => ([],[])
  | e :: es
    => let '(le,e') := lift_e up e in
      let '(les,es') := lift_e_list (length le + up) es in
      (les ++ le, rename_e (plus $ length les) e' :: es')
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
      (les ++ le, rename_arg (plus $ length les) e' :: es')
  end.

(** [unwind_vars [e₁;...;eₙ] s = Stmt.Var eₙ (...(Stmt.Var e₁ s )...)]. *)
Definition unwind_vars (es : list Expr.e) : Stmt.s -> Stmt.s :=
  List.fold_left (fun b e => Stmt.Var "" (inr e) b) es.

Definition lift_trans (up : nat) (e : Parser.trns)
  : list Expr.e * Parser.trns :=
  match e with
  | Parser.Direct _ => ([],e)
  | Parser.Select e d cases
    => let '(le,e) := lift_e up e in
      (le, Parser.Select e d cases)
  end.

Definition lift_fun_kind (up : nat) (fk : Stmt.fun_kind)
  : list Expr.e * Stmt.fun_kind :=
  match fk with
  | Stmt.Funct _ _ None
  | Stmt.Method _ _ _ None => ([],fk)
  | Stmt.Funct f τs (Some e)
    => let '(le,e) := lift_e up e in (le, Stmt.Funct f τs (Some e))
  | Stmt.Method x m τs (Some e)
    => let '(le,e) := lift_e up e in (le, Stmt.Method x m τs (Some e))
  | Stmt.Action a es
    => let '(les,es) := lift_e_list up es in (les, Stmt.Action a es)
  end.

Local Open Scope stmt_scope.

Fixpoint lift_s (up : nat) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Return None => s
  | Stmt.Invoke t es =>
      let '(le, es) := lift_e_list up es in
      unwind_vars le $ Stmt.Invoke t es
  | Stmt.Return (Some e)
    => let '(le, e) := lift_e up e in
      unwind_vars le $ Stmt.Return $ Some e
  | Stmt.Transition e =>
      let '(le, e) := lift_trans up e in
      unwind_vars le $ Stmt.Transition $ e
  | e₁ `:= e₂
    => let '(le₁, e₁) := lift_e up e₁ in
      let '(le₂, e₂) := lift_e (length le₁ + up) e₂ in
      unwind_vars (le₂ ++ le₁) $ rename_e (plus $ length le₂) e₁ `:= e₂
  | Stmt.Call fk args
    => let '(lfk,fk) := lift_fun_kind up fk in
      let '(largs,args) := lift_args (length lfk + up) args in
      unwind_vars
        (largs ++ lfk) $
        Stmt.Call (rename_fun_kind (plus $ length args) fk) args
  | Stmt.Apply x exts args
    => let '(inits, args) := lift_args up args in
      unwind_vars inits $ Stmt.Apply x exts args
  | Stmt.Var og (inl t) s => Stmt.Var og (inl t) (lift_s up s)
  | Stmt.Var og (inr e) s =>
      let '(le,e) := lift_e up e in
      unwind_vars
        le $ Stmt.Var og (inr e)
        $ lift_s (length le + up) s
  | s₁ `; s₂ => lift_s up s₁ `; lift_s up s₂
  | If e Then s₁ Else s₂ =>
      let '(le,e) := lift_e up e in
      unwind_vars
        le $ If e Then lift_s (length le + up) s₁
        Else lift_s (length le + up) s₂
  end.

Local Close Scope stmt_scope.

Definition lift_control_decl (cd : Control.d) : Control.d :=
    match cd with
    | Control.Action a cps dps body
      => Control.Action a cps dps $ lift_s 0 body
    | Control.Table _ _ _ => cd
    end.

Definition lift_top_decl (td : TopDecl.d) : TopDecl.d := 
  match td with 
  | TopDecl.Instantiate _ _ _ _ _
  | TopDecl.Extern _ _ _ _ _ => td
  | TopDecl.Control c cparams expr_cparams eps params body apply_blk =>
      TopDecl.Control
        c cparams expr_cparams eps params
        (map lift_control_decl body)
        $ lift_s 0 apply_blk  
  | TopDecl.Parser p cparams expr_cparams eps params start states =>
      TopDecl.Parser
        p cparams expr_cparams eps params
        (lift_s 0 start) $ map (lift_s 0) states
  | TopDecl.Funct f tparams signature body =>
      TopDecl.Funct f tparams signature $ lift_s 0 body
  end.

Definition lift_program : list TopDecl.d -> list TopDecl.d :=
  map lift_top_decl.
