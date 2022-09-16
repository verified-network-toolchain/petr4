Require Import Coq.Strings.String.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift.
Import ListNotations AllCubNotations.

Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.

Section Lift.
  Context {A B : Set}.
  Variable Lift : nat -> nat -> A -> list B * A.
  Variable Rename : (nat -> nat) -> A -> A.
  Variable new : nat.

  Fixpoint lift_list
    (up : nat) (l : list A) : list B * list A :=
    match l with
    | []    => ([],[])
    | a :: l =>
        let '(bs, a') := Lift new up a in
        let '(bss, l') := lift_list (length bs + up) l in
        (bss ++ bs, Rename (plus $ length bss) a' :: l')
    end.
End Lift.

(** [lift_e new up e = (l, e')],
    where e' is a lifted expression,
    & l is a list of lifted expressions. *)
Fixpoint lift_e (new up : nat) (e : Expr.e) {struct e}
  : list Expr.e * Expr.e :=
  match e with
  | Expr.Bool _
  | Expr.Error _ => ([], e)
  | Expr.Var τ og x => ([], Expr.Var τ og (up + x))
  | Expr.Member t x e
    => let '(inits, e) := lift_e new up e in
      (inits, Expr.Member t x e)
  | Expr.Bit _ _
  | Expr.Int _ _ => ([e], Expr.Var (t_of_e e) "" (up + new))
  | Expr.Slice hi lo eₛ =>
      let '(inits, eₛ) := lift_e new up eₛ in
      (Expr.Slice hi lo eₛ :: inits, Expr.Var (t_of_e e) "" (up + new))
  | Expr.Cast t e =>
      let '(inits, e) := lift_e new up e in
      (Expr.Cast t e :: inits, Expr.Var t "" (up + new))
  | Expr.Uop t op e =>
      let '(inits, e) := lift_e new up e in
      (Expr.Uop t op e :: inits, Expr.Var t "" (up + new))
  | Expr.Bop t op lhs rhs => 
      let '(ll, lhs) := lift_e new up lhs in
      let '(lr, rhs) := lift_e new (length ll + up) rhs in
      (Expr.Bop
         t op (rename_e (plus $ length lr) lhs) rhs
         :: lr ++ ll, Expr.Var t "" (up + new))
  | Expr.Index t e1 e2 =>
      let '(l1, e1) := lift_e new up e1 in
      let '(l2, e2) := lift_e new (length l1 + up) e2 in
      (l2 ++ l1, Expr.Index t (rename_e (plus $ length l2) e1) e2)
  | Expr.Lists l es =>
      let '(les, es) := lift_list lift_e rename_e new up es in
      (Expr.Lists l es :: les, Expr.Var (t_of_e e) "" (up + new))
  end.

Definition lift_e_list
  : nat -> nat -> list Expr.e -> list Expr.e * list Expr.e :=
  lift_list lift_e rename_e.

Definition lift_arg (new up : nat) (arg : paramarg Expr.e Expr.e)
  : list Expr.e * paramarg Expr.e Expr.e :=
  match arg with
  | PAIn e =>
      let '(le, e) := lift_e new up e in (le, PAIn e)
  | PAOut e =>
      let '(le, e) := lift_e new up e in (le, PAOut e)
  | PAInOut e =>
      let '(le, e) := lift_e new up e in (le, PAInOut e)
  end.

Definition lift_args
  : nat -> nat -> Expr.args -> list Expr.e * Expr.args :=
  lift_list lift_arg rename_arg.

(** [unwind_vars [e₁;...;eₙ] s = Stmt.Var eₙ (...(Stmt.Var e₁ s )...)]. *)
Definition unwind_vars (es : list Expr.e) : Stmt.s -> Stmt.s :=
  List.fold_left (fun b e => Stmt.Var "" (inr e) b) es.

Definition lift_trans (new up : nat) (e : Parser.trns)
  : list Expr.e * Parser.trns :=
  match e with
  | Parser.Direct _ => ([],e)
  | Parser.Select e d cases
    => let '(le,e) := lift_e new up e in
      (le, Parser.Select e d cases)
  end.

Definition lift_fun_kind (new up : nat) (fk : Stmt.fun_kind)
  : list Expr.e * Stmt.fun_kind :=
  match fk with
  | Stmt.Funct _ _ None
  | Stmt.Method _ _ _ None => ([],fk)
  | Stmt.Funct f τs (Some e)
    => let '(le,e) := lift_e new up e in (le, Stmt.Funct f τs (Some e))
  | Stmt.Method x m τs (Some e)
    => let '(le,e) := lift_e new up e in (le, Stmt.Method x m τs (Some e))
  | Stmt.Action a es
    => let '(les,es) := lift_e_list new up es in (les, Stmt.Action a es)
  end.

Local Open Scope stmt_scope.

Fixpoint lift_s (new up : nat) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Invoke _
  | Stmt.Exit
  | Stmt.Return None => s
  | Stmt.Return (Some e)
    => let '(le, e) := lift_e new up e in
      unwind_vars le $ Stmt.Return $ Some e
  | Stmt.Transition e =>
      let '(le, e) := lift_trans new up e in
      unwind_vars le $ Stmt.Transition $ e
  | e₁ `:= e₂
    => let '(le₁, e₁) := lift_e new up e₁ in
      let '(le₂, e₂) := lift_e new (length le₁ + up) e₂ in
      unwind_vars (le₂ ++ le₁) $ rename_e (plus $ length le₂) e₁ `:= e₂
  | Stmt.Call fk args
    => let '(lfk,fk) := lift_fun_kind new up fk in
      let '(largs,args) := lift_args new (length lfk + up) args in
      unwind_vars
        (largs ++ lfk) $
        Stmt.Call (rename_fun_kind (plus $ length args) fk) args
  | Stmt.Apply x exts args
    => let '(inits, args) := lift_args new up args in
      unwind_vars inits $ Stmt.Apply x exts args
  | Stmt.Var og (inl t) s => Stmt.Var og (inl t) (lift_s (S new) up s)
  | Stmt.Var og (inr e) s =>
      let '(le,e) := lift_e new up e in
      unwind_vars
        le $ Stmt.Var og (inr e)
        $ lift_s (S new) (length le + up) s
  | s₁ `; s₂ => lift_s new up s₁ `; lift_s new up s₂
  | If e Then s₁ Else s₂ =>
      let '(le,e) := lift_e new up e in
      unwind_vars
        le $ If e Then lift_s new (length le + up) s₁
        Else lift_s new (length le + up) s₂
  end.

Local Close Scope stmt_scope.

Definition lift_control_decl (new up : nat) (cd : Control.d) : nat * list Control.d :=
  match cd with
  | Control.Var x (inl t) => (0,[Control.Var x $ inl t])
  | Control.Var x (inr e) =>
      let '(es, e) := lift_e new up e in
      (List.length es,
        List.map (Control.Var "" ∘ inr) es ++ [Control.Var x $ inr e])
  | Control.Action a cps dps body
    => (0,[Control.Action a cps dps $ lift_s new up body])
  | Control.Table t key acts =>
      let '(es,mks) := List.split key in
      let '(acts,argss) := List.split acts in
      let '(ees,es) := lift_e_list new up es in
      let '(argsss,argss) :=
        lift_list
          lift_args
          (fun ρ => List.map (rename_arg ρ))
          new (List.length ees + up) argss in
      (List.length ees + List.length argsss,
        List.map (Control.Var "" ∘ inr) argsss
          ++ List.map (Control.Var "" ∘ inr)
          (List.map (rename_e (plus $ length argsss)) es)
          ++ [Control.Table
                t (List.combine es mks) (List.combine acts argss)])
      
  end.

Fixpoint lift_control_decls (new up : nat) (cds : list Control.d) : nat * list Control.d :=
  match cds with
  | [] => (0, [])
  | d :: ds =>
      let '(n, d) := lift_control_decl new up d in
      let '(ns, ds) := lift_control_decls new (n + up) ds in
      (n + ns, d ++ ds)
  end.

Definition lift_top_decl (td : TopDecl.d) : TopDecl.d := 
  match td with 
  | TopDecl.Instantiate _ _ _ _ _
  | TopDecl.Extern _ _ _ _ _ => td
  | TopDecl.Control c cparams expr_cparams eps params body apply_blk =>
      let (up, ds) := lift_control_decls 0 0 body in
      TopDecl.Control
        c cparams expr_cparams eps params ds
        $ lift_s 0 up apply_blk  
  | TopDecl.Parser p cparams expr_cparams eps params start states =>
      TopDecl.Parser
        p cparams expr_cparams eps params
        (lift_s 0 0 start) $ map (lift_s 0 0) states
  | TopDecl.Funct f tparams signature body =>
      TopDecl.Funct f tparams signature $ lift_s 0 0 body
  end.

Definition lift_program : list TopDecl.d -> list TopDecl.d :=
  map lift_top_decl.
