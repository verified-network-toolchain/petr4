From Poulet4 Require Import
     Utils.Util.FunUtil
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import AllCubNotations.

(** * Philip Wadler style de Bruijn shifts for expression variables. *)

Section Rename.
  Variable ρ : nat -> nat.

  Definition ext (x : nat) :=
    match x with
    | O   => O
    | S n => S $ ρ x
    end.

  Local Open Scope expr_scope.
  
  Fixpoint rename_e  (e : Expr.e) : Expr.e :=
    match e with
    | Expr.Bool _
    | _ `W _
    | _ `S _
    | Expr.Error _     => e
    | Expr.Var t x     => Expr.Var t $ ρ x
    | Expr.Slice h l e => Expr.Slice h l $ rename_e e
    | Expr.Cast t e    => Expr.Cast t $ rename_e e
    | Expr.Uop t op e  => Expr.Uop t op $ rename_e e
    | Expr.Index t e1 e2
      => Expr.Index t (rename_e e1) $ rename_e e2
    | Expr.Member t x e
      => Expr.Member t x $ rename_e e
    | Expr.Bop t op e1 e2
      => Expr.Bop t op (rename_e e1) $ rename_e e2
    | Expr.Lists l es => Expr.Lists l $ map rename_e es
    end.
  
  Local Close Scope expr_scope.

  Definition rename_arg
    : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
    paramarg_map_same $ rename_e.

  Definition rename_fun_kind (fk : Stmt.fun_kind)
    : Stmt.fun_kind :=
    match fk with
    | Stmt.Funct f τs oe
      => Stmt.Funct f τs $ option_map rename_e oe
    | Stmt.Action a cargs
      => Stmt.Action a $ map rename_e cargs
    | Stmt.Method e m τs oe
      => Stmt.Method e m τs $ option_map rename_e oe
    end.

  Definition rename_transition (e : Parser.e) : Parser.e :=
    match e with
    | Parser.Direct _ => e
    | Parser.Select e d cases
      => Parser.Select (rename_e e) d cases
    end.
End Rename.

Local Open Scope stmt_scope.

Fixpoint rename_s (ρ : nat -> nat) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit => s
  | Stmt.Invoke t es => Stmt.Invoke t $ map (rename_e ρ) es
  | Stmt.Return oe
    => Stmt.Return $ option_map (rename_e ρ) oe
  | Stmt.Transition e
    => Stmt.Transition $ rename_transition ρ e
  | e1 `:= e2 => rename_e ρ e1 `:= rename_e ρ e2
  | Stmt.Call fk args
    => Stmt.Call fk $ map (rename_arg ρ) args
  | Stmt.Apply x eas args
    => Stmt.Apply
        x eas
        $ map (rename_arg ρ) args
  | Stmt.Var te b
    => Stmt.Var
        (map_sum id (rename_e ρ) te)
        $ rename_s (ext ρ) b
  | s₁ `; s₂ => rename_s ρ s₁ `; rename_s ρ s₂
  | If e Then s₁ Else s₂
    => If rename_e ρ e Then rename_s ρ s₁ Else rename_s ρ s₂
  end.

Local Close Scope stmt_scope.

Section TermSub.
  Variable σ : nat -> Expr.t -> Expr.e.

  Local Open Scope expr_scope.
  
  Definition exts (x : nat) (t : Expr.t) : Expr.e :=
    match x with
    | O => Expr.Var t O
    | S n => rename_e S $ σ n t
    end.

  Fixpoint esub_e (e : Expr.e) : Expr.e :=
    match e with
    | Expr.Bool _
    | _ `W _
    | _ `S _
    | Expr.Error _ => e
    | Expr.Var t x => σ x t
    | Expr.Slice hi lo e => Expr.Slice hi lo $ esub_e e
    | Expr.Cast t e => Expr.Cast t $ esub_e e
    | Expr.Uop t op e => Expr.Uop t op $ esub_e e
    | Expr.Bop t op e₁ e₂ => Expr.Bop t op (esub_e e₁) $ esub_e e₂
    | Expr.Lists ls es => Expr.Lists ls $ map esub_e es
    | Expr.Index t e₁ e₂ => Expr.Index t (esub_e e₁) $ esub_e e₂
    | Expr.Member t x e => Expr.Member t x $ esub_e e
    end.
  
  Local Close Scope expr_scope.

  Definition esub_arg
    : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
    paramarg_map_same $ esub_e.

  Definition esub_transition (pe : Parser.e) : Parser.e :=
    match pe with
    | Parser.Direct s => Parser.Direct s
    | Parser.Select discriminee default cases =>
        Parser.Select (esub_e discriminee) default cases
    end.

  Definition esub_fun_kind (fk : Stmt.fun_kind) : Stmt.fun_kind :=
    match fk with
    | Stmt.Funct f τs oe
      => Stmt.Funct f τs $ option_map esub_e oe
    | Stmt.Action a cargs
      => Stmt.Action a $ map esub_e cargs
    | Stmt.Method e m τs oe
      => Stmt.Method e m τs $ option_map esub_e oe
    end.
End TermSub.

Local Open Scope stmt.

Fixpoint esub_s (σ : nat -> Expr.t -> Expr.e) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Return None
  | Stmt.Exit => s
  | Stmt.Return (Some e) => Stmt.Return $ Some $ esub_e σ e
  | Stmt.Transition e => Stmt.Transition $ esub_transition σ e
  | e₁ `:= e₂ => esub_e σ e₁ `:= esub_e σ e₂
  | Stmt.Call fk args => Stmt.Call (esub_fun_kind σ fk) $ List.map (esub_arg σ) args
  | Stmt.Invoke tbl es => Stmt.Invoke tbl $ List.map (esub_e σ) es
  | Stmt.Apply inst eargs args => Stmt.Apply inst eargs $ map (esub_arg σ) args
  | Stmt.Var te s => Stmt.Var (map_sum id (esub_e σ) te) $ esub_s (exts σ) s
  | s₁ `; s₂ => esub_s σ s₁ `; esub_s σ s₂
  | If e Then s₁ Else s₂ => If esub_e σ e Then esub_s σ s₁ Else esub_s σ s₂
  end.

Local Close Scope stmt.
