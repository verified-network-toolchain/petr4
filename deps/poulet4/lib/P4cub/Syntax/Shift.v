From Poulet4 Require Import
     Utils.Util.FunUtil
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import AllCubNotations.

Local Open Scope expr_scope.

(** * Philip Wadler style de Bruijn shifts for expression variables. *)

Definition ext (ρ : nat -> nat) (x : nat) :=
  match x with
  | O   => O
  | S n => S $ ρ x
  end.

Fixpoint rename_e (ρ : nat -> nat) (e : Expr.e) : Expr.e :=
  match e with
  | Expr.Bool _
  | _ `W _
  | _ `S _
  | Expr.Error _     => e
  | Expr.Var t x     => Expr.Var t $ ρ x
  | Expr.Slice e h l => Expr.Slice (rename_e ρ e) h l
  | Expr.Cast t e    => Expr.Cast t $ rename_e ρ e
  | Expr.Uop t op e  => Expr.Uop t op $ rename_e ρ e
  | Expr.Member t x e
    => Expr.Member t x $ rename_e ρ e
  | Expr.Bop t op e1 e2
    => Expr.Bop t op (rename_e ρ e1) (rename_e ρ e2)
  | Expr.Struct es ob
    => Expr.Struct (map (rename_e ρ) es) ob
  end.

Local Close Scope expr_scope.

Definition rename_arg (ρ : nat -> nat)
  : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
  paramarg_map_same $ rename_e ρ.

Definition rename_fun_kind (ρ : nat -> nat) (fk : Stmt.fun_kind)
  : Stmt.fun_kind :=
  match fk with
  | Stmt.Funct f τs oe
    => Stmt.Funct f τs $ option_map (rename_e ρ) oe
  | Stmt.Action a cargs
    => Stmt.Action a $ map (rename_e ρ) cargs
  | Stmt.Method e m τs oe
    => Stmt.Method e m τs $ option_map (rename_e ρ) oe
  end.

Definition rename_transition (ρ : nat -> nat) (e : Parser.e) : Parser.e :=
  match e with
  | Parser.Goto _ => e
  | Parser.Select e d cases
    => Parser.Select (rename_e ρ e) d cases
  end.

Local Open Scope stmt_scope.

Fixpoint rename_s (ρ : nat -> nat) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Invoke _ => s
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
