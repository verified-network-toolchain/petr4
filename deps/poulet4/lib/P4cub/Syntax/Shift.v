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
  | Expr.Struct es oe
    => Expr.Struct
        (map (rename_e ρ) es)
        (option_map (rename_e ρ) oe)
  end.

Local Close Scope expr_scope.

Definition rename_arg (ρ : nat -> nat)
  : paramarg Expr.e Expr.e -> paramarg Expr.e Expr.e :=
  paramarg_map_same $ rename_e ρ.

Definition rename_arrowE
           (ρ : nat -> nat)
           '({|paramargs:=args;rtrns:=oe|} : Expr.arrowE)
  : Expr.arrowE :=
  {| paramargs := map (rename_arg ρ) args
  ;  rtrns     := oe >>| rename_e ρ |}.

Local Open Scope stmt_scope.

Definition rename_s (ρ : nat -> nat) (s : Stmt.s) : Stmt.s :=
  match s with
  | Stmt.Invoke _ => s
  | e1 `:= e2 => rename_e ρ e1 `:= rename_e ρ e2
  | Stmt.MethodCall x m ts arr
    => Stmt.MethodCall x m ts $ rename_arrowE ρ arr
  | Stmt.FunCall f ts arr
    => Stmt.FunCall f ts $ rename_arrowE ρ arr
  | Stmt.ActCall a cas das
    => Stmt.ActCall
        a (map (rename_e ρ) cas)
        (map (rename_arg ρ) das)
  | Stmt.Apply x eas args
    => Stmt.Apply
        x eas
        $ map (rename_arg ρ) args
  end.

Local Close Scope stmt_scope.
Local Open Scope block_scope.

Fixpoint rename_block (ρ : nat -> nat) (b : Stmt.block) : Stmt.block :=
  match b with
  | Stmt.Skip
  | Stmt.Exit => b
  | Stmt.Var te b
    => Stmt.Var
        (map_sum id (rename_e ρ) te)
        $ rename_block (ext ρ) b
  | Stmt.Return oe
    => Stmt.Return $ option_map (rename_e ρ) oe
  | h `; t => rename_s ρ h `; rename_block ρ t
  | Stmt.Block b1 b2
    => Stmt.Block (rename_block ρ b1) $ rename_block ρ b2
  | If e {` s1 `} Else {` s2 `} `; b
    => If rename_e ρ e {` rename_block ρ s1 `}
         Else {` rename_block ρ s2 `} `; rename_block ρ b
  end.

Local Close Scope block_scope.
