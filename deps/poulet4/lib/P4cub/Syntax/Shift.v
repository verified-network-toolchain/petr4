From Poulet4 Require Import
     Utils.Util.FunUtil
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import AllCubNotations.

Local Open Scope expr_scope.

(** * Philip Wadler style de Bruijn shifts. *)

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

Definition rename_arrowE
           (ρ : nat -> nat)
           '({|paramargs:=args;rtrns:=oe|} : Expr.arrowE)
  : Expr.arrowE :=
  {| paramargs := map
                    (paramarg_map
                       (rename_e ρ)
                       $ rename_e ρ)
                    args
  ;  rtrns     := oe >>| rename_e ρ |}.

Local Open Scope stmt_scope.

Fixpoint rename_s (ρ : nat -> nat) (s : Stmt.s) : (nat -> nat) * Stmt.s :=
  match s with
  | Stmt.Skip
  | Stmt.Exit
  | Stmt.Invoke _ => (ρ, s)
  | Stmt.Var te
    => (ext ρ, Stmt.Var $ map_sum id (rename_e ρ) te)
  | e1 `:= e2 => (ρ, rename_e ρ e1 `:= rename_e ρ e2)
  | Stmt.Return oe
    => (ρ, Stmt.Return $ option_map (rename_e ρ) oe)
  | Stmt.MethodCall x m ts arr
    => (ρ, Stmt.MethodCall x m ts $ rename_arrowE ρ arr)
  | Stmt.FunCall f ts arr
    => (ρ, Stmt.FunCall f ts $ rename_arrowE ρ arr)
  | Stmt.ActCall a cas das
    => (ρ, Stmt.ActCall
            a (map (rename_e ρ) cas)
            (map (paramarg_map
                    (rename_e ρ)
                    (rename_e ρ)) das))
  | Stmt.Apply x eas args
    => (ρ, Stmt.Apply
            x eas
            $ map (paramarg_map
                    (rename_e ρ)
                    (rename_e ρ)) args)
  | s1 `; s2
    => let '(ρ1, s1') := rename_s ρ s1 in
      let '(ρ2, s2') := rename_s ρ1 s2 in (ρ2, s1 `; s2)
  | Stmt.Block s => (ρ, Stmt.Block $ snd $ rename_s ρ s)
  | If e Then s1 Else s2
    => (ρ, If rename_e ρ e
             Then snd $ rename_s ρ s1
             Else snd $ rename_s ρ s2)
  end.
