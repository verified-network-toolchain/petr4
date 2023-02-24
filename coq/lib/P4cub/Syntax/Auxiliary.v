Require Import Coq.PArith.BinPos
        Poulet4.Monads.Monad Poulet4.Monads.Option
        Coq.NArith.BinNat.
From Poulet4 Require Import Utils.P4Arith
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import Expr ExprNotations.

Definition stmt_of_list : list Stmt.s -> Stmt.s :=
  List.fold_right Stmt.Seq Stmt.Skip.

Fixpoint width_of_typ (τ : t) : option nat :=
  match τ with
  | TBool  => Some 1%nat
  | TBit w => Some $ N.to_nat w
  | TInt w => Some $ Pos.to_nat w
  | TVarBit w => Some $ N.to_nat w
  | TError => Some 0%nat
  | TVar _ => None
  | TArray n t =>
      width_of_typ
        t >>| mult $ N.to_nat n
  | TStruct b fs =>
      sequence
        $ List.map width_of_typ fs
        >>| List.fold_right Nat.add 0%nat
        >>| plus (if b then 1%nat else 0%nat)
  end.

(** Syntactic type of an expression. *)
Fixpoint t_of_e (exp: e) : t := 
  match exp with
  | Bool _  => TBool
  | Error _ => TError
  | Var τ _ _
  | Cast τ _
  | Uop τ _ _
  | Bop τ _ _ _
  | Index τ _ _
  | Member τ _ _  => τ
  | (w `W _)%expr => TBit w
  | (w `S _)%expr => TInt w
  | VarBit m w _    => TVarBit m
  | Slice hi lo _ => TBit (Npos hi - Npos lo + 1)%N
  | Lists (lists_array τ) es  => TArray (N.of_nat $ List.length es) τ
  | Lists lists_struct es     => TStruct false (List.map t_of_e es)
  | Lists (lists_header _) es => TStruct true (List.map t_of_e es)
  end.

Definition t_of_lists (ls : Expr.lists) (es : list Expr.e) : Expr.t :=
  match ls with
  | lists_array t  => TArray (N.of_nat $ List.length es) t
  | lists_struct   => TStruct false (List.map t_of_e es)
  | lists_header _ => TStruct true (List.map t_of_e es)
  end.
