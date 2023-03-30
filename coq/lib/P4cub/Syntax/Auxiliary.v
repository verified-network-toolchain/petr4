Require Import Coq.PArith.BinPos
        Poulet4.Monads.Monad Poulet4.Monads.Option
        Coq.NArith.BinNat.
From Poulet4 Require Import Utils.P4Arith
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.

Definition stmt_of_list : list Stm.t -> Stm.t :=
  List.fold_right Stm.Seq Stm.Skip.

Fixpoint width_of_typ (τ : Typ.t) : option nat :=
  match τ with
  | Typ.Bool  => Some 1%nat
  | Typ.Bit w => Some $ N.to_nat w
  | Typ.Int w => Some $ Pos.to_nat w
  | Typ.VarBit w => Some $ N.to_nat w
  | Typ.Error => Some 0%nat
  | Typ.Var _ => None
  | Typ.Array n t =>
      width_of_typ
        t >>| mult $ N.to_nat n
  | Typ.Struct b fs =>
      sequence
        $ List.map width_of_typ fs
        >>| List.fold_right Nat.add 0%nat
        >>| plus (if b then 1%nat else 0%nat)
  end.

(** Syntactic type of an expression. *)
Fixpoint typ_of_exp (exp: Exp.t) : Typ.t := 
  match exp with
  | Exp.Bool _  => Typ.Bool
  | Exp.Error _ => Typ.Error
  | Exp.Var τ _ _
  | Exp.Cast τ _
  | Exp.Uop τ _ _
  | Exp.Bop τ _ _ _
  | Exp.Index τ _ _
  | Exp.Member τ _ _  => τ
  | (w `W _)%exp => Typ.Bit w
  | (w `S _)%exp => Typ.Int w
  | Exp.VarBit m w _    => Typ.VarBit m
  | Exp.Slice hi lo _ => Typ.Bit (Npos hi - Npos lo + 1)%N
  | Exp.Lists (Lst.Array τ) es  => Typ.Array (N.of_nat $ List.length es) τ
  | Exp.Lists Lst.Struct es     => Typ.Struct false (List.map typ_of_exp es)
  | Exp.Lists (Lst.Header _) es => Typ.Struct true (List.map typ_of_exp es)
  end.

Definition typ_of_lists (ls : Lst.t) (es : list Exp.t) : Typ.t :=
  match ls with
  | Lst.Array t  => Typ.Array (N.of_nat $ List.length es) t
  | Lst.Struct   => Typ.Struct false (List.map typ_of_exp es)
  | Lst.Header _ => Typ.Struct true (List.map typ_of_exp es)
  end.
