Set Warnings "custom-entry-overridden,parsing".
Require Import Coq.PArith.BinPos
        Poulet4.Monads.Monad Poulet4.Monads.Option
        Coq.NArith.BinNatDef Coq.NArith.BinNat.
From Poulet4 Require Import Utils.P4Arith
     P4cub.Syntax.AST P4cub.Syntax.CubNotations.
Import Expr ExprNotations.

Fixpoint width_of_typ (τ : t) : option nat :=
  match τ with
  | TBool  => Some 1%nat
  | TBit w => Some $ N.to_nat w
  | TInt w => Some $ Pos.to_nat w
  | TError => Some 0%nat
  | TVar _ => None
  | TStruct fs _ =>
    let^ ns := sequence $ List.map width_of_typ fs in
    List.fold_left Nat.add ns 0%nat
  end.

(** Syntactic type of an expression. *)
Fixpoint t_of_e (exp: e) : t := 
  match exp with
  | Bool _  => TBool
  | Error _ => TError
  | Var τ _
  | Cast τ _
  | Uop τ _ _
  | Bop τ _ _ _
  | Member τ _ _       => τ
  | (w `W _)%expr       => TBit w
  | (w `S _)%expr       => TInt w
  | Slice _ hi lo      => TBit (Npos hi - Npos lo + 1)%N
  | Struct es None     => TStruct (List.map t_of_e es) false
  | Struct es (Some _) => TStruct (List.map t_of_e es) true
  end.

(** Restrictions on type-nesting. *)
Module ProperType.
  Section ProperTypeNesting.
    (** Evidence a type is a base type. *)
    Variant base_type : t -> Prop :=
    | base_bool : base_type TBool
    | base_bit (w : N) : base_type (TBit w)
      | base_int (w : positive) : base_type (TInt w).
    
    (* TODO: Allowed types within headers. *)
    Variant proper_inside_header : t -> Prop :=.
    
    (* TODO: Properly nested type. *)
    Inductive proper_nesting : t -> Prop :=.
    
    Lemma proper_inside_header_nesting : forall τ,
        proper_inside_header τ ->
        proper_nesting τ.
    Proof.
    Admitted.
  End ProperTypeNesting.
  
  (*Ltac invert_base_ludicrous :=.*)
  
  Ltac invert_proper_nesting :=
    match goal with
    | H: proper_nesting _
      |- _ => inv H(*; try invert_base_ludicrous*)
    end.
End ProperType.
