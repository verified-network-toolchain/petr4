From Coq Require Import ZArith.BinInt NArith.BinNat.
From Poulet4 Require Import P4cub.Syntax.Syntax
     P4cub.Semantics.Static.Util
     P4cub.Semantics.Dynamic.BigStep.Value.Syntax.

Reserved Notation "'⊢ᵥ' V ∈ τ"
         (at level 80, no associativity).

Reserved Notation "Γ '⊢l' LV ∈ τ"
         (at level 80, no associativity).

Local Open Scope val_scope.

Inductive type_val : Val.t -> Typ.t -> Prop :=
| typ_bool (b : bool) :  ⊢ᵥ Val.Bool b ∈ Typ.Bool
| typ_bit w n :
  BitArith.bound w n ->
  ⊢ᵥ w VW n ∈ Typ.Bit w
| typ_int w z :
  IntArith.bound w z ->
  ⊢ᵥ w VS z ∈ Typ.Int w
| typ_varbit m w n :
  N.le w m ->
  BitArith.bound w n ->
  ⊢ᵥ Val.VarBit m w n ∈ Typ.VarBit m
| typ_lists ls vs τ τs :
  type_lst_ok ls τ τs ->
  Forall2 type_val vs τs ->
  ⊢ᵥ Val.Lists ls vs ∈ τ
| typ_error err :
  ⊢ᵥ Val.Error err ∈ Typ.Error
where "'⊢ᵥ' V ∈ τ" := (type_val V τ) : type_scope.

(** Custom induction for val typing. *)
Section ValTypingInduction.
  (** Arbitrary predicate. *)
  Variable P : Val.t -> Typ.t -> Prop.
  
  Hypothesis HBool : forall b, P (Val.Bool b) Typ.Bool.
  
  Hypothesis HBit : forall w n,
      BitArith.bound w n ->
      P (w VW n) (Typ.Bit w).
  
  Hypothesis HInt : forall w z,
      IntArith.bound w z ->
      P (w VS z) (Typ.Int w).

  Hypothesis HVarBit : forall m w n,
      N.le w m ->
      BitArith.bound w n ->
      P (Val.VarBit m w n) (Typ.VarBit m).
  
  Hypothesis HError : forall err,
      P (Val.Error err) Typ.Error.
  
  Hypothesis HLists : forall ls vs t ts,
      type_lst_ok ls t ts ->
      Forall2 type_val vs ts ->
      Forall2 P vs ts ->
      P (Val.Lists ls vs) t.

  (** Custom induction principle.
      Do [induction ?H using custom_type_val_ind]. *)
  Definition custom_type_val_ind :
    forall (V : Val.t) (τ : Typ.t),
      ⊢ᵥ V ∈ τ -> P V τ :=
    fix tvind V τ Hy :=
      match Hy with
      | typ_bool b => HBool b
      | typ_bit _ _ H => HBit _ _ H
      | typ_int _ _ H => HInt _ _ H
      | typ_varbit _ _ _ Hwm Hbd => HVarBit _ _ _ Hwm Hbd
      | typ_error err => HError err
      | typ_lists _ _ _ _ H Hfs =>
          HLists _ _ _ _ H Hfs
            (Forall2_ind
               (Forall2 P)
               (Forall2_nil _)
               (fun _ _ _ _ hvt _ ih => Forall2_cons _ _ (tvind _ _ hvt) ih) Hfs)
      end.
End ValTypingInduction.

Local Close Scope val_scope.
Local Open Scope lval_scope.

Inductive type_lval (Γ : list Typ.t)
  : Lval.t -> Typ.t -> Prop :=
| typ_var x τ :
  nth_error Γ x = Some τ ->
  Γ ⊢l Lval.Var x ∈ τ
| typ_slice hi lo LV w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  Γ ⊢l LV ∈ τ ->
  Γ ⊢l Lval.Slice hi lo LV ∈ Typ.Bit (Npos hi - Npos lo + 1)%N
| typ_member LV x τ τs b :
  nth_error τs x = Some τ ->
  Γ ⊢l LV ∈ Typ.Struct b τs ->
  Γ ⊢l LV DOT x ∈ τ
| typ_index lv i n τ :
  (i < n)%N ->
  Γ ⊢l lv ∈ Typ.Array n τ ->
  Γ ⊢l Lval.Index i lv ∈ τ
where "Γ '⊢l' LV ∈ τ" := (type_lval Γ LV τ).

Local Close Scope lval_scope.
