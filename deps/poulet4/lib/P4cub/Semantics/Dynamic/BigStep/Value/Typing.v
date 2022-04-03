From Coq Require Import ZArith.BinInt NArith.BinNat.
From Poulet4 Require Import P4cub.Syntax.Syntax
     P4cub.Semantics.Static.Util
     P4cub.Semantics.Dynamic.BigStep.Value.Syntax.
Import Val ValueNotations LValueNotations.

Reserved Notation "'⊢ᵥ' V ∈ τ"
         (at level 80, no associativity).

Reserved Notation "Γ '⊢ₗ' LV ∈ τ"
         (at level 80, no associativity).

Local Open Scope value_scope.

Inductive type_value : v -> Expr.t -> Prop :=
| typ_bool (b : bool) :  ⊢ᵥ b ∈ Expr.TBool
| typ_bit w n :
  BitArith.bound w n ->
  ⊢ᵥ w VW n ∈ Expr.TBit w
| typ_int w z :
  IntArith.bound w z ->
  ⊢ᵥ w VS z ∈ Expr.TInt w
| typ_struct vs ts ob b :
  match ob, b with
  | Some _, true
  | None, false => True
  | _, _ => False
  end ->
  Forall2 type_value vs ts ->
  ⊢ᵥ Struct vs ob ∈ Expr.TStruct ts b
| typ_error err :
  ⊢ᵥ Error err ∈ Expr.TError
where "'⊢ᵥ' V ∈ τ" := (type_value V τ) : type_scope.

(** Custom induction for value typing. *)
Section ValueTypingInduction.
  (** Arbitrary predicate. *)
  Variable P : v -> Expr.t -> Prop.
  
  Hypothesis HBool : forall b, P (Bool b) Expr.TBool.
  
  Hypothesis HBit : forall w n,
      BitArith.bound w n ->
      P (w VW n) (Expr.TBit w).
  
  Hypothesis HInt : forall w z,
      IntArith.bound w z ->
      P (w VS z) (Expr.TInt w).

  Hypothesis HError : forall err,
      P (Error err) Expr.TError.
    
  Hypothesis HStruct : forall vs ts ob b,
      match ob, b with
      | Some _, true
      | None, false => True
      | _, _ => False
      end ->
      Forall2 type_value vs ts ->
      Forall2 P vs ts ->
      P (Struct vs ob) (Expr.TStruct ts b).

  (** Custom induction principle.
      Do [induction ?H using custom_type_value_ind]. *)
  Definition custom_type_value_ind :
    forall (V : v) (τ : Expr.t),
      ⊢ᵥ V ∈ τ -> P V τ :=
    fix tvind V τ Hy :=
      let fix lind {vs : list v}
              {ts : list Expr.t}
              (HR : Forall2 type_value vs ts)
        : Forall2 P vs ts :=
        match HR with
        | Forall2_nil _ => Forall2_nil _
        | Forall2_cons _ _ Hh Ht
          => Forall2_cons _ _ (tvind _ _ Hh) (lind Ht)
        end in
      match Hy with
      | typ_bool b => HBool b
      | typ_bit _ _ H => HBit _ _ H
      | typ_int _ _ H => HInt _ _ H
      | typ_error err => HError err
      | typ_struct _ _ _ _ H Hfs => HStruct _ _ _ _ H Hfs (lind Hfs)
      end.
End ValueTypingInduction.

Local Close Scope value_scope.
Local Open Scope lvalue_scope.

Inductive type_lvalue (Γ : list Expr.t)
  : lv -> Expr.t -> Prop :=
| typ_var x τ :
  nth_error Γ x = Some τ ->
  Γ ⊢ₗ x ∈ τ
| typ_slice LV hi lo w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  Γ ⊢ₗ LV ∈ τ ->
  Γ ⊢ₗ Slice LV hi lo ∈ Expr.TBit (Npos hi - Npos lo + 1)%N
| typ_member LV x τ τs b :
  nth_error τs x = Some τ ->
  Γ ⊢ₗ LV ∈ Expr.TStruct τs b ->
  Γ ⊢ₗ LV DOT x ∈ τ
where "Γ '⊢ₗ' LV ∈ τ" := (type_lvalue Γ LV τ).

Local Close Scope lvalue_scope.
