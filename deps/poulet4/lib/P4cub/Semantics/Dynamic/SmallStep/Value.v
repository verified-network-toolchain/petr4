Require Import Poulet4.P4cub.Semantics.Static.Static.

(** * Small-Step Values *)
Import String AllCubNotations.

Inductive value : Expr.e -> Prop :=
| value_bool (b : bool) :
  value b
| value_bit (w : N) (n : Z) :
  value (w `W n)%expr
| value_int (w : positive) (z : Z) :
  value (w `S z)%expr
| value_struct (es : list Expr.e) ob :
  Forall value es ->
  value (Expr.Struct es ob)
| value_error (err : option (string)) :
  value (Expr.Error err).

Section IsValueInduction.
  Variable P : Expr.e -> Prop.
  
  Hypothesis HBool : forall b : bool, P b.
  
  Hypothesis HBit : forall w n, P (w `W n)%expr.
  
  Hypothesis HInt : forall w z, P (w `S z)%expr.
  
  Hypothesis HStruct : forall es ob,
      Forall value es ->
      Forall P es ->
      P (Expr.Struct es ob).
  
  Hypothesis HError : forall err, P (Expr.Error err).
  
  Definition custom_value_ind : forall e : Expr.e, value e -> P e :=
    fix vind e H : P e :=
      let fix lind {es : list Expr.e}
              (Hes : Forall value es) : Forall P es :=
          match Hes with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (lind Ht)
          end in
      match H with
      | value_bool b => HBool b
      | value_bit w n => HBit w n
      | value_int w z => HInt w z
      | value_struct _ ob Hes => HStruct _ ob Hes (lind Hes)
      | value_error err => HError err
      end.
End IsValueInduction.

Section Lemmas.
  Local Hint Constructors value : core.
  Local Hint Extern 0 => inv_Forall_cons : core.
  
  Lemma value_exm : forall e, value e \/ ~ value e.
  Proof.
    induction e using custom_e_ind; auto 2;
      try (right; intros H'; inv H'; contradiction).
    - assert (Forall value fields \/ ~ Forall value fields).
      { ind_list_Forall; intuition. }
      intuition. right; intros H'; inv H'. contradiction.
  Qed.
End Lemmas.

Inductive lvalue : Expr.e -> Prop :=
| lvalue_var x τ :
    lvalue (Expr.Var τ x)
| lvalue_slice lv hi lo :
    lvalue lv ->
    lvalue (Expr.Slice lv hi lo)
| lvalue_member τ lv x :
    lvalue lv ->
    lvalue (Expr.Member τ x lv).

Module CanonicalForms.
  Ltac invert_value :=
    match goal with
    | H: value _ |- _ => inv H
    end.
  
  Ltac invert_expr_check :=
    match goal with
    | H: _ ⊢ₑ _ ∈ _ |- _ => inv H
    end.
  
  Ltac invert_canonical := invert_value; invert_expr_check.
  
  Ltac crush_canonical := intros; invert_canonical; eauto 4.
  
  Section CanonicalForms.
    Variable Γ : expr_type_env.
    
    Variable v : Expr.e.
    
    Hypothesis Hv : value v.
    
    Lemma canonical_forms_bool :
      Γ ⊢ₑ v ∈ Expr.TBool -> exists b : bool, v = b.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_bit : forall w,
        Γ ⊢ₑ v ∈ Expr.TBit w -> exists n, v = (w `W n)%expr.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_int : forall w,
        Γ ⊢ₑ v ∈ Expr.TInt w -> exists z, v = (w `S z)%expr.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_struct : forall ts b,
        Γ ⊢ₑ v ∈ Expr.TStruct ts b -> exists es ob, v = Expr.Struct es ob.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_error :
      Γ ⊢ₑ v ∈ Expr.TError -> exists err, v = (Expr.Error err).
    Proof. crush_canonical. Qed.
  End CanonicalForms.
  
  Ltac inv_eq_val_expr :=
    match goal with
    | H: Expr.Bool _ = Expr.Bool _ |- _ => inv H
    | H: (_ `W _)%expr = (_ `W _)%expr |- _ => inv H
    | H: (_ `S _)%expr = (_ `S _)%expr |- _ => inv H
    | H: Expr.Struct _ _ = Expr.Struct _ |- _ => inv H
    | H: Expr.Error _ = Expr.Error _ |- _ => inv H
    end.
  
  Ltac assert_canonical_forms :=
    match goal with
    | Hv: value ?v, Ht: _ ⊢ₑ ?v ∈ Expr.TBool |- _
      => pose proof canonical_forms_bool _ _ Hv Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: _ ⊢ₑ ?v ∈ Expr.TBit _ |- _
      => pose proof canonical_forms_bit _ _ Hv _ Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: _ ⊢ₑ ?v ∈ Expr.TInt _ |- _
      => pose proof canonical_forms_int _ _ Hv _ Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: _ ⊢ₑ ?v ∈ Expr.TStruct _ _ |- _
      => pose proof canonical_forms_struct _ _ Hv _ _ Ht as (? & ? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: _ ⊢ₑ ?v ∈ Expr.TError |- _
      => pose proof canonical_forms_error _ _ Hv Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    end.
End CanonicalForms.
