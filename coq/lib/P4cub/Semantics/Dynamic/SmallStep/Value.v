Require Import Poulet4.P4cub.Semantics.Static.Static.

(** * Small-Step Values *)

Inductive value : Exp.t -> Prop :=
| value_bool (b : bool) :
  value (Exp.Bool b)
| value_bit w n :
  value (w `W n)%exp
| value_int w z :
  value (w `S z)%exp
| value_varbit m w n :
  value (Exp.VarBit m w n)
| value_lists ls es :
  Forall value es ->
  value (Exp.Lists ls es)
| value_error err :
  value (Exp.Error err).

Section IsValueInduction.
  Variable P : Exp.t -> Prop.
  
  Hypothesis HBool : forall b : bool, P (Exp.Bool b).
  
  Hypothesis HBit : forall w n, P (w `W n)%exp.

  Hypothesis HVarBit : forall m w n, P (Exp.VarBit m w n).
  
  Hypothesis HInt : forall w z, P (w `S z)%exp.
  
  Hypothesis HLists : forall ls es,
      Forall value es ->
      Forall P es ->
      P (Exp.Lists ls es).
  
  Hypothesis HError : forall err, P (Exp.Error err).
  
  Definition custom_value_ind : forall e : Exp.t, value e -> P e :=
    fix vind e H : P e :=
      match H with
      | value_bool b => HBool b
      | value_bit w n => HBit w n
      | value_varbit m w n => HVarBit m w n
      | value_int w z => HInt w z
      | value_error err => HError err
      | value_lists ls _ Hes
        => HLists
            ls _ Hes
            $ Forall_ind
            (Forall P)
            (Forall_nil _)
            (fun _ _ hv _ => Forall_cons _ (vind _ hv)) Hes
      end.
End IsValueInduction.

Section Lemmas.
  Local Hint Constructors value : core.
  Local Hint Extern 0 => inv_Forall_cons : core.
  
  Lemma value_exm : forall e, value e \/ ~ value e.
  Proof.
    induction e using custom_exp_ind; auto 2;
      try (right; intros H'; inv H'; contradiction).
    assert (Forall value es \/ ~ Forall value es).
    { ind_list_Forall; intuition. }
    intuition. right; intros H'; inv H'. contradiction.
  Qed.
End Lemmas.

Inductive lvalue : Exp.t -> Prop :=
| lvalue_var τ og x :
    lvalue (Exp.Var τ og x)
| lvalue_slice hi lo lv :
    lvalue lv ->
    lvalue (Exp.Slice hi lo lv)
| lvalue_index τ v lv :
  value v ->
  lvalue lv ->
  lvalue (Exp.Index τ lv v)
| lvalue_member τ lv x :
    lvalue lv ->
    lvalue (Exp.Member τ x lv).

Module CanonicalForms.
  Ltac invert_value :=
    match goal with
    | H: value _ |- _ => inv H
    end.
  
  Ltac invert_canonical :=
    invert_value; invert_type_exp; try invert_type_lst_ok.
  
  Ltac crush_canonical := intros; invert_canonical; eauto 4.
  
  Section CanonicalForms.
    Variable Δ : nat.
    Variable Γ : list Typ.t.
    Variable v : Exp.t.
    
    Hypothesis Hv : value v.
    
    Lemma canonical_forms_bool :
      `⟨ Δ, Γ ⟩ ⊢ v ∈ Typ.Bool -> exists b : bool, v = Exp.Bool b.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_bit : forall w,
        `⟨ Δ, Γ ⟩ ⊢ v ∈ Typ.Bit w -> exists n, v = (w `W n)%exp.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_int : forall w,
        `⟨ Δ, Γ ⟩ ⊢ v ∈ Typ.Int w -> exists z, v = (w `S z)%exp.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_struct : forall b ts,
        `⟨ Δ, Γ ⟩ ⊢ v ∈ Typ.Struct b ts -> exists ls es, v = Exp.Lists ls es.
    Proof. crush_canonical. Qed.

    Lemma canonical_forms_array : forall n t,
        `⟨ Δ, Γ ⟩ ⊢ v ∈ Typ.Array n t ->
        exists es, v = Exp.Lists (Lst.Array t) es.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_error :
      `⟨ Δ, Γ ⟩ ⊢ v ∈ Typ.Error -> exists err, v = (Exp.Error err).
    Proof. crush_canonical. Qed.
  End CanonicalForms.
  
  Ltac inv_eq_val_exp :=
    match goal with
    | H: Exp.Bool _ = Exp.Bool _ |- _ => inv H
    | H: (_ `W _)%exp = (_ `W _)%exp |- _ => inv H
    | H: (_ `S _)%exp = (_ `S _)%exp |- _ => inv H
    | H: Exp.Lists _ _ = Exp.Lists _ |- _ => inv H
    | H: Exp.Error _ = Exp.Error _ |- _ => inv H
    end.
  
  Ltac assert_canonical_forms :=
    lazymatch goal with
    | Hv: value ?v, Ht: `⟨ _, _ ⟩ ⊢ ?v ∈ Typ.Bool |- _
      => pose proof canonical_forms_bool _ _ _ Hv Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: `⟨ _, _ ⟩ ⊢ ?v ∈ Typ.Bit _ |- _
      => pose proof canonical_forms_bit _ _ _ Hv _ Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: `⟨ _, _ ⟩ ⊢ ?v ∈ Typ.Int _ |- _
      => pose proof canonical_forms_int _ _ _ Hv _ Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: `⟨ _, _ ⟩ ⊢ ?v ∈ Typ.Struct _ _ |- _
      => pose proof canonical_forms_struct _ _ _ Hv _ _ Ht as (? & ? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: `⟨ _, _ ⟩ ⊢ ?v ∈ Typ.Array _ _ |- _
      => pose proof canonical_forms_array _ _ _ Hv _ _ Ht as (? & ? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: `⟨ _, _ ⟩ ⊢ ?v ∈ Typ.Error |- _
      => pose proof canonical_forms_error _ _ _ Hv Ht as (? & Hcanon);
        inv Hcanon; inv Hv; inv Ht
    end.
End CanonicalForms.
