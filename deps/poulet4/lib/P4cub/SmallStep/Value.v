Set Warnings "-custom-entry-overridden".
Require Import Poulet4.P4cub.Static.Static.

(** * Small-Step Values *)
Import String.
Import AllCubNotations Env.EnvNotations.

Inductive value {tags_t : Type} : Expr.e tags_t -> Prop :=
| value_bool (b : bool) (i : tags_t) :
    value <{ BOOL b @ i }>
| value_bit (w : N) (n : Z) (i : tags_t) :
    value <{ w W n @ i }>
| value_int (w : positive) (z : Z) (i : tags_t) :
    value <{ w S z @ i }>
| value_tuple (es : list (Expr.e tags_t)) (i : tags_t) :
    Forall value es ->
    value <{ tup es @ i }>
| value_struct (fs : F.fs string (Expr.e tags_t))
               (i : tags_t) :
    F.predfs_data value fs ->
    value <{ struct { fs } @ i }>
| value_header (fs : F.fs string (Expr.e tags_t))
               (b : Expr.e tags_t) (i : tags_t) :
    value b ->
    F.predfs_data value fs ->
    value <{ hdr { fs } valid:=b @ i }>
| value_error (err : option (string)) (i : tags_t) :
    value <{ Error err @ i }>
| value_matchkind (mk : Expr.matchkind) (i : tags_t) :
    value <{ Matchkind mk @ i }>
| value_headerstack (fs : F.fs string (Expr.t))
                    (hs : list (Expr.e tags_t))
                    (ni : Z) (i : tags_t) :
    Forall value hs ->
    value <{ Stack hs:fs nextIndex:=ni @ i }>.
(**[]*)

Section IsValueInduction.
  Variable tags_t : Type.
  
  Variable P : Expr.e tags_t -> Prop.
  
  Hypothesis HBool : forall b i, P <{ BOOL b @ i }>.
  
  Hypothesis HBit : forall w n i, P <{ w W n @ i }>.
  
  Hypothesis HInt : forall w z i, P <{ w S z @ i }>.
  
  Hypothesis HTuple : forall es i,
      Forall value es ->
      Forall P es ->
      P <{ tup es @ i }>.
  
  Hypothesis HStruct : forall fs i,
      F.predfs_data value fs ->
      F.predfs_data P fs ->
      P <{ struct { fs } @ i }>.
  
  Hypothesis HHeader : forall fs b i,
      value b ->
      P b ->
      F.predfs_data value fs ->
      F.predfs_data P fs ->
      P <{ hdr { fs } valid:=b @ i }>.
  
  Hypothesis HError : forall err i, P <{ Error err @ i }>.
  
  Hypothesis HMatchkind : forall mk i, P <{ Matchkind mk @ i }>.
  
  Hypothesis HStack : forall fs hs ni i,
      Forall value hs ->
      Forall P hs ->
      P <{ Stack hs:fs nextIndex:=ni @ i }>.
  
  Definition custom_value_ind : forall (e : Expr.e tags_t),
      value e -> P e :=
    fix vind (e : Expr.e tags_t) (H : value e) : P e :=
      let fix lind {es : list (Expr.e tags_t)}
              (Hes : Forall value es) : Forall P es :=
          match Hes with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (lind Ht)
          end in
      let fix find {fs : F.fs string (Expr.e tags_t)}
              (Hfs : F.predfs_data value fs) :
            F.predfs_data P fs :=
          match Hfs with
          | Forall_nil _ => Forall_nil _
          | Forall_cons _ Hh Ht => Forall_cons _ (vind _ Hh) (find Ht)
          end in
      match H with
      | value_bool b i => HBool b i
      | value_bit w n i => HBit w n i
      | value_int w z i => HInt w z i
      | value_tuple _ i Hes => HTuple _ i Hes (lind Hes)
      | value_struct _ i Hfs => HStruct _ i Hfs (find Hfs)
      | value_header _ _ i Hb Hfs
        => HHeader _ _ i Hb (vind _ Hb) Hfs (find Hfs)
      | value_error err i => HError err i
      | value_matchkind mk i => HMatchkind mk i
      | value_headerstack fs _ ni i Hhs => HStack fs _ ni i Hhs (lind Hhs)
      end.
End IsValueInduction.

Section Lemmas.
  Import F.FieldTactics.
  
  Hint Constructors value : core.
  Hint Extern 0 => inv_Forall_cons : core.
  
  Lemma value_exm : forall {tags_t : Type} (e : Expr.e tags_t), value e \/ ~ value e.
  Proof.
    induction e using custom_e_ind; auto 2;
      try (right; intros H'; inv H'; contradiction).
    - assert (Forall value es \/ ~ Forall value es).
      { ind_list_Forall; intuition. }
      intuition. right; intros H'; inv H'. contradiction.
    - assert (F.predfs_data value fields \/
              ~ F.predfs_data value fields).
      { ind_list_predfs; unfold F.predfs_data in *; intuition. }
      intuition. right; intros H'; inv H'. contradiction.
    - assert (F.predfs_data value fields \/
              ~ F.predfs_data value fields).
      { ind_list_predfs; unfold F.predfs_data in *; intuition. }
      intuition; right; intros H'; inv H'; contradiction.
    - assert (Forall value hs \/ ~ Forall value hs).
      { ind_list_Forall; intuition. }
      intuition. right; intros H'; inv H'. contradiction.
  Qed.
End Lemmas.

Inductive lvalue {tags_t : Type} : Expr.e tags_t -> Prop :=
| lvalue_var x τ i :
    lvalue <{ Var x:τ @ i }>
| lvalue_slice lv hi lo i :
    lvalue lv ->
    lvalue <{ Slice lv [hi:lo] @ i }>
| lvalue_member τ lv x i :
    lvalue lv ->
    lvalue <{ Mem lv dot x : τ @ i }>
| lvalue_access ts lv idx i :
    lvalue lv ->
    lvalue <{ Access lv[idx] : ts @ i }>.
(**[]*)

Module CanonicalForms.
  Ltac invert_value :=
    match goal with
    | H: value _ |- _ => inv H
    end.
  (**[]*)
  
  Ltac invert_expr_check :=
    match goal with
    | H: ⟦ _, _ ⟧ ⊢ _ ∈ _ |- _ => inv H
    end.
  (**[]*)
  
  Ltac invert_canonical := invert_value; invert_expr_check.
  
  Ltac crush_canonical := intros; invert_canonical; eauto 4.
  
  Section CanonicalForms.
    Variable Δ : Delta.
    
    Variable Γ : Gamma.
    
    Context {tags_t : Type}.
    
    Variable v : Expr.e tags_t.
    
    Hypothesis Hv : value v.
    
    Lemma canonical_forms_bool :
      ⟦ Δ, Γ ⟧ ⊢ v ∈ Bool -> exists b i, v = <{ BOOL b @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_bit : forall w,
        ⟦ Δ, Γ ⟧ ⊢ v ∈ bit<w> -> exists n i, v = <{ w W n @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_int : forall w,
        ⟦ Δ, Γ ⟧ ⊢ v ∈ int<w> -> exists z i, v = <{ w S z @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_tuple : forall ts,
        ⟦ Δ, Γ ⟧ ⊢ v ∈ tuple ts -> exists es i, v = <{ tup es @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_struct : forall ts,
        ⟦ Δ, Γ ⟧ ⊢ v ∈ struct { ts } -> exists fs i, v = <{ struct { fs } @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_header : forall ts,
        ⟦ Δ, Γ ⟧ ⊢ v ∈ hdr { ts } -> exists fs b i, v = <{ hdr { fs } valid:=b @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_error :
      ⟦ Δ, Γ ⟧ ⊢ v ∈ error -> exists err i, v = <{ Error err @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_matchkind :
      ⟦ Δ, Γ ⟧ ⊢ v ∈ matchkind -> exists mk i, v = <{ Matchkind mk @ i }>.
    Proof. crush_canonical. Qed.
    
    Lemma canonical_forms_headerstack : forall ts n,
        ⟦ Δ, Γ ⟧ ⊢ v ∈ stack ts[n] ->
        exists hs ni i, v = <{ Stack hs:ts nextIndex:= ni @ i }>.
    Proof. crush_canonical. Qed.
  End CanonicalForms.
  
  Ltac inv_eq_val_expr :=
    match goal with
    | H: <{ BOOL _ @ _ }> = <{ BOOL _ @ _ }> |- _ => inv H
    | H: <{ _ W _ @ _ }> = <{ _ W _ @ _ }> |- _ => inv H
    | H: <{ _ S _ @ _ }> = <{ _ S _ @ _ }> |- _ => inv H
    | H: <{ tup _ @ _ }> = <{ tup _ @ _ }> |- _ => inv H
    | H: <{ struct { _ } @ _ }> = <{ struct { _ } @ _ }> |- _ => inv H
    | H: <{ hdr { _ } valid:=_ @ _ }> = <{ hdr { _ } valid:=_ @ _ }>
      |- _ => inv H
    | H: <{ Stack _:_ nextIndex:=_ @ _ }> = <{ Stack _:_ nextIndex:=_ @ _ }>
      |- _ => inv H
    end.
  (**[]*)
  
  Ltac assert_canonical_forms :=
    match goal with
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ Bool |- _
      => pose proof canonical_forms_bool _ _ _ Hv Ht as [? [? Hcanon]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ bit<_> |- _
      => pose proof canonical_forms_bit _ _ _ Hv _ Ht as [? [? Hcanon]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ int<_> |- _
      => pose proof canonical_forms_int _ _ _ Hv _ Ht as [? [? Hcanon]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ tuple _ |- _
      => pose proof canonical_forms_tuple _ _ _ Hv _ Ht as [? [? Hcanon]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ struct { _ } |- _
      => pose proof canonical_forms_struct _ _ _ Hv _ Ht as [? [? Hcanon]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ hdr { _ } |- _
      => pose proof canonical_forms_header _ _ _ Hv _ Ht as [? [? [? Hcanon]]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ error |- _
      => pose proof canonical_forms_error _ _ _ Hv Ht as [? [? Hcanon]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ matchkind |- _
      => pose proof canonical_forms_matchkind _ _ _ Hv Ht as [? [? Hcanon]];
        inv Hcanon; inv Hv; inv Ht
    | Hv: value ?v, Ht: ⟦ _, _ ⟧ ⊢ ?v ∈ stack _[_] |- _
      => pose proof canonical_forms_headerstack
             _ _ _ Hv _ _ Ht as [? [? [? Hcanon]]];
        inv Hcanon; inv Hv; inv Ht
    end.
  (**[]*)
End CanonicalForms.
