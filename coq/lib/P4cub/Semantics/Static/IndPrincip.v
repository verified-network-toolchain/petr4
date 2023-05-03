Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Static.Util
        Poulet4.P4cub.Semantics.Static.Typing
        Poulet4.P4cub.Syntax.CubNotations.

(** Custom induction principle for ok types. *)
Section OkBoomerInduction.
  Local Open Scope type_scope.
  
  Variable P : nat -> Typ.t -> Prop.

  Hypothesis HBool : forall Δ, P Δ Typ.Bool.
  Hypothesis HBit : forall Δ w, P Δ (Typ.Bit w).
  Hypothesis HInt : forall Δ w, P Δ (Typ.Int w).
  Hypothesis HVarBit : forall Δ w, P Δ (Typ.VarBit w).
  Hypothesis HError : forall Δ, P Δ Typ.Error.
  Hypothesis HArray : forall Δ n t,
      typ_ok Δ t -> P Δ t -> P Δ (Typ.Array n t).
  Hypothesis HStruct : forall Δ b ts,
      Forall (typ_ok Δ) ts ->
      Forall (P Δ) ts ->
      P Δ (Typ.Struct b ts).
  Hypothesis HVar : forall Δ T,
      (T < Δ)%nat -> P Δ (Typ.Var T).

  (** Custom induction principle for expression typing.
      Do [induction ?H using custom_typ_ok_ind]. *)
  Definition custom_typ_ok_ind :
    forall (Δ : nat) (τ : Typ.t), typ_ok Δ τ -> P Δ τ :=
    fix toind Δ τ HY :=
      match HY with
      | bool_ok _     => HBool _
      | bityp_ok _ w    => HBit _ w
      | intyp_ok _ w    => HInt _ w
      | varbityp_ok _ w => HVarBit _ w
      | error_ok _    => HError _
      | var_ok _ T HT => HVar _ _ HT
      | array_ok _ n T HT => HArray _ n T HT (toind _ _ HT)
      | structyp_ok _ _ b Hts
        => HStruct
            _ _ b Hts
            (Forall_ind
               (A:=Typ.t)
               (P:=typ_ok Δ)
               (Forall (P Δ))
               (Forall_nil _)
               (fun _ _ h _ => Forall_cons _ (toind _ _ h)) Hts)
      end.
End OkBoomerInduction.

(** Custom induction principle for expression typing. *)
Section TypeExprInduction.
  Local Open Scope exp_scope.
  
  Variable P : nat -> list Typ.t -> Exp.t -> Typ.t -> Prop.
  
  Hypothesis HBool : forall Δ Γ b,
      P Δ Γ (Exp.Bool b) Typ.Bool.
  
  Hypothesis HBit : forall Δ Γ w n,
      BitArith.bound w n ->
      P Δ Γ (w `W n) (Typ.Bit w).
  
  Hypothesis HInt : forall Δ Γ w z,
      IntArith.bound w z ->
      P Δ Γ (w `S z) (Typ.Int w).
  
  Hypothesis HVarBit : forall Δ Γ m w n,
      (w <= m)%N ->
      BitArith.bound w n ->
      P Δ Γ (Exp.VarBit m w n) (Typ.VarBit m).

  Hypothesis HVar : forall Δ Γ τ og x,
      nth_error Γ x = Some τ ->
      typ_ok Δ τ ->
      P Δ Γ (Exp.Var τ og x) τ.
  
  Hypothesis HSlice : forall Δ Γ hi lo w e τ,
      (Npos lo <= Npos hi < w)%N ->
      numeric_width w τ ->
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
      P Δ Γ e τ ->
      P Δ Γ (Exp.Slice hi lo e) (Typ.Bit (Npos hi - Npos lo + 1)%N).
  
  Hypothesis HCast : forall Δ Γ τ τ' e,
      proper_cast τ' τ ->
      typ_ok Δ τ ->
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ' ->
      P Δ Γ e τ' ->
      P Δ Γ (Exp.Cast τ e) τ.
  
  Hypothesis HUop : forall Δ Γ op τ τ' e,
      una_type op τ τ' ->
      typ_ok Δ τ' ->
      `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
      P Δ Γ e τ ->
      P Δ Γ (Exp.Uop τ' op e) τ'.
  
  Hypothesis HBop : forall Δ Γ op τ₁ τ₂ τ e₁ e₂,
      bin_type op τ₁ τ₂ τ ->
      typ_ok Δ τ ->
      `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ τ₁ ->
      P Δ Γ e₁ τ₁ ->
      `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ τ₂ ->
      P Δ Γ e₂ τ₂ ->
      P Δ Γ (Exp.Bop τ op e₁ e₂) τ.

  Hypothesis HIndex : forall Δ Γ e₁ e₂ w τ,
      typ_ok Δ τ ->
      `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ Typ.Array (Z.to_N (BitArith.upper_bound w)) τ ->
      P Δ Γ e₁ (Typ.Array (Z.to_N (BitArith.upper_bound w)) τ) ->
      `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ Typ.Bit w ->
      P Δ Γ e₂ (Typ.Bit w) ->
      P Δ Γ (Exp.Index τ e₁ e₂) τ.
  
  Hypothesis HMem : forall Δ Γ τ x e τs b,
      nth_error τs x = Some τ ->
      typ_ok Δ τ ->
      `⟨ Δ, Γ ⟩ ⊢ e ∈ Typ.Struct b τs ->
      P Δ Γ e (Typ.Struct b τs) ->
      P Δ Γ (Exp.Member τ x e) τ.

  Hypothesis HLists : forall Δ Γ ls es τ τs,
      typ_ok_lists Δ ls ->
      type_lst_ok ls τ τs ->
      Forall2 (type_exp Δ Γ) es τs ->
      Forall2 (P Δ Γ) es τs ->
      P Δ Γ (Exp.Lists ls es) τ.
  
  Hypothesis HError : forall Δ Γ err,
      P Δ Γ (Exp.Error err) (Typ.Error).
  
  (** Custom induction principle for expression typing.
      Do [induction ?H using custom_type_exp_ind]. *)
  Definition custom_type_exp_ind :
    forall Δ Γ e τ, `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> P Δ Γ e τ :=
    fix teind Δ Γ e τ HY :=
      match HY with
      | type_bool _ _ b     => HBool _ _ b
      | type_bit _ _ _ _ H => HBit _ _ _ _ H
      | type_int _ _ _ _ H => HInt _ _ _ _ H
      | type_varbit _ _ _ _ _ Hwm H => HVarBit _ _ _ _ _ Hwm H
      | type_var _ _ _ _ _ Hnth H => HVar _ _ _ _ _ Hnth H
      | type_slice _ _ _ _ _ _ _ Hlohiw Ht He
        => HSlice _ _ _ _ _ _ _ Hlohiw Ht He (teind _ _ _ _ He)
      | type_cast _ _ _ _ _ HPC Hok He
        => HCast _ _ _ _ _ HPC Hok He (teind _ _ _ _ He)
      | type_uop _ _ _ _ _ _ Huop Hok He
        => HUop _ _ _ _ _ _ Huop Hok He (teind _ _ _ _ He)
      | type_bop _ _ _ _ _ _ _ _ Hbop Hok He1 He2
        => HBop _ _ _ _ _ _ _ _ Hbop Hok
               He1 (teind _ _ _ _ He1)
               He2 (teind _ _ _ _ He2)
      | type_index _ _ _ _ _ _ Hok He₁ He₂
        => HIndex
            _ _ _ _ _ _ Hok
            He₁ (teind _ _ _ _ He₁)
            He₂ (teind _ _ _ _ He₂)
      | type_member _ _ _ _ _ _ _ Hnth Hok He
        => HMem _ _ _ _ _ _ _ Hnth Hok He (teind _ _ _ _ He)
      | type_error _ _ err => HError _ _ err
      | type_lists _ _ _ _ _ _ Hok lok Hes
        => HLists _ _ _ _ _ _ Hok lok Hes
            (Forall2_ind
               (Forall2 (P Δ Γ))
               (Forall2_nil _)
               (fun _ _ _ _ het _ => Forall2_cons _ _ (teind _ _ _ _ het)) Hes)
      end.
End TypeExprInduction.

Section TypePatternInduction.
  Local Open Scope pat_scope.
  
  Variable P : Pat.t -> Typ.t -> Prop.
  
  Hypothesis HWild : forall t, P Pat.Wild t.
  
  Hypothesis HMask : forall p1 p2 w,
      type_pat p1 (Typ.Bit w) ->
      P p1 (Typ.Bit w) ->
      type_pat p2 (Typ.Bit w) ->
      P p2 (Typ.Bit w) ->
      P (Pat.Mask p1 p2) (Typ.Bit w).
  
  Hypothesis HRange : forall p1 p2 w,
      type_pat p1 (Typ.Bit w) ->
      P p1 (Typ.Bit w) ->
      type_pat p2 (Typ.Bit w) ->
      P p2 (Typ.Bit w) ->
      P (Pat.Range p1 p2) (Typ.Bit w).
  
  Hypothesis HBit : forall w n, P (w PW n) (Typ.Bit w).
  
  Hypothesis HInt : forall w z, P (w PS z) (Typ.Int w).
  
  Hypothesis HStruct : forall ps ts,
      Forall2 type_pat ps ts ->
      Forall2 P ps ts ->
      P (Pat.Lists ps) (Typ.Struct false ts).
  
  Definition custom_type_pat_ind : forall p t,
      type_pat p t -> P p t :=
    fix pind p t (H : type_pat p t) :=
      match H with
      | type_wild _ => HWild _
      | type_mask _ _ _ Hp1 Hp2
        => HMask _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
      | type_range _ _ _ Hp1 Hp2
        => HRange _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
      | type_pbit w n => HBit w n
      | type_pint w z => HInt w z
      | type_pstruct _ _ H
        => HStruct
            _ _ H
            $ Forall2_ind
            (Forall2 P)
            (Forall2_nil _)
            (fun _ _ _ _ hpt _ => Forall2_cons _ _ (pind _ _ hpt)) H
      end.
End TypePatternInduction.
