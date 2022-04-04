Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Static.Util
        Poulet4.P4cub.Semantics.Static.Typing
        Poulet4.P4cub.Syntax.CubNotations.
Import String AllCubNotations.

(** Custom induction principle for ok types. *)
Section OkBoomerInduction.
  Local Open Scope ty_scope.
  
  Variable P : nat -> Expr.t -> Prop.

  Hypothesis HBool : forall Δ, P Δ Expr.TBool.
  Hypothesis HBit : forall Δ w, P Δ (Expr.TBit w).
  Hypothesis HInt : forall Δ w, P Δ (Expr.TInt w).
  Hypothesis HError : forall Δ, P Δ Expr.TError.
  Hypothesis HStruct : forall Δ ts b,
      Forall (t_ok Δ) ts ->
      Forall (P Δ) ts ->
      P Δ (Expr.TStruct ts b).
  Hypothesis HVar : forall Δ T,
      (T < Δ)%nat -> P Δ T.

  (** Custom induction principle for expression typing.
      Do [induction ?H using custom_t_ok_ind]. *)
  Definition custom_t_ok_ind :
    forall (Δ : nat) (τ : Expr.t), t_ok Δ τ -> P Δ τ :=
    fix toind Δ τ HY :=
      let fix lind {ts : list Expr.t} (Hts : Forall (t_ok Δ) ts)
          : Forall (P Δ) ts :=
          match Hts with
          | Forall_nil _         => Forall_nil _
          | Forall_cons _ Pt Pts => Forall_cons _ (toind _ _ Pt) (lind Pts)
          end in
      match HY with
      | bool_ok _     => HBool _
      | bit_ok _ w    => HBit _ w
      | int_ok _ w    => HInt _ w
      | error_ok _    => HError _
      | var_ok _ T HT => HVar _ _ HT
      | struct_ok _ _ b Hts => HStruct _ _ b Hts (lind Hts)
      end.
End OkBoomerInduction.

(** Custom induction principle for expression typing. *)
Section TypeExprInduction.
  Local Open Scope expr_scope.
  
  Variable P : expr_type_env -> Expr.e -> Expr.t -> Prop.
  
  Hypothesis HBool : forall Γ b,
      P Γ (Expr.Bool b) Expr.TBool.
  
  Hypothesis HBit : forall Γ w n,
      BitArith.bound w n ->
      P Γ (w `W n) (Expr.TBit w).
  
  Hypothesis HInt : forall Γ w z,
      IntArith.bound w z ->
      P Γ (w `S z) (Expr.TInt w).
  
  Hypothesis HVar : forall Γ x τ,
      nth_error (types Γ) x = Some τ ->
      t_ok (type_vars Γ) τ ->
      P Γ (Expr.Var τ x) τ.
  
  Hypothesis HSlice : forall Γ e τ hi lo w,
      (Npos lo <= Npos hi < w)%N ->
      numeric_width w τ ->
      Γ ⊢ₑ e ∈ τ ->
      P Γ e τ ->
      P Γ (Expr.Slice e hi lo) (Expr.TBit (Npos hi - Npos lo + 1)%N).
  
  Hypothesis HCast : forall Γ τ τ' e,
      proper_cast τ' τ ->
      t_ok (type_vars Γ) τ' ->
      t_ok (type_vars Γ) τ ->
      Γ ⊢ₑ e ∈ τ' ->
      P Γ e τ' ->
      P Γ (Expr.Cast τ e) τ.
  
  Hypothesis HUop : forall Γ op τ τ' e,
      uop_type op τ τ' ->
      Γ ⊢ₑ e ∈ τ ->
      P Γ e τ ->
      P Γ (Expr.Uop τ' op e) τ'.
  
  Hypothesis HBop : forall Γ op τ₁ τ₂ τ e₁ e₂,
      bop_type op τ₁ τ₂ τ ->
      Γ ⊢ₑ e₁ ∈ τ₁ ->
      P Γ e₁ τ₁ ->
      Γ ⊢ₑ e₂ ∈ τ₂ ->
      P Γ e₂ τ₂ ->
      P Γ (Expr.Bop τ op e₁ e₂) τ.
  
  Hypothesis HMem : forall Γ e x τs τ b,
      nth_error τs x = Some τ ->
      t_ok (type_vars Γ) τ ->
      Γ ⊢ₑ e ∈ Expr.TStruct τs b ->
      P Γ e (Expr.TStruct τs b) ->
      P Γ (Expr.Member τ x e) τ.
  
  Hypothesis HStruct : forall Γ es oe τs (b : bool),
      relop (type_expr Γ) oe (if b then Some Expr.TBool else None) ->
      relop (P Γ) oe (if b then Some Expr.TBool else None) ->
      Forall2 (type_expr Γ) es τs ->
      Forall2 (P Γ) es τs ->
      P Γ (Expr.Struct es oe) (Expr.TStruct τs b).
  
  Hypothesis HError : forall Γ err,
      P Γ (Expr.Error err) (Expr.TError).
  
  (** Custom induction principle for expression typing.
      Do [induction ?H using custom_type_expr_ind]. *)
  Definition custom_type_expr_ind :
    forall Γ (e : Expr.e) (τ : Expr.t), Γ ⊢ₑ e ∈ τ -> P Γ e τ :=
    fix teind Γ e τ HY :=
      let relopind
            (oe : option Expr.e) (b : bool)
            (HR : relop (type_expr Γ) oe (if b then Some Expr.TBool else None))
        : relop (P Γ) oe (if b then Some Expr.TBool else None) :=
        if b then
          match HR with
          | relop_some _ _ _ He => relop_some _ _ _ (teind _ _ _ He)
          | relop_none _ => relop_none _
          end
        else
          match HR with
          | relop_some _ _ _ He => relop_some _ _ _ (teind _ _ _ He)
          | relop_none _ => relop_none _
          end in
      let fix lind
              {es : list Expr.e}
              {ts : list Expr.t}
              (HR : Forall2 (type_expr Γ) es ts)
        : Forall2 (P Γ) es ts :=
        match HR with
        | Forall2_nil _ => Forall2_nil _
        | Forall2_cons _ _ Hh Htail
          => Forall2_cons _ _ (teind _ _ _ Hh) (lind Htail)
        end in
      match HY with
      | type_bool _ b     => HBool _ b
      | type_bit _ _ _ H => HBit _ _ _ H
      | type_int _ _ _ H => HInt _ _ _ H
      | type_var _ _ _ Hnth H => HVar _ _ _ Hnth H
      | type_slice _ _ _ _ _ _ Hlohiw Ht He
        => HSlice _ _ _ _ _ _ Hlohiw Ht He (teind _ _ _ He)
      | type_cast _ _ _ _ HPC Hok Hok' He
        => HCast _ _ _ _ HPC Hok Hok' He (teind _ _ _ He)
      | type_uop _ _ _ _ _ Huop He
        => HUop _ _ _ _ _ Huop He (teind _ _ _ He)
      | type_bop _ _ _ _ _ _ _ Hbop He1 He2
        => HBop _ _ _ _ _ _ _ Hbop
               He1 (teind _ _ _ He1)
               He2 (teind _ _ _ He2)
      | type_member _ _ _ _ _ _ Hnth Hok He
        => HMem _ _ _ _ _ _ Hnth Hok He (teind _ _ _ He)
      | type_error _ err => HError _ err
      | type_struct _ _ oe _ b Hoe Hes
        => HStruct _ _ oe _ b Hoe (relopind oe b Hoe) Hes (lind Hes)
      end.
End TypeExprInduction.

(** Test of induction principle. *)
Lemma t_of_e_correct : forall Γ e τ,
    Γ ⊢ₑ e ∈ τ -> t_of_e e = τ.
Proof.
  intros Γ e τ H.
  induction H using custom_type_expr_ind;
    unravel in *; try reflexivity.
  f_equal.
  - (* Require Poulet4.Utils.ForallMap.
       rewrite ForallMap.Forall2_map_l,
       ForallMap.Forall2_eq in H2; subst. *)
    clear dependent Γ. clear dependent b. clear oe.
    induction H2; cbn in *; f_equal; auto.
  - destruct oe as [e |]; destruct b; cbn in *;
      inv H; inv H0; reflexivity.
Qed.

Section TypePatternInduction.
  Local Open Scope pat_scope.
  
  Variable P : Parser.pat -> Expr.t -> Prop.
  
  Hypothesis HWild : forall t, P Parser.Wild t.
  
  Hypothesis HMask : forall p1 p2 w,
      type_pat p1 (Expr.TBit w) ->
      P p1 (Expr.TBit w) ->
      type_pat p2 (Expr.TBit w) ->
      P p2 (Expr.TBit w) ->
      P (Parser.Mask p1 p2) (Expr.TBit w).
  
  Hypothesis HRange : forall p1 p2 w,
      type_pat p1 (Expr.TBit w) ->
      P p1 (Expr.TBit w) ->
      type_pat p2 (Expr.TBit w) ->
      P p2 (Expr.TBit w) ->
      P (Parser.Range p1 p2) (Expr.TBit w).
  
  Hypothesis HBit : forall w n, P (w PW n) (Expr.TBit w).
  
  Hypothesis HInt : forall w z, P (w PS z) (Expr.TInt w).
  
  Hypothesis HStruct : forall ps ts,
      Forall2 type_pat ps ts ->
      Forall2 P ps ts ->
      P (Parser.Struct ps) (Expr.TStruct ts false).
  
  Definition custom_type_pat_ind : forall p t,
      type_pat p t -> P p t :=
    fix pind p t (H : type_pat p t) :=
      let fix lind {ps : list Parser.pat} {ts : list Expr.t}
              (H : Forall2 type_pat ps ts) : Forall2 P ps ts :=
          match H with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Ht
            => Forall2_cons _ _ (pind _ _ Hh) (lind Ht)
          end in
      match H with
      | type_wild _ => HWild _
      | type_mask _ _ _ Hp1 Hp2
        => HMask _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
      | type_range _ _ _ Hp1 Hp2
        => HRange _ _ _ Hp1 (pind _ _ Hp1) Hp2 (pind _ _ Hp2)
      | type_pbit w n => HBit w n
      | type_pint w z => HInt w z
      | type_pstruct _ _ H => HStruct _ _ H (lind H)
      end.
End TypePatternInduction.
