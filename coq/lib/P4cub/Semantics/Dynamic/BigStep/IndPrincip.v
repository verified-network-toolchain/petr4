Require Import Poulet4.P4cub.Syntax.AST Coq.ZArith.BinInt.
From Poulet4.P4cub.Semantics.Dynamic Require Import
     BigStep.Value.Value BigStep.Semantics.
Import ExprNotations Val.ValueNotations.

(** A custom induction principle for
    the expression big-step relation. *)
Section ExprEvalInduction.
  Local Open Scope expr_scope.
  Local Open Scope value_scope.
  
  Variable P : list Val.v -> Expr.e -> Val.v -> Prop.
  
  Hypothesis HBool : forall ϵ (b : bool), P ϵ b b.
  
  Hypothesis HBit : forall ϵ w n, P ϵ (w `W n) (w VW n).
  
  Hypothesis HInt : forall ϵ w z, P ϵ (w `S z) (w VS z).

  Hypothesis HVarBit : forall ϵ m w n,
      P ϵ (Expr.VarBit m w n) (Val.VarBit m w n).
  
  Hypothesis HVar : forall ϵ τ og x v,
      nth_error ϵ x = Some v ->
      P ϵ (Expr.Var τ og x) v.
  
  Hypothesis HSlice : forall ϵ e hi lo v v',
      slice_val hi lo v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ (Expr.Slice hi lo e) v'.
  
  Hypothesis HCast : forall ϵ τ e v v',
      eval_cast τ v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ (Expr.Cast τ e) v'.
  
  Hypothesis HError : forall ϵ err,
      P ϵ (Expr.Error err) (Val.Error err).
  
  Hypothesis HUop : forall ϵ τ op e v v',
      eval_uop op v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ (Expr.Uop τ op e) v'.
  
  Hypothesis HBop : forall ϵ τ op e1 e2 v v1 v2,
      eval_bop op v1 v2 = Some v ->
      ⟨ ϵ, e1 ⟩ ⇓ v1 ->
      P ϵ e1 v1 ->
      ⟨ ϵ, e2 ⟩ ⇓ v2 ->
      P ϵ e2 v2 ->
      P ϵ (Expr.Bop τ op e1 e2) v.
  
  Hypothesis HMember : forall ϵ τ x e ls vs v,
      nth_error vs x = Some v ->
      ⟨ ϵ, e ⟩ ⇓ Val.Lists ls vs ->
      P ϵ e (Val.Lists ls vs) ->
      P ϵ (Expr.Member τ x e) v.

  Hypothesis HIndex : forall ϵ τ e₁ e₂ ls vs w n v,
      nth_error vs (Z.to_nat n) = Some v ->
      ⟨ ϵ, e₁ ⟩ ⇓ Val.Lists ls vs ->
      P ϵ e₁ (Val.Lists ls vs) ->
      ⟨ ϵ, e₂ ⟩ ⇓ w VW n ->
      P ϵ e₂ (w VW n) ->
      P ϵ (Expr.Index τ e₁ e₂) v.

  Hypothesis HLists : forall ϵ ls es vs,
      Forall2 (expr_big_step ϵ) es vs ->
      Forall2 (P ϵ) es vs ->
      P ϵ (Expr.Lists ls es) (Val.Lists ls vs).
  
  (** Custom induction principle for
      the expression big-step relation.
      [Do induction ?H using custom_expr_big_step_ind]. *)
  Definition custom_expr_big_step_ind :
    forall (ϵ : list Val.v) (e : Expr.e)
      (v : Val.v), ⟨ ϵ, e ⟩ ⇓ v -> P ϵ e v :=
    fix ebsind ϵ e v Hy :=
      let fix lind
              {es : list Expr.e} {vs : list Val.v}
              (HR : Forall2 (expr_big_step ϵ) es vs)
          : Forall2 (P ϵ) es vs :=
          match HR with
          | Forall2_nil _ => Forall2_nil _
          | Forall2_cons _ _ Hh Ht
            => Forall2_cons _ _ (ebsind _ _ _ Hh) (lind Ht)
          end in
      match Hy with
      | ebs_bool _ b => HBool ϵ b
      | ebs_bit _ w n => HBit ϵ w n
      | ebs_int _ w z => HInt ϵ w z
      | ebs_varbit _ m w n => HVarBit ϵ m w n
      | ebs_var _ _ _ _ _ Hx => HVar _ _ _ _ _ Hx
      | ebs_slice _ _ _ _ _ _ Hv He
        => HSlice _ _ _ _ _ _ Hv He (ebsind _ _ _ He)
      | ebs_cast _ _ _ _ _ Hv He
        => HCast _ _ _ _ _ Hv He (ebsind _ _ _ He)
      | ebs_error _ err => HError _ err
      | ebs_uop _ t _ _ _ Hu Hv He
        => HUop _ t _ _ _ Hu Hv He (ebsind _ _ _ He)
      | ebs_bop _ t _ _ _ _ _ _ Hv He1 He2
        => HBop
            _ t _ _ _ _ _ _ Hv
            He1 (ebsind _ _ _ He1)
            He2 (ebsind _ _ _ He2)
      | ebs_member _ t _ _ _ _ _ Hnth He
        => HMember
            _ t _ _ _ _ _ Hnth
            He (ebsind _ _ _ He)
      | ebs_index _ _ _ _ _ _ _ _ _ Hnth He₁ He₂
        => HIndex
            _ _ _ _ _ _ _ _ _ Hnth
            He₁ (ebsind _ _ _ He₁)
            He₂ (ebsind _ _ _ He₂)
      | ebs_lists _ _ _ _ Hes
        => HLists _ _ _ _ Hes (lind Hes)
      end.
End ExprEvalInduction.
