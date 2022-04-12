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
  
  Hypothesis HVar : forall ϵ x τ v,
      nth_error ϵ x = Some v ->
      P ϵ (Expr.Var τ x) v.
  
  Hypothesis HSlice : forall ϵ e hi lo v v',
      eval_slice hi lo v = Some v' ->
      ⟨ ϵ, e ⟩ ⇓ v ->
      P ϵ e v ->
      P ϵ (Expr.Slice e hi lo) v'.
  
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
  
  Hypothesis HMember : forall ϵ τ x e vs v ob,
      nth_error vs x = Some v ->
      ⟨ ϵ, e ⟩ ⇓ Val.Struct vs ob ->
      P ϵ e (Val.Struct vs ob) ->
      P ϵ (Expr.Member τ x e) v.

  Hypothesis HStruct : forall ϵ es oe vs ob,
      relop (expr_big_step ϵ) oe (option_map Val.Bool ob) ->
      relop (P ϵ) oe (option_map Val.Bool ob) ->
      Forall2 (expr_big_step ϵ) es vs ->
      Forall2 (P ϵ) es vs ->
      P ϵ (Expr.Struct es oe) (Val.Struct vs ob).
  
  (** Custom induction principle for
      the expression big-step relation.
      [Do induction ?H using custom_expr_big_step_ind]. *)
  Definition custom_expr_big_step_ind :
    forall (ϵ : list Val.v) (e : Expr.e)
      (v : Val.v), ⟨ ϵ, e ⟩ ⇓ v -> P ϵ e v :=
    fix ebsind ϵ e v Hy :=
      let relopind
            {oe : option Expr.e} {ob : option bool}
            (H : relop (expr_big_step ϵ) oe (option_map Val.Bool ob))
        : relop (P ϵ) oe (option_map Val.Bool ob) :=
        match H with
        | relop_some _ _ _ He => relop_some _ _ _ (ebsind _ _ _ He)
        | relop_none _ => relop_none _
        end in
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
      | ebs_var _ _ τ _ Hx => HVar _ _ τ _ Hx
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
      | ebs_struct _ _ _ _ _ Ho Hes
        => HStruct _ _ _ _ _ Ho (relopind Ho) Hes (lind Hes)
      end.
End ExprEvalInduction.

(** Mutual indution scheme for statement evaluation. *)
(* TODO: plan on collapsing
   statements to avoid mutual induction. *)
(*Scheme stmt_big_step_ind_mut := Induction for stmt_big_step Sort Prop
    with block_big_step_ind_mut := Induction for block_big_step Sort Prop
    with bigstep_state_machine_ind_mut := Induction for bigstep_state_machine Sort Prop
    with bigstep_state_block_ind_mut := Induction for bigstep_state_block Sort Prop.*)
