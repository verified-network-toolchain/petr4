Require Import Poulet4.Utils.P4Arith
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
        Coq.Bool.Bool Coq.ZArith.BinInt Coq.NArith.BinNat
        Coq.Arith.Compare_dec Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Auxilary Poulet4.P4cub.Semantics.Climate.
Require Poulet4.P4cub.Semantics.Static.Util.
Import Val.ValueNotations ExprNotations.

Local Open Scope value_scope.

(** Bit-slicing. *)
Definition eval_slice (hi lo : positive) (v : Val.v) : option Val.v :=
  match v with
  | _ VW z
  | _ VS z
    => let w' := (Npos hi - Npos lo + 1)%N in
      Some $ Val.Bit w' $
           BitArith.mod_bound w' $
           BitArith.bitstring_slice z hi lo
  | _ => None
  end.

(** Unary Operations. *)
Definition eval_uop (op : Expr.uop) (v : Val.v) : option Val.v :=
  match op, v with
  | `!%uop, Val.Bool b => Some $ Val.Bool  $ negb b
  | `~%uop, w VW n => Some $ Val.Bit w $ BitArith.bit_not w n
  | `~%uop, w VS n => Some $ Val.Int w $ IntArith.bit_not w n
  | `-%uop, w VW z => Some $ Val.Bit w $ BitArith.neg w z
  | `-%uop, w VS z => Some $ Val.Int w $ IntArith.neg w z
  | Expr.IsValid, Val.Struct _ (Some b)
    => Some (Val.Bool b)
  | Expr.SetValidity b, Val.Struct vs _
    => Some $ Val.Struct vs $ Some b
  | _, _ => None
  end.

(** Binary operations. *)
Definition eval_bop (op : Expr.bop) (v1 v2 : Val.v) : option Val.v :=
  match op, v1, v2 with
  | `+%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.plus_mod w n1 n2
  | `+%bop, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.plus_mod w z1 z2
  | |+|%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.plus_sat w n1 n2
  | |+|%bop,  w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.plus_sat w z1 z2
  | `-%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.minus_mod w n1 n2
  | `-%bop, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.minus_mod w z1 z2
  | |-|%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.minus_sat w n1 n2
  | |-|%bop, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.minus_sat w z1 z2
  | ×%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.mult_mod w n1 n2
  | ×%bop, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.mult_mod w z1 z2
  | <<%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.shift_left w n1 n2
  | <<%bop, w VS z1, _ VW z2
    => Some $ Val.Int w $ IntArith.shift_left w z1 z2
  | >>%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.shift_right w n1 n2
  | >>%bop, w VS z1, _ VW z2
    => Some $ Val.Int w $ IntArith.shift_right w z1 z2
  | &%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_and w n1 n2
  | &%bop, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_and w z1 z2
  | ^%bop, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_xor w n1 n2
  | ^%bop, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_xor w z1 z2
  | Expr.BitOr, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_or w n1 n2
  | Expr.BitOr, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_or w z1 z2
  | ≤%bop, w VW n1, _ VW n2 => Some $ Val.Bool (n1 <=? n2)%Z
  | ≤%bop, w VS z1, _ VS z2 => Some $ Val.Bool (z1 <=? z2)%Z
  | `<%bop, w VW n1, _ VW n2 => Some $ Val.Bool (n1 <? n2)%Z
  | `<%bop, w VS z1, _ VS z2 => Some $ Val.Bool (z1 <? z2)%Z
  | ≥%bop, w VW n1, _ VW n2 => Some $ Val.Bool (n2 <=? n1)%Z
  | ≥%bop, w VS z1, _ VS z2 => Some $ Val.Bool (z2 <=? z1)%Z
  | `>%bop, w VW n1, _ VW n2 => Some $ Val.Bool (n2 <? n1)%Z
  | `>%bop, w VS z1, _ VS z2 => Some $ Val.Bool (z2 <? z1)%Z
  | `&&%bop, Val.Bool b1, Val.Bool b2 => Some $ Val.Bool (b1 && b2)
  | `||%bop, Val.Bool b1, Val.Bool b2 => Some $ Val.Bool (b1 || b2)
  | `==%bop, _, _ => Some $ Val.Bool $ eqbv v1 v2
  | !=%bop, _, _ => Some $ Val.Bool $ negb $ eqbv v1 v2
  | `++%bop, w1 VW n1, w2 VW n2
    => Some $ Val.Bit (w1 + w2)%N $ BitArith.concat w1 w2 n1 n2
  | `++%bop, w1 VW n1, w2 VS n2
    => Some $ Val.Bit (w1 + Npos w2)%N $ BitArith.concat w1 (Npos w2) n1 n2
  | `++%bop, w1 VS n1, w2 VS n2
    => Some $ Val.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
  | `++%bop, w1 VS n1, w2 VW n2
    => match w2 with
      | Npos w2 => Some $ Val.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
      | N0 => Some $ Val.Int w1 n1
      end
  | _, _, _ => None
  end.

Definition eval_cast
           (target : Expr.t) (v : Val.v) : option Val.v :=
  match target, v with
  | Expr.TBit 1%N, Val.Bool b
    => Some $ Val.Bit 1%N $ if b then 1%Z else 0%Z
  | Expr.TBool, Val.Bit 1%N n
    => Some $ Val.Bool
           match n with
           | Z0 => false
           | _  => true
           end
  | Expr.TBit w, _ VS z => Some $ w VW (BitArith.mod_bound w z)
  | Expr.TInt w, _ VW n => Some $ w VS (IntArith.mod_bound w n)
  | Expr.TBit w, _ VW n => Some $ w VW (BitArith.mod_bound w n)
  | Expr.TInt w, _ VS z => Some $ w VS (IntArith.mod_bound w z)
  | Expr.TStruct _ true, Val.Struct vs _
    => Some $ Val.Struct vs (Some true)
  | _, _ => None
  end.

Section Lemmas.
  Import P4ArithTactics (*ProperType*)
         Poulet4.P4cub.Semantics.Static.Util.
  
  Section HelpersType.
    Local Hint Constructors type_value : core.
    
    Lemma eval_member_types : forall x vs v τs τ,
        nth_error τs x = Some τ ->
        nth_error vs x = Some v ->
        Forall2 type_value vs τs ->
        ⊢ᵥ v ∈ τ.
    Proof.
      intros x vs v ts t ht hv h.
      rewrite ForallMap.Forall2_forall_nth_error in h.
      destruct h as [_ h]; eauto.
    Qed.
    
    Local Hint Extern 0 => bit_bounded : core.
    Local Hint Extern 0 => int_bounded : core.
    
    Lemma eval_slice_types : forall v v' τ hi lo w,
        eval_slice hi lo v = Some v' ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        ⊢ᵥ v ∈ τ ->
        ⊢ᵥ v' ∈ Expr.TBit (Npos hi - Npos lo + 1)%N.
    Proof.
      intros v v' τ hi lo w Heval Hw Hnum Hv.
      inv Hnum; inv Hv; unravel in *; inv Heval; auto 2.
    Qed.
    
    Lemma eval_bop_type : forall op τ1 τ2 τ v1 v2 v,
        bop_type op τ1 τ2 τ ->
        eval_bop op v1 v2 = Some v ->
        ⊢ᵥ v1 ∈ τ1 -> ⊢ᵥ v2 ∈ τ2 -> ⊢ᵥ v ∈ τ.
    Proof.
      intros op τ1 τ2 τ v1 v2 v Hbop Heval Ht1 Ht2; inv Hbop;
        repeat match goal with
               | H: Some _ = Some _ |- _ => inv H; constructor; auto 2
               | H: numeric _ |- _ => inv H
               | H: numeric_width _ _ |- _ => inv H
               | |- _ => inv Ht1; inv Ht2; unravel in *
               | |- BitArith.bound _ _ => unfold_bit_operation; auto 2
               | |- IntArith.bound _ _ => unfold_int_operation; auto 2
               end; auto 2.
    Qed.
    
    (*Local Hint Resolve proper_inside_header_nesting : core.*)
    
    Lemma eval_cast_types : forall v v' τ τ',
        proper_cast τ τ' ->
        eval_cast τ' v = Some v' ->
        ⊢ᵥ v ∈ τ -> ⊢ᵥ v' ∈ τ'.
    Proof.
      intros v v' τ τ' Hpc Heval Ht; inv Hpc; inv Ht;
        unravel in *; try some_inv; auto 2.
      - constructor; destruct b; cbv; auto 2.
      - destruct w; inv Heval; auto 2.
      - destruct w2; [|destruct p]; inv Heval; auto 2.
    Qed.
    
    (*Local Hint Constructors proper_nesting : core.*)
    (*Hint Rewrite repeat_length : core.
    Hint Rewrite app_length : core.
    Hint Rewrite firstn_length : core.
    Hint Rewrite skipn_length : core.
    Hint Rewrite Forall_app : core.
    Hint Rewrite @map_compose : core.
    Hint Rewrite (@Forall2_map_l Expr.t) : core.
    Hint Rewrite (@Forall2_Forall Expr.t) : core.
    Local Hint Resolve Forall_impl : core.
    Local Hint Resolve v_of_t_types : core.
    Local Hint Resolve Forall_firstn : core.
    Local Hint Resolve Forall_skipn : core.*)
    
    Lemma eval_uop_types : forall op τ τ' v v',
        uop_type op τ τ' ->
        eval_uop op v = Some v' ->
        ⊢ᵥ v ∈ τ -> ⊢ᵥ v' ∈ τ'.
    Proof.
      intros op τ τ' v v' Huop Heval Ht;
        inv Huop; inv Ht; unravel in *; inv Heval; auto 2;
        repeat match goal with
               | H: Some _ = Some _ |- _ => inv H
               | H: (if ?b then _ else _) = _ |- _ => destruct b as [? | ?]
               end; try constructor; try (destruct n; lia); auto 2;
        autorewrite with core; try split; auto 2.
      match_some_inv; some_inv; auto.
    Qed.
  End HelpersType.
  
  Section HelpersExist.
    Lemma eval_slice_exists : forall v τ hi lo w,
      (Npos lo <= Npos hi < w)%N ->
      numeric_width w τ ->
      ⊢ᵥ v ∈ τ ->
      exists v', eval_slice hi lo v = Some v'.
    Proof.
      intros v τ hi lo w Hw Hnum Hv;
        inv Hnum; inv Hv; unravel; eauto 2.
    Qed.
    
    Lemma eval_bop_exists : forall op τ1 τ2 τ v1 v2,
        bop_type op τ1 τ2 τ ->
        ⊢ᵥ v1 ∈ τ1 -> ⊢ᵥ v2 ∈ τ2 ->
        exists v, eval_bop op v1 v2 = Some v.
    Proof.
      intros op τ1 τ2 τ v1 v2 Hbop Ht1 Ht2; inv Hbop;
        repeat inv_numeric; inv Ht1; inv Ht2; unravel;
          try inv_numeric_width; eauto 2.
    Qed.
    
    Lemma eval_cast_exists : forall τ τ' v,
        proper_cast τ τ' ->
        ⊢ᵥ v ∈ τ ->
        exists v', eval_cast τ' v = Some v'.
    Proof.
      intros τ τ' v Hpc Ht; inv Hpc; inv Ht; unravel; eauto 2.
      - destruct w; eauto 2.
      - destruct w2; eauto 2.
        destruct p; eauto 2.
    Qed.
    
    Lemma eval_uop_exist : forall op τ τ' v,
        uop_type op τ τ' ->
        ⊢ᵥ v ∈ τ ->
        exists v', eval_uop op v = Some v'.
    Proof.
      intros op τ τ' v Huop Ht; inv Huop; inv Ht;
        unravel; repeat inv_numeric; eauto 2.
      destruct ob as [b |]; eauto 2 || contradiction.
    Qed.
      
    Lemma eval_member_exists : forall x τ τs vs,
        nth_error τs x = Some τ ->
        Forall2 type_value vs τs ->
        exists v, nth_error vs x = Some v.
    Proof.
      intros x t ts vs hnth h.
      apply nth_error_exists.
      apply Forall2_length in h.
      rewrite h.
      eauto using ForallMap.nth_error_some_length.
    Qed.
  End HelpersExist.
End Lemmas.
