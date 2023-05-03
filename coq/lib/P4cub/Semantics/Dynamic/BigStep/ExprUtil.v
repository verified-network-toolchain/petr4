Require Import Poulet4.Utils.P4Arith
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
        Coq.Bool.Bool Coq.ZArith.BinInt Coq.NArith.BinNat
        Coq.Arith.Compare_dec Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Auxiliary Poulet4.P4cub.Semantics.Climate.
Require Import Poulet4.P4cub.Semantics.Static.Util Poulet4.P4cub.Semantics.Static.Auxiliary.
Require Poulet4.P4light.Semantics.Ops.

Local Open Scope val_scope.

(** Bit-slicing. *)
Definition eval_slice (hi lo : positive) (v : Val.t) : option Val.t :=
  match v with
  | _ VW z
  | _ VS z
    => let w' := (Npos hi - Npos lo + 1)%N in
      Some $ Val.Bit w' $
           BitArith.mod_bound w' $
           BitArith.bitstring_slice z hi lo
  | _ => None
  end.

Lemma eval_slice_bit_correct : forall hi lo w n,
    Val.Bit (Npos hi - Npos lo + 1)%N 
      (BitArith.mod_bound (Npos hi - Npos lo + 1)%N
         (BitArith.bitstring_slice n hi lo)) =
      let (w',n') :=
        BitArith.from_lbool
          (Ops.bitstring_slice
             (to_lbool w n) (Pos.to_nat lo) (Pos.to_nat hi)) in
      (w' VW n').
Proof.
  intros hi lo w z.
  destruct (BitArith.from_lbool
              (Ops.bitstring_slice
                 (to_lbool w z) (Pos.to_nat lo) (Pos.to_nat hi))) as [w' n] eqn:hwn.
Abort.

Definition slice_val (hi lo : positive) (v : Val.t) : option Val.t :=
  match v with
  | w VW n =>
      let bits := to_lbool w n in
      let bits' := Ops.bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi) in
      let (w',n') := BitArith.from_lbool bits' in
      Some $ w' VW n'
  | w VS z =>
      let bits := to_lbool (Npos w) z in
      let bits' := Ops.bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi) in
      let (w',z') := BitArith.from_lbool bits' in
      Some $ w' VW z'
  | _ => None
  end.

(** Unary Operations. *)
Definition eval_una (op : Una.t) (v : Val.t) : option Val.t :=
  match op, v with
  | `!%una, Val.Bool b => Some $ Val.Bool  $ negb b
  | `~%una, w VW n => Some $ Val.Bit w $ BitArith.bit_not w n
  | `~%una, w VS n => Some $ Val.Int w $ IntArith.bit_not w n
  | `-%una, w VW z => Some $ Val.Bit w $ BitArith.neg w z
  | `-%una, w VS z => Some $ Val.Int w $ IntArith.neg w z
  | Una.IsValid, Val.Lists (Lst.Header b) _
    => Some (Val.Bool b)
  | Una.SetValidity b, Val.Lists _ vs
    => Some $ Val.Lists (Lst.Header b) vs
  | _, _ => None
  end.

(** Binary operations. *)
Definition eval_bin (op : Bin.t) (v1 v2 : Val.t) : option Val.t :=
  match op, v1, v2 with
  | `+%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.plus_mod w n1 n2
  | `+%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.plus_mod w z1 z2
  | |+|%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.plus_sat w n1 n2
  | |+|%bin,  w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.plus_sat w z1 z2
  | `-%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.minus_mod w n1 n2
  | `-%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.minus_mod w z1 z2
  | |-|%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.minus_sat w n1 n2
  | |-|%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.minus_sat w z1 z2
  | ×%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.mult_mod w n1 n2
  | ×%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.mult_mod w z1 z2
  | <<%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.shift_left w n1 n2
  | <<%bin, w VS z1, _ VW z2
    => Some $ Val.Int w $ IntArith.shift_left w z1 z2
  | >>%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.shift_right w n1 n2
  | >>%bin, w VS z1, _ VW z2
    => Some $ Val.Int w $ IntArith.shift_right w z1 z2
  | &%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_and w n1 n2
  | &%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_and w z1 z2
  | ^%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_xor w n1 n2
  | ^%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_xor w z1 z2
  | Bin.BitOr, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_or w n1 n2
  | Bin.BitOr, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_or w z1 z2
  | ≤%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n1 <=? n2)%Z
  | ≤%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z1 <=? z2)%Z
  | `<%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n1 <? n2)%Z
  | `<%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z1 <? z2)%Z
  | ≥%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n2 <=? n1)%Z
  | ≥%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z2 <=? z1)%Z
  | `>%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n2 <? n1)%Z
  | `>%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z2 <? z1)%Z
  | `&&%bin, Val.Bool b1, Val.Bool b2 => Some $ Val.Bool (b1 && b2)
  | `||%bin, Val.Bool b1, Val.Bool b2 => Some $ Val.Bool (b1 || b2)
  | `==%bin, _, _ => Some $ Val.Bool $ eqb_val v1 v2
  | !=%bin, _, _ => Some $ Val.Bool $ negb $ eqb_val v1 v2
  | `++%bin, w1 VW n1, w2 VW n2
    => Some $ Val.Bit (w1 + w2)%N $ BitArith.concat w1 w2 n1 n2
  | `++%bin, w1 VW n1, w2 VS n2
    => Some $ Val.Bit (w1 + Npos w2)%N $ BitArith.concat w1 (Npos w2) n1 n2
  | `++%bin, w1 VS n1, w2 VS n2
    => Some $ Val.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
  | `++%bin, w1 VS n1, w2 VW n2
    => match w2 with
      | Npos w2 => Some $ Val.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
      | N0 => Some $ Val.Int w1 n1
      end
  | _, _, _ => None
  end.

Definition eval_cast
           (target : Typ.t) (v : Val.t) : option Val.t :=
  match target, v with
  | Typ.Bit 1%N, Val.Bool b
    => Some $ Val.Bit 1%N $ if b then 1%Z else 0%Z
  | Typ.Bool, Val.Bit 1%N n
    => Some $ Val.Bool
           match n with
           | Z0 => false
           | _  => true
           end
  | Typ.Bit w, _ VS z => Some $ w VW (BitArith.mod_bound w z)
  | Typ.Int w, _ VW n => Some $ w VS (IntArith.mod_bound w n)
  | Typ.Bit w, _ VW n => Some $ w VW (BitArith.mod_bound w n)
  | Typ.Int w, _ VS z => Some $ w VS (IntArith.mod_bound w z)
  | Typ.Struct false _, Val.Lists (Lst.Header _) vs
    => Some $ Val.Lists Lst.Struct vs
  | _, _ => None
  end.

Section Lemmas.
  Import P4ArithTactics (*ProperType*)
         Poulet4.P4cub.Semantics.Static.Util.
  
  Section HelpersType.
    Local Hint Constructors type_val : core.

    Lemma eval_index_types : forall vs v n t,
      nth_error vs n = Some v ->
      Forall (fun v => type_val v t) vs ->
      type_val v t.
    Proof.
      intros vs v n t hnth hvs.
      pose proof Forall_nth_error _ _ _ _ hvs hnth as h.
      assumption.
    Qed.
    
    Lemma eval_member_types : forall x vs v τs τ,
        nth_error τs x = Some τ ->
        nth_error vs x = Some v ->
        Forall2 type_val vs τs ->
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
        ⊢ᵥ v' ∈ Typ.Bit (Npos hi - Npos lo + 1)%N.
    Proof.
      intros v v' τ hi lo w Heval Hw Hnum Hv.
      inv Hnum; inv Hv; unravel in *; inv Heval; auto 2.
    Qed.

    Lemma slice_val_types : forall v v' τ hi lo w,
        slice_val hi lo v = Some v' ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        ⊢ᵥ v ∈ τ ->
        ⊢ᵥ v' ∈ Typ.Bit (Npos hi - Npos lo + 1)%N.
    Proof.
      intros v v' t hi lo w hslice hw hnum hvt.
      inv hnum; inv hvt; inv hslice; cbn in * |-.
      - assert
          (Z.to_N
             (Zcomplements.Zlength
                (Ops.bitstring_slice
                   (to_lbool w n) (Pos.to_nat lo) (Pos.to_nat hi)))
           = (N.pos hi - N.pos lo + 1)%N) as h.
        { rewrite Zcomplements.Zlength_correct.
          rewrite Ops.bitstring_slice_length.
          lia.
          rewrite length_to_lbool. lia. }
        rewrite h. constructor.
    Admitted.
    
    Lemma eval_bin_type : forall op τ1 τ2 τ v1 v2 v,
        bin_type op τ1 τ2 τ ->
        eval_bin op v1 v2 = Some v ->
        ⊢ᵥ v1 ∈ τ1 -> ⊢ᵥ v2 ∈ τ2 -> ⊢ᵥ v ∈ τ.
    Proof.
      intros op τ1 τ2 τ v1 v2 v Hbin Heval Ht1 Ht2; inv Hbin;
        repeat match goal with
               | H: Some _ = Some _ |- _ => inv H; constructor; auto 2
               | H: numeric _ |- _ => inv H
               | H: numeric_width _ _ |- _ => inv H
               | H: type_lst_ok _ _ _ |- _ => inv H
               | |- _ => inv Ht1; inv Ht2; unravel in *
               | |- BitArith.bound _ _ => unfold_bit_operation; auto 2
               | |- IntArith.bound _ _ => unfold_int_operation; auto 2
               end; auto 2.
    Qed.

    Local Hint Constructors type_lst_ok : core.
    
    Lemma eval_cast_types : forall v v' τ τ',
        proper_cast τ τ' ->
        eval_cast τ' v = Some v' ->
        ⊢ᵥ v ∈ τ -> ⊢ᵥ v' ∈ τ'.
    Proof.
      intros v v' τ τ' Hpc Heval Ht; inv Hpc; inv Ht;
        unravel in *; try invert_type_lst_ok;
        try some_inv; eauto.
      - constructor; destruct b; cbv; auto 2.
      - destruct w; inv Heval; auto 2.
      - destruct w2; [|destruct p]; inv Heval; auto 2.
    Qed.
    
    Lemma eval_una_types : forall op τ τ' v v',
        una_type op τ τ' ->
        eval_una op v = Some v' ->
        ⊢ᵥ v ∈ τ -> ⊢ᵥ v' ∈ τ'.
    Proof.
      intros op τ τ' v v' Huna Heval Ht;
        inv Huna; inv Ht; unravel in *; inv Heval; auto 2;
        try invert_type_lst_ok;
        repeat match goal with
               | H: Some _ = Some _ |- _ => inv H
               | H: (if ?b then _ else _) = _ |- _ => destruct b as [? | ?]
               end; try constructor; try (destruct n; lia); auto 2;
        autorewrite with core; try split; eauto.
    Qed.
  End HelpersType.
  
  Section HelpersExist.
    Lemma eval_index_exists : forall {A : Set} w n (vs : list A),
        BitArith.bound w n ->
        length vs = Z.to_nat (BitArith.upper_bound w) ->
        exists v, nth_error vs (Z.to_nat n) = Some v.
    Proof.
      intros A w n vs hwn hlen.
      unfold BitArith.bound,BitArith.upper_bound in *.
      apply length_nth_error_some. lia.
    Qed.
    
    Lemma eval_slice_exists : forall v τ hi lo w,
      (Npos lo <= Npos hi < w)%N ->
      numeric_width w τ ->
      ⊢ᵥ v ∈ τ ->
      exists v', eval_slice hi lo v = Some v'.
    Proof.
      intros v τ hi lo w Hw Hnum Hv;
        inv Hnum; inv Hv; try invert_type_lst_ok; unravel; eauto 2.
    Qed.

    Lemma slice_val_exists : forall v τ hi lo w,
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        ⊢ᵥ v ∈ τ ->
        exists v', slice_val hi lo v = Some v'.
    Proof.
      intros v t hi lo w hw hnum hv;
        inv hnum; inv hv; try invert_type_lst_ok; unravel; eauto 2.
    Qed.
    
    Lemma eval_bin_exists : forall op τ1 τ2 τ v1 v2,
        bin_type op τ1 τ2 τ ->
        ⊢ᵥ v1 ∈ τ1 -> ⊢ᵥ v2 ∈ τ2 ->
        exists v, eval_bin op v1 v2 = Some v.
    Proof.
      intros op τ1 τ2 τ v1 v2 Hbin Ht1 Ht2; inv Hbin;
        repeat inv_numeric; inv Ht1; inv Ht2; unravel;
        try inv_numeric_width; try invert_type_lst_ok; eauto 2.
    Qed.
    
    Lemma eval_cast_exists : forall τ τ' v,
        proper_cast τ τ' ->
        ⊢ᵥ v ∈ τ ->
        exists v', eval_cast τ' v = Some v'.
    Proof.
      intros τ τ' v Hpc Ht; inv Hpc; inv Ht;
        try invert_type_lst_ok; unravel; eauto 2.
      - destruct w; eauto 2.
      - destruct w2; eauto 2.
        destruct p; eauto 2.
    Qed.
    
    Lemma eval_una_exist : forall op τ τ' v,
        una_type op τ τ' ->
        ⊢ᵥ v ∈ τ ->
        exists v', eval_una op v = Some v'.
    Proof.
      intros op τ τ' v Huna Ht; inv Huna; inv Ht;
        try invert_type_lst_ok;
        unravel; repeat inv_numeric; eauto 2.
    Qed.
      
    Lemma eval_member_exists : forall x τ τs vs,
        nth_error τs x = Some τ ->
        Forall2 type_val vs τs ->
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
