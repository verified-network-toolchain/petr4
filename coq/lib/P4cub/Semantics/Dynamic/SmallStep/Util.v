Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Value
        Poulet4.P4cub.Semantics.Climate Poulet4.Utils.P4Arith
        Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Coq.Arith.Compare_dec Coq.micromega.Lia
        Poulet4.P4cub.Semantics.Static.Static
        Poulet4.Utils.ForallMap Poulet4.Monads.Option.

Section StepDefs.
  Import String P4ArithTactics.
  
  (** Bit-slicing. *)
  Definition eval_slice (hi lo : positive) (v : Exp.t) : option Exp.t :=
    match v with
    | (_ `W z)%exp
    | (_ `S z)%exp
      => let w' := (Npos hi - Npos lo + 1)%N in
        Some $ Exp.Bit w'
             (BitArith.mod_bound
                w' $ BitArith.bitstring_slice z hi lo)
    | _ => None
    end.
  
  Definition eval_cast
             (target : Typ.t) (v : Exp.t) : option Exp.t :=
    match target, v with
    | Typ.Bit (Npos 1), Exp.Bool true => Some $ Exp.Bit 1%N 1%Z
    | Typ.Bit (Npos 1), Exp.Bool false => Some $ Exp.Bit 1%N 0%Z
    | Typ.Bool, Exp.Bit 1%N 1%Z=> Some $ Exp.Bool true
    | Typ.Bool, Exp.Bit 1%N 0%Z=> Some $ Exp.Bool true
    | Typ.Bit w, (_ `S z)%exp
      => Some $ Exp.Bit w $ BitArith.mod_bound w z
    | Typ.Int w, (_ `W n)%exp
      => Some $ Exp.Int w $ IntArith.mod_bound w n
    | Typ.Bit w, (_ `W n)%exp
      => Some $ Exp.Bit w $ BitArith.mod_bound w n
    | Typ.Int w, (_ `S z)%exp
      => Some $ Exp.Int w $ IntArith.mod_bound w z
    | Typ.Struct false _, Exp.Lists _ vs
      => Some $ Exp.Lists Lst.Struct vs
    | _, _ => None
    end.
  
  (** Default (value) Expession. *)
  Fixpoint exp_of_typ (τ : Typ.t) : option Exp.t :=
    match τ with
    | Typ.Bool => Some $ Exp.Bool false
    | Typ.Bit w => Some $ Exp.Bit w 0%Z
    | Typ.Int w => Some $ Exp.Int w 0%Z
    | Typ.VarBit w => Some $ Exp.VarBit w w 0%Z
    | Typ.Error => Some $ Exp.Error "no error"%string
    | Typ.Array n t =>
        let^ v := exp_of_typ t in
        Exp.Lists
          (Lst.Array t)
          $ List.repeat v $ N.to_nat n
    | Typ.Struct b τs =>
        sequence
          $ List.map exp_of_typ τs
          >>| Exp.Lists
          (if b then Lst.Header false else Lst.Struct)
    | Typ.Var _ => None
    end.
  
  (** Unary Operations. *)
  Definition eval_una (op : Una.t) (e : Exp.t) : option Exp.t :=
    match op, e with
    | `!%una, (Exp.Bool b) => Some (Exp.Bool $ negb b)
    | `~%una, (w `W n)%exp => Some $ Exp.Bit w $ BitArith.bit_not w n
    | `~%una, (w `S n)%exp => Some $ Exp.Int w $ IntArith.bit_not w n
    | `-%una, (w `W z)%exp => Some $ Exp.Bit w $ BitArith.neg w z
    | `-%una, (w `S z)%exp => Some $ Exp.Int w $ IntArith.neg w z
    | Una.IsValid, Exp.Lists (Lst.Header b) _ => Some $ Exp.Bool b
    | Una.SetValidity b, Exp.Lists _ fs
      => Some $ Exp.Lists (Lst.Header b) fs
    | _, _ => None
    end.

  Local Open Scope exp_scope.
  
  (** Binary operations. *)
  Definition eval_bin
             (op : Bin.t) (v1 v2 : Exp.t) : option Exp.t :=
    match op, v1, v2 with
    | `+%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.plus_mod w n1 n2
    | `+%bin, w `S z1, _ `S z2
      => Some $ Exp.Int w $ IntArith.plus_mod w z1 z2
    | |+|%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.plus_sat w n1 n2
    | |+|%bin,  w `S z1, _ `S z2
      => Some $ Exp.Int w $ IntArith.plus_sat w z1 z2
    | `-%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.minus_mod w n1 n2
    | `-%bin, w `S z1, _ `S z2
      => Some $ Exp.Int w $ IntArith.minus_mod w z1 z2
    | |-|%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.minus_sat w n1 n2
    | |-|%bin, w `S z1, _ `S z2
      => Some $ Exp.Int w $ IntArith.minus_sat w z1 z2
    | ×%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.mult_mod w n1 n2
    | ×%bin, w `S n1, _ `S n2
      => Some $ Exp.Int w $ IntArith.mult_mod w n1 n2
    | <<%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.shift_left w n1 n2
    | <<%bin, w `S z1, _ `W z2
      => Some $ Exp.Int w $ IntArith.shift_left w z1 z2
    | >>%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.shift_right w n1 n2
    | >>%bin, w `S z1, _ `W z2
      => Some $ Exp.Int w $ IntArith.shift_right w z1 z2
    | &%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.bit_and w n1 n2
    | &%bin, w `S z1, _ `S z2
      => Some $ Exp.Int w $ IntArith.bit_and w z1 z2
    | ^%bin, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.bit_xor w n1 n2
    | ^%bin, w `S z1, _ `S z2
      => Some $ Exp.Int w $ IntArith.bit_xor w z1 z2
    | Bin.BitOr, w `W n1, _ `W n2
      => Some $ Exp.Bit w $ BitArith.bit_or w n1 n2
    | Bin.BitOr, w `S z1, _ `S z2
      => Some $ Exp.Int w $ IntArith.bit_or w z1 z2
    | ≤%bin, w `W n1, _ `W n2 => Some $ Exp.Bool (n1 <=? n2)%Z
    | ≤%bin, w `S z1, _ `S z2 => Some $ Exp.Bool (z1 <=? z2)%Z
    | `<%bin, w `W n1, _ `W n2 => Some $ Exp.Bool (n1 <? n2)%Z
    | `<%bin, w `S z1, _ `S z2 => Some $ Exp.Bool (z1 <? z2)%Z
    | ≥%bin, w `W n1, _ `W n2 => Some $ Exp.Bool (n2 <=? n1)%Z
    | ≥%bin, w `S z1, _ `S z2 => Some $ Exp.Bool (z2 <=? z1)%Z
    | `>%bin, w `W n1, _ `W n2 => Some $ Exp.Bool (n2 <? n1)%Z
    | `>%bin, w `S z1, _ `S z2 => Some $ Exp.Bool (z2 <? z1)%Z
    | `&&%bin, Exp.Bool b1, Exp.Bool b2 => Some $ Exp.Bool (b1 && b2)
    | `||%bin, Exp.Bool b1, Exp.Bool b2 => Some $ Exp.Bool (b1 || b2)
    | `==%bin, _, _ => Some $ Exp.Bool $ eqb_exp v1 v2
    | !=%bin, _, _ => Some $ Exp.Bool $ negb $ eqb_exp v1 v2
    | `++%bin, w1 `W n1, w2 `W n2
      => Some $ Exp.Bit (w1 + w2)%N $ BitArith.concat w1 w2 n1 n2
    | `++%bin, w1 `W n1, w2 `S n2
      => Some $ Exp.Bit (w1 + Npos w2)%N $ BitArith.concat w1 (Npos w2) n1 n2
    | `++%bin, w1 `S n1, w2 `S n2
      => Some $ Exp.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
    | `++%bin, w1 `S n1, w2 `W n2
      => match w2 with
        | 0%N => 
            Some $ Exp.Int w1 n1
        | Npos w2 =>
            Some
              $ Exp.Int (w1 + w2)%positive
              $ IntArith.concat (Npos w1) (Npos w2) n1 n2
        end
    | _, _, _ => None
    end.
  
  Section Edefault.
    Local Hint Constructors value : core.
    
    Lemma value_exp_of_typ : forall τ e,
        exp_of_typ τ = Some e -> value e.
    Proof.
      intro t;
        induction t using custom_typ_ind;
        intros e h; unravel in *; try discriminate;
        try (inv h; auto; assumption).
      - match_some_inv; some_inv;
          eauto using sublist.Forall_repeat.
      - destruct (sequence (map exp_of_typ ts))
          as [es |] eqn:hseq; try discriminate.
        inv h. constructor.
        rewrite <- Forall2_sequence_iff in hseq.
        rewrite <- Forall2_map_l in hseq.
        eauto using Forall2_Forall_impl_Forall.
    Qed.
  End Edefault.
  
  Section HelpersType.
    Local Hint Constructors type_exp : core.
    Local Hint Resolve type_array : core.
    Local Hint Resolve type_struct : core.
    Local Hint Resolve type_header : core.
    Local Hint Extern 0 => bit_bounded : core.
    Local Hint Extern 0 => int_bounded : core.
    Local Hint Constructors type_lst_ok : core.
    
    Import CanonicalForms.
    
    Lemma eval_slice_types : forall Δ Γ v v' τ hi lo w,
        eval_slice hi lo v = Some v' ->
        value v ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        `⟨ Δ, Γ ⟩ ⊢ v ∈ τ ->
        `⟨ Δ, Γ ⟩ ⊢ v' ∈ Typ.Bit (Npos hi - Npos lo + 1)%N.
    Proof.
      intros Δ Γ v v' τ hi lo w Heval Hv Hw Hnum Ht; inv Hnum;
        assert_canonical_forms; simpl in Heval;
        unfold "$" in Heval; inv Heval; auto.
    Qed.
    
    Local Hint Resolve BitArith.bound0 : core.
    Local Hint Resolve IntArith.bound0 : core.
    
    Lemma eval_cast_types : forall Δ Γ τ τ' v v',
        eval_cast τ' v = Some v' ->
        value v ->
        proper_cast τ τ' ->
        `⟨ Δ, Γ ⟩ ⊢ v ∈ τ ->
        `⟨ Δ, Γ ⟩ ⊢ v' ∈ τ'.
    Proof.
      intros Δ Γ τ τ' v v' Heval Hv Hpc Ht;
        inv Hpc; assert_canonical_forms; unravel in *;
        try match goal with
            | H: context [ if ?b then _ else _ ]
              |- _ => destruct b eqn:?
            end; try (inv Heval; auto 2; assumption).
      - destruct x; try (inv Heval; auto 2; assumption).
        inv Heval; auto 2.
        constructor.
        unfold BitArith.bound.
        unfold BitArith.upper_bound.
        lia.
      - destruct x; inv Heval; auto.
        destruct p; inv H1; auto.
      - destruct w; inv Heval; auto.
      - destruct w2; inv Heval; auto.
        destruct p; inv H1; auto.
      - some_inv; invert_type_lst_ok; eauto.
    Qed.
    
    Lemma eval_bin_types : forall Δ Γ op τ1 τ2 τ v1 v2 v,
        bin_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        eval_bin op v1 v2 = Some v ->
        `⟨ Δ, Γ ⟩ ⊢ v1 ∈ τ1 -> `⟨ Δ, Γ ⟩ ⊢ v2 ∈ τ2 -> `⟨ Δ, Γ ⟩ ⊢ v ∈ τ.
    Proof.
      intros Δ Γ op τ1 τ2 τ v1 v2 v Hbin Hv1 Hv2 Heval Ht1 Ht2;
        inv Hbin; unravel in *; try inv_numeric;
        repeat assert_canonical_forms;
        try (inv_numeric_width; assert_canonical_forms);
        try (inv Heval; auto 2; assumption).
    Qed.
    
    Lemma eval_member_types : forall Δ Γ x vs v ts τ,
        nth_error ts x = Some τ ->
        nth_error vs x = Some v ->
        value v ->
        Forall2 (type_exp Δ Γ) vs ts ->
        `⟨ Δ, Γ ⟩ ⊢ v ∈ τ.
    Proof.
      intros Δ Γ x vs v ts t hntht hnthv hv hvsts.
      rewrite Forall2_forall_nth_error in hvsts.
      destruct hvsts as [_ hvt]; eauto.
    Qed.
    
    Local Hint Resolve BitArith.bound0 : core.
    Local Hint Resolve IntArith.bound0 : core.
    Local Hint Constructors typ_ok : core.
    
    Lemma exp_of_typ_ok_0 : forall τ e,
        exp_of_typ τ = Some e -> typ_ok 0 τ.
    Proof.
      intro t; induction t using custom_typ_ind;
        intros e h; unravel in *;
        try match_some_inv; try some_inv;
        try discriminate; eauto.
      constructor.
      rewrite <- Forall2_sequence_iff in Heqo.
      rewrite sublist.Forall2_map1 in Heqo.
      assert (hlen: List.length ts = List.length l)
        by eauto using Forall2_length.
      pose proof Forall_specialize_Forall2
           _ _ _ _ H _ hlen as h.
      pose proof Forall2_impl _ _ _ _ _ _ h Heqo as h'.
      apply Forall2_only_l_Forall in h'; assumption.
    Qed.

    Local Hint Resolve exp_of_typ_ok_0 : core.
    Local Hint Resolve typ_ok_0 : core.
    Local Hint Resolve sublist.Forall_repeat : core.
    
    Lemma exp_of_typ_types : forall Δ Γ τ e,
        exp_of_typ τ = Some e -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ.
    Proof.
      intros Δ Γ t; induction t using custom_typ_ind;
        unravel in *; intros e h; try discriminate;
        try match_some_inv; try some_inv; eauto.
      - replace n
          with (N.of_nat (List.length (repeat t0 (N.to_nat n)))) at 2
          by (rewrite repeat_length; lia); eauto 6.
      - rename Heqo into hes; rename l into es.
        rewrite <- Forall2_sequence_iff in hes.
        rewrite <- Forall2_map_l in hes.
        assert (hlen: List.length ts = List.length es)
          by eauto using Forall2_length.
        pose proof Forall_specialize_Forall2
             _ _ _ _ H _ hlen as h; clear H hlen.
        rewrite Forall2_flip in hes, h.
        eapply Forall2_impl in hes; destruct b; eauto.
    Qed.
    
    Local Hint Resolve Forall_impl : core.
    Local Hint Resolve exp_of_typ_types : core.
    Hint Rewrite app_length.
    Hint Rewrite Forall_app.
    Hint Rewrite map_length.
    
    Lemma eval_una_types : forall Δ Γ op e v τ τ',
        una_type op τ τ' -> value e -> eval_una op e = Some v ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> `⟨ Δ, Γ ⟩ ⊢ v ∈ τ'.
    Proof.
      intros Δ Γ op e v τ τ' Huna Hev Heval Het;
        inv Huna; try inv_numeric;
        assert_canonical_forms; unravel in *;
        inv Heval; auto 2;
        repeat match goal with
                     | H: (if ?b then _ else _) = Some _
                       |- _ => destruct b as [? | ?] eqn:?
               | H: Some _ = Some _ |- _ => inv H
               end; eauto 2.
      - destruct x; discriminate || some_inv; auto.
      - inv H3; eauto.
    Qed.
  End HelpersType.
  
  Section HelpersExist.
    Import CanonicalForms.
    
    Lemma eval_slice_exists : forall Δ Γ v τ hi lo w,
        value v ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        `⟨ Δ, Γ ⟩ ⊢ v ∈ τ ->
        exists v', eval_slice hi lo v = Some v'.
    Proof.
      intros Δ Γ v τ hi lo w Hv Hw Hnum Ht;
        inv Hnum; assert_canonical_forms; unravel; eauto 2.
    Qed.
    
    Lemma eval_cast_exists : forall Δ Γ e τ τ',
        value e ->
        proper_cast τ τ' ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        exists v, eval_cast τ' e = Some v.
    Proof.
      intros ? ? ? ? ? Hv Hpc Het; inv Hpc; assert_canonical_forms;
        unravel; simpl in *; eauto 2.
      - destruct x; eauto 2.
      - destruct x; eauto 2; destruct p; eauto 2;
          try (cbv in H0; destruct H0; try destruct p; discriminate).
      - destruct w; eauto 2.
      - destruct w2; eauto 2.
        destruct p; eauto.
    Qed.
    
    Lemma eval_bin_exists : forall Δ Γ op τ1 τ2 τ v1 v2,
        bin_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        `⟨ Δ, Γ ⟩ ⊢ v1 ∈ τ1 -> `⟨ Δ, Γ ⟩ ⊢ v2 ∈ τ2 ->
        exists v, eval_bin op v1 v2 = Some v.
    Proof.
      intros Δ Γ op τ1 τ2 τ v1 v2 Hbin Hv1 Hv2 Ht1 Ht2;
        inv Hbin; try inv_numeric; try inv_numeric_width;
          repeat assert_canonical_forms; unravel; eauto 2.
    Qed.
    
    Lemma eval_una_exists : forall op Δ Γ e τ τ',
        una_type op τ τ' -> value e -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        exists v, eval_una op e = Some v.
    Proof.
      intros op Δ Γ e τ τ' Hu Hv Het; inv Hu;
        try inv_numeric; assert_canonical_forms;
        try invert_type_lst_ok; unravel; eauto 2.
    Qed.
      
    Lemma eval_member_exists : forall Δ Γ x vs ts τ,
        Forall value vs ->
        Forall2 (type_exp Δ Γ) vs ts ->
        nth_error ts x = Some τ ->
        exists v, nth_error vs x = Some v.
    Proof.
      intros Δ Γ x vs ts t hv h hnth.
      apply nth_error_exists.
      apply Forall2_length in h.
      rewrite h.
      eauto using ForallMap.nth_error_some_length.
    Qed.
  End HelpersExist.
End StepDefs.
  
(** Lookup an lvalue. *)
Fixpoint lv_lookup (ϵ : list Exp.t) (lv : Exp.t) : option Exp.t :=
  match lv with
  | Exp.Var _ _ x => nth_error ϵ x
  | Exp.Member _ x lv =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Exp.Lists
          (Lst.Struct
          | Lst.Header _) fs => nth_error fs x
      | _ => None
      end
  | Exp.Slice hi lo lv => lv_lookup ϵ lv >>= eval_slice hi lo
  | Exp.Index _ lv (Exp.Bit _ n) =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Exp.Lists (Lst.Array _) vs => nth_error vs $ Z.to_nat n
      | _ => None
      end
  | _ => None
  end.
  
(** Updating an lvalue in an environment. *)
Fixpoint lv_update (lv v : Exp.t) (ϵ : list Exp.t) : list Exp.t :=
  match lv with
  | Exp.Var _ _ x => nth_update x v ϵ
  | Exp.Member _ x lv
    => match lv_lookup ϵ lv with
      | Some
          (Exp.Lists
             ((Lst.Struct
              | Lst.Header _) as ls) vs)
        => lv_update lv (Exp.Lists ls (nth_update x v vs)) ϵ
      | _ => ϵ
      end
  | Exp.Slice hi lo lv
    => match v, lv_lookup ϵ lv with
      | (Exp.Bit _ n | Exp.Int _ n), Some (Exp.Bit w _) =>
          let rhs := N.shiftl (Z.to_N n) w in
          let mask :=
            Z.to_N
              (-1 -
                 (Z.of_N (N.lxor
                            (N.pow 2 (Npos hi + 1) - 1)
                            (N.pow 2 (Npos lo - 1))))) in
          let new := Z.lxor (Z.land n (Z.of_N mask)) (Z.of_N rhs) in
          lv_update lv (Exp.Bit w new) ϵ
      | _, _ => ϵ
      end
  | Exp.Index _ lv (Exp.Bit _ n) =>
      match lv_lookup ϵ lv with
      | Some
          (Exp.Lists
             (Lst.Array _ as ls) vs)
        => lv_update lv (Exp.Lists ls $ nth_update (Z.to_nat n) v vs) ϵ
      | _ => ϵ
      end
  | _ => ϵ
  end.

(** Create a new environment
    from a closure environment where
    values of [In] args are substituted
    into the function parameters. *)
Definition copy_in
           (argsv : Exp.args)
           (ϵcall : list Exp.t) : option (list Exp.t) :=
  argsv
    ▷ map (fun arg =>
             match arg with
             | PAIn v     => Some v
             | PAOut lv
             | PAInOut lv => lv_lookup ϵcall lv
             end)
    ▷ sequence.

(** Update call-site environment with
    out variables from function call evaluation. *)
Definition copy_out
           (argsv : Exp.args) (ϵ_func : list Exp.t)
           (ϵ_call : list Exp.t) : list Exp.t :=
  fold_right
    (fun arg ϵ_call =>
       match arg with
       | PAIn _ => ϵ_call
       | PAOut lv
       | PAInOut lv
         => match lv_lookup ϵ_func lv with
           | None   => ϵ_call
           | Some v => lv_update lv v ϵ_call
           end
       end) ϵ_call argsv.
