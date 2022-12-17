Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Dynamic.SmallStep.Value
        Poulet4.P4cub.Semantics.Climate Poulet4.Utils.P4Arith
        Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Coq.Arith.Compare_dec Coq.micromega.Lia
        Poulet4.P4cub.Semantics.Static.Static
        Poulet4.Utils.ForallMap Poulet4.Monads.Option.

Section StepDefs.
  Import String P4ArithTactics AllCubNotations.
  
  (** Bit-slicing. *)
  Definition eval_slice (hi lo : positive) (v : Expr.e) : option Expr.e :=
    match v with
    | (_ `W z)%expr
    | (_ `S z)%expr
      => let w' := (Npos hi - Npos lo + 1)%N in
        Some $ Expr.Bit w'
             (BitArith.mod_bound
                w' $ BitArith.bitstring_slice z hi lo)
    | _ => None
    end.
  
  Definition eval_cast
             (target : Expr.t) (v : Expr.e) : option Expr.e :=
    match target, v with
    | Expr.TBit (Npos 1), Expr.Bool true => Some $ Expr.Bit 1%N 1%Z
    | Expr.TBit (Npos 1), Expr.Bool false => Some $ Expr.Bit 1%N 0%Z
    | Expr.TBool, Expr.Bit 1%N 1%Z=> Some $ Expr.Bool true
    | Expr.TBool, Expr.Bit 1%N 0%Z=> Some $ Expr.Bool true
    | Expr.TBit w, (_ `S z)%expr
      => Some $ Expr.Bit w $ BitArith.mod_bound w z
    | Expr.TInt w, (_ `W n)%expr
      => Some $ Expr.Int w $ IntArith.mod_bound w n
    | Expr.TBit w, (_ `W n)%expr
      => Some $ Expr.Bit w $ BitArith.mod_bound w n
    | Expr.TInt w, (_ `S z)%expr
      => Some $ Expr.Int w $ IntArith.mod_bound w z
    | Expr.TStruct false _, Expr.Lists _ vs
      => Some $ Expr.Lists Expr.lists_struct vs
    | _, _ => None
    end.
  
  (** Default (value) Expression. *)
  Fixpoint e_of_t (τ : Expr.t) : option Expr.e :=
    match τ with
    | Expr.TBool => Some $ Expr.Bool false
    | Expr.TBit w => Some $ Expr.Bit w 0%Z
    | Expr.TInt w => Some $ Expr.Int w 0%Z
    | Expr.TVarBit w => Some $ Expr.VarBit w w 0%Z
    | Expr.TError => Some $ Expr.Error "no error"%string
    | Expr.TArray n t =>
        let^ v := e_of_t t in
        Expr.Lists
          (Expr.lists_array t)
          $ List.repeat v $ N.to_nat n
    | Expr.TStruct b τs =>
        sequence
          $ List.map e_of_t τs
          >>| Expr.Lists
          (if b then Expr.lists_header false else Expr.lists_struct)
    | Expr.TVar _ => None
    end.
  
  (** Unary Operations. *)
  Definition eval_uop (op : Expr.uop) (e : Expr.e) : option Expr.e :=
    match op, e with
    | `!%uop, (Expr.Bool b) => Some (Expr.Bool $ negb b)
    | `~%uop, (w `W n)%expr => Some $ Expr.Bit w $ BitArith.bit_not w n
    | `~%uop, (w `S n)%expr => Some $ Expr.Int w $ IntArith.bit_not w n
    | `-%uop, (w `W z)%expr => Some $ Expr.Bit w $ BitArith.neg w z
    | `-%uop, (w `S z)%expr => Some $ Expr.Int w $ IntArith.neg w z
    | Expr.IsValid, Expr.Lists (Expr.lists_header b) _ => Some $ Expr.Bool b
    | Expr.SetValidity b, Expr.Lists _ fs
      => Some $ Expr.Lists (Expr.lists_header b) fs
    | _, _ => None
    end.

  Local Open Scope expr_scope.
  
  (** Binary operations. *)
  Definition eval_bop
             (op : Expr.bop) (v1 v2 : Expr.e) : option Expr.e :=
    match op, v1, v2 with
    | `+%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.plus_mod w n1 n2
    | `+%bop, w `S z1, _ `S z2
      => Some $ Expr.Int w $ IntArith.plus_mod w z1 z2
    | |+|%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.plus_sat w n1 n2
    | |+|%bop,  w `S z1, _ `S z2
      => Some $ Expr.Int w $ IntArith.plus_sat w z1 z2
    | `-%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.minus_mod w n1 n2
    | `-%bop, w `S z1, _ `S z2
      => Some $ Expr.Int w $ IntArith.minus_mod w z1 z2
    | |-|%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.minus_sat w n1 n2
    | |-|%bop, w `S z1, _ `S z2
      => Some $ Expr.Int w $ IntArith.minus_sat w z1 z2
    | ×%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.mult_mod w n1 n2
    | ×%bop, w `S n1, _ `S n2
      => Some $ Expr.Int w $ IntArith.mult_mod w n1 n2
    | <<%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.shift_left w n1 n2
    | <<%bop, w `S z1, _ `W z2
      => Some $ Expr.Int w $ IntArith.shift_left w z1 z2
    | >>%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.shift_right w n1 n2
    | >>%bop, w `S z1, _ `W z2
      => Some $ Expr.Int w $ IntArith.shift_right w z1 z2
    | &%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.bit_and w n1 n2
    | &%bop, w `S z1, _ `S z2
      => Some $ Expr.Int w $ IntArith.bit_and w z1 z2
    | ^%bop, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.bit_xor w n1 n2
    | ^%bop, w `S z1, _ `S z2
      => Some $ Expr.Int w $ IntArith.bit_xor w z1 z2
    | Expr.BitOr, w `W n1, _ `W n2
      => Some $ Expr.Bit w $ BitArith.bit_or w n1 n2
    | Expr.BitOr, w `S z1, _ `S z2
      => Some $ Expr.Int w $ IntArith.bit_or w z1 z2
    | ≤%bop, w `W n1, _ `W n2 => Some $ Expr.Bool (n1 <=? n2)%Z
    | ≤%bop, w `S z1, _ `S z2 => Some $ Expr.Bool (z1 <=? z2)%Z
    | `<%bop, w `W n1, _ `W n2 => Some $ Expr.Bool (n1 <? n2)%Z
    | `<%bop, w `S z1, _ `S z2 => Some $ Expr.Bool (z1 <? z2)%Z
    | ≥%bop, w `W n1, _ `W n2 => Some $ Expr.Bool (n2 <=? n1)%Z
    | ≥%bop, w `S z1, _ `S z2 => Some $ Expr.Bool (z2 <=? z1)%Z
    | `>%bop, w `W n1, _ `W n2 => Some $ Expr.Bool (n2 <? n1)%Z
    | `>%bop, w `S z1, _ `S z2 => Some $ Expr.Bool (z2 <? z1)%Z
    | `&&%bop, Expr.Bool b1, Expr.Bool b2 => Some $ Expr.Bool (b1 && b2)
    | `||%bop, Expr.Bool b1, Expr.Bool b2 => Some $ Expr.Bool (b1 || b2)
    | `==%bop, _, _ => Some $ Expr.Bool $ eqbe v1 v2
    | !=%bop, _, _ => Some $ Expr.Bool $ negb $ eqbe v1 v2
    | `++%bop, w1 `W n1, w2 `W n2
      => Some $ Expr.Bit (w1 + w2)%N $ BitArith.concat w1 w2 n1 n2
    | `++%bop, w1 `W n1, w2 `S n2
      => Some $ Expr.Bit (w1 + Npos w2)%N $ BitArith.concat w1 (Npos w2) n1 n2
    | `++%bop, w1 `S n1, w2 `S n2
      => Some $ Expr.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
    | `++%bop, w1 `S n1, w2 `W n2
      => match w2 with
        | 0%N => 
            Some $ Expr.Int w1 n1
        | Npos w2 =>
            Some
              $ Expr.Int (w1 + w2)%positive
              $ IntArith.concat (Npos w1) (Npos w2) n1 n2
        end
    | _, _, _ => None
    end.
  
  Section Edefault.
    Local Hint Constructors value : core.
    
    Lemma value_e_of_t : forall τ e,
        e_of_t τ = Some e -> value e.
    Proof.
      intro t;
        induction t using custom_t_ind;
        intros e h; unravel in *; try discriminate;
        try (inv h; auto; assumption).
      - match_some_inv; some_inv;
          eauto using sublist.Forall_repeat.
      - destruct (sequence (map e_of_t ts))
          as [es |] eqn:hseq; try discriminate.
        inv h. constructor.
        rewrite <- Forall2_sequence_iff in hseq.
        rewrite <- Forall2_map_l in hseq.
        eauto using Forall2_Forall_impl_Forall.
    Qed.
  End Edefault.
  
  Section HelpersType.
    Local Hint Constructors type_expr : core.
    Local Hint Resolve type_array : core.
    Local Hint Resolve type_struct : core.
    Local Hint Resolve type_header : core.
    Local Hint Extern 0 => bit_bounded : core.
    Local Hint Extern 0 => int_bounded : core.
    Local Hint Constructors type_lists_ok : core.
    
    Import CanonicalForms.
    
    Lemma eval_slice_types : forall Δ Γ v v' τ hi lo w,
        eval_slice hi lo v = Some v' ->
        value v ->
        (Npos lo <= Npos hi < w)%N ->
        numeric_width w τ ->
        `⟨ Δ, Γ ⟩ ⊢ v ∈ τ ->
        `⟨ Δ, Γ ⟩ ⊢ v' ∈ Expr.TBit (Npos hi - Npos lo + 1)%N.
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
      - some_inv; invert_type_lists_ok; eauto.
    Qed.
    
    Lemma eval_bop_types : forall Δ Γ op τ1 τ2 τ v1 v2 v,
        bop_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        eval_bop op v1 v2 = Some v ->
        `⟨ Δ, Γ ⟩ ⊢ v1 ∈ τ1 -> `⟨ Δ, Γ ⟩ ⊢ v2 ∈ τ2 -> `⟨ Δ, Γ ⟩ ⊢ v ∈ τ.
    Proof.
      intros Δ Γ op τ1 τ2 τ v1 v2 v Hbop Hv1 Hv2 Heval Ht1 Ht2;
        inv Hbop; unravel in *; try inv_numeric;
        repeat assert_canonical_forms;
        try (inv_numeric_width; assert_canonical_forms);
        try (inv Heval; auto 2; assumption).
    Qed.
    
    Lemma eval_member_types : forall Δ Γ x vs v ts τ,
        nth_error ts x = Some τ ->
        nth_error vs x = Some v ->
        value v ->
        Forall2 (type_expr Δ Γ) vs ts ->
        `⟨ Δ, Γ ⟩ ⊢ v ∈ τ.
    Proof.
      intros Δ Γ x vs v ts t hntht hnthv hv hvsts.
      rewrite Forall2_forall_nth_error in hvsts.
      destruct hvsts as [_ hvt]; eauto.
    Qed.
    
    Local Hint Resolve BitArith.bound0 : core.
    Local Hint Resolve IntArith.bound0 : core.
    Local Hint Constructors t_ok : core.
    
    Lemma e_of_t_ok_0 : forall τ e,
        e_of_t τ = Some e -> t_ok 0 τ.
    Proof.
      intro t; induction t using custom_t_ind;
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

    Local Hint Resolve e_of_t_ok_0 : core.
    Local Hint Resolve t_ok_0 : core.
    Local Hint Resolve sublist.Forall_repeat : core.
    
    Lemma e_of_t_types : forall Δ Γ τ e,
        e_of_t τ = Some e -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ.
    Proof.
      intros Δ Γ t; induction t using custom_t_ind;
        unravel in *; intros e h; try discriminate;
        try match_some_inv; try some_inv; eauto.
      - replace n
          with (N.of_nat (List.length (repeat e0 (N.to_nat n)))) at 2
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
    Local Hint Resolve e_of_t_types : core.
    Hint Rewrite app_length.
    Hint Rewrite Forall_app.
    Hint Rewrite map_length.
    
    Lemma eval_uop_types : forall Δ Γ op e v τ τ',
        uop_type op τ τ' -> value e -> eval_uop op e = Some v ->
        `⟨ Δ, Γ ⟩ ⊢ e ∈ τ -> `⟨ Δ, Γ ⟩ ⊢ v ∈ τ'.
    Proof.
      intros Δ Γ op e v τ τ' Huop Hev Heval Het;
        inv Huop; try inv_numeric;
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
    
    Lemma eval_bop_exists : forall Δ Γ op τ1 τ2 τ v1 v2,
        bop_type op τ1 τ2 τ ->
        value v1 -> value v2 ->
        `⟨ Δ, Γ ⟩ ⊢ v1 ∈ τ1 -> `⟨ Δ, Γ ⟩ ⊢ v2 ∈ τ2 ->
        exists v, eval_bop op v1 v2 = Some v.
    Proof.
      intros Δ Γ op τ1 τ2 τ v1 v2 Hbop Hv1 Hv2 Ht1 Ht2;
        inv Hbop; try inv_numeric; try inv_numeric_width;
          repeat assert_canonical_forms; unravel; eauto 2.
    Qed.
    
    Lemma eval_uop_exists : forall op Δ Γ e τ τ',
        uop_type op τ τ' -> value e -> `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
        exists v, eval_uop op e = Some v.
    Proof.
      intros op Δ Γ e τ τ' Hu Hv Het; inv Hu;
        try inv_numeric; assert_canonical_forms;
        try invert_type_lists_ok; unravel; eauto 2.
    Qed.
      
    Lemma eval_member_exists : forall Δ Γ x vs ts τ,
        Forall value vs ->
        Forall2 (type_expr Δ Γ) vs ts ->
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
Fixpoint lv_lookup (ϵ : list Expr.e) (lv : Expr.e) : option Expr.e :=
  match lv with
  | Expr.Var _ _ x => nth_error ϵ x
  | Expr.Member _ x lv =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Expr.Lists
          (Expr.lists_struct
          | Expr.lists_header _) fs => nth_error fs x
      | _ => None
      end
  | Expr.Slice hi lo lv => lv_lookup ϵ lv >>= eval_slice hi lo
  | Expr.Index _ lv (Expr.Bit _ n) =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Expr.Lists (Expr.lists_array _) vs => nth_error vs $ Z.to_nat n
      | _ => None
      end
  | _ => None
  end.
  
(** Updating an lvalue in an environment. *)
Fixpoint lv_update (lv v : Expr.e) (ϵ : list Expr.e) : list Expr.e :=
  match lv with
  | Expr.Var _ _ x => nth_update x v ϵ
  | Expr.Member _ x lv
    => match lv_lookup ϵ lv with
      | Some
          (Expr.Lists
             ((Expr.lists_struct
              | Expr.lists_header _) as ls) vs)
        => lv_update lv (Expr.Lists ls (nth_update x v vs)) ϵ
      | _ => ϵ
      end
  | Expr.Slice hi lo lv
    => match v, lv_lookup ϵ lv with
      | (Expr.Bit _ n | Expr.Int _ n), Some (Expr.Bit w _) =>
          let rhs := N.shiftl (Z.to_N n) w in
          let mask :=
            Z.to_N
              (-1 -
                 (Z.of_N (N.lxor
                            (N.pow 2 (Npos hi + 1) - 1)
                            (N.pow 2 (Npos lo - 1))))) in
          let new := Z.lxor (Z.land n (Z.of_N mask)) (Z.of_N rhs) in
          lv_update lv (Expr.Bit w new) ϵ
      | _, _ => ϵ
      end
  | Expr.Index _ lv (Expr.Bit _ n) =>
      match lv_lookup ϵ lv with
      | Some
          (Expr.Lists
             (Expr.lists_array _ as ls) vs)
        => lv_update lv (Expr.Lists ls $ nth_update (Z.to_nat n) v vs) ϵ
      | _ => ϵ
      end
  | _ => ϵ
  end.

(** Create a new environment
    from a closure environment where
    values of [In] args are substituted
    into the function parameters. *)
Definition copy_in
           (argsv : Expr.args)
           (ϵcall : list Expr.e) : option (list Expr.e) :=
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
           (argsv : Expr.args) (ϵ_func : list Expr.e)
           (ϵ_call : list Expr.e) : list Expr.e :=
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
