Require Import Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Poulet4.P4cub.Semantics.Static.Util
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.IndPrincip
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Auxilary
        Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat
        Poulet4.Utils.ForallMap Coq.micromega.Lia.
Import (*String ProperType*) Val ValueNotations
       LValueNotations.

Reserved Notation "'⊢ᵥ' V ∈ τ"
         (at level 80, no associativity).

Reserved Notation "Γ '⊢ₗ' LV ∈ τ"
         (at level 80, no associativity).

Local Open Scope value_scope.

Inductive type_value : v -> Expr.t -> Prop :=
| typ_bool (b : bool) :  ⊢ᵥ b ∈ Expr.TBool
| typ_bit w n :
  BitArith.bound w n ->
  ⊢ᵥ w VW n ∈ Expr.TBit w
| typ_int w z :
  IntArith.bound w z ->
  ⊢ᵥ (Npos w) VS z ∈ Expr.TInt (Npos w)
| typ_struct vs ts ob b :
  match ob, b with
  | Some _, true
  | None, false => True
  | _, _ => False
  end ->
  Forall2 type_value vs ts ->
  ⊢ᵥ Struct vs ob ∈ Expr.TStruct ts b
| typ_error err :
  ⊢ᵥ Error err ∈ Expr.TError
where "'⊢ᵥ' V ∈ τ" := (type_value V τ) : type_scope.

(** Custom induction for value typing. *)
Section ValueTypingInduction.
  (** Arbitrary predicate. *)
  Variable P : v -> Expr.t -> Prop.
  
  Hypothesis HBool : forall b, P (Bool b) Expr.TBool.
  
  Hypothesis HBit : forall w n,
      BitArith.bound w n ->
      P (w VW n) (Expr.TBit w).
  
  Hypothesis HInt : forall w z,
      IntArith.bound w z ->
      P ((Npos w) VS z) (Expr.TInt (Npos w)).

  Hypothesis HError : forall err,
      P (Error err) Expr.TError.
    
  Hypothesis HStruct : forall vs ts ob b,
      match ob, b with
      | Some _, true
      | None, false => True
      | _, _ => False
      end ->
      Forall2 type_value vs ts ->
      Forall2 P vs ts ->
      P (Struct vs ob) (Expr.TStruct ts b).

  (** Custom induction principle.
      Do [induction ?H using custom_type_value_ind]. *)
  Definition custom_type_value_ind :
    forall (V : v) (τ : Expr.t),
      ⊢ᵥ V ∈ τ -> P V τ :=
    fix tvind V τ Hy :=
      let fix lind {vs : list v}
              {ts : list Expr.t}
              (HR : Forall2 type_value vs ts)
        : Forall2 P vs ts :=
        match HR with
        | Forall2_nil _ => Forall2_nil _
        | Forall2_cons _ _ Hh Ht
          => Forall2_cons _ _ (tvind _ _ Hh) (lind Ht)
        end in
      match Hy with
      | typ_bool b => HBool b
      | typ_bit _ _ H => HBit _ _ H
      | typ_int _ _ H => HInt _ _ H
      | typ_error err => HError err
      | typ_struct _ _ _ _ H Hfs => HStruct _ _ _ _ H Hfs (lind Hfs)
      end.
End ValueTypingInduction.

Inductive type_lvalue (Γ : expr_type_env) : lv -> Expr.t -> Prop :=
| typ_var (x : string) (τ : Expr.t) :
    Γ x = Some τ ->
    t_ok Δ τ ->
    LL Δ, Γ ⊢ VAR x ∈ τ
| typ_slice (lval : lv) (hi lo : positive) (w : N) (τ : Expr.t) :
    (Npos lo <= Npos hi < w)%N ->
    numeric_width w τ ->
    LL Δ, Γ ⊢ lval ∈ τ ->
    let w' := Npos (hi - lo + 1)%positive in
    LL Δ, Γ ⊢ SLICE lval [hi:lo] ∈ bit<w'>
| typ_member (lval : lv) (x : string) (τ τ' : Expr.t) (ts : F.fs string Expr.t) :
    F.get x ts = Some τ' ->
    member_type ts τ ->
    t_ok Δ τ ->
    t_ok Δ τ' ->
    LL Δ, Γ ⊢ lval ∈ τ ->
    LL Δ, Γ ⊢ lval DOT x ∈ τ'
| typ_access (lval : lv) (idx : Z)
             (n : positive) (ts : F.fs string Expr.t) :
    (0 <= idx < Zpos n)%Z ->
    t_ok Δ Expr.Tstack ts[n] }} ->
    LL Δ, Γ ⊢ lval ∈ stack ts[n] ->
    LL Δ, Γ ⊢ ACCESS lval[idx] ∈ hdr { ts }
where "'LL' Δ , Γ ⊢ lval ∈ τ" := (type_lvalue Δ Γ lval τ).

Require Import Poulet4.P4cub.Semantics.Static.Static.

Section Lemmas.
  Import F.FieldTactics.
  
  Local Hint Resolve BitArith.bound0 : core.
  Local Hint Resolve IntArith.bound0 : core.
  Local Hint Resolve proper_inside_header_nesting : core.
  Local Hint Constructors type_value : core.
  Local Hint Constructors proper_nesting : core.
  Hint Rewrite repeat_length.
  Hint Rewrite Pos2Nat.id : core.
  
  Lemma vdefault_types : forall τ val,
      proper_nesting τ ->
      vdefault τ = Some val ->
      ∇  ⊢ val ∈ τ.
  Proof.
    intros t val HPN; generalize dependent val.
    induction t using custom_t_ind;
      intros val HV; unravel in *;
        try invert_proper_nesting; inv HV; auto.
    - destruct (sequence (map vdefault ts)) as [vs |] eqn:Heqvs; inv H2.
      constructor.
      rewrite Forall_forall in H, H1.
      pose proof reduce_inner_impl_forall
           _ _ _ _ H H1 as H'; cbn in *.
      apply forall_Forall2 with (bs := vs) in H'.
      + apply sequence_Forall2 in Heqvs.
        rewrite Forall2_flip.
        rewrite <- ForallMap.Forall2_map_l in Heqvs.
        pose proof Forall2_impl
             _ _ (fun t v => vdefault t = Some v) (fun t v => ∇ ⊢ v ∈ t)
          as HF2impl; cbn in *; auto.
      + apply sequence_length in Heqvs.
        rewrite map_length in Heqvs; auto.
    - destruct
        (sequence
           (map (fun '(x, t) => match vdefault t with
                             | Some a => Some (x, a)
                             | None => None
                             end) fields))
        as [xvs |] eqn:Heqxvs; inv H2.
      unfold F.predfs_data, F.predf_data in *; unravel in *.
      constructor.
      rewrite Forall_forall in H, H1.
      pose proof reduce_inner_impl_forall
           _ _ _ _ H H1 as H'; cbn in *.
      apply forall_Forall2 with (bs := map snd xvs) in H'.
      + apply sequence_Forall2 in Heqxvs.
        unfold Field.relfs, Field.relf; unravel.
        rewrite map_pat_both in Heqxvs.
        rewrite <- ForallMap.Forall2_map_l in Heqxvs.
        rewrite Forall2_destr_pair_eq in Heqxvs.
        destruct Heqxvs as [Hfst Hsnd].
        rewrite Forall2_conj; split; unfold Field.f.
        * rewrite Forall2_map_both, Forall2_eq; auto.
        * rewrite Forall2_map_both.
          rewrite Forall2_flip in H', Hsnd.
          pose proof Forall2_map_r _ _ _
               (fun v t => vdefault t = Some v -> ∇ ⊢ v ∈ t)
               snd (map snd xvs) fields as H''; cbn in *.
          rewrite H'' in H'; clear H''.
          pose proof Forall2_impl
               _ _ (fun v t => vdefault t = Some v) type_value
            as HF2impl; cbn in *; auto.
      + apply sequence_length in Heqxvs.
        rewrite map_length in Heqxvs.
        rewrite map_length; auto.
    - destruct
        (sequence
           (map (fun '(x, t) => match vdefault t with
                             | Some a => Some (x, a)
                             | None => None
                             end) fields))
        as [xvs |] eqn:Heqxvs; inv H2.
      unfold F.predfs_data, F.predf_data in *; unravel in *.
      constructor; auto.
      rewrite Forall_forall in H, H1.
      pose proof reduce_inner_impl_forall_impl
           _ _ _ _ _
           (fun xv => proper_inside_header_nesting (snd xv))
           H H1 as H'; cbn in *.
      apply forall_Forall2 with (bs := map snd xvs) in H'.
      + apply sequence_Forall2 in Heqxvs.
        unfold Field.relfs, Field.relf; unravel.
        rewrite map_pat_both in Heqxvs.
        rewrite <- ForallMap.Forall2_map_l in Heqxvs.
        rewrite Forall2_destr_pair_eq in Heqxvs.
        destruct Heqxvs as [Hfst Hsnd].
        rewrite Forall2_conj; split; unfold Field.f.
        * rewrite Forall2_map_both, Forall2_eq; auto.
        * rewrite Forall2_map_both.
          rewrite Forall2_flip in H', Hsnd.
          pose proof Forall2_map_r _ _ _
               (fun v t => vdefault t = Some v -> ∇ ⊢ v ∈ t)
               snd (map snd xvs) fields as H''; cbn in *.
          rewrite H'' in H'; clear H''.
          pose proof Forall2_impl
               _ _ (fun v t => vdefault t = Some v) type_value
            as HF2impl; cbn in *; auto.
      + apply sequence_length in Heqxvs.
        rewrite map_length in Heqxvs.
        rewrite map_length; auto.
    - destruct
        (sequence
           (map (fun '(x, t) => match vdefault t with
                             | Some a => Some (x, a)
                             | None => None
                             end) fields))
        as [xvs |] eqn:Heqxvs; inv H1.
      unfold F.predfs_data, F.predf_data in *; unravel in *.
      assert (Hsize : size =
                      Pos.of_nat
                        (length (repeat (false, xvs) (Pos.to_nat size))))
        by (autorewrite with core; lia).
      rewrite Hsize at 2;
        constructor; autorewrite with core; auto; try lia.
      apply repeat_Forall; simpl.
      constructor; auto; unfold Field.relfs, Field.relf; unravel.
      rewrite Forall_forall in H, H3.
      pose proof reduce_inner_impl_forall_impl
           _ _ _ _ _
           (fun xv => proper_inside_header_nesting (snd xv))
           H H3 as H'; cbn in *.
      apply forall_Forall2 with (bs := map snd xvs) in H'.
      + apply sequence_Forall2 in Heqxvs.
        unfold Field.relfs, Field.relf; unravel.
        rewrite map_pat_both in Heqxvs.
        rewrite <- ForallMap.Forall2_map_l in Heqxvs.
        rewrite Forall2_destr_pair_eq in Heqxvs.
        destruct Heqxvs as [Hfst Hsnd].
        rewrite Forall2_conj; split; unfold Field.f.
        * rewrite Forall2_map_both, Forall2_eq; auto.
        * rewrite Forall2_map_both.
          rewrite Forall2_flip in H', Hsnd.
          pose proof Forall2_map_r _ _ _
               (fun v t => vdefault t = Some v -> ∇ ⊢ v ∈ t)
               snd (map snd xvs) fields as H''; cbn in *.
          rewrite H'' in H'; clear H''.
          pose proof Forall2_impl
               _ _ (fun v t => vdefault t = Some v) type_value
            as HF2impl; cbn in *; auto.
      + apply sequence_length in Heqxvs.
        rewrite map_length in Heqxvs.
        rewrite map_length; auto.
  Qed.

  Lemma approx_type_typing : forall  V T,
      ∇  ⊢ V ∈ T -> approx_type V = T.
  Proof.
    intros  V T H;
      induction H using custom_type_value_ind;
      unravel; auto.
    - f_equal; induction H; inv H0;
        unravel; subst; f_equal; auto.
    - f_equal; induction H; inv H0;
        repeat relf_destruct;
        unravel; subst; f_equal; auto.
    - clear H; f_equal;
        induction H0; inv H1;
          repeat relf_destruct;
          unravel; subst; f_equal; auto.
      (* XXX broken due to missing size in header stack *)
  Admitted.
  
  Local Hint Constructors check_expr : core.
  Local Hint Resolve approx_type_typing : core.
  Local Hint Constructors proper_nesting : core.
  Hint Rewrite map_length : core. 
  
  Lemma expr_of_value_types {tags_t : Type} :
    forall  V T,
      ∇  ⊢ V ∈ T ->
      forall i : tags_t,
        let e := expr_of_value i V in
        ⟦ [] , ∅ ⟧ ⊢ e ∈ T.
  Proof.
    intros  V T Hvt;
      induction Hvt using custom_type_value_ind;
      intros i e; subst e; unravel in *; eauto. (*
    - constructor; induction H;
        inv H0; unravel in *; auto.
    - constructor.
      unfold F.relfs in *.
      induction H; inv H0;
        repeat relf_destruct; subst;
          unravel in *; intuition.
      constructor;
        unfold F.relf; unravel; eauto.
    - constructor; auto; clear H.
      unfold F.relfs in *.
      induction H0; inv H1;
        try predf_destruct;
        repeat relf_destruct; subst;
          unravel in *; intuition.
      constructor;
        unfold F.relf; unravel; eauto.
    - constructor;
        autorewrite with core; auto.
      clear n ni H H0 H1 H2.
      ind_list_Forall; unravel;
        repeat inv_Forall_cons; auto.
      destruct a; constructor; auto. *)
  Admitted.
End Lemmas.
