Require Import Coq.NArith.BinNat Coq.ZArith.BinInt
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
        Poulet4.P4cub.Semantics.Climate Poulet4.Utils.P4Arith
        Poulet4.P4cub.Semantics.Dynamic.BigStep.ExprUtil
        Poulet4.P4light.Semantics.Ops Poulet4.Utils.ForallMap.

Local Open Scope val_scope.
Local Open Scope lval_scope.
  

(** Environments for
    evaluation are De Bruijn lists of vals [Val.v].
    Lookup is done via l-vals [Val.lv]. *)

(** Lookup an lval. *)
Fixpoint lv_lookup (ϵ : list Val.t) (lv : Lval.t) : option Val.t :=
  match lv with
  | Lval.Var x => nth_error ϵ x
  | Lval.Slice hi lo lv =>
      let* v := lv_lookup ϵ lv in
      match v with
      | w VW n =>
          let bits := to_lbool w n in
          let bits' := bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi) in
          let (w',n') := BitArith.from_lbool bits' in
          Some $ w' VW n'
      | w VS z =>
          let bits := to_lbool (Npos w) z in
          let bits' := bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi) in
          let (w',z') := BitArith.from_lbool bits' in
          Some $ w' VW z'
      | _ => None
      end
  | lv DOT x =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Val.Lists _ vs => nth_error vs x
      | _ => None
      end
  | Lval.Index n lv =>
      let* v := lv_lookup ϵ lv in
      match v with
      | Val.Lists _ vs => nth_error vs $ N.to_nat n
      | _ => None
      end
  end.

(** Updating an lval in an environment. *)
Fixpoint lv_update
         (lv : Lval.t) (v : Val.t)
         (ϵ : list Val.t) : list Val.t :=
  match lv with
  | Lval.Var x => nth_update x v ϵ
  | Lval.Slice hi lo lv =>
      match v, lv_lookup ϵ lv with
      | wz VW z, Some (wn VW n) =>
          let bits := to_lbool wn n in
          let bits' := to_lbool wz z in
          let bits'' := update_bitstring bits (Pos.to_nat lo) (Pos.to_nat hi) bits' in
          lv_update lv (wn VW (snd $ BitArith.from_lbool bits'')) ϵ
      | wz VW z, Some (wn VS n) =>
          let bits := to_lbool (Npos wn) n in
          let bits' := to_lbool wz z in
          let bits'' := update_bitstring bits (Pos.to_nat lo) (Pos.to_nat hi) bits' in
          lv_update lv (wn VS (snd $ IntArith.from_lbool bits'')) ϵ
      | _, _ => ϵ
      end
  | lv DOT x =>
    match lv_lookup ϵ lv with
    | Some
        (Val.Lists ls vs)
      => lv_update lv (Val.Lists ls $ nth_update x v vs) ϵ
    | _ => ϵ
    end
  | Lval.Index n lv =>
      match lv_lookup ϵ lv with
      | Some
          (Val.Lists ls vs)
        => lv_update lv (Val.Lists ls $ nth_update (N.to_nat n) v vs) ϵ
      | _ => ϵ
      end
  end.

(** Get initial values for out parameters for copy in. *)
Definition get_out_inits (out_args : list Exp.t) : option (list Val.t) :=
  sequence $ map val_of_typ $ map typ_of_exp $ out_args.

Lemma get_out_inits_length : forall out_args out_inits,
    get_out_inits out_args = Some out_inits -> length out_args = length out_inits.
Proof.
  intros es vs h.
  unfold get_out_inits in h.
  unravel in h.
  rewrite <- Forall2_sequence_iff in h.
  apply Forall2_length in h.
  do 2 rewrite map_length in h.
  assumption.
Qed.

(** Update call-site environment with
    out values from function call evaluation. *)
Definition copy_out
  (lvs : list Lval.t) (vs ϵ_call : list Val.t)  : list Val.t :=
  List.fold_right (uncurry lv_update) ϵ_call (combine lvs vs).

Lemma copy_out_nil : forall ϵ,
    copy_out [] [] ϵ = ϵ.
Proof. intro eps; reflexivity. Qed.

Lemma copy_out_cons : forall lv lvs v vs ϵ,
    copy_out (lv :: lvs) (v :: vs) ϵ = lv_update lv v (copy_out lvs vs ϵ).
Proof. intros lv lvs v vs eps; reflexivity. Qed.

Section Properties.
  Local Hint Constructors type_val : core.
  Local Hint Constructors Static.Util.type_lst_ok : core.
  
  Lemma lv_update_length : forall lv v ϵ,
      length (lv_update lv v ϵ) = length ϵ.
  Proof.
    intro lv;
      induction lv; intros v eps; simpl.
    - rewrite nth_update_length; reflexivity.
    - destruct v; auto;
        destruct (lv_lookup eps lv) eqn:hlook; auto;
        destruct t; auto.
    - destruct (lv_lookup eps lv) eqn:hlook; auto.
      destruct t; auto.
    - destruct (lv_lookup eps lv) eqn:hlook; auto.
      destruct t; auto.
  Qed.

  Local Hint Rewrite lv_update_length : core.
  
  Lemma copy_out_length : forall lvs vs ϵ,
      length (copy_out lvs vs ϵ) = length ϵ.
  Proof using.
    intros lvs vs ϵ.
    unfold copy_out.
    remember (combine lvs vs) as lvvs.
    clear dependent lvs. clear vs.
    induction lvvs as [| [lv v] lvvs ih]; cbn;
      autorewrite with core; auto.
  Qed.

  Local Hint Rewrite Zcomplements.Zlength_correct : core.
  Local Hint Rewrite nat_to_Z_to_N : core.
  Local Hint Rewrite @bitstring_slice_length : core.
  Local Hint Rewrite Nnat.Nat2N.inj_add : core.
  Local Hint Rewrite Nnat.Nat2N.inj_sub : core.
  Local Hint Rewrite Znat.positive_nat_N : core.
  Local Hint Rewrite Zlength_to_lbool : core.
  Local Hint Rewrite rev_length : core.
  Local Hint Rewrite @bitstring_slice'_length : core.
  Local Hint Rewrite length_to_lbool : core.
  Local Hint Rewrite length_to_lbool' : core.
  Local Hint Rewrite N.add_0_r : core.
  Local Hint Rewrite plus_n_O : core.
  
  Lemma lv_lookup_types : forall lv τ v Γ ϵ,
      Forall2 type_val ϵ Γ ->
      Γ ⊢l lv ∈ τ ->
      lv_lookup ϵ lv = Some v ->
      ⊢ᵥ v ∈ τ.
  Proof.
    intros lv t v g eps henv hlvt;
      generalize dependent v.
    induction hlvt; intros v hv; cbn in * |-.
    - rewrite ForallMap.Forall2_forall_nth_error in henv.
      firstorder.
    - unravel in hv.
      destruct (lv_lookup eps LV) as [V |] eqn:Veq;
        cbn in * |-; try discriminate.
      pose proof IHhlvt _ eq_refl as ihv; clear IHhlvt.
      inv H0; inv ihv; cbn in * |-; inv hv;
        do 2 autorewrite with core in *;
        try lia; constructor.
      + pose proof BitArith.from_lbool_bound as h.
        unfold BitArith.from_lbool in h.
        specialize h with
          (bitstring_slice (to_lbool w n) (Pos.to_nat lo) (Pos.to_nat hi)).
        autorewrite with core in h;
          autorewrite with core in |-*;
          unfold uncurry in h;
          assumption || lia.
      + pose proof BitArith.from_lbool_bound as h.
        unfold BitArith.from_lbool in h.
        specialize h with
          (bitstring_slice (to_lbool (Npos w0) z) (Pos.to_nat lo) (Pos.to_nat hi)).
        unfold bitstring_slice,to_lbool in h.
        autorewrite with core in h;
          autorewrite with core in |-*;
          unfold uncurry in h;
          assumption || lia.
    - destruct (lv_lookup eps LV) as [V |] eqn:Veq;
        cbn in *; try discriminate.
      destruct V; cbn in *; try discriminate.
      pose proof IHhlvt _ eq_refl as ih; clear IHhlvt; inv ih.
      inv H2; eauto using ExprUtil.eval_member_types.
    - destruct (lv_lookup eps lv) as [V |] eqn:Veq;
        cbn in *; try discriminate.
      destruct V; cbn in *; try discriminate.
      pose proof IHhlvt _ eq_refl as ih; clear IHhlvt; inv ih.
      inv H2; unravel in *.
      apply Forall2_repeat_r_Forall in H4.
      rewrite Forall_forall in H4.
      eauto using nth_error_In.
  Qed.
  
  Local Hint Resolve nth_update_length : core.
  Local Hint Resolve lv_lookup_types : core.
  Arguments N.sub : simpl never.
  
  Lemma lv_update_correct : forall lv v v' ϵ τ Γ,
      Forall2 type_val ϵ Γ ->
      Γ ⊢l lv ∈ τ ->
      ⊢ᵥ v ∈ τ ->
      ⊢ᵥ v' ∈ τ ->
      lv_lookup ϵ lv = Some v' ->
      lv_lookup (lv_update lv v ϵ) lv = Some v.
  Proof.
    intros lv v v' eps t g h hlv;
      generalize dependent v';
      generalize dependent v;
      generalize dependent eps.
    induction hlv; intros eps henv v v' hv hv' h; simpl in *.
    - apply nth_update_correct.
      eauto using ForallMap.nth_error_some_length.
    - unfold option_bind in h.
      destruct (lv_lookup eps LV) as [V |] eqn:hlook;
        cbn in *; try discriminate.
      inv hv; inv hv';
        try match goal with
          | h: Util.type_lst_ok _ _ _ |- _ => inv h
          end.
      assert (⊢ᵥ V ∈ τ) as hVt by eauto.
      destruct V as [ | q z | q z | q z | |]; unravel in *; try discriminate; some_inv;
        inv hVt; inv H0;
        autorewrite with core in *;
        autorewrite with core in |-*; try lia;
        erewrite IHhlv; eauto;
        autorewrite with core;
        autorewrite with core in |-*; try lia.
      + do 2 f_equal. admit.
      + constructor. admit.
      + do 2 f_equal. admit.
      + constructor. admit.
    - destruct (lv_lookup eps LV) as [V |] eqn:hlook;
        cbn in *; try discriminate.
      destruct V; try discriminate.
      pose proof lv_lookup_types
           _ _ _ _ _ henv hlv hlook as h'.
      inv h'; inv H2; unravel;
        erewrite IHhlv; clear IHhlv; eauto;
        rename τs0 into ts;
        try (rewrite nth_update_correct; eauto using nth_error_some_length).
      + econstructor; eauto. eauto using Forall2_nth_update_r.
  Admitted.
End Properties.

Local Close Scope val_scope.
Local Close Scope lval_scope.
