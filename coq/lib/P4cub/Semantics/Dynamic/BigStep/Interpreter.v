From Coq Require Import NArith.BinNat ZArith.BinInt ssr.ssrbool.

From Poulet4 Require Import
  Monads.Monad
  P4cub.Syntax.Syntax
  P4cub.Syntax.CubNotations
  P4cub.Semantics.Dynamic.BigStep.ExprUtil
  P4cub.Semantics.Dynamic.BigStep.Semantics
  P4cub.Semantics.Dynamic.BigStep.Value.Value
  P4cub.Semantics.Dynamic.BigStep.Value.Embed
  P4light.Architecture.Target
  Utils.Util.ListUtil.

Import Option String.

Local Open Scope type_scope.

Section Exp.

  (** Binds variables' de Bruijn indices to their values *)
  Variable ϵ : list Val.t.

  Definition to_bit (v : Val.t) : option (N * Z) :=
    match v with
    | Val.Bit w n => Some (w, n)
    | _ => None
    end.

  Definition index idx array :=
    match array with
    | Val.Lists _ vs => nth_error vs idx
    | _ => None
    end.

  Definition interpret_index array n := index (Z.to_nat n) array.

  (** [interpret_exp e] is [Some v] iff [⟨ ϵ, e ⟩ ⇓ v], or [None] if [e] is
      ill-typed *)
  Fixpoint interpret_exp (e : Exp.t) : option Val.t :=
    match e with
    | Exp.Bool b => mret $ Val.Bool b
    | Exp.Bit w n => mret $ Val.Bit w n
    | Exp.Int w n => mret $ Val.Int w n
    | Exp.Var _ _ index => nth_error ϵ index
    | Exp.VarBit m w n => mret $ Val.VarBit m w n
    | Exp.Slice hi lo e => slice_val hi lo =<< interpret_exp e
    | Exp.Cast t e => eval_cast t =<< interpret_exp e
    | Exp.Uop _ op e => eval_una op =<< interpret_exp e
    | Exp.Bop _ op e1 e2 =>
      let* v1 := interpret_exp e1 in
      let* v2 := interpret_exp e2 in
      eval_bin op v1 v2
    | Exp.Lists ls es => map_monad interpret_exp es >>| Val.Lists ls
    | Exp.Index _ array index =>
      let* array := interpret_exp array in
      let* (_, index) := to_bit =<< interpret_exp index in
      interpret_index array index
    | Exp.Member _ field member => index field =<< interpret_exp member
    | Exp.Error err => mret $ Val.Error err
    end.

  Theorem interpret_exp_sound : 
    forall e v, interpret_exp e = Some v -> ⟨ ϵ, e ⟩ ⇓ v.
  Proof.
    induction e using custom_exp_ind.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor. assumption.
    - simpl. unfold option_bind. intros. option_solve. econstructor; eauto.
    - simpl. unfold option_bind. intros. option_solve. econstructor; eauto.
    - simpl. unfold option_bind. intros. option_solve. econstructor; eauto.
    - simpl. unfold option_bind. intros. repeat option_solve. econstructor; eauto.
    - simpl. unfold option_bind, map_monad, "∘". intros.
      option_solve E. inv H0.
      apply sequence_Forall2 in E. apply Forall2_map_comm_fwd in E.
      constructor. generalize dependent l0.
      induction es; intros; inv H; inv E; constructor; auto.
    - simpl. unfold option_bind, interpret_index, index, to_bit. intros.
      destruct (interpret_exp e1);
      destruct (interpret_exp e2);
      try discriminate.
      destruct t; destruct t0; try discriminate.
      econstructor; eauto.
    - simpl. unfold option_bind, index. intros.
      repeat option_solve. destruct t; try discriminate.
      econstructor; eauto.
    - intros. unravel in *. inv H. constructor.
    Qed.

    Theorem interpret_exp_complete :
      forall e v, ⟨ ϵ, e ⟩ ⇓ v -> interpret_exp e = Some v.
    Proof.
      induction e using custom_exp_ind.
      - intros. inv H. reflexivity.
      - intros. inv H. reflexivity.
      - intros. inv H. reflexivity.
      - intros. inv H. reflexivity.
      - intros. inv H. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_exp e); apply IHe in H5; try discriminate.
        inv H5. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_exp e); apply IHe in H4; try discriminate.
        inv H4. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_exp e); apply IHe in H5; try discriminate.
        inv H5. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_exp e1); apply IHe1 in H6;
        destruct (interpret_exp e2); apply IHe2 in H7;
        try discriminate. inv H6. inv H7. assumption.
      - intros. simpl. unfold option_bind, map_monad, "∘".
        inv H0. destruct (sequence (map interpret_exp es)) eqn:E.
        + apply sequence_Forall2 in E.
          apply Forall2_map_comm_fwd in E.
          repeat f_equal.
          generalize dependent vs.
          generalize dependent l0.
          induction es; intros;
          inv E; inv H; inv H4; auto.
          apply H3 in H1. assert (Some y0 = Some y).
          { rewrite <- H1. rewrite H2. reflexivity. }
          inv H. f_equal. auto.
        + assert (sequence (map interpret_exp es) <> Some vs).
          { rewrite E. discriminate. }
          clear E.
          apply (contra_not (Forall2_sequence (map interpret_exp es) vs)) in H0.
          exfalso. apply H0. clear H0. apply Forall2_map_comm_rev.
          generalize dependent vs. induction es; intros;
          inv H4; constructor. inv H; auto. inv H.
          apply IHes with (vs := l') in H4; assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_exp e1); apply IHe1 in H5; try discriminate.
        destruct (interpret_exp e2); apply IHe2 in H6; try discriminate.
        inv H5. inv H6. simpl. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_exp e); apply IHe in H5; try discriminate.
        inv H5. simpl. assumption.
      - intros. inv H. reflexivity.
    Qed.

    Lemma interpret_exp_adequate :
      forall e v, interpret_exp e = Some v <-> ⟨ ϵ, e ⟩ ⇓ v.
    Proof.
      split.
      - apply interpret_exp_sound.
      - apply interpret_exp_complete.
    Qed.

    Fixpoint interpret_lexp (e : Exp.t) : option Lval.t :=
      match e with
      | Exp.Var _ _ x => mret $ Lval.Var x
      | Exp.Slice hi lo e => interpret_lexp e >>| Lval.Slice hi lo
      | Exp.Member _ x e => interpret_lexp e >>| Lval.Member x
      | Exp.Index _ e1 e2 =>
        let* lv := interpret_lexp e1 in
        let^ (_, n) := to_bit =<< interpret_exp e2 in
        Lval.Index (Z.to_N n) lv
      | _ => None
      end.

    Lemma interpret_lexp_sound :
      forall e lv, interpret_lexp e = Some lv -> l⟨ ϵ , e ⟩ ⇓ lv.
    Proof.
      induction e; try discriminate; intros; inv H; unfold option_bind in *.
      - constructor.
      - option_solve ?. inv H1. constructor. auto.
      - unfold to_bit in *.
        option_solve. destruct (interpret_exp e2) eqn:?; try discriminate.
        destruct t0; try discriminate.
        inv H1. econstructor; eauto. 
        apply interpret_exp_sound. eauto.
      - option_solve. inv H1. constructor. auto.
    Qed.

    Lemma interpret_lexp_complete :
      forall e lv, l⟨ ϵ , e ⟩ ⇓ lv -> interpret_lexp e = Some lv.
    Proof.
      intros. induction H; cbn; unfold option_bind in *.
      - reflexivity.
      - destruct (interpret_lexp e); try discriminate.
        f_equal. inv IHlexp_big_step. auto.
      - destruct (interpret_lexp e); try discriminate.
        f_equal. inv IHlexp_big_step. auto.
      - unfold to_bit. destruct (interpret_lexp e₁) eqn:?; try discriminate.
        apply interpret_exp_complete in H.
        destruct (interpret_exp e₂); try discriminate.
        destruct t0; try discriminate.
        inv H. inv IHlexp_big_step. auto.
    Qed.

    Lemma interpret_lexp_adequate : forall e lv, 
      interpret_lexp e = Some lv <-> l⟨ ϵ , e ⟩ ⇓ lv.
    Proof.
      split.
      - apply interpret_lexp_sound.
      - apply interpret_lexp_complete.
    Qed.

    Definition interpret_parser_exp (pat : Trns.t) : option Lbl.t :=
      match pat with
      | Trns.Direct st => mret st
      | Trns.Select e default cases =>
        let^ v := interpret_exp e in
        match Field.find_value (fun p => match_pattern p v) cases with
        | Some st => st
        | None => default
        end
      end.

    Lemma interpret_parser_exp_sound :
      forall pat state, interpret_parser_exp pat = Some state -> p⟨ ϵ , pat ⟩ ⇓ state.
    Proof.
      intros. destruct pat; inv H.
      - constructor.
      - unfold option_bind in *. option_solve ?.
        inv H1. constructor. apply interpret_exp_sound. assumption.
    Qed.

    Lemma interpret_parser_exp_complete :
      forall pat state, p⟨ ϵ , pat ⟩ ⇓ state -> interpret_parser_exp pat = Some state.
    Proof.
      intros. inv H; cbn.
      - reflexivity.
      - unfold option_bind in *.
        apply interpret_exp_complete in H0.
        destruct (interpret_exp e) eqn:?; try discriminate.
        inv H0. reflexivity. 
    Qed.

    Lemma interpret_parser_exp_adequate :
      forall pat state, interpret_parser_exp pat = Some state <-> p⟨ ϵ , pat ⟩ ⇓ state.
    Proof.
      split.
      - apply interpret_parser_exp_sound.
      - apply interpret_parser_exp_complete.
    Qed.

End Exp.

Definition interpret_table_entry (entry : table_entry (Expression := Exp.t)) : option (Pat.t * action_ref) :=
  let 'mk_table_entry matches action_ref := entry in
  let^ pats := unembed_valsets matches in
  (Pat.Lists pats, action_ref).

Lemma interpret_table_entry_sound :
  forall entry pat action_ref,
    interpret_table_entry entry = Some (pat, action_ref) -> table_entry_big_step entry pat action_ref.
Proof.
  unfold interpret_table_entry. intros. destruct entry.
  cbn in *. unfold option_bind in *.
  option_solve HSome. inv H.
  constructor. apply unembed_valsets_sound. assumption.
Qed.
