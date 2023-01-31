Require Import
  Coq.ZArith.BinInt
  Coq.ssr.ssrbool
  Poulet4.Monads.Monad
  Poulet4.P4cub.Syntax.Syntax
  Poulet4.P4cub.Syntax.CubNotations
  Poulet4.P4cub.Semantics.Dynamic.BigStep.Semantics
  Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Value
  Poulet4.Utils.Util.ListUtil
  Poulet4.P4cub.Semantics.Dynamic.BigStep.ExprUtil.

Import
  Option
  Val.ValueNotations
  ExprNotations
  ParserNotations
  Val.LValueNotations
  StmtNotations
  String.

Local Open Scope type_scope.

Section Expr.

  (** Binds variables' de Bruijn indices to their values *)
  Variable ϵ : list Val.v.

  Definition index idx array :=
    match array with
    | Val.Lists _ vs => nth_error vs idx
    | _ => None
    end.

  Definition interpret_index array idx :=
    match idx with
    | Val.Bit _ n => index (Z.to_nat n) array
    | _ => None
    end.

  (** [interpret_expr e] is [Some v] iff [⟨ ϵ, e ⟩ ⇓ v], or [None] if [e] is
      ill-typed *)
  Fixpoint interpret_expr (e : Expr.e) : option Val.v :=
    match e with
    | Expr.Bool b => mret (Val.Bool b)
    | Expr.Bit w n => mret (Val.Bit w n)
    | Expr.Int w n => mret (Val.Int w n)
    | Expr.Var _ _ index => nth_error ϵ index
    | Expr.VarBit m w n => mret (Val.VarBit m w n)
    | Expr.Slice hi lo e => slice_val hi lo =<< interpret_expr e
    | Expr.Cast t e => eval_cast t =<< interpret_expr e
    | Expr.Uop _ op e => eval_uop op =<< interpret_expr e
    | Expr.Bop _ op e1 e2 =>
      let* v1 := interpret_expr e1 in
      let* v2 := interpret_expr e2 in
      eval_bop op v1 v2
    | Expr.Lists ls es => map_monad interpret_expr es >>| Val.Lists ls
    | Expr.Index _ array index =>
      let* array := interpret_expr array in
      let* index := interpret_expr index in
      interpret_index array index
    | Expr.Member _ field member => index field =<< interpret_expr member
    | Expr.Error err => mret (Val.Error err)
    end.

  Theorem interpret_expr_sound : 
    forall e v, interpret_expr e = Some v -> ⟨ ϵ, e ⟩ ⇓ v.
  Proof.
    induction e using custom_e_ind.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor. assumption.
    - simpl. unfold option_bind. intros.
      destruct (interpret_expr e); try discriminate.
      econstructor; eauto.
    - simpl. unfold option_bind. intros.
      destruct (interpret_expr e); try discriminate.
      econstructor; eauto.
    - simpl. unfold option_bind. intros.
      destruct (interpret_expr e); try discriminate.
      econstructor; eauto.
    - simpl. unfold option_bind. intros.
      destruct (interpret_expr e1); try discriminate.
      destruct (interpret_expr e2); try discriminate.
      econstructor; eauto.
    - simpl. unfold option_bind, map_monad, "∘". intros.
      destruct (sequence (map interpret_expr exps)) eqn:E; try discriminate.
      inv H0.
      apply sequence_Forall2 in E.
      apply Forall2_map_comm_fwd in E.
      constructor. generalize dependent l0.
      induction exps; intros; inv H; inv E; constructor; auto.
    - simpl. unfold option_bind, interpret_index, index. intros.
      destruct (interpret_expr e1);
      destruct (interpret_expr e2);
      try discriminate.
      destruct v1; destruct v0; try discriminate.
      econstructor; eauto.
    - simpl. unfold option_bind, index. intros.
      destruct (interpret_expr e); try discriminate.
      destruct v0; try discriminate.
      econstructor; eauto.
    - intros. inv H. constructor.
    Qed.

    Theorem interpret_expr_complete :
      forall e v, ⟨ ϵ, e ⟩ ⇓ v -> interpret_expr e = Some v.
    Proof.
      induction e using custom_e_ind.
      - intros. inv H. reflexivity.
      - intros. inv H. reflexivity.
      - intros. inv H. reflexivity.
      - intros. inv H. reflexivity.
      - intros. inv H. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_expr e); apply IHe in H5; try discriminate.
        inv H5. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_expr e); apply IHe in H4; try discriminate.
        inv H4. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_expr e); apply IHe in H5; try discriminate.
        inv H5. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_expr e1); apply IHe1 in H6;
        destruct (interpret_expr e2); apply IHe2 in H7;
        try discriminate. inv H6. inv H7. assumption.
      - intros. simpl. unfold option_bind, map_monad, "∘".
        inv H0. destruct (sequence (map interpret_expr exps)) eqn:E.
        + apply sequence_Forall2 in E.
          apply Forall2_map_comm_fwd in E.
          repeat f_equal.
          generalize dependent vs.
          generalize dependent l0.
          induction exps; intros;
          inv E; inv H; inv H4; auto.
          apply H3 in H1. assert (Some y0 = Some y).
          { rewrite <- H1. rewrite H2. reflexivity. }
          inv H. f_equal. auto.
        + assert (sequence (map interpret_expr exps) <> Some vs).
          { rewrite E. discriminate. }
          clear E.
          apply (contra_not (Forall2_sequence (map interpret_expr exps) vs)) in H0.
          exfalso. apply H0. clear H0. apply Forall2_map_comm_rev.
          generalize dependent vs. induction exps; intros;
          inv H4; constructor. inv H; auto. inv H.
          apply IHexps with (vs := l') in H4; assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_expr e1); apply IHe1 in H5; try discriminate.
        destruct (interpret_expr e2); apply IHe2 in H6; try discriminate.
        inv H5. inv H6. simpl. assumption.
      - intros. inv H. simpl. unfold option_bind.
        destruct (interpret_expr e); apply IHe in H5; try discriminate.
        inv H5. simpl. assumption.
      - intros. inv H. reflexivity.
    Qed.

    Lemma interpret_expr_adequate :
      forall e v, interpret_expr e = Some v <-> ⟨ ϵ, e ⟩ ⇓ v.
    Proof.
      split.
      - apply interpret_expr_sound.
      - apply interpret_expr_complete.
    Qed.

End Expr.
