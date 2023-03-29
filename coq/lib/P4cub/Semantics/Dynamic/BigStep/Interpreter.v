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

  Definition to_bit (v : Val.v) : option (N * Z) :=
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

  (** [interpret_expr e] is [Some v] iff [⟨ ϵ, e ⟩ ⇓ v], or [None] if [e] is
      ill-typed *)
  Fixpoint interpret_expr (e : Expr.e) : option Val.v :=
    match e with
    | Expr.Bool b => mret $ Val.Bool b
    | Expr.Bit w n => mret $ Val.Bit w n
    | Expr.Int w n => mret $ Val.Int w n
    | Expr.Var _ _ index => nth_error ϵ index
    | Expr.VarBit m w n => mret $ Val.VarBit m w n
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
      let* (_, index) := to_bit =<< interpret_expr index in
      interpret_index array index
    | Expr.Member _ field member => index field =<< interpret_expr member
    | Expr.Error err => mret $ Val.Error err
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
    - simpl. unfold option_bind, interpret_index, index, to_bit. intros.
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

    Fixpoint interpret_lexpr (e : Expr.e) : option Val.lv :=
      match e with
      | Expr.Var _ _ x => mret $ Val.Var x
      | Expr.Slice hi lo e => interpret_lexpr e >>| Val.Slice hi lo
      | Expr.Member _ x e => interpret_lexpr e >>| Val.Member x
      | Expr.Index _ e1 e2 =>
        let* lv := interpret_lexpr e1 in
        let^ (_, n) := to_bit =<< interpret_expr e2 in
        Val.Index (Z.to_N n) lv
      | _ => None
      end.

    Lemma interpret_lexpr_sound :
      forall e lv, interpret_lexpr e = Some lv -> l⟨ ϵ , e ⟩ ⇓ lv.
    Proof.
      induction e; try discriminate; intros; inv H; unfold option_bind in *.
      - constructor.
      - destruct (interpret_lexpr e) eqn:?; try discriminate. inv H1.
        constructor. auto.
      - unfold to_bit in *.
        destruct (interpret_lexpr e1); try discriminate.
        destruct (interpret_expr e2) eqn:?; try discriminate.
        destruct v; try discriminate.
        inv H1. econstructor; eauto. 
        apply interpret_expr_sound. eauto.
      - destruct (interpret_lexpr e); try discriminate.
        inv H1. constructor. auto.
    Qed.

    Lemma interpret_lexpr_complete :
      forall e lv, l⟨ ϵ , e ⟩ ⇓ lv -> interpret_lexpr e = Some lv.
    Proof.
      intros. induction H; cbn; unfold option_bind in *.
      - reflexivity.
      - destruct (interpret_lexpr e); try discriminate.
        f_equal. inv IHlexpr_big_step. auto.
      - destruct (interpret_lexpr e); try discriminate.
        f_equal. inv IHlexpr_big_step. auto.
      - unfold to_bit. destruct (interpret_lexpr e₁) eqn:?; try discriminate.
        apply interpret_expr_complete in H.
        destruct (interpret_expr e₂); try discriminate.
        destruct v; try discriminate.
        inv H. inv IHlexpr_big_step. auto.
    Qed.

    Lemma interpret_lexpr_adequate : forall e lv, 
      interpret_lexpr e = Some lv <-> l⟨ ϵ , e ⟩ ⇓ lv.
    Proof.
      split.
      - apply interpret_lexpr_sound.
      - apply interpret_lexpr_complete.
    Qed.

    Definition interpret_parser_expr (pat : Parser.pt) : option Parser.state_label :=
      match pat with
      | Parser.Direct st => mret st
      | Parser.Select e default cases =>
        let^ v := interpret_expr e in
        match Field.find_value (fun p => match_pattern p v) cases with
        | Some st => st
        | None => default
        end
      end.

    Lemma interpret_parser_expr_sound :
      forall pat state, interpret_parser_expr pat = Some state -> p⟨ ϵ , pat ⟩ ⇓ state.
    Proof.
      intros. destruct pat; inv H.
      - constructor.
      - unfold option_bind in *.
        destruct (interpret_expr discriminee) eqn:?; try discriminate.
        inv H1. constructor. apply interpret_expr_sound. assumption.
    Qed.

    Lemma interpret_parser_expr_complete :
      forall pat state, p⟨ ϵ , pat ⟩ ⇓ state -> interpret_parser_expr pat = Some state.
    Proof.
      intros. inv H; cbn.
      - reflexivity.
      - unfold option_bind in *.
        apply interpret_expr_complete in H0.
        destruct (interpret_expr e) eqn:?; try discriminate.
        inv H0. reflexivity. 
    Qed.

    Lemma interpret_parser_expr_adequate :
      forall pat state, interpret_parser_expr pat = Some state <-> p⟨ ϵ , pat ⟩ ⇓ state.
    Proof.
      split.
      - apply interpret_parser_expr_sound.
      - apply interpret_parser_expr_complete.
    Qed.

End Expr.

Definition interpret_table_entry (entry : table_entry (Expression := Expr.e)) : option (Parser.pat * action_ref) :=
  let 'mk_table_entry matches action_ref := entry in
  let^ pats := unembed_valsets matches in
  (Parser.Lists pats, action_ref).

Lemma interpret_table_entry_sound :
  forall entry pat action_ref,
    interpret_table_entry entry = Some (pat, action_ref) -> table_entry_big_step entry pat action_ref.
Proof.
  unfold interpret_table_entry. intros. destruct entry.
  cbn in *. unfold option_bind in *.
  destruct (unembed_valsets matches) eqn:HSome; try discriminate. inv H.
  constructor. apply unembed_valsets_sound. assumption.
Qed.
