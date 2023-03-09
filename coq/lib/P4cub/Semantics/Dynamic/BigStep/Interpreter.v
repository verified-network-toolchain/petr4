From Coq Require Import NArith.BinNat ZArith.BinInt ssr.ssrbool.

From RecordUpdate Require Import RecordSet.

From Poulet4 Require Import
  Monads.Monad
  P4cub.Syntax.Syntax
  P4cub.Syntax.CubNotations
  P4cub.Semantics.Dynamic.BigStep.ExprUtil
  P4cub.Semantics.Dynamic.BigStep.Value.Value
  P4cub.Semantics.Dynamic.BigStep.Value.Embed
  P4cub.Semantics.Dynamic.BigStep.Semantics
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

    Definition interpret_exprs := map_monad interpret_expr.

    Lemma interpret_exprs_sound :
      forall es vs, interpret_exprs es = Some vs -> Forall2 (expr_big_step ϵ) es vs.
    Proof.
      unfold interpret_exprs. intros. rewrite map_monad_some in H. generalize dependent vs.
      induction es.
      - intros. inv H. constructor.
      - intros. inv H. constructor; auto. apply interpret_expr_sound. assumption.
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

Section Parser.

  Variable ϵ : list Val.v.

  Open Scope pat_scope.

  Definition interpret_pre_match (e : @MatchPreT unit) : option Parser.pat :=
    match e with
    | MatchDontCare => mret $ Parser.Wild
    | MatchMask l1 l2 =>
        let* (w1, n1) := to_bit =<< interpret_expr [] =<< unembed_expr l1 in
        let* (w2, n2) := to_bit =<< interpret_expr [] =<< unembed_expr l2 in
        guard (N.eqb w1 w2) ;;
        mret $ Parser.Mask (w1 PW n1) (w2 PW n2)
    | MatchRange l1 l2 =>
        let* (w1, n1) := to_bit =<< interpret_expr [] =<< unembed_expr l1 in
        let* (w2, n2) := to_bit =<< interpret_expr [] =<< unembed_expr l2 in
        guard (N.eqb w1 w2) ;;
        mret $ Parser.Range (w1 PW n1) (w2 PW n2)
    | _ => None
    end.

  Lemma interpret_pre_match_sound :
    forall e pat, interpret_pre_match e = Some pat -> pre_match_big_step e pat.
  Proof.
    intros. destruct e; try discriminate.
    - inv H. constructor.
    - inv H. unfold option_bind in *.
      destruct (unembed_expr expr) eqn:?; try discriminate.
      destruct (interpret_expr [] e) eqn:?; try discriminate.
      unfold to_bit in *.
      destruct v; try discriminate.
      destruct (unembed_expr mask) eqn:?; try discriminate.
      destruct (interpret_expr [] e0) eqn:?; try discriminate.
      destruct v; try discriminate.
      destruct (width =? width0)%N eqn:?; try discriminate.
      cbn in *. apply N.eqb_eq in Heqb. subst.
      inv H1. apply unembed_expr_sound in Heqo, Heqo1.
      apply interpret_expr_sound in Heqo0, Heqo2. econstructor; eauto.
    - inv H. unfold option_bind in *.
      destruct (unembed_expr lo) eqn:?; try discriminate.
      destruct (interpret_expr [] e) eqn:?; try discriminate.
      unfold to_bit in *.
      destruct v; try discriminate.
      destruct (unembed_expr hi) eqn:?; try discriminate.
      destruct (interpret_expr [] e0) eqn:?; try discriminate.
      destruct v; try discriminate.
      destruct (width =? width0)%N eqn:?; try discriminate.
      cbn in *. apply N.eqb_eq in Heqb. subst.
      inv H1. apply unembed_expr_sound in Heqo, Heqo1.
      apply interpret_expr_sound in Heqo0, Heqo2. econstructor; eauto.
  Qed.

  Definition interpret_actions_of_ctx ctx :=
    match ctx with
    | CAction a => mret a
    | CApplyBlock _ aa _ => mret aa
    | _ => None
    end.

  Lemma interpret_actions_of_ctx_sound :
    forall ctx actions,
      interpret_actions_of_ctx ctx = Some actions -> actions_of_ctx ctx actions.
  Proof.
    intros. destruct ctx; try discriminate; inv H; constructor.
  Qed.

  Lemma interpret_actions_of_ctx_complete :
    forall ctx actions,
      actions_of_ctx ctx actions -> interpret_actions_of_ctx ctx = Some actions.
  Proof.
    intros. inv H; auto.
  Qed.

  Lemma interpret_pre_match_complete :
    forall e pat, pre_match_big_step e pat -> interpret_pre_match e = Some pat.
  Proof.
    intros. inv H.
    - auto.
    - apply unembed_expr_complete in H0, H1.
      apply interpret_expr_complete in H2, H3.
      cbn. unfold option_bind.
      destruct (unembed_expr l₁) eqn:?; try discriminate.
      destruct (unembed_expr l₂) eqn:?; try discriminate.
      inv H0. inv H1.
      destruct (interpret_expr [] e₁); try discriminate.
      destruct (interpret_expr [] e₂); try discriminate.
      inv H2. inv H3.
      destruct (to_bit (w) VW (n₁)%value) eqn:?; try discriminate. destruct p.
      destruct (to_bit (w) VW (n₂)%value) eqn:?; try discriminate. destruct p.
      cbn in *. inv Heqo1. inv Heqo2.
      assert ((n0 =? n0)%N = true).
      { rewrite N.eqb_eq. reflexivity. }
      replace ((n0 =? n0)%N) with true. cbn. f_equal.
    - apply unembed_expr_complete in H0, H1.
      apply interpret_expr_complete in H2, H3.
      cbn. unfold option_bind.
      destruct (unembed_expr l₁) eqn:?; try discriminate.
      destruct (unembed_expr l₂) eqn:?; try discriminate.
      inv H0. inv H1.
      destruct (interpret_expr [] e₁); try discriminate.
      destruct (interpret_expr [] e₂); try discriminate.
      inv H2. inv H3.
      destruct (to_bit (w) VW (n₁)%value) eqn:?; try discriminate. destruct p.
      destruct (to_bit (w) VW (n₂)%value) eqn:?; try discriminate. destruct p.
      cbn in *. inv Heqo1. inv Heqo2.
      assert ((n0 =? n0)%N = true).
      { rewrite N.eqb_eq. reflexivity. }
      replace ((n0 =? n0)%N) with true. cbn. f_equal.
  Qed.

  Lemma interpret_pre_match_adequate :
    forall e pat, interpret_pre_match e = Some pat <-> pre_match_big_step e pat.
  Proof.
    split.
    - apply interpret_pre_match_sound.
    - apply interpret_pre_match_complete.
  Qed.

  Close Scope pat_scope.

  Definition interpret_match (e : @Match unit) : option Parser.pat :=
    let 'MkMatch tt e _ := e in
    interpret_pre_match e.

  Lemma interpret_match_sound :
    forall e pat, interpret_match e = Some pat -> match_big_step e pat.
  Proof.
    intros. unfold interpret_match in *. destruct e, tags.
    econstructor. apply interpret_pre_match_sound. assumption.
  Qed.

  Lemma interpret_match_complete :
    forall e pat, match_big_step e pat -> interpret_match e = Some pat.
  Proof.
    intros. inv H. apply interpret_pre_match_complete in H0. auto.
  Qed.

  Lemma interpret_match_adequate :
    forall e pat, interpret_match e = Some pat <-> match_big_step e pat.
  Proof.
    split.
    - apply interpret_match_sound.
    - apply interpret_match_complete.
  Qed.

  Definition interpret_table_entry {tags_t : Type} (entry : @table_entry unit tags_t) : option (Parser.pat * action_ref) :=
    let 'mk_table_entry matches action := entry in
    let^ patterns := map_monad interpret_match matches in
    (Parser.Lists patterns, action).

  Lemma interpret_table_entry_sound :
    forall entry pat action,
      interpret_table_entry entry = Some (pat, action) -> table_entry_big_step entry pat action.
  Proof.
    unfold interpret_table_entry. cbn. unfold option_bind.
    destruct entry. intros. 
    destruct (map_monad interpret_match matches) eqn:?; try discriminate.
    inv H. econstructor. generalize dependent matches.
    induction l; unfold map_monad, "∘" in *; intros.
    - rewrite sequence_nil in Heqo. apply map_eq_nil in Heqo. subst. constructor.
    - destruct matches. inv Heqo. cbn in *.
      unfold option_bind in *. 
      destruct (interpret_match m) eqn:?; try discriminate.
      destruct (sequence (map interpret_match matches)) eqn:?; try discriminate.
      inv Heqo. constructor; auto. apply interpret_match_sound. assumption.
  Qed.

  Lemma interpret_table_entry_complete :
    forall entry pat action,
      table_entry_big_step entry pat action -> interpret_table_entry entry = Some (pat, action).
  Proof.
    intros. inv H. cbn. unfold option_bind. induction H0.
    - auto.
    - destruct (map_monad interpret_match l) eqn:?; try discriminate.
      inv IHForall2. cbn. unfold option_bind. apply interpret_match_complete in H.
      destruct (interpret_match x); try discriminate. inv H.
      unfold map_monad, "∘" in *. rewrite Heqo. f_equal.
  Qed.

  Lemma interpret_table_entry_adequate :
    forall entry pat action,
      interpret_table_entry entry = Some (pat, action) <-> table_entry_big_step entry pat action.
  Proof.
    split.
    - apply interpret_table_entry_sound.
    - apply interpret_table_entry_complete.
  Qed.

  Definition get_final_state (state : Parser.state_label) : option signal :=
    match state with
    | Parser.Accept => mret Acpt
    | Parser.Reject => mret Rjct
    | _ => None
    end.

  Lemma get_final_state_sound :
    forall state sig,
      get_final_state state = Some sig -> final_state state sig.
  Proof.
    intros. destruct state.
    - discriminate.
    - inv H. constructor.
    - inv H. constructor.
    - inv H.
  Qed.

  Lemma get_final_state_complete :
  forall state sig,
    final_state state sig -> get_final_state state = Some sig.
Proof.
  intros. destruct state.
  - inv H.
  - inv H. reflexivity.
  - inv H. constructor.
  - inv H.
Qed.

  Lemma intermediate_iff_not_final :
    forall lbl, intermediate_state lbl <-> ~ exists sig, final_state lbl sig.
  Proof.
    split; intros.
    - inv H; unfold "~"; intros; inv H; inv H0.
    - unfold "~" in H. destruct lbl.
      + constructor.
      + exfalso. apply H. exists Acpt. constructor.
      + exfalso. apply H. exists Rjct. constructor.
      + constructor.
  Qed.

  Definition is_intermediate_state (state : Parser.state_label) :=
    match state with
    | Parser.Start | Parser.Name _ => true
    | _ => false
    end.

  Lemma is_intermediate_state_sound :
    forall state,
      is_intermediate_state state = true -> intermediate_state state.
  Proof.
    unfold is_intermediate_state.
    intros. destruct state; try discriminate; constructor.
  Qed.

End Parser.

Section Stmt.

  Context {ext_sem : Extern_Sem}.

  Definition interpret_relop {A B : Type} (f : A -> option B) (x : option A) : option (option B) :=
    match x with
    | None => mret None
    | Some x => f x >>| Some
    end.

  Definition interpret_return Ψ ϵ e :=
    let^ v := interpret_relop (interpret_expr ϵ) e in
    (ϵ, Rtrn v , extrn_state Ψ).

  Inductive Fuel :=
    | NoFuel
    | MoreFuel (t : Fuel).

  Definition interpret_assign Ψ ϵ e1 e2 :=
    let* lv := interpret_lexpr ϵ e1 in
    let^ v := interpret_expr ϵ e2 in
    (lv_update lv v ϵ, Cont, extrn_state Ψ).

  Lemma interpret_assign_sound :
    forall Ψ ϵ ϵ' c e₁ e₂ sig ψ, 
      interpret_assign Ψ ϵ e₁ e₂ = Some (ϵ', sig, ψ) ->
        ⧼ Ψ, ϵ, c, Stmt.Assign e₁ e₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
  Proof.
    cbn. unfold option_bind. intros.
    destruct (interpret_lexpr ϵ e₁) eqn:E; try discriminate.
    destruct (interpret_expr ϵ e₂) eqn:E'; try discriminate.
    inv H. intros. constructor.
    - apply interpret_lexpr_sound. assumption.
    - apply interpret_expr_sound. assumption.
  Qed.

  Definition interpret_arg (ϵ : list Val.v) : Expr.arg -> option Val.argv := 
    paramarg_strength ∘ paramarg_map (interpret_expr ϵ) (interpret_lexpr ϵ).

  Lemma interpret_arg_sound :
    forall ϵ e v, 
      interpret_arg ϵ e = Some v -> arg_big_step ϵ e v.
  Proof.
    destruct e; cbn; unfold option_bind; intros.
    - destruct (interpret_expr ϵ a) eqn:E; try discriminate. inv H.
      constructor. apply interpret_expr_sound. assumption.
    - destruct (interpret_lexpr ϵ b) eqn:E; try discriminate. inv H.
      constructor. apply interpret_lexpr_sound. assumption.
    - destruct (interpret_lexpr ϵ b) eqn:E; try discriminate. inv H.
      constructor. apply interpret_lexpr_sound. assumption.
  Qed.

  Lemma interpret_arg_complete :
    forall ϵ e v, 
      arg_big_step ϵ e v -> interpret_arg ϵ e = Some v.
  Proof.
    intros. inv H; cbn; unfold option_bind.
    - apply interpret_expr_complete in H0. rewrite H0. reflexivity.
    - apply interpret_lexpr_complete in H0. rewrite H0. reflexivity.
    - apply interpret_lexpr_complete in H0. rewrite H0. reflexivity.
  Qed.

  Definition interpret_arg_adequate :
    forall ϵ e v, 
      interpret_arg ϵ e = Some v <-> arg_big_step ϵ e v.
  Proof.
    split.
    - apply interpret_arg_sound.
    - apply interpret_arg_complete.
  Qed.

  Definition interpret_args ϵ := map_monad (interpret_arg ϵ).

  Lemma interpret_args_sound :
    forall ϵ es vs,
      interpret_args ϵ es = Some vs -> args_big_step ϵ es vs.
  Proof.
    induction es.
    - cbn. intros. inv H. constructor.
    - cbn. unfold option_bind. intros.
      destruct (interpret_arg ϵ a) eqn:E; try discriminate.
      destruct (sequence (map (interpret_arg ϵ) es)) eqn:E'; try discriminate.
      inv H. constructor.
      + apply interpret_arg_sound. assumption.
      + apply IHes. assumption.
  Qed.

  Lemma interpret_args_complete :
    forall ϵ es vs,
      args_big_step ϵ es vs -> interpret_args ϵ es = Some vs.
  Proof.
    intros. induction H.
    - reflexivity.
    - cbn. unfold option_bind.
      apply interpret_arg_complete in H. rewrite H.
      unfold interpret_args, map_monad, "∘" in IHForall2.
      rewrite IHForall2. reflexivity.
  Qed.

  Lemma interpret_args_adequate :
    forall ϵ es vs,
      interpret_args ϵ es = Some vs <-> args_big_step ϵ es vs.
  Proof.
    split.
    - apply interpret_args_sound.
    - apply interpret_args_complete.
  Qed.

  Local Open Scope nat_scope.

  Import RecordSetNotations.

  Lemma args_invariant : 
    forall (vargs : Val.argsv), Forall2 (rel_paramarg eq (fun _ _ => True)) vargs vargs.
  Proof.
    induction vargs; constructor; auto. destruct a; constructor; auto.
  Qed.

  Definition initialized_value (ϵ : list Val.v) (initializer : Expr.t + Expr.e) : option Val.v :=
    match initializer with
    | inl t => v_of_t t
    | inr e => interpret_expr ϵ e
    end.

  Lemma initialized_value_sound :
    forall ϵ initializer v, 
      initialized_value ϵ initializer = Some v ->
        SumForall (fun τ => v_of_t τ = Some v) (fun e => ⟨ ϵ, e ⟩ ⇓ v) initializer.
  Proof.
    intros. destruct initializer; inv H.
    - constructor. reflexivity.
    - constructor. apply interpret_expr_sound. assumption.
  Qed.

  Definition get_bool (v : Val.v) : option bool :=
    match v with
    | Val.Bool b => mret b
    | _ => None
    end.

  Fixpoint interpret_stmt (fuel : Fuel) (Ψ : stmt_eval_env ext_sem) (ϵ : list Val.v) (c : ctx) (s : Stmt.s) : option (list Val.v * signal * extern_state) :=
    match fuel with
    | MoreFuel fuel =>
      match s with
      | Stmt.Skip => mret (ϵ, Cont, extrn_state Ψ)
      | Stmt.Exit => mret (ϵ, Exit, extrn_state Ψ)
      | Stmt.Return e => interpret_return Ψ ϵ e
      | Stmt.Transition trns =>
        match c with
        | CParserState n start states parsers =>
          let* lbl := interpret_parser_expr ϵ trns in
          match get_final_state lbl with
          | Some sig => mret (ϵ, sig, extrn_state Ψ)
          | None =>
            guard (n <=? List.length ϵ) ;;
            let* (ϵ₁, ϵ₂) := split_at (List.length ϵ - n) ϵ in
            let* state := get_state_block start states lbl in
            let ctx := CParserState n start states parsers in
            let^ (ϵ₃, sig, ψ) := interpret_stmt fuel Ψ ϵ₂ ctx state in
            (ϵ₁ ++ ϵ₃, sig, ψ)
          end
        | _ => None
        end
      | Stmt.Assign e1 e2 => interpret_assign Ψ ϵ e1 e2
      | Stmt.Call (Stmt.Funct f τs eo) args =>
        let* FDecl fun_clos body := functs Ψ f in
        let* olv := interpret_relop (interpret_lexpr ϵ) eo in
        let* vargs := interpret_args ϵ args in
        let* ϵ' := copy_in vargs ϵ in
        let env := Ψ <| functs := fun_clos |> in
        let body := tsub_s (gen_tsub τs) body in
        let^ (ϵ'', sig, ψ) := interpret_stmt fuel env ϵ' CFunction body in
        let ϵ''' := lv_update_signal olv sig (copy_out O vargs ϵ'' ϵ) in
        (ϵ''', Cont, ψ)
      | Stmt.Call (Stmt.Action a ctrl_args) data_args =>
        let* actions := interpret_actions_of_ctx c in
        let* ADecl clos act_clos body := actions a in
        let* vctrl_args := interpret_exprs ϵ ctrl_args in
        let* vdata_args := interpret_args ϵ data_args in
        let* ϵ' := copy_in vdata_args ϵ in
        let action_env := vctrl_args ++ ϵ' ++ clos in
        let^ (ϵ'', sig, ψ) := interpret_stmt fuel Ψ action_env (CAction act_clos) body in
        (copy_out O vdata_args ϵ'' ϵ, Cont, ψ)
      | Stmt.Var og te s =>
        let* v := initialized_value ϵ te in
        let* (ϵ', sig, ψ) := interpret_stmt fuel Ψ (v :: ϵ) c s in
        let^ ϵ' := tl_error ϵ' in
        (ϵ', sig, ψ)
      | Stmt.Seq s1 s2 =>
        let* (ϵ', sig, ψ) := interpret_stmt fuel Ψ ϵ c s1 in
        match sig with
        | Cont => interpret_stmt fuel (Ψ <| extrn_state := ψ |>) ϵ' c s2
        | Exit | Rtrn _ | Rjct => mret (ϵ', sig, ψ)
        | Acpt => None
        end
      | Stmt.Conditional e s1 s2 =>
        let* b : bool := get_bool =<< interpret_expr ϵ e in
        interpret_stmt fuel Ψ ϵ c $ if b then s1 else s2
      | _ => None
      end
    | NoFuel => None
    end.

  Lemma interpret_stmt_sound :
    forall fuel Ψ ϵ c s ϵ' sig ψ,
      interpret_stmt fuel Ψ ϵ c s = Some (ϵ' , sig , ψ) ->
        ⧼ Ψ , ϵ , c , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽.
  Proof.
    induction fuel; try discriminate. destruct s; try discriminate; cbn; intros.
    - inv H. constructor.
    - unfold option_bind in *. 
      destruct (interpret_relop (interpret_expr ϵ) e) eqn:?;
      try discriminate. inv H. destruct e; cbn in *.
      + unfold option_bind in *. destruct (interpret_expr ϵ' e) eqn:?; cbn in *.
        * inv Heqo. do 2 constructor.
          apply interpret_expr_sound. assumption.
        * discriminate.
      + inv Heqo. repeat constructor.
    - inv H. constructor.
    - unfold option_bind in *. destruct c eqn:E; try discriminate.
      destruct (interpret_parser_expr ϵ trns) eqn:?; try discriminate.
      apply interpret_parser_expr_sound in Heqo.
      destruct (get_final_state s) eqn:?.
      + inv H. apply get_final_state_sound in Heqo0.
        econstructor; eauto.
      + destruct (parser_arg_length <=? List.length ϵ) eqn:?; try discriminate. cbn in *.
        apply Nat.leb_le in Heqb.
        destruct (split_at (List.length ϵ - parser_arg_length) ϵ) eqn:?; 
        try discriminate. destruct p as [ϵ₁ ϵ₂].
        destruct (get_state_block start states s) eqn:?; try discriminate.
        destruct (interpret_stmt fuel Ψ ϵ₂ (CParserState parser_arg_length start states available_parsers) s0) eqn:?; 
        try discriminate. inv H. repeat destruct p. inv H1.
        apply IHfuel in Heqo3.
        apply split_at_partition in Heqo1 as ?.
        apply split_at_length_l2 in Heqo1 as ?.
        assert (List.length ϵ₂ = parser_arg_length) by lia. subst.
        econstructor; eauto. apply intermediate_iff_not_final.
        unfold "~". intros. inv H.
        assert (get_final_state s <> Some x).
        { unfold "~". intros. rewrite H in Heqo0. discriminate. }
        apply get_final_state_complete in H1. contradiction.
    - apply interpret_assign_sound. assumption.
    - unfold option_bind in *. destruct call eqn:E; try discriminate.
      destruct (functs Ψ function_name) eqn:?; try discriminate.
      destruct f. 
      destruct (interpret_relop (interpret_lexpr ϵ) returns) eqn:?; try discriminate.
      destruct (interpret_args ϵ args) eqn:?; try discriminate.
      destruct (copy_in l ϵ) eqn:?; try discriminate.
      destruct (interpret_stmt fuel _ _ _ _) eqn:?; try discriminate.
      inv H. do 2 destruct p. inv H1.
      apply interpret_args_sound in Heqo1.
      apply IHfuel in Heqo3. econstructor; eauto.
      destruct returns; cbn in *; unfold option_bind in *.
      + destruct (interpret_lexpr ϵ e) eqn:?; try discriminate. inv Heqo0.
        apply interpret_lexpr_sound in Heqo4. constructor. assumption.
      + inv Heqo0. constructor.
      + destruct (interpret_actions_of_ctx c) eqn:?; try discriminate.
        apply interpret_actions_of_ctx_sound in Heqo.
        destruct (a action_name) eqn:?; try discriminate. destruct a0.
        destruct (interpret_exprs ϵ control_plane_args) eqn:?; try discriminate.
        apply interpret_exprs_sound in Heqo1.
        destruct (interpret_args ϵ args) eqn:?; try discriminate.
        apply interpret_args_sound in Heqo2.
        destruct (copy_in _ _) eqn:?; try discriminate.
        destruct (interpret_stmt _ _ _ _ _) eqn:?; try discriminate. 
        inv H. do 2 destruct p. inv H1. apply IHfuel in Heqo4.
        econstructor; eauto.
    - unfold option_bind in *.
      destruct (initialized_value ϵ expr) eqn:E; try discriminate.
      apply initialized_value_sound in E.
      destruct (interpret_stmt _ _ _ _ _) eqn:?; try discriminate.
      do 2 destruct p. apply IHfuel in Heqo. destruct (tl_error l) eqn:?; try discriminate.
      inv H. destruct l; try discriminate. cbn in *. inv Heqo0. econstructor; eauto.
    - unfold option_bind in *. destruct (interpret_stmt fuel Ψ ϵ c s1) eqn:?; try discriminate.
      do 2 destruct p. apply IHfuel in Heqo. destruct s.
      + apply IHfuel in H. econstructor; eauto.
      + inv H. constructor; auto; constructor.
      + discriminate.
      + inv H. constructor; auto; constructor.
      + inv H. constructor; auto; constructor.
    - unfold option_bind in *.
      destruct (interpret_expr ϵ guard) eqn:?; try discriminate.
      apply interpret_expr_sound in Heqo.
      destruct v; try discriminate. cbn in *. unfold "$" in *.
      apply IHfuel in H. econstructor; eauto.
  Qed.

End Stmt.
