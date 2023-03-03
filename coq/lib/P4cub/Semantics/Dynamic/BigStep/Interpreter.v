From Coq Require Import NArith.BinNat ZArith.BinInt ssr.ssrbool.

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

  Variable Ψ : stmt_eval_env ext_sem.

  Definition interpret_return ϵ e :=
    match e with
    | None => mret (ϵ, Rtrn None, extrn_state Ψ)
    | Some e =>
      let^ v := interpret_expr ϵ e in
      (ϵ, Rtrn $ Some v, extrn_state Ψ)
    end.

  Inductive Fuel :=
  | NoFuel
  | MoreFuel (t : Fuel).

  Local Open Scope nat_scope.

  Fixpoint interpret_stmt (fuel : Fuel) (ϵ : list Val.v) (c : ctx) (s : Stmt.s) : option (list Val.v * signal * extern_state) :=
    match fuel with
    | MoreFuel fuel =>
      match s with
      | Stmt.Skip => mret (ϵ, Cont, extrn_state Ψ)
      | Stmt.Exit => mret (ϵ, Exit, extrn_state Ψ)
      | Stmt.Return e => interpret_return ϵ e
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
            let^ (ϵ₃, sig, ψ) := interpret_stmt fuel ϵ₂ ctx state in
            (ϵ₁ ++ ϵ₃, sig, ψ)
          end
        | _ => None
        end
      | _ => None
      end
    | NoFuel => None
    end.

  Search (_ <=? _ = true <-> _ <= _).

  Lemma interpret_stmt_sound :
    forall fuel ϵ c s ϵ' sig ψ,
      interpret_stmt fuel ϵ c s = Some (ϵ' , sig , ψ) ->
        ⧼ Ψ , ϵ , c , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽.
  Proof.
    induction fuel; try discriminate. destruct s; try discriminate; cbn; intros.
    - inv H. constructor.
    - unfold interpret_return in *. destruct e.
      + destruct (interpret_expr ϵ e) eqn:?; cbn in *.
        * inv H. do 2 constructor.
          apply interpret_expr_sound. assumption.
        * discriminate.
      + inv H. repeat constructor.
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
        destruct (interpret_stmt fuel ϵ₂ (CParserState parser_arg_length start states available_parsers) s0) eqn:?; 
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
  Qed.

End Stmt.
