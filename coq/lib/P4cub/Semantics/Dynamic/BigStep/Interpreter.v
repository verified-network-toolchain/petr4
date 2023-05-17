From Coq Require Import NArith.BinNat ZArith.BinInt ssr.ssrbool.

From RecordUpdate Require Import RecordSet.

From Poulet4 Require Import
  Monads.Option
  P4cub.Syntax.Syntax
  P4cub.Syntax.CubNotations
  P4cub.Semantics.Climate
  P4cub.Semantics.Dynamic.BigStep.ExprUtil
  P4cub.Semantics.Dynamic.BigStep.Value.Value
  P4cub.Semantics.Dynamic.BigStep.Value.Embed
  P4cub.Semantics.Dynamic.BigStep.Semantics
  P4cub.Semantics.Dynamic.BigStep.Properties
  P4light.Syntax.Syntax
  P4light.Architecture.Target
  Utils.Util.ListUtil.

Import Option String.
Import RecordSetNotations.

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
    induction e using custom_exp_ind; unravel in *.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor.
    - intros. inv H. constructor. assumption.
    - intros. match_some_inv. econstructor; eauto.
    - intros. match_some_inv. econstructor; eauto.
    - intros. match_some_inv. econstructor; eauto.
    - simpl. unfold option_bind. intros.
      repeat match_some_inv. econstructor; eauto.
    - intros. match_some_inv as Hsome. some_inv.
      rewrite map_monad_some in Hsome.
      constructor. generalize dependent l0.
      induction es; intros; inv H; inv Hsome; constructor; auto.
    - unfold interpret_index, index, to_bit. intros.
      destruct (interpret_exp e1);
      destruct (interpret_exp e2);
      try discriminate.
      destruct t; destruct t0; try discriminate.
      econstructor; eauto.
    - unfold index. intros. match_some_inv.
      destruct t; try discriminate.
      econstructor; eauto.
    - intros. inv H. constructor.
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

    Definition interpret_exps := map_monad interpret_exp.

    Lemma interpret_exps_sound :
      forall es vs, interpret_exps es = Some vs -> Forall2 (exp_big_step ϵ) es vs.
    Proof.
      unfold interpret_exps. intros. rewrite map_monad_some in H. generalize dependent vs.
      induction es.
      - intros. inv H. constructor.
      - intros. inv H. constructor; auto. apply interpret_exp_sound. assumption.
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
      - match_some_inv. some_inv. constructor. auto.
      - unfold to_bit in *. match_some_inv.
        destruct (interpret_exp e2) eqn:?; try discriminate.
        destruct t0; try discriminate.
        inv H1. econstructor; eauto. 
        apply interpret_exp_sound. eauto.
      - match_some_inv. some_inv. econstructor. auto.
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
      - unravel in *. match_some_inv. some_inv.
        constructor. apply interpret_exp_sound. assumption.
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
  unravel in *. match_some_inv. some_inv.
  constructor. apply unembed_valsets_sound. assumption.
Qed.

Definition interpret_table_entries entries := 
  let^ l := map_monad interpret_table_entry entries in
  List.split l.

Lemma interpret_table_entries_sound :
  forall entries pats arefs,
    interpret_table_entries entries = Some (pats, arefs) -> Forall3 table_entry_big_step entries pats arefs.
Proof.
  unfold interpret_table_entries. unravel. intros.
  match_some_inv as Hsome. some_inv. rewrite map_monad_some in Hsome.
  generalize dependent pats. generalize dependent arefs. generalize dependent l.
  induction entries.
  - intros. inv Hsome. inv H1. constructor.
  - intros. inv Hsome. inv H1. destruct y, (split l') eqn:E. inv H0.
    apply interpret_table_entry_sound in H2.
    eapply IHentries in H4.
    + econstructor; eauto.
    + f_equal. assumption.
Qed.

Definition interpret_actions_of_ctx ctx :=
  match ctx with
  | CAction a | CApplyBlock _ a _ => mret a
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

Definition get_final_state (state : Lbl.t) : option signal :=
  match state with
  | Lbl.Accept => mret Acpt
  | Lbl.Reject => mret Rjct
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

Definition is_intermediate_state (state : Lbl.t) :=
  match state with
  | Lbl.Start | Lbl.Name _ => true
  | _ => false
  end.

Lemma is_intermediate_state_sound :
  forall state,
    is_intermediate_state state = true -> intermediate_state state.
Proof.
  unfold is_intermediate_state.
  intros. destruct state; try discriminate; constructor.
Qed.

Section Stm.

  Context {ext_sem : Extern_Sem}.

  Definition interpret_relop {A B : Type} (f : A -> option B) (x : option A) : option (option B) :=
    match x with
    | None => mret None
    | Some x => f x >>| Some
    end.

  Lemma interpret_relop_sound :
    forall
      (A B : Type) (f : A -> option B) (R : A -> B -> Prop)
      (H : forall x y, f x = Some y -> R x y) x y,
        interpret_relop f x = Some y -> relop R x y.
  Proof.
    intros. destruct x; unravel in *.
    - match_some_inv. some_inv. constructor. auto.
    - some_inv. constructor.
  Qed.

  Definition interpret_return Ψ ϵ e :=
    let^ v := interpret_relop (interpret_exp ϵ) e in
    (ϵ, Rtrn v , extrn_state Ψ).

  Inductive Fuel :=
    | NoFuel
    | MoreFuel (t : Fuel).

  Definition interpret_assign Ψ ϵ e1 e2 :=
    let* lv := interpret_lexp ϵ e1 in
    let^ v := interpret_exp ϵ e2 in
    (lv_update lv v ϵ, Cont, extrn_state Ψ).

  Lemma interpret_assign_sound :
    forall Ψ ϵ ϵ' c e₁ e₂ sig ψ, 
      interpret_assign Ψ ϵ e₁ e₂ = Some (ϵ', sig, ψ) ->
        ⧼ Ψ, ϵ, c, Stm.Asgn e₁ e₂ ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
  Proof.
    cbn. unfold option_bind. intros.
    destruct (interpret_lexp ϵ e₁) eqn:E; try discriminate.
    destruct (interpret_exp ϵ e₂) eqn:E'; try discriminate.
    inv H. intros. constructor.
    - apply interpret_lexp_sound. assumption.
    - apply interpret_exp_sound. assumption.
  Qed.

  Definition interpret_args (ϵ : list Val.t) : Exp.args -> option Argsv :=
    InOut.opt_seq ∘ InOut.map (interpret_exp ϵ) (interpret_lexp ϵ).

  Lemma interpret_args_sound :
    forall ϵ es vs,
      interpret_args ϵ es = Some vs -> args_big_step ϵ es vs.
  Proof using.
    intros. unfold interpret_args, InOut.opt_seq in H.
    unravel in H.
    do 2 match_some_inv. some_inv.
    unfold args_big_step.
    constructor; cbn;
      auto using interpret_exps_sound.
    rewrite <- Forall2_sequence_iff in Heqo0.
    rewrite sublist.Forall2_map1 in Heqo0.
    eapply sublist.Forall2_impl in Heqo0; eauto using interpret_lexp_sound.
  Qed.

  Lemma interpret_args_complete :
    forall ϵ es vs,
      args_big_step ϵ es vs -> interpret_args ϵ es = Some vs.
  Proof.
    intros. inv H.
    unfold interpret_args, InOut.opt_seq; unravel.
    apply
      (sublist.Forall2_impl
         _ _ $ interpret_exp_complete ϵ)
      in inn_forall2.
    apply
      (sublist.Forall2_impl
         _ _ $ interpret_lexp_complete ϵ)
      in out_forall2.
    rewrite <- sublist.Forall2_map1
      with (P := fun ov v => ov = Some v)
           (f:=interpret_exp ϵ)
      in inn_forall2.
    rewrite <- sublist.Forall2_map1
      with (P := fun ov v => ov = Some v)
           (f:=interpret_lexp ϵ)
      in out_forall2.
    rewrite Forall2_sequence_iff in inn_forall2.
    rewrite Forall2_sequence_iff in out_forall2.
    rewrite inn_forall2, out_forall2.
    destruct vs; reflexivity.
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

  Definition initialized_value (ϵ : list Val.t) (initializer : Typ.t + Exp.t) : option Val.t :=
    match initializer with
    | inl t => val_of_typ t
    | inr e => interpret_exp ϵ e
    end.

  Lemma initialized_value_sound :
    forall ϵ initializer v, 
      initialized_value ϵ initializer = Some v ->
        SumForall (fun τ => val_of_typ τ = Some v) (fun e => ⟨ ϵ, e ⟩ ⇓ v) initializer.
  Proof.
    intros. destruct initializer; inv H.
    - constructor. reflexivity.
    - constructor. apply interpret_exp_sound. assumption.
  Qed.

  Definition interpret_parser_signal (sig : signal) : option signal :=
    match sig with
    | Acpt => mret Cont
    | Rjct => mret Rjct
    | Exit => mret Exit
    | _ => None
    end.

  Lemma interpret_parser_signal_sound :
    forall sig sig',
      interpret_parser_signal sig = Some sig' -> parser_signal sig sig'.
  Proof.
    destruct sig; intros; inv H; constructor.
  Qed.

  Definition interpret_table_action (def : option (string * list Exp.t)) (aref : option (@action_ref Exp.t)) :=
    match aref, def with
    | Some (mk_action_ref a opt_ctrl_args), _ =>
      let^ ctrl_args := sequence opt_ctrl_args in
      (true, a, ctrl_args)
    | None, Some (a, ctrl_args) => mret (false, a, ctrl_args)
    | None, None => None
    end.

  Lemma interpret_table_action_sound :
    forall def aref hit a ctrl_args,
      interpret_table_action def aref = Some (hit, a, ctrl_args) ->
        eval_table_action def aref hit a ctrl_args.
  Proof.
    unfold interpret_table_action. intros. destruct aref.
    - destruct a0. destruct (sequence args) eqn:Hsome; try discriminate.
      cbn in *. some_inv. constructor. apply sequence_Forall2. assumption.
    - destruct def; try discriminate. destruct p. inv H. constructor.
  Qed.

  (*Fixpoint write_out_values {A B C : Set} (args : list (paramarg A B)) (values : list C) : option (list (paramarg A C)) :=
    match args, values with
    | [], [] => Some []
    | PAIn v as arg :: args, _ =>
      let^ args' := write_out_values args values in
      PAIn v :: args'
    | PAInOut _ :: args, v :: values =>
      let^ args' := write_out_values args values in
      PAInOut v :: args'
    | PAOut _ :: args, v :: values =>
      let^ args' := write_out_values args values in
      PAOut v :: args'
    | _, _ => None
    end.

    Lemma write_out_values_sound :
      forall 
        A B C (args : list (paramarg A B)) (args' : list (paramarg A C)) values,
          write_out_values args values = Some args' ->
          values =
            List.flat_map
            (fun v => match v with PAOut v | PAInOut v => [v] | _ => [] end)
            args'.
    Proof.
      induction args; intros.
      - cbn in *. destruct values; try discriminate. some_inv. reflexivity.
      - destruct a; cbn in *; unravel in *.
        + match_some_inv. some_inv. cbn. auto.
        + destruct values; try discriminate.
          match_some_inv. some_inv. cbn. f_equal. auto.
        + destruct values; try discriminate.
          match_some_inv. some_inv. cbn. f_equal. auto.
    Qed.

    Lemma write_out_values_invariant :
      forall 
        A B C (args : list (paramarg A B)) (args' : list (paramarg A C)) values,
          write_out_values args values = Some args' ->
            Forall2 (rel_paramarg eq (fun _ _ => True)) args args'.
    Proof.
      induction args; intros; cbn in *; unravel in *.
      - cbn in *. destruct values; try discriminate. some_inv. constructor.
      - destruct a.
        + match_some_inv. some_inv. repeat constructor. eauto.
        + destruct values; try discriminate. match_some_inv. some_inv.
          repeat constructor. eauto.
        + destruct values; try discriminate. match_some_inv. some_inv.
          repeat constructor. eauto.
    Qed.*)

  Definition project_signal (sig : Value.signal) : option signal :=
    match sig with
    | Value.SContinue => mret Cont
    | Value.SExit => mret Exit
    | Value.SReject _ => mret Rjct
    | Value.SReturn ValBaseNull => mret $ Rtrn None
    | Value.SReturn v' =>
      let^ v := project v' in
      Rtrn (Some v)
    end.

  Lemma project_signal_sound sig sig' :
    project_signal sig = Some sig' -> Embed_signal sig' sig.
  Proof.
    intros. destruct sig; try (cbn in *; some_inv; constructor).
    unravel in *. destruct v; try (some_inv; constructor);
    (match_some_inv; some_inv; constructor; apply project_sound; auto).
  Qed.
  
  Fixpoint interpret_stmt (fuel : Fuel) (Ψ : stm_eval_env ext_sem) (ϵ : list Val.t) (c : ctx) (s : Stm.t) : option (list Val.t * signal * extern_state) :=
    match fuel with
    | MoreFuel fuel =>
      match s, c with
      | Stm.Skip, _ => mret (ϵ, Cont, extrn_state Ψ)
      | Stm.Exit, _ => mret (ϵ, Exit, extrn_state Ψ)
      | Stm.Ret e, _ => interpret_return Ψ ϵ e
      | Stm.Trans trns, CParserState n start states parsers =>
        let* lbl := interpret_parser_exp ϵ trns in
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
      | Stm.Asgn e1 e2, _ => interpret_assign Ψ ϵ e1 e2
      | Stm.App (Call.Funct f τs eo) args, _ =>
        let* FDecl fun_clos _ body := functs Ψ f in
        let* olv := interpret_relop (interpret_lexp ϵ) eo in
        let* vargs := interpret_args ϵ args in
        let* out_inits := get_out_inits args.(InOut.out) in
        let env := Ψ <| functs := fun_clos |> in
        let body := tsub_stm (gen_tsub τs) body in
        let^ (ϵ', sig, ψ) := interpret_stmt fuel env (vargs.(InOut.inn) ++ out_inits) CFunction body in
        let ϵ'' := lv_update_signal olv sig (copy_out vargs.(InOut.out) (skipn (List.length vargs.(InOut.inn)) ϵ') ϵ) in
        (ϵ'', Cont, ψ)
      | Stm.App (Call.Action a ctrl_args) data_args, _ =>
        let* actions := interpret_actions_of_ctx c in
        let* ADecl clos act_clos _ _ body := actions a in
        let* vctrl_args := interpret_exps ϵ ctrl_args in
        let* vdata_args := interpret_args ϵ data_args in
        let* out_inits := get_out_inits data_args.(InOut.out) in
        let action_env := vctrl_args ++ vdata_args.(InOut.inn) ++ out_inits ++ clos in
        let^ (ϵ', sig, ψ) := interpret_stmt fuel Ψ action_env (CAction act_clos) body in
        (copy_out
           (InOut.out vdata_args)
           (firstn (List.length out_inits) $
              skipn (List.length vctrl_args + List.length (A:=Val.t) $ InOut.inn vdata_args) ϵ') ϵ, Cont, ψ)
      | Stm.LetIn og te s, _ =>
        let* v := initialized_value ϵ te in
        let* (ϵ', sig, ψ) := interpret_stmt fuel Ψ (v :: ϵ) c s in
        let^ ϵ' := tl_error ϵ' in
        (ϵ', sig, ψ)
      | Stm.Seq s1 s2, _ =>
        let* '(ϵ', sig, ψ) := interpret_stmt fuel Ψ ϵ c s1 in
        match sig with
        | Cont => interpret_stmt fuel (Ψ <| extrn_state := ψ |>) ϵ' c s2
        | Exit | Rtrn _ | Rjct => Some (ϵ', sig, ψ)
        | Acpt => None
        end
      | Stm.App (Call.Method ext meth τs eo) args, _ =>
        let* olv := interpret_relop (interpret_lexp ϵ) eo in
        let* vargs := interpret_args ϵ args in
        let* light_typs := embed_types (dummy_tags:=tt) (string_list:=[]) τs in
        let light_in_vals := embed_values $ InOut.inn vargs in
        let* (ψ, light_out_vals, light_sig) :=
          to_opt $ interp_extern (extrn_env Ψ) (extrn_state Ψ) ext meth [] light_typs light_in_vals
        in
        let* out_vals := project_values light_out_vals in
        let^ sig := project_signal light_sig in
        ( lv_update_signal olv sig (copy_out vargs.(InOut.out) out_vals ϵ), sig, ψ )
      | Stm.Invoke eo t, CApplyBlock tbls acts insts =>
        let* Table.mk_t n key actions def := tbls t in
        let* lvo := interpret_relop (interpret_lexp ϵ) eo in
        guard (n <=? List.length ϵ) ;;
        let* (ϵ₁, ϵ₂) := split_at (List.length ϵ - n) ϵ in
        let* vs := interpret_exps ϵ₂ $ map fst key in
        let* (pats, arefs) := interpret_table_entries $ extern_get_entries Ψ.(extrn_state) [] in
        let light_vals := embed_values vs in
        let* light_sets := embed_pats pats in
        let aref := extern_match (combine light_vals (map snd key)) (combine light_sets arefs) in
        let* (hit, a, ctrl_args) := interpret_table_action def aref in
        let* data_args := Field.get a actions in
        let* idx := Field.get_index a actions in
        let? '(ϵ', Cont, ψ) := interpret_stmt fuel Ψ ϵ₂ (CApplyBlock tbls acts insts) (Stm.App (Call.Action a ctrl_args) data_args) in
        let sig := 
          lv_update_signal
            lvo
            (Rtrn
              (Some 
              (Val.Lists
                  Lst.Struct
                  [Val.Bool hit; Val.Bool (negb hit);
                  Val.Bit (BinNat.N.of_nat (List.length actions)) (Z.of_nat idx)])))
            (ϵ₁ ++ ϵ')
        in
        mret (sig, Cont, ψ )
      | Stm.App (Call.Inst p ext_args) args, CParserState n strt states parsers =>
        let? 'ParserInst p_fun p_prsr p_eps _ p_strt p_states := parsers p in
        let* vargs := interpret_args ϵ args in
        let* out_inits := get_out_inits args.(InOut.out) in
        let ctx' := CParserState (InOut.length args) p_strt p_states p_prsr in
        let* (ϵ', final, ψ) := interpret_stmt fuel (Ψ <| functs := p_fun |>) (InOut.inn vargs ++ out_inits ++ p_eps) ctx' p_strt in
        let^ sig := interpret_parser_signal final in
        (copy_out vargs.(InOut.out) (firstn (List.length out_inits) $ skipn (List.length vargs.(InOut.inn)) ϵ') ϵ, sig, ψ)
      | Stm.App (Call.Inst c ext_args) args, CApplyBlock tbls actions control_insts =>
        let? 'ControlInst fun_clos inst_clos tbl_clos action_clos eps_clos _ apply_block := control_insts c in
        let* vargs := interpret_args ϵ args in
        let* out_inits := get_out_inits args.(InOut.out) in
        let ctx' := CApplyBlock tbl_clos action_clos inst_clos in
        let^ (ϵ', sig, ψ) := interpret_stmt fuel (Ψ <| functs := fun_clos |>) (InOut.inn vargs ++ out_inits ++ eps_clos) ctx' apply_block in
        (copy_out vargs.(InOut.out) (firstn (List.length out_inits) $ skipn (List.length vargs.(InOut.inn)) ϵ') ϵ, Cont, ψ)
      | Stm.Cond e s1 s2, _ =>
        let? 'Val.Bool b := interpret_exp ϵ e in
        interpret_stmt fuel Ψ ϵ c $ if b then s1 else s2
      | _, _ => None
      end
    | NoFuel => None
    end.

  Local Arguments interpret_args : simpl never.
  
  Lemma interpret_stmt_sound :
    forall fuel Ψ ϵ c s ϵ' sig ψ,
      interpret_stmt fuel Ψ ϵ c s = Some (ϵ' , sig , ψ) ->
        ⧼ Ψ , ϵ , c , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽.
  Proof.
    induction fuel; try discriminate. destruct s eqn:?; try discriminate; cbn; intros.
    - inv H; constructor.
    - unfold option_bind in *. match_some_inv. some_inv. destruct e; cbn in *.
      + unfold option_bind in *. match_some_inv. some_inv.
        do 2 constructor. apply interpret_exp_sound. assumption.
      + some_inv. repeat constructor.
    - some_inv. constructor.
    - unravel in *. unfold option_bind in *. destruct c eqn:E; try discriminate.
      match_some_inv. apply interpret_parser_exp_sound in Heqo.
      destruct (get_final_state _) eqn:?.
      + inv H. apply get_final_state_sound in Heqo0.
        econstructor; eauto.
      + destruct (parser_arg_length <=? List.length ϵ) eqn:?; try discriminate. cbn in *.
        apply Nat.leb_le in Heqb. match_some_inv. destruct p as [ϵ₁ ϵ₂].
        repeat match_some_inv. some_inv. repeat destruct p. inv H1.
        apply IHfuel in Heqo3.
        apply split_at_partition in Heqo1 as ?.
        apply split_at_length_l2 in Heqo1 as ?.
        assert (List.length ϵ₂ = parser_arg_length) by lia. subst.
        econstructor; eauto. apply intermediate_iff_not_final.
        unfold "~". intros. inv H.
        assert (get_final_state t <> Some x).
        { unfold "~". intros. rewrite H in Heqo0. discriminate. }
        apply get_final_state_complete in H1. contradiction.
    - apply interpret_assign_sound. assumption.
    - unfold option_bind in *. destruct call eqn:E; try discriminate.
      + destruct (functs Ψ function_name) eqn:?; try discriminate.
        destruct f. repeat match_some_inv. destruct p as [[eps' sig'] ψ'].
        some_inv.
        apply interpret_args_sound in Heqo1.
        apply IHfuel in Heqo3.
        eapply sbs_funct_call with (prefix:=firstn (List.length (InOut.inn a)) eps'); eauto.
        * rewrite firstn_length.
          apply sbs_length in Heqo3.
          rewrite app_length in Heqo3.
          lia.
        * eapply interpret_relop_sound; eauto using interpret_lexp_sound.
        * rewrite firstn_skipn. assumption.
      + repeat match_some_inv. apply interpret_actions_of_ctx_sound in Heqo.
        destruct a0. repeat match_some_inv. some_inv. repeat destruct p. inv H1.
        apply interpret_exps_sound in Heqo1.
        apply interpret_args_sound in Heqo2.
        apply IHfuel in Heqo4.
        unravel.
        rewrite <- firstn_skipn with (n:=List.length l) (l:=l1) in Heqo4.
        rewrite <- firstn_skipn with (n:=List.length (InOut.inn a0)) (l:=skipn (List.length l) l1) in Heqo4.
        rewrite <- firstn_skipn with
          (n:=List.length l0)
          (l:= skipn (List.length (InOut.inn a0)) (skipn (List.length l) l1)) in Heqo4.
        rewrite Nat.add_comm.
        rewrite <- sublist.skipn_drop.
        eapply sbs_action_call with
          (ctrl_prefix:=firstn (List.length l) l1)
          (data_prefix:=firstn (List.length (InOut.inn a0)) (skipn (List.length l) l1))
          (*(out_vals:=firstn (List.length (InOut.out a0)) (skipn (List.length (InOut.inn a0)) (skipn (List.length l) l1)))*)
          (ϵ':=skipn (List.length l0) (skipn (List.length (InOut.inn a0)) (skipn (List.length l) l1)))
          (vctrl_args:=l) (out_inits:=l0); eauto.
        * apply sbs_length in Heqo4.
          repeat rewrite firstn_skipn in Heqo4.
          repeat rewrite app_length in Heqo4.
          rewrite firstn_length. lia.
        * apply sbs_length in Heqo4.
          repeat rewrite firstn_skipn in Heqo4.
          repeat rewrite app_length in Heqo4.
          rewrite firstn_length,skipn_length. lia.
        * apply sbs_length in Heqo4.
          repeat rewrite firstn_skipn in Heqo4.
          repeat rewrite app_length in Heqo4.
          rewrite firstn_length.
          do 2 rewrite skipn_length.
          apply get_out_inits_length in Heqo3.
          inv Heqo2.
          apply Forall2_length in inn_forall2, out_forall2. lia.
      + repeat match_some_inv. unravel in *. repeat destruct p.
        repeat match_some_inv. some_inv.
        simpl_to_opt as Hextern. cbn in *. some_inv.
        unfold embed_values in Hextern.
        apply project_values_sound in Heqo3.
        apply project_signal_sound in Heqo4.
        econstructor; eauto using embed_types_sound, embed_values_sound, interpret_args_sound, interp_extern_safe.
        eapply interpret_relop_sound; eauto. apply interpret_lexp_sound.
      + destruct c; try discriminate.
        * match_some_inv. destruct i; try discriminate.
          match_some_inv as Eargs. apply interpret_args_sound in Eargs.
          match_some_inv as Eoutinits. match_some_inv as Estmt. some_inv.
          repeat destruct p. inv H1. eapply IHfuel in Estmt. unravel.
          rewrite <- firstn_skipn with (n:=List.length a.(InOut.inn)) (l:=l0) in Estmt.
          rewrite <- firstn_skipn with (n:=List.length l) (l:=skipn (List.length (InOut.inn a)) l0) in Estmt.
          eapply sbs_apply_control with (prefix:=firstn (List.length (InOut.inn a)) l0); eauto.
          rewrite firstn_length.
          apply sbs_length in Estmt.
          repeat rewrite firstn_skipn in Estmt.
          repeat rewrite app_length in Estmt. lia.
        * match_some_inv. destruct i; try discriminate.
          match_some_inv as Eargs. apply interpret_args_sound in Eargs.
          match_some_inv as Eoutinits. match_some_inv as Estmt.
          repeat destruct p. match_some_inv as Esignal. some_inv.
          apply interpret_parser_signal_sound in Esignal.
          eapply IHfuel in Estmt. unravel.
          rewrite <- firstn_skipn with (n:=List.length a.(InOut.inn)) (l:=l0) in Estmt.
          rewrite <- firstn_skipn with (n:=List.length l) (l:=skipn (List.length (InOut.inn a)) l0) in Estmt.
          eapply sbs_apply_parser with
            (out_inits:=l)
            (prefix:=firstn (List.length (InOut.inn a)) l0); eauto.
          -- rewrite firstn_length.
             apply sbs_length in Estmt.
             repeat rewrite firstn_skipn in Estmt.
             repeat rewrite app_length in Estmt. lia.
          -- rewrite firstn_length, skipn_length.
             apply sbs_length in Estmt.
             repeat rewrite firstn_skipn in Estmt.
             repeat rewrite app_length in Estmt. lia.
    - (* Table Invocations *)
      destruct c; try discriminate. unravel in *.
      match_some_inv as Htables.
      destruct t as [n tkey tacts tdef].
      match_some_inv as Hlhs.
      destruct (n <=? List.length ϵ) eqn:Hlen; try discriminate. cbn in *.
      apply Nat.leb_le in Hlen. match_some_inv as Hϵ.
      destruct p as [ϵ₁ ϵ₂]. apply split_at_partition in Hϵ as Hpartition.
      apply split_at_length_l2 in Hϵ as Hϵ₂.
      assert (List.length ϵ₂ = n) by lia.
      match_some_inv as Hes.
      apply interpret_exps_sound in Hes.
      match_some_inv as Hentries. repeat destruct p.
      apply interpret_table_entries_sound in Hentries.
      match_some_inv. match_some_inv as Haction.
      repeat destruct p.
      apply interpret_table_action_sound in Haction.
      match_some_inv. match_some_inv. match_some_inv as Hstmt.
      repeat destruct p. destruct s1; try discriminate. some_inv.
      eapply IHfuel in Hstmt.
      econstructor; eauto.
      + eapply interpret_relop_sound; eauto. apply interpret_lexp_sound.
      + apply embed_values_sound.
      + apply embed_pats_sound. assumption.
    - unfold option_bind in *.
      destruct (initialized_value ϵ init) eqn:E; try discriminate.
      apply initialized_value_sound in E.
      destruct (interpret_stmt _ _ _ _ _) eqn:?; try discriminate.
      do 2 destruct p. apply IHfuel in Heqo. destruct (tl_error l) eqn:?; try discriminate.
      inv H. destruct l; try discriminate. cbn in *. inv Heqo0. econstructor; eauto.
    - unfold option_bind in *. destruct (interpret_stmt fuel Ψ ϵ c _) eqn:?; try discriminate.
      do 2 destruct p. apply IHfuel in Heqo. destruct s0.
      + apply IHfuel in H. econstructor; eauto.
      + inv H. constructor; auto; constructor.
      + discriminate.
      + inv H. constructor; auto; constructor.
      + inv H. constructor; auto; constructor.
    - unfold option_bind in *.
      destruct (interpret_exp ϵ guard) eqn:?; try discriminate.
      apply interpret_exp_sound in Heqo.
      destruct t; try discriminate. cbn in *. unravel in *.
      apply IHfuel in H. econstructor; eauto.
  Qed.

End Stm.

Section Top.
  Local Open Scope climate_scope.

  Import Clmt.Notations.

  Definition interpret_ctrl_var (cbs_env : ctrl_bs_env) te :=
    let^ v := initialized_value (cbs_epsilon cbs_env) te in
    cbs_env <| cbs_epsilon := v :: cbs_epsilon cbs_env |>.

  Definition interpret_ctrl (cbs_env : ctrl_bs_env) (c : Ctrl.t) : option ctrl_bs_env :=
    match c with
    | Ctrl.Var _ te => interpret_ctrl_var cbs_env te
    | Ctrl.Action a ctrl_params data_params body =>
        mret (cbs_env
                <| cbs_actions :=
                a ↦ ADecl (cbs_epsilon cbs_env) (cbs_actions cbs_env)
                  (map snd ctrl_params) data_params body ,, cbs_actions cbs_env |>)
    | Ctrl.Table t key actions def => 
        mret $ cbs_env <| cbs_tables := t ↦ Table.mk_t (List.length (cbs_epsilon cbs_env)) key actions def ,, cbs_tables cbs_env |>
    end.

  Lemma interpret_ctrl_sound :
    forall c env env',
      interpret_ctrl env c = Some env' -> ctrl_big_step env c env'.
  Proof.
    destruct c; cbn; unravel; intros.
    - match_some_inv. some_inv. constructor. apply initialized_value_sound. assumption.
    - some_inv. constructor.
    - some_inv. constructor.
  Qed.

  Fixpoint interpret_ctrls ctrls env :=
    match ctrls with
    | [] => mret env
    | ctrl :: ctrls => interpret_ctrls ctrls =<< interpret_ctrl env ctrl 
    end.

  Lemma interpret_ctrls_sound :
    forall ctrls env env',
      interpret_ctrls ctrls env = Some env' -> ctrls_big_step ctrls env env'.
  Proof.
    induction ctrls; cbn; unravel; intros.
    - some_inv. constructor.
    - match_some_inv. econstructor.
      + apply interpret_ctrl_sound. eassumption.
      + apply IHctrls. assumption.
  Qed.

  Definition interpret_top (tbs_env : top_bs_env) (top : Top.t) : option top_bs_env :=
    match top with
    | Top.Control c cparams ecparams extparams params body s =>
      mret $ tbs_env <| top_decls := c ↦ ControlDecl (top_functs tbs_env) (top_insts tbs_env) (map fst cparams) params body s ,, top_decls tbs_env |>
    | Top.Parser p cparams ecparams extparams params strt states =>
      mret $ tbs_env <| top_decls := p ↦ ParserDecl (top_functs tbs_env) (top_insts tbs_env) (map fst cparams) params strt states ,, top_decls tbs_env |>
    | Top.Extern ext TS cparams ecparams methods =>
      mret $ tbs_env <| top_decls := ext ↦ ExternDecl (top_functs tbs_env) (top_insts tbs_env) (map fst cparams) ,, top_decls tbs_env |>
    | Top.Funct f TS arrow body =>
      mret $ tbs_env <| top_functs := f ↦ FDecl (top_functs tbs_env) arrow.(Arr.inout) body ,, top_functs tbs_env |>
    | Top.Instantiate c x τs cargs es =>
      let* decls := top_decls tbs_env c in
      let* vs := interpret_exps [] es in
      match decls, τs with
      | ControlDecl cfs cinsts cparams params local_decls apply_blk, [] =>
        let^ cbs_env := interpret_ctrls local_decls {| cbs_tables := ∅; cbs_actions := ∅; cbs_epsilon  := vs |} in
        tbs_env
          <| top_insts :=
          x ↦ ControlInst
            cfs (bind_constructor_args cparams cargs (top_insts tbs_env) cinsts)
            (cbs_tables cbs_env) (cbs_actions cbs_env) vs params apply_blk ,, top_insts tbs_env |>
      | ParserDecl pfs pinsts cparams params strt states, [] =>
        mret $ tbs_env
          <| top_insts :=
          x ↦ ParserInst
            pfs (bind_constructor_args cparams cargs (top_insts tbs_env) pinsts)
            vs params strt states ,, top_insts tbs_env |>
      | ExternDecl extfs extinsts cparams, _ =>
        mret $ tbs_env <| top_insts := x ↦ ExternInst extfs (bind_constructor_args cparams cargs (top_insts tbs_env) extinsts) vs ,, top_insts tbs_env |>
      | _, _ => None
      end
    end.

    Lemma interpret_top_sound :
      forall env top env',
        interpret_top env top = Some env' -> top_big_step env top env'.
    Proof.
      destruct top; cbn; unravel; intros.
      - repeat match_some_inv. destruct t.
        + destruct type_args; try discriminate. match_some_inv. some_inv.
          econstructor; eauto.
          * apply interpret_exps_sound. assumption.
          * apply interpret_ctrls_sound. assumption.
        + destruct type_args; try discriminate. some_inv.
          constructor. assumption. apply interpret_exps_sound. assumption.
        + some_inv. constructor. assumption. apply interpret_exps_sound. assumption.
      - some_inv. constructor.
      - some_inv. constructor.
      - some_inv. constructor.
      - some_inv. constructor.
    Qed.

End Top.
