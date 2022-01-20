Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Poulet4.Syntax.
Require Import Poulet4.SyntaxUtil.
Require Import Poulet4.ValueUtil.
Require Import Poulet4.ExprInd.
Require Import Poulet4.Monads.Monad.
Require Import Poulet4.Monads.Option.
Require Poulet4.Semantics.
Require Poulet4.Interpreter.
Check @Interpreter.interp_expr.
Print Interpreter.interp_expr.

Ltac destruct_match H :=
  match goal with
  | H: context [match ?A with | _ => _ end] |- _ => destruct A eqn:?H
  end.

Ltac destruct_optbind H :=
  match goal with
  | H: context [Option.option_bind _ _ ?A _] |- _ =>
      destruct A eqn:?H; unfold Option.option_bind in H
  end.

Lemma val_to_sval_eval:
  forall v : Value.ValueBase, val_to_sval v (eval_val_to_sval v).
Proof.
  remember (fix eval_val_to_svals (vl : list Value.ValueBase) : list Value.ValueBase :=
              match vl with
              | nil => nil
              | (s :: rest)%list => (eval_val_to_sval s :: eval_val_to_svals rest)%list
              end) as eval_val_to_svals. rename Heqeval_val_to_svals into Hevals.
  remember (fix val_to_avals (sl : AList.StringAList Value.ValueBase) :
             AList.StringAList Value.ValueBase :=
              match sl with
              | nil => nil
              | ((k, s) :: rest)%list =>
                  ((k, eval_val_to_sval s) :: val_to_avals rest)%list
              end) as val_to_avals. rename Heqval_to_avals into Havals.
  unfold val_to_sval.
  induction v using Value.custom_ValueBase_ind; try (now constructor); simpl.
  1, 3: constructor; induction n; simpl; constructor; auto; easy.
  1: constructor; induction z; simpl; constructor; auto; easy.
  1, 6: rewrite <- Hevals; constructor; induction H; rewrite Hevals;
  [constructor | rewrite <- Hevals; constructor; auto].
  1, 2, 4: rewrite <- Havals; constructor; induction H; rewrite Havals;
  [constructor | rewrite <- Havals; destruct x; constructor; simpl; auto].
  rewrite <- Havals. constructor. 1: constructor. induction H; rewrite Havals.
  1: constructor. rewrite <- Havals. destruct x. constructor; simpl; auto.
Qed.

#[local] Hint Resolve val_to_sval_eval : core.

Lemma read_ndetbit_init:
  forall b : option bool, read_ndetbit b (Interpreter.bit_init b).
Proof. intros b. unfold Interpreter.bit_init. destruct b; constructor. Qed.

#[local] Hint Resolve read_ndetbit_init : core.

Lemma sval_to_val_interp: forall v : Value.ValueBase,
    sval_to_val read_ndetbit v (Interpreter.interp_sval_val v).
Proof.
  unfold sval_to_val. induction v using Value.custom_ValueBase_ind;
    try (now constructor); simpl; constructor; auto.
  1, 3: induction n; simpl; constructor; auto.
  1: induction z; simpl; constructor; auto.
  1, 6: induction H; simpl; constructor; auto.
  all: induction H; simpl; constructor; destruct x; auto.
Qed.

#[local] Hint Resolve sval_to_val_interp : core.

Section InterpreterSafe.
  Context {tags_t: Type} {tag: Sublist.Inhabitant tags_t}.
  Variable (target: @Target.Target tags_t (@Expression tags_t)).
  Variable (ge: Semantics.genv).
  Variable (read_one_bit: option bool -> bool -> Prop).

  Lemma find_member_get:
    forall (name : string) (sv v : Value.ValueBase),
    Interpreter.find_member v name = Some sv ->
    Semantics.get_member v name sv.
  Proof.
    intros. revert sv H. induction v using Value.custom_ValueBase_ind; intros;
      try (now inversion H); simpl in H0; try now constructor. destruct_match H0.
    - rewrite e. inversion H0. subst. clear H0. constructor.
    - destruct_match H0. 2: inversion H0. rewrite e. constructor.
      unfold Interpreter.last_index_of_next in H0.
      destruct_match H0; [|inversion H0]; auto.
  Qed.

  Theorem interp_expr_safe:
    forall expr this st sv,
      Interpreter.interp_expr ge this st expr = Some sv ->
      Semantics.exec_expr ge read_ndetbit this st expr sv.
  Proof.
    induction expr using expr_ind; intros.
    - cbv in H.
      inversion H.
      subst sv.
      constructor.
    - cbn in H.
      unfold Option.option_ret in H.
      inversion H.
      subst sv.
      constructor.
      reflexivity.
    - cbv in H.
      inversion H.
      subst sv.
      constructor.
    - cbn in H. destruct_match H.
      + constructor; auto.
      + now apply Semantics.exec_expr_name_const.
    - cbn in H. destruct_optbind H. 2: inversion H.
      destruct_match H. 2: inversion H. destruct_match H. 2: inversion H.
      destruct v0; try now inversion H. destruct_match H. 2: inversion H.
      destruct_match H; inversion H; subst; clear H. econstructor; eauto.
    - cbn in H. destruct_optbind H. 2: inversion H.
      destruct_match H. 2: inversion H. destruct p.
      destruct n. 1: rewrite Bool.andb_false_r in H; inversion H.
      destruct_match H; inversion H; subst; clear H. econstructor; eauto.
      apply andb_prop in H2. destruct H2. apply PeanoNat.Nat.leb_le in H, H2. lia.
    - cbn in H0. destruct_optbind H0; inversion H0. subst; clear H0.
      constructor. revert l H1. induction H; intros.
      + simpl in H1. inversion H1. constructor.
      + destruct l0; simpl in H1; destruct_match H1; try now inversion H1.
        all: destruct_match H1; inversion H1; subst. constructor; auto.
    - cbn in H0. destruct_optbind H0; inversion H0. subst. clear H0.
      constructor. revert l H1. induction H; intros.
      + simpl in H1. inversion H1. simpl. constructor.
      + destruct l0; simpl in H1; destruct x; destruct_match H1; try now inversion H1.
        all: destruct_match H1; inversion H1; subst. clear H1.
        simpl. destruct t0. simpl. constructor; auto. now apply IHForall.
    - cbn in H. destruct_optbind H. 2: inversion H. destruct_match H. 2: inversion H.
      unfold Interpreter.interp_val_sval in H. inversion H; subst; clear H.
      econstructor; eauto.
    - cbn in H. destruct args. destruct_optbind H. 2: inversion H.
      do 2 (destruct_match H; [| inversion H]).
      unfold Interpreter.interp_val_sval in H. inversion H; subst; clear H.
      econstructor; eauto.
    - cbn in H. destruct_optbind H. 2: inversion H. destruct_match H; [| inversion H].
      destruct_match H; inversion H; subst. econstructor; eauto.
    - cbn in H. destruct_optbind H. 2: inversion H. destruct p; inversion H.
      clear H2. destruct typ0.
      + destruct_match H. 2: inversion H.
        destruct_match H; inversion H; subst; clear H. econstructor; eauto.
      + destruct_match H; inversion H. subst. clear H. econstructor; eauto.
        apply List.find_some in H1. admit.
    - simpl in H. inversion H. subst. constructor.
    - cbn in H. destruct_optbind H. 2: inversion H.
      destruct_match H; inversion H; subst; clear H. econstructor; eauto.
      now apply find_member_get.
    - cbn in H. destruct_optbind H. 2: inversion H. destruct_match H; inversion H.
      clear H3. assert (sval_to_val read_ndetbit v (Value.ValBaseBool b)). {
        rewrite <- H1. auto. } econstructor; eauto. destruct b; auto.
    - simpl in H0. inversion H0.
    - simpl in H0. inversion H0.
    - simpl in H. inversion H. constructor.
  Admitted.

  (* This theorem is not really completeness, but close enough.
   * We don't expect every behavior of exec_expr to be exhibited by
   * the interpreter, but things that do run under exec_expr should at
   * least evaluate to something under interp_expr. They may differ due
   * to how the interpreter resolves nondeterminism.
   *
   * This is a lower priority to prove, IMO, than safety/soundness.
   *)
  Theorem interp_expr_complete:
    forall expr this st sv,
      Semantics.exec_expr ge read_one_bit this st expr sv ->
      exists sv',
        Interpreter.interp_expr ge this st expr = Some sv'.
  Proof.
  Admitted.

  Ltac optbind_inv :=
    match goal with
    | H: Option.option_bind _ _ ?c ?f = Some ?v |- _ =>
      let a := fresh "a" in
      destruct c as [a|] eqn:?;
      simpl in H;
      [|congruence]
    end.

  Lemma sval_to_bits_width_sval_val_comm:
    forall (sv: @Value.ValueBase (option bool)) bits len,
      Semantics.sval_to_bits_width sv = Some (bits, len) ->
      Semantics.sval_to_bits_width (Interpreter.interp_sval_val sv) = Some (Interpreter.bits_init bits, len).
  Proof.
    intros.
    unfold Semantics.sval_to_bits_width.
    destruct sv;
      cbn in *;
      try intuition congruence.
    - inversion H.
      subst len.
      inversion H; subst; auto.
      unfold Interpreter.bits_init.
      rewrite List.map_length.
      reflexivity.
    - inversion H.
      subst len.
      inversion H; subst; auto.
      unfold Interpreter.bits_init.
      rewrite List.map_length.
      reflexivity.
  Qed.

  Theorem interp_lexpr_safe:
    forall expr this st lv sig,
      Interpreter.interp_lexpr ge this st expr = Some (lv, sig) ->
      Semantics.exec_lexpr ge read_ndetbit this st expr lv sig.
  Proof.
    induction expr using expr_ind;
      try solve [simpl; intros; congruence].
    - intros.
      simpl.
      inversion H; subst. 
      constructor.
    - intros.
      cbn in H.
      repeat optbind_inv.
      destruct a.
      repeat optbind_inv.
      inversion H; subst.
      destruct (Interpreter.interp_sval_val a) eqn:?; try discriminate.
      destruct (BinInt.Z.ltb a2 Z0) eqn:?.
      + econstructor; eauto.
        * econstructor;
            [|rewrite <- Heqv0;
              eauto using sval_to_val_interp];
          eapply interp_expr_safe; eauto.
        * econstructor; eauto.
          eapply interp_expr_safe; eauto.
        * rewrite Heqb.
          congruence.
      + econstructor; eauto.
        * econstructor;
            [|rewrite <- Heqv0;
              eauto using sval_to_val_interp];
          eapply interp_expr_safe; eauto.
        * econstructor; eauto.
          eapply interp_expr_safe; eauto.
        * rewrite Heqb.
          congruence.
    - intros.
      simpl in H.
      repeat optbind_inv.
      destruct a.
      repeat optbind_inv.
      destruct a0.
      destruct ((lo <=? hi)%N && (hi <? N.of_nat n)%N)%bool eqn:?;
               [|congruence].
      inversion H; subst.
      econstructor; eauto using sval_to_bits_width_sval_val_comm.
      + econstructor; eauto using interp_expr_safe.
      + apply andb_prop in Heqb.
        destruct Heqb.
        split.
        * now apply N.leb_le.
        * apply N.ltb_lt; eauto.
    - intros.
      simpl in H.
      repeat optbind_inv.
      destruct a.
      destruct (P4String.str name =? "next")%string eqn:?.
      + optbind_inv.
        destruct a; try congruence.
        inversion H; subst.
        econstructor.
        * assumption.
        * eapply IHexpr.
          eassumption.
        * eapply interp_expr_safe; eauto.
        * destruct (next <? N.of_nat _)%N; reflexivity.
      + inversion H; subst.
        econstructor.
        * assumption.
        * eapply IHexpr; eauto.
  Qed.

  Theorem interp_read_safe:
    forall lv ge st v,
      Interpreter.interp_read ge st lv = Some v ->
      Semantics.exec_read ge st lv v.
  Proof.
    intro lv.
    pattern lv.
    match goal with
    | |- ?P lv => set (lval_ok := P)
    end.
    set (pre_lval_ok plv := forall typ, lval_ok (Value.MkValueLvalue plv typ)).
    eapply (ValueUtil.lvalue_mut_ind lval_ok pre_lval_ok); repeat (intros; unfold lval_ok, pre_lval_ok in *; simpl).
    - eapply H; eauto.
    - constructor.
      assumption.
    - simpl in H0.
      optbind_inv.
      econstructor; eauto using find_member_get.
    - simpl in H0.
      optbind_inv.
      optbind_inv.
      destruct a0.
      destruct (PeanoNat.Nat.leb (N.to_nat lo) (N.to_nat hi) && PeanoNat.Nat.ltb (N.to_nat hi) n)%bool
               eqn:?;
               [|discriminate].
      inversion H0; subst.
      econstructor; eauto.
      apply andb_prop in Heqb.
      destruct Heqb.
      split.
      + eapply Bool.reflect_iff in H1; eauto using PeanoNat.Nat.leb_spec0.
      + eapply Bool.reflect_iff in H2; eauto using PeanoNat.Nat.leb_spec0.
    - simpl in H0.
      optbind_inv.
      destruct a; try discriminate.
      optbind_inv.
      optbind_inv.
      inversion H0.
      subst.
      econstructor; eauto.
  Qed.

  Lemma set_member_safe:
    forall hdr fname v hdr',
      Interpreter.set_member hdr fname v = Some hdr' ->
      Semantics.update_member hdr fname v hdr'.
  Proof.
    destruct hdr; intros; try discriminate.
    - simpl in H.
      optbind_inv.
      inversion H.
      subst.
      now constructor.
    - simpl in H.
      constructor.
      unfold Interpreter.set_header_field in H.
      destruct is_valid as [[ | ] | ]; simpl in H;
        optbind_inv;
        inversion H;
        constructor;
        auto.
    - simpl in H.
      destruct v; try discriminate.
      optbind_inv.
      inversion H.
      subst.
      econstructor; eauto.
  Qed.

  Definition lval_safe lv :=
    forall ge st v st',
      Interpreter.interp_write ge st lv v = Some st' ->
      Semantics.exec_write ge st lv v st'.

  Definition pre_lval_safe plv :=
    forall typ, lval_safe (Value.MkValueLvalue plv typ).

  Theorem interp_write_safe:
    forall lv ge st v st',
      Interpreter.interp_write ge st lv v = Some st' ->
      Semantics.exec_write ge st lv v st'.
  Proof.
    simpl.
    eapply (ValueUtil.lvalue_mut_ind lval_safe pre_lval_safe);
      unfold pre_lval_safe, lval_safe; intros.
    - apply H; auto.
    - simpl in H.
      inversion H.
      subst.
      constructor.
      auto.
    - simpl in H0.
      optbind_inv.
      optbind_inv.
      apply H in H0.
      econstructor; eauto using interp_read_safe, set_member_safe.
    - simpl in H0.
      optbind_inv.
      destruct v; try discriminate.
      destruct a; try discriminate.
      + destruct (PeanoNat.Nat.leb (N.to_nat lo) (N.to_nat hi) &&
                  PeanoNat.Nat.ltb (N.to_nat hi) (Datatypes.length value0))%bool
                 eqn:?;
                 [|discriminate].
        rewrite Bool.andb_true_iff in Heqb.
        destruct Heqb as [Hle Hlt].
        rewrite <- Bool.reflect_iff in Hle
          by eauto using PeanoNat.Nat.leb_spec0.
        rewrite <- Bool.reflect_iff in Hlt
          by eauto using PeanoNat.Nat.ltb_spec0.
        solve [econstructor; eauto using interp_read_safe].
      + destruct (PeanoNat.Nat.leb (N.to_nat lo) (N.to_nat hi) &&
                  PeanoNat.Nat.ltb (N.to_nat hi) (Datatypes.length value0))%bool
                 eqn:?;
                 [|discriminate].
        rewrite Bool.andb_true_iff in Heqb.
        destruct Heqb as [Hle Hlt].
        rewrite <- Bool.reflect_iff in Hle
          by eauto using PeanoNat.Nat.leb_spec0.
        rewrite <- Bool.reflect_iff in Hlt
          by eauto using PeanoNat.Nat.ltb_spec0.
        solve [econstructor; eauto using interp_read_safe].
    - simpl in H0.
      optbind_inv.
      destruct a;
        try discriminate.
      econstructor; eauto using interp_read_safe.
  Qed.

  Definition stmt_safe stmt :=
    forall this st fuel st' sig,
      Interpreter.interp_stmt ge this st fuel stmt = Some (st', sig) ->
      Semantics.exec_stmt ge read_ndetbit this st stmt st' sig.

  Definition pre_stmt_safe pre_stmt :=
    forall tags styp,
      stmt_safe (MkStatement tags pre_stmt styp).

  Definition block_safe block :=
    forall this st fuel st' sig,
      Interpreter.interp_block ge this st fuel block = Some (st', sig) ->
      Semantics.exec_block ge read_ndetbit this st block st' sig.

  Definition switch_case_safe switch_case :=
    match switch_case with
    | StatSwCaseAction _ _ block => block_safe block
    | StatSwCaseFallThrough _ _ => True
    end.

  Definition switch_cases_safe switch_cases :=
    forall member,
      block_safe (Semantics.match_switch_case member switch_cases).

  Lemma empty_block_safe:
    forall tags,
      block_safe (BlockEmpty tags).
  Proof.
    unfold block_safe.
    intros.
    destruct fuel; [discriminate|].
    cbn in H.
    inversion H.
    constructor.
  Qed.

  Lemma interp_expr_det_safe:
    forall this st expr v,
      Interpreter.interp_expr_det ge this st expr = Some v ->
      Semantics.exec_expr_det ge read_ndetbit this st expr v.
  Proof.
    unfold Interpreter.interp_expr_det.
    intros.
    simpl in H.
    optbind_inv.
    inversion H.
    econstructor.
    - eapply interp_expr_safe.
      eapply Heqo.
    - eapply sval_to_val_interp.
  Qed.

  Lemma interp_arg_safe:
    forall this st exp dir arg sig,
      Interpreter.interp_arg ge this st exp dir = Some (arg, sig) ->
      Semantics.exec_arg ge read_ndetbit this st exp dir arg sig.
  Proof.
    intros.
    unfold Interpreter.interp_arg in H.
    destruct exp.
    - destruct dir;
        simpl in *;
        try (optbind_inv; inversion H);
        subst.
      + econstructor; eauto using interp_expr_det_safe.
      + destruct a.
        inversion H.
        subst.
        econstructor; eauto using interp_lexpr_safe.
      + destruct a.
        optbind_inv.
        optbind_inv.
        inversion H.
        subst.
        econstructor; eauto using interp_lexpr_safe, interp_read_safe.
      + discriminate.
    - destruct dir; try discriminate.
      inversion H.
      econstructor; eauto.
  Qed.

  Lemma interp_args_safe:
    forall exps this st dirs args sig,
      Interpreter.interp_args ge this st exps dirs = Some (args, sig) ->
      Semantics.exec_args ge read_ndetbit this st exps dirs args sig.
  Proof.
    induction exps; intros.
    - simpl.
      destruct dirs; simpl in H.
      + inversion H.
        constructor.
      + discriminate.
    - destruct dirs; simpl in H; try discriminate.
      optbind_inv.
      destruct a0.
      optbind_inv.
      destruct a1.
      inversion H.
      subst.
      econstructor; eauto using interp_arg_safe.
      destruct (Semantics.is_continue s); reflexivity.
  Qed.

  Definition fuel_stmt_safe (fuel: nat) : Prop :=
    forall stmt this st st' sig,
      Interpreter.interp_stmt ge this st fuel stmt = Some (st', sig) ->
      Semantics.exec_stmt ge read_ndetbit this st stmt st' sig.

  Definition fuel_block_safe (fuel: nat) : Prop :=
    forall block this st st' sig,
      Interpreter.interp_block ge this st fuel block = Some (st', sig) ->
      Semantics.exec_block ge read_ndetbit this st block st' sig.

  Definition fuel_call_safe (fuel: nat) : Prop :=
    forall this st call st' sig,
      Interpreter.interp_call ge this st fuel call = Some (st', sig) ->
      Semantics.exec_call ge read_ndetbit this st call st' sig.

  Definition fuel_func_safe (fuel: nat) : Prop :=
    forall this st fn typ_args args st' retvs sig,
      Interpreter.interp_func ge this st fuel fn typ_args args = Some (st', retvs, sig) ->
      Semantics.exec_func ge read_ndetbit this st fn typ_args args st' retvs sig.

  Theorem fuel_safe:
    forall fuel,
      fuel_stmt_safe fuel /\
      fuel_block_safe fuel /\
      fuel_call_safe fuel /\
      fuel_func_safe fuel.
  Proof.
    induction fuel;
      unfold fuel_stmt_safe, fuel_block_safe, fuel_call_safe, fuel_func_safe;
      [unfold Interpreter.interp_stmt,
              Interpreter.interp_block,
              Interpreter.interp_call,
              Interpreter.interp_func;
       intuition discriminate|].
    destruct IHfuel as [IHstmt [IHblock [IHcall IHfunc]]].
    repeat split; intros;
      [destruct stmt; destruct stmt
      |destruct block
      |destruct call; destruct expr; try solve [unfold Interpreter.interp_call in H;
                                                discriminate]
      |destruct fn].
    - cbn in H.
      optbind_inv.
      destruct a.
      inversion H.
      subst.
      econstructor; eauto.
    - cbn in H.
      destruct (Interpreter.is_call rhs) eqn:?.
      + optbind_inv.
        destruct a.
        optbind_inv.
        destruct a.
        destruct (Semantics.not_continue s1) eqn:?.
        * eapply Semantics.exec_stmt_assign_func_call; eauto using interp_lexpr_safe.
          rewrite Heqb0.
          intuition congruence.
        * destruct (Semantics.not_return s0) eqn:?.
          -- eapply Semantics.exec_stmt_assign_func_call; eauto using interp_lexpr_safe.
             rewrite Heqb0, Heqb1.
             destruct s0; simpl in *; intuition congruence.
          -- destruct s0; try discriminate.
             optbind_inv.
             inversion H.
             subst.
             destruct s1; try discriminate.
             eapply Semantics.exec_stmt_assign_func_call; eauto using interp_lexpr_safe.
             rewrite Heqb0, Heqb1.
             repeat split; eauto using interp_write_safe.
      + optbind_inv.
        eapply interp_expr_det_safe in Heqo.
        optbind_inv.
        destruct a0.
        optbind_inv.
        inversion H; subst.
        econstructor; eauto using interp_lexpr_safe.
        destruct (Semantics.is_continue sig) eqn:?;
                 eauto using interp_write_safe.
    - cbn in H.
      optbind_inv.
      destruct a.
      inversion H.
      subst.
      econstructor; eauto.
    - cbn in H.
      destruct fls.
      + optbind_inv.
        destruct (Interpreter.interp_sval_val a) eqn:?; try discriminate.
        econstructor; eauto.
        econstructor;
          [|rewrite <- Heqv; eapply sval_to_val_interp].
        eapply interp_expr_safe; eauto.
      + optbind_inv.
        destruct (Interpreter.interp_sval_val a) eqn:?; try discriminate.
        econstructor; eauto.
        econstructor;
          [|rewrite <- Heqv; eapply sval_to_val_interp].
        eapply interp_expr_safe; eauto.
    - set (eval := Interpreter.interp_block ge this st fuel block).
      assert (eval = Some (st', sig))
        by (rewrite <- H; reflexivity).
      unfold eval in *.
      constructor; eauto.
    - inversion H.
      constructor.
    - inversion H.
      constructor.
    - cbn in H.
      destruct expr.
      + optbind_inv.
        inversion H.
        subst.
        econstructor.
        econstructor;
          eauto using sval_to_val_interp, interp_expr_safe.
      + inversion H. 
        subst.
        econstructor.
    - cbn in H.
      optbind_inv.
      destruct (Interpreter.interp_sval_val a) eqn:?; try discriminate.
      econstructor.
      + rewrite <- Heqv.
        econstructor;
          eauto using sval_to_val_interp, interp_expr_safe.
      + reflexivity.
      + eauto.
    - cbn in H.
      inversion H.
      subst.
      constructor.
    - cbn in H.
      destruct init.
      + destruct (Interpreter.is_call e) eqn:?.
        * optbind_inv.
          destruct a.
          destruct s0; simpl in *.
          -- inversion H.
             subst.
             change Value.SContinue with (Semantics.force_continue_signal Value.SContinue).
             eapply Semantics.exec_stmt_variable_func_call; eauto.
             simpl.
             eauto.
          -- inversion H.
             subst.
             change Value.SContinue with (Semantics.force_continue_signal (Value.SReturn v)).
             eapply Semantics.exec_stmt_variable_func_call; eauto.
             simpl.
             repeat split; eauto using interp_write_safe.
          -- inversion H.
             change Value.SExit with (Semantics.force_continue_signal Value.SExit).
             eapply Semantics.exec_stmt_variable_func_call; eauto.
             simpl; intuition eauto.
          -- inversion H.
             subst.
             change (Value.SReject s0) with (Semantics.force_continue_signal (Value.SReject s0)).
             eapply Semantics.exec_stmt_variable_func_call; eauto.
             simpl; intuition eauto.
        * optbind_inv.
          inversion H.
          optbind_inv.
          inversion Heqo.
          econstructor; [ | | rewrite <- H1; eapply interp_write_safe; reflexivity];
            eauto.
          econstructor; eauto using sval_to_val_interp, interp_expr_safe.
      + optbind_inv.
        optbind_inv.
        inversion H.
        subst.
        econstructor; eauto using interp_write_safe.
    - discriminate.
    - cbn in H.
      inversion H.
      constructor.
    - cbn in H.
      optbind_inv.
      destruct a.
      optbind_inv.
      destruct a.
      inversion H.
      subst.
      econstructor; eauto.
    - destruct (Semantics.is_builtin_func func) eqn:?.
      + destruct func; simpl in Heqb.
        destruct typ0; simpl in Heqb; try discriminate.
        destruct fn; simpl in Heqb; try discriminate.
        destruct kind; simpl in Heqb; try discriminate.
        cbn in H.
        destruct expr; try discriminate.
        destruct type_args; try discriminate.
        optbind_inv.
        destruct a.
        optbind_inv.
        destruct a.
        eapply Semantics.exec_call_builtin; eauto using interp_lexpr_safe, interp_args_safe.
        destruct (Semantics.not_continue s), (Semantics.not_continue s0);
          try intuition congruence.
        admit. (* interp_builtin *)
      + destruct func; simpl in Heqb.
        cbn in H.
        rewrite Heqb in H.
        optbind_inv.
        destruct a.
        optbind_inv.
        destruct a.
        optbind_inv.
        destruct a as [[? ?] ?].
        optbind_inv.
        econstructor; eauto using interp_lexpr_safe, interp_args_safe.
        * admit. (* interp_call_copy_out *)
        * destruct (Semantics.is_continue s); intuition congruence.
    - unfold Interpreter.interp_func in H.
      simpl in H.
      destruct typ_args; [|discriminate].
      optbind_inv.
      destruct a.
      optbind_inv.
      inversion H.
      subst.
      econstructor; eauto.
    - unfold Interpreter.interp_func in H.
      simpl in H.
      destruct default_action, typ_args, args; try discriminate.
      + optbind_inv.
        destruct (Interpreter.interp_table_match ge this st name keys entries) eqn:?.
        destruct a0.
        optbind_inv.
        destruct a.
        optbind_inv.
        destruct a; try discriminate.
        * destruct s1; try discriminate.
          destruct v; try discriminate.
          eapply IHcall in Heqo2.
          inversion H.
          inversion Heqo.
          subst.
          admit. (* need lemma about interp_table_match *)
        * destruct a.
          optbind_inv.
          destruct a; try discriminate.
          destruct s1; try discriminate.
          destruct v; try discriminate.
          inversion H.
          eapply IHcall in Heqo1.
          subst.
          admit. (* need lemma about interp_table_match *)
    - cbn in H.
      destruct st.
      optbind_inv.
      destruct a as [[? ?] ?].
      optbind_inv.
      inversion H.
      subst.
      econstructor.
      + admit. (* svals_to_vals/map *)
      + admit. (* interp_extern/exec_extern *)
      + admit. (* vals_to_svals/lift_option *)
  Admitted.
      
  Theorem interp_call_safe:
    forall this st fuel call st' sig,
      Interpreter.interp_call ge this st fuel call = Some (st', sig) ->
      Semantics.exec_call ge read_ndetbit this st call st' sig.
  Proof.
    intros.
    eapply fuel_safe; eauto.
  Qed.

  Theorem interp_stmt_safe:
    forall stmt this st fuel st' sig,
      Interpreter.interp_stmt ge this st fuel stmt = Some (st', sig) ->
      Semantics.exec_stmt ge read_ndetbit this st stmt st' sig.
  Proof.
    intros.
    eapply fuel_safe.
    eauto.
  Qed.

End InterpreterSafe.
