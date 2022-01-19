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
    forall (name : P4String.t tags_t) (sv v : Value.ValueBase),
    Interpreter.find_member v (P4String.str name) = Some sv ->
    Semantics.get_member v (P4String.str name) sv.
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
      destruct (BinInt.Z.geb a0 Z0) eqn:?; try congruence.
      econstructor; eauto.
      inversion Heqo2; subst.
      + econstructor; eauto.
        eapply interp_expr_safe; eauto.
      + admit. (* need to change defn in Semantics for this to go through. *)
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
        * (* Issue: size is no longer constrained by anything since it is not part of the value datatype anymore. *)
          admit.
      + inversion H; subst.
        econstructor.
        * assumption.
        * eapply IHexpr; eauto.
  (* some shelved goals left that need investigating, probably more
  unconstrained constructor parameters. *)
  Admitted.

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

  Theorem interp_stmt_safe:
    forall stmt this st fuel st' sig,
      Interpreter.interp_stmt ge this st fuel stmt = Some (st', sig) ->
      Semantics.exec_stmt ge read_ndetbit this st stmt st' sig.
  Proof.
    intro stmt.
    pattern stmt.
    eapply (Syntax.statement_rec
              (PBlock := block_safe)
              (PStatement := stmt_safe)
              (PStatementMaybe := fun s =>
                                    match s with
                                    | Some stmt => stmt_safe stmt
                                    | None => True
                                    end)
              (PStatementPreT := pre_stmt_safe)
              (PStatementSwitchCase := fun _ => True)
              (PStatementSwitchCaseList := fun _ => True)
              (PInitializer := fun _ => True)
              (PInitializerList := fun _ => True)
           );
      unfold pre_stmt_safe, stmt_safe, block_safe;
      intros.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - destruct fuel; [discriminate|].
      unfold Interpreter.interp_stmt in H.
      inversion H; subst.
      constructor.
    - destruct fuel; [discriminate|].
      unfold Interpreter.interp_stmt in H.
      inversion H; subst.
      constructor.
    - admit.
    - admit.
    - admit.
    - admit.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - destruct fuel; discriminate.
    - eauto.
    - tauto.
    - eauto.
    - destruct fuel; [discriminate|].
      inversion H; subst.
      constructor.
    - destruct fuel; [discriminate|].
      set (eval :=
             let* (st, sig) := Interpreter.interp_stmt ge this st fuel stmt0 in
             let* (st', sig') :=
                Interpreter.interp_block ge this st fuel
                                         (if Semantics.is_continue sig
                                          then rest
                                          else Semantics.empty_block)
             in
             Some (st', if Semantics.is_continue sig then sig' else sig)).
      assert (eval = Some (st', sig)) by (rewrite <- H1; reflexivity).
      unfold eval in H2.
      simpl in H2.
      optbind_inv.
      destruct a.
      optbind_inv.
      destruct a.
      inversion H2.
      subst.
      econstructor.
      + eapply H.
        eapply Heqo.
      + destruct (Semantics.is_continue s0) eqn:?.
        * eapply H0; eauto.
        * destruct fuel; [discriminate|].
          inversion Heqo0; subst.
          constructor.
  Admitted.

End InterpreterSafe.