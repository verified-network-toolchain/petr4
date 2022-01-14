Require Import Poulet4.Syntax.
Require Import Poulet4.ExprInd.
Require Poulet4.Semantics.
Require Poulet4.Interpreter.
Check @Interpreter.interp_expr.
Print Interpreter.interp_expr.

Section InterpreterSafe.
  Context {tags_t: Type} {tag: Sublist.Inhabitant tags_t}.
  Variable (target: @Target.Target tags_t (@Expression tags_t)).
  Variable (ge: Semantics.genv).
  Variable (read_one_bit: option bool -> bool -> Prop).
  Theorem interp_expr_safe:
    forall expr this st sv,
      Interpreter.interp_expr ge this st expr = Some sv ->
      Semantics.exec_expr ge ValueUtil.read_ndetbit this st expr sv.
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
    - cbn in H. destruct (Semantics.is_directional dir) eqn:?H.
      + constructor; auto.
      + now apply Semantics.exec_expr_name_const.
    - cbn in H. destruct (Interpreter.interp_expr ge this st expr2) eqn:?H;
        unfold Option.option_bind in H. 2: inversion H.
      destruct (Semantics.array_access_idx_to_z
                  (Interpreter.interp_sval_val v)) eqn: ?H. 2: inversion H.
      destruct (Interpreter.interp_expr ge this st expr1) eqn:?H. 2: inversion H.
      destruct v0; try now inversion H.
      destruct (Semantics.get_real_type ge typ) eqn:?H. 2: inversion H.
      destruct (ValueUtil.uninit_sval_of_typ None p) eqn:?H. 2: inversion H.
      inversion H; subst; clear H. econstructor; eauto. red. clear H0.
      induction v; simpl in H1; try now inversion H1.
      all: simpl; constructor.
      + clear. induction value; simpl; constructor; auto.
        unfold Interpreter.bit_init. destruct a; constructor.
      + clear. induction value; simpl; constructor; auto.
        unfold Interpreter.bit_init. destruct a; constructor.
      + apply IHv; auto.
    - cbn in H.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
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

End InterpreterSafe.
