Require Import Poulet4.Syntax.
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
      Semantics.exec_expr ge read_one_bit this st expr sv.
  Proof.
    destruct expr.
    (* Will need a real induction scheme. Not sure if that's defined anywhere already. *)
    induction expr; intros.
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
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
  
End InterpreterSafe.
