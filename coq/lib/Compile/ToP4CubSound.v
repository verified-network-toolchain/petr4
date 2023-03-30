Require Import Poulet4.Compile.ToP4cub.
Require Import Poulet4.P4cub.ExportAll.
Require Import Poulet4.P4light.Semantics.ExportAll.

Check translate_expression.

Section ToP4CubSound.
  Variable (tags_t: Type).
  Context {t: @Target tags_t (@Expression tags_t)}.

  Inductive read_one_bit: option bool -> bool -> Prop :=
  | ReadSome: forall b, read_one_bit (Some b) b
  | ReadNoneFalse: read_one_bit None false.

  Definition val_rel
             (light_val: @ValueBase (option bool))
             (cub_val: Val.v) : Prop :=
    exists light_val_det,
      exec_val read_one_bit light_val light_val_det /\
      Embed cub_val light_val_det.

  Definition env_rel (light_env: state) (cub_env: list Val.v) : Prop :=
    False.

  Lemma translate_expression_sound :
    forall typ_names term_names (light_expr: Expression) (cub_expr: E.e),
      translate_expression tags_t typ_names term_names light_expr = Result.Ok cub_expr ->
      forall cub_env cub_val,
        expr_big_step cub_env cub_expr cub_val ->
        forall ge this (light_env: state),
          env_rel light_env cub_env ->
          exists light_val,
            exec_expr ge read_one_bit this light_env light_expr light_val /\
            val_rel light_val cub_val.
  Proof.
    induction light_expr using expr_ind; intros;
      simpl translate_expression in *;
      try (simpl_result_all; subst).
    - inversion H0; subst.
      exists (ValBaseBool (Some b)); split.
      + constructor.
      + econstructor; split.
        * constructor.
          constructor.
        * constructor.
    - admit.
    - admit.
    - (* Names *)
      destruct n as [[? ?]|? ?];
        simpl_result_all;
        [|tauto].
      apply from_opt_Ok in Hw.
      destruct (translate_exp_type _ _ _) eqn:?.
      + simpl_result_all.
        inversion Hw0; subst.
        eexists.
        split.
        * constructor.
          admit.
          inversion H0; subst.
          
        admit.
        * admit.
      + simpl_result_all.
        congruence.
    - admit.
    - admit.
    - admit.
    - admit.
    - (* unary operations *)
      admit.
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

End ToP4CubSound.
