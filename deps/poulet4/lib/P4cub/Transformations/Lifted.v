Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Transformations.Statementize
        Coq.Numbers.DecimalString
        Coq.Strings.Ascii Coq.Strings.String.
Import P4cub.P4cubNotations StringSyntax Field.FieldTactics.
Module E := P4cub.Expr.
Module ST := P4cub.Stmt.

Section Lifted.
  (*Open Scope char_scope.*)
  Open Scope string_scope.
  
  Context {tags_t : Type}.
  
  Inductive lifted_expr : E.e tags_t -> Prop :=
  | lifted_bool b i :
      lifted_expr <{ BOOL b @ i }>
  | lifted_var x τ i :
      lifted_expr <{ Var x:τ @ i }>
  | lifted_member e x τ i :
      lifted_expr e ->
      lifted_expr <{ Mem e:τ dot x @ i }>
  | lifted_error err i :
      lifted_expr <{ Error err @ i }>
  | lifted_matchkind mk i :
      lifted_expr <{ Matchkind mk @ i }>
  | lifted_access e z i :
      lifted_expr e ->
      lifted_expr <{ Access e[z] @ i }>.

  Local Hint Constructors lifted_expr : core.

  Ltac transformExpr_destr :=
    match goal with
    | |- context [TransformExpr _ ?e ?env]
      => destruct (TransformExpr _ e env) as [[? ?] ?] eqn:?; simpl in *
    end.

  Ltac transformExpr_destr_hyp :=
    match goal with
    | H: context [TransformExpr _ ?e ?env] |- _
      => destruct (TransformExpr _ e env) as [[? ?] ?] eqn:?; simpl in *
    end.

  Ltac fold_destr :=
    match goal with
    | |- context [fold_left ?f ?l ?acc]
      => destruct (fold_left f l acc) as [[? ?] ?] eqn:Hfoldl; simpl in *
    | |- context [fold_right ?f ?acc ?l]
      => destruct (fold_right f acc l) as [[? ?] ?] eqn:Hfoldl; simpl in *
    end.
  
  (*Arguments VarNameGen.new_var env : simpl never.*)
  
  Lemma TransformExpr_lifted : forall e env,
      lifted_expr (snd (fst (TransformExpr _ e env))).
  Proof.
    intro e; induction e using custom_e_ind;
      intro env; unravel in *;
        repeat transformExpr_destr; auto;
        try (generalize dependent env;
             unfold TransformExprList';
             ind_list_Forall; intro env; simpl;
             try fold_destr; auto; assumption);
        try (generalize dependent env;
             unfold TransformFields', Field.fold;
             ind_list_predfs; intro env; simpl; auto;
             try fold_destr; auto;
             destruct p as [? ?] eqn:Heqp;
             repeat transformExpr_destr; auto; assumption);
        try (constructor; specialize IHe with env;
             transformExpr_destr_hyp; inv Heqp; auto; assumption).
  Qed.
End Lifted.
