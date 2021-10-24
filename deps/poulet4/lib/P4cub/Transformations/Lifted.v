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

  Inductive lifted_args : E.arrowE tags_t -> Prop :=
  | lifted_args_arrow tes teo :
      F.predfs_data (P4cub.pred_paramarg_same (lifted_expr ∘ snd)) tes ->
      predop (lifted_expr ∘ snd) teo ->
      lifted_args (P4cub.Arrow tes teo).
  
  Inductive lifted_stmt : ST.s tags_t -> Prop :=
  | lifted_skip i :
      lifted_stmt -{ skip @ i }-
  | lifted_vardecl x τ i :
      lifted_stmt -{ var x:τ @ i }-
  | lifted_assign τ e1 e2 i :
      lifted_expr e1 ->
      lifted_expr e2 ->
      lifted_stmt -{ asgn e1 := e2:τ @ i }-
  | lifted_bit x w n τ τx i ix iw :
      lifted_stmt -{ asgn Var x:τx @ ix := w W n @ iw : τ @ i }-
  | lifted_int x w z τ τx i ix iw :
      lifted_stmt -{ asgn Var x:τx @ ix := w S z @ iw : τ @ i }-
  | lifted_uop op x e τ τx τe i ix ie :
      lifted_expr e ->
      lifted_stmt -{ asgn Var x:τx @ ix := UOP op e:τe @ ie :τ @ i}-
  | lifted_bop op x e1 e2 τ τx τ1 τ2 i ix ie1e2 :
      lifted_expr e1 ->
      lifted_expr e2 ->
      lifted_stmt
      -{ asgn Var x:τx @ ix := BOP e1:τ1 op e2:τ2 @ ie1e2 : τ @ i }-
  | lifted_slice x e hi lo τ τx τe i ix ie :
      lifted_expr e ->
      lifted_stmt
      -{ asgn Var x:τx @ ix := Slice e:τe [hi:lo] @ ie : τ @ i }-
  | lifted_cast x e τ τx τe i ix ie :
      lifted_expr e ->
      lifted_stmt -{ asgn Var x:τx @ ix := Cast e:τe @ ie : τ @ i }-
  | lifted_tuple x es τ τx i ix ies :
      Forall lifted_expr es ->
      lifted_stmt -{ asgn Var x:τx @ ix := tup es @ ies : τ @ i }-
  | lifted_struct x es τ τx i ix ies :
      F.predfs_data (lifted_expr ∘ snd) es ->
      lifted_stmt -{ asgn Var x:τx @ ix := struct { es } @ ies : τ @ i }-
  | lifted_header x e es τ τx i ix ies :
      lifted_expr e ->
      F.predfs_data (lifted_expr ∘ snd) es ->
      lifted_stmt
      -{ asgn Var x:τx @ ix := hdr { es } valid:=e @ ies : τ @ i }-
  | lifted_stack x es n ni τ τx τs i ix ies :
      Forall lifted_expr es ->
      lifted_stmt
      -{ asgn Var x:τx @ ix
         := Stack es:τs[n] nextIndex:=ni @ ies : τ @ i }-
  | lifted_cond e s1 s2 i :
      lifted_expr e ->
      lifted_stmt s1 ->
      lifted_stmt s2 ->
      lifted_stmt -{ if e then s1 else s2 @ i }-
  | lifted_seq s1 s2 i :
      lifted_stmt s1 ->
      lifted_stmt s2 ->
      lifted_stmt -{ s1; s2 @ i }-
  | lifted_block s :
      lifted_stmt s ->
      lifted_stmt -{ b{ s }b }-
  | lifted_extern_method_call e f targs args i :
      lifted_args args ->
      lifted_stmt (ST.SExternMethodCall e f targs args i)
  | lifted_fun_call f targs args i :
      lifted_args args ->
      lifted_stmt (ST.SFunCall f targs args i)
  | lifted_act_call a args i :
      F.predfs_data (P4cub.pred_paramarg_same (lifted_expr ∘ snd)) args ->
      lifted_stmt -{ calling a with args @ i }-
  | lifted_return_void i :
      lifted_stmt -{ returns @ i }-
  | lifted_return_fruit τ e i :
      lifted_expr e ->
      lifted_stmt -{ return e:τ @ i }-
  | lifted_exit i :
      lifted_stmt -{ exit @ i }-
  | lifted_invoke t i :
      lifted_stmt -{ invoke t @ i }-
  | lifted_apply x ext_args args i :
      F.predfs_data (P4cub.pred_paramarg_same (lifted_expr ∘ snd)) args ->
      lifted_stmt -{ apply x with ext_args & args @ i }-.
  
  Local Hint Constructors lifted_expr : core.

  Ltac transformExpr_destr :=
    match goal with
    | |- context [TransformExpr _ ?e ?env]
      => destruct (TransformExpr _ e env) as [[? ?] ?] eqn:?; simpl in *
    end.

  Ltac transformExpr_destr_hyp :=
    match goal with
    | H: context [TransformExpr _ ?e ?env] |- _
      => destruct (TransformExpr _ e env)
        as [[? ?] ?] eqn:?; simpl in *
    end.

  Ltac transformExpr_destr_hyp_rewrite :=
    match goal with
    | H: TransformExpr _ ?e ?env = (_,_,_),
         Hy : context [TransformExpr _ ?e ?env]
      |- _ => rewrite H in Hy; simpl in *
    end.

  (*Ltac quantify_varNameGen :=
    match goal with
    | env: VarNameGen.t, H: (forall _: VarNameGen.t, _)
      |- _ => specialize H with env
    end.*)
  
  Ltac fold_destr :=
    match goal with
    | |- context [fold_left ?f ?l ?acc]
      => destruct (fold_left f l acc) as [[? ?] ?] eqn:Hfoldl; simpl in *
    | |- context [fold_right ?f ?acc ?l]
      => destruct (fold_right f acc l) as [[? ?] ?] eqn:Hfoldl; simpl in *
    end.
  
  Lemma TransformExpr_lifted_expr : forall e env,
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

  Local Hint Constructors lifted_stmt : core.

  Ltac seq_lift :=
    match goal with
    | |- lifted_stmt -{ _; _ @ _ }-
      => apply lifted_seq
    end.

  Local Hint Resolve TransformExpr_lifted_expr : core.
  
  Lemma TransformExpr_lifted_stmt : forall e env,
      lifted_stmt (fst (fst (TransformExpr _ e env))).
  Proof.
    intro e; induction e using custom_e_ind;
      intro env; unravel in *;
        repeat transformExpr_destr;
        repeat seq_lift; auto;
          try (specialize IHe with env;
               transformExpr_destr_hyp_rewrite;
               assumption);
          try (specialize IHe with env;
               transformExpr_destr_hyp_rewrite;
               apply f_equal with (f:= (snd ∘ fst)) in Heqp;
               unravel in *; rewrite <- Heqp; auto; assumption).
    - specialize IHe1 with env;
        transformExpr_destr_hyp_rewrite; assumption.
    - specialize IHe2 with t;
        transformExpr_destr_hyp_rewrite; assumption.
    - specialize IHe1 with env;
        specialize IHe2 with t;
        transformExpr_destr_hyp_rewrite;
        apply f_equal with (f:= (snd ∘ fst)) in Heqp;
        apply f_equal with (f:= (snd ∘ fst)) in Heqp0.
      unravel in *; rewrite <- Heqp, <- Heqp0; auto.
    - admit.
    - admit.
    - admit.
    - admit. 
  Admitted.
End Lifted.
