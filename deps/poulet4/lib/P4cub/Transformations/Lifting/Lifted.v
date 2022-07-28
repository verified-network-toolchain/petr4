Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Syntax.Shift
        Poulet4.P4cub.Transformations.Lifting.Statementize.
Import AllCubNotations.

Ltac pair_destr :=
  match goal with
  | h: (_,_) = (_,_) |- _ => inv h
  end.

Ltac lift_e_destr :=
  match goal with
  | |- context [lift_e ?up ?e]
    => destruct (lift_e up e) as [? ?] eqn:?; simpl in *
  end.

Ltac lift_e_destr_hyp :=
  match goal with
  | H: context [lift_e ?up ?e] |- _
    => destruct (lift_e up e)
      as [? ?] eqn:?; simpl in *
  end.

Ltac lift_e_destr_hyp_rewrite :=
  match goal with
  | H: lift_e ?up ?e = (_,_),
      Hy : context [lift_e ?up ?e]
    |- _ => rewrite H in Hy; simpl in *
  end.

Inductive lifted_expr : Expr.e -> Prop :=
| lifted_bool (b : bool) :
  lifted_expr b
| lifted_var τ x :
  lifted_expr (Expr.Var τ x)
| lifted_index τ e₁ e₂ :
  lifted_expr e₁ ->
  lifted_expr e₂ ->
  lifted_expr (Expr.Index τ e₁ e₂)
| lifted_member τ e x :
  lifted_expr e ->
  lifted_expr (Expr.Member τ x e)
| lifted_error err :
  lifted_expr (Expr.Error err).

Definition lifted_arg : paramarg Expr.e Expr.e -> Prop :=
  pred_paramarg_same lifted_expr.

Variant lifted_rexpr : Expr.e -> Prop :=
  | lifted_lifted_expr e :
    lifted_expr e ->
    lifted_rexpr e
  | lifted_bit w n :
    lifted_rexpr (Expr.Bit w n)
  | lifted_int w z :
    lifted_rexpr (Expr.Int w z)
  | lifted_slice hi lo e :
    lifted_expr e ->
    lifted_rexpr (Expr.Slice hi lo e)
  | lifted_cast τ e :
    lifted_expr e ->
    lifted_rexpr (Expr.Cast τ e)
  | lifted_uop τ op e :
    lifted_expr e ->
    lifted_rexpr (Expr.Uop τ op e)
  | lifted_bop τ op e₁ e₂ :
    lifted_expr e₁ ->
    lifted_expr e₂ ->
    lifted_rexpr (Expr.Bop τ op e₁ e₂)
  | lifted_lists ls es :
    Forall lifted_expr es ->
    lifted_rexpr (Expr.Lists ls es).

Variant lifted_fun_kind : Stmt.fun_kind -> Prop :=
  | lifted_Funct x τs oe :
    predop lifted_expr oe ->
    lifted_fun_kind (Stmt.Funct x τs oe)
  | lifted_Action x es :
    Forall lifted_expr es ->
    lifted_fun_kind (Stmt.Action x es)
  | lifted_Method x m τs oe :
    predop lifted_expr oe ->
    lifted_fun_kind (Stmt.Method x m τs oe).

Variant lifted_parser_expr : Parser.e -> Prop :=
  | lifted_goto st : 
    lifted_parser_expr (Parser.Direct st)
  | lifted_select exp default cases : 
    lifted_expr exp ->
    lifted_parser_expr (Parser.Select exp default cases).

Inductive lifted_stmt : Stmt.s -> Prop :=
| lifted_skip :
  lifted_stmt Stmt.Skip
| lifted_vardecl te s :
  match te with
  | inl t => True
  | inr e => lifted_rexpr e
  end ->
  lifted_stmt s ->
  lifted_stmt (Stmt.Var te s)
| lifted_assign e1 e2 :
  lifted_expr e1 ->
  lifted_expr e2 ->
  lifted_stmt (Stmt.Assign e1 e2)
| lifted_cond e s1 s2 :
  lifted_expr e ->
  lifted_stmt s1 ->
  lifted_stmt s2 ->
  lifted_stmt (Stmt.Conditional e s1 s2)
| lifted_seq s1 s2 :
  lifted_stmt s1 ->
  lifted_stmt s2 ->
  lifted_stmt (Stmt.Seq s1 s2)
| lifted_call fk args :
  lifted_fun_kind fk ->
  Forall lifted_arg args ->
  lifted_stmt (Stmt.Call fk args)
| lifted_return eo :
  match eo with
  | Some e => lifted_expr e
  | None   => True
  end ->
  lifted_stmt (Stmt.Return eo)
| lifted_exit :
  lifted_stmt Stmt.Exit
| lifted_transition e :
  lifted_parser_expr e ->
  lifted_stmt (Stmt.Transition e)
| lifted_invoke t es :
  Forall lifted_expr es ->
  lifted_stmt (Stmt.Invoke t es)
| lifted_apply x ext_args args :
  Forall lifted_arg args ->
  lifted_stmt (Stmt.Apply x ext_args args).

Variant lifted_control_Decl : Control.d -> Prop :=
  | lifted_Decl_Action act cps dps body :
    lifted_stmt body ->
    lifted_control_Decl (Control.Action act cps dps body)
  | lifted_Table table_name key actions :
    lifted_control_Decl (Control.Table table_name key actions).

Inductive lifted_top_Decl : TopDecl.d -> Prop :=
| lifted_Instantiate c_name i_name type_args cargs expr_cargs :
  lifted_top_Decl (TopDecl.Instantiate c_name i_name type_args cargs expr_cargs)
| lifted_Extern e_name type_params c_params expr_c_params methods : 
  lifted_top_Decl (TopDecl.Extern e_name type_params c_params expr_c_params methods)
| lifted_Control c cparams expr_cparams eps params body apply_blk :
  Forall lifted_control_Decl body -> lifted_stmt apply_blk ->
  lifted_top_Decl (TopDecl.Control c cparams expr_cparams eps params body apply_blk)
| lifted_Parser p cparams expr_cparams eps params start_state states :
  lifted_stmt start_state -> Forall lifted_stmt states ->
  lifted_top_Decl (TopDecl.Parser p cparams expr_cparams eps params start_state states)
| lifted_Function f tparams signature body :
  lifted_stmt body -> lifted_top_Decl (TopDecl.Funct f tparams signature body).

Local Hint Constructors lifted_expr : core.
Local Hint Constructors lifted_rexpr : core.
Local Hint Constructors lifted_parser_expr : core.

Lemma rename_e_lifted_expr : forall ρ e,
    lifted_expr e -> lifted_expr (rename_e ρ e).
Proof.
  intros ρ e h; induction h; unravel; auto.
Qed.

Local Hint Resolve rename_e_lifted_expr : core.

Lemma rename_e_lifted_rexpr : forall ρ e,
    lifted_rexpr e -> lifted_rexpr (rename_e ρ e).
Proof.
  intros ρ e h; inv h; unravel; auto;
    constructor; rewrite sublist.Forall_map;
    rewrite Forall_forall in *; unravel; auto.
Qed.

Local Hint Resolve rename_e_lifted_rexpr : core.

Lemma lift_e_lifted_expr : forall e E l up,
    lift_e up e = (l, E) ->
    Forall lifted_rexpr l /\ lifted_expr E.
Proof.
  intro e; induction e using custom_e_ind;
    intros E ll up h; unravel in *;
    repeat lift_e_destr;
    try lift_e_destr_hyp;
    repeat pair_destr; auto.
  - apply IHe in Heqp as [? ?]; auto.
  - apply IHe in Heqp as [? ?]; auto.
  - apply IHe in Heqp as [? ?]; auto.
  - destruct (lift_e (length l + up) e2) as [l2  e2'] eqn:eql2.
    apply IHe1 in Heqp as [? ?].
    apply IHe2 in eql2 as [? ?].
    pair_destr.
    split; auto.
    constructor.
    + apply lifted_bop; auto.
    + rewrite Forall_app; auto.
  - destruct ((fix lift_e_list up es :=
                 match es with
                 | [] => ([], [])
                 | e :: es0 =>
                     let '(le, e') := lift_e up e in
                     let '(les, es') := lift_e_list (Datatypes.length le + up) es0 in
                     (les ++ le, rename_e (Nat.add (Datatypes.length les)) e' :: es')
                 end) up exps)
      as [l' E'] eqn:eql; inv h.
    split; auto.
    assert (yes: Forall lifted_rexpr l' /\ Forall lifted_expr E').
    { generalize dependent l';
        generalize dependent E';
        generalize dependent up; clear l.
      induction H as [| e es he hes ihes]; intros up E l H.
      - inv H; auto.
      - lift_e_destr_hyp.
        destruct ((fix lift_e_list up es :=
                     match es with
                     | [] => ([], [])
                     | e :: es0 =>
                         let '(le, e') := lift_e up e in
                         let '(les, es') := lift_e_list (Datatypes.length le + up) es0 in
                         (les ++ le, rename_e (Nat.add (Datatypes.length les)) e' :: es')
                     end) (Datatypes.length l0 + up))
          as [L' Es'] eqn:eqes; inv H.
        apply he in Heqp as [? ?]; clear he.
        apply ihes in eqes as [? ?]; clear ihes.
        split; auto. rewrite Forall_app; auto. }
    destruct yes; auto.
  - destruct (lift_e (length l + up) e2) as [l2  e2'] eqn:eql2.
    apply IHe1 in Heqp as [? ?].
    apply IHe2 in eql2 as [? ?].
    pair_destr.
    split; auto; rewrite Forall_app; auto.
  - apply IHe in Heqp as [? ?]; auto.
Qed.

Local Hint Resolve lift_e_lifted_expr : core.

Lemma lift_e_list_lifted_expr : forall es es' le up,
    lift_e_list up es = (le, es') ->
    Forall lifted_rexpr le /\ Forall lifted_expr es'.
Proof.
  intro es; induction es as [| e es ih];
    intros es' le up h; unravel in *;
    try lift_e_destr_hyp; try pair_destr; eauto.
  destruct (lift_e_list (length l + up) es)
    as [les es''] eqn:eqles; inv h.
  rewrite Forall_app.
  apply ih in eqles as [? ?].
  apply lift_e_lifted_expr in Heqp as [? ?]; auto.
Qed.

Local Hint Resolve lift_e_list_lifted_expr : core.

Lemma lift_arg_lifted_arg : forall arg arg' le up,
    lift_arg up arg = (le, arg') ->
    Forall lifted_rexpr le /\ lifted_arg arg'.
Proof.
  intros arg arg' le up h;
    destruct arg as [e | e | e]; unravel in *;
    lift_e_destr_hyp; pair_destr;
    eapply lift_e_lifted_expr; eauto.
Qed.
  
Local Hint Resolve lift_arg_lifted_arg : core.

Lemma rename_arg_lifted_arg : forall ρ arg,
    lifted_arg arg -> lifted_arg (rename_arg ρ arg).
Proof.
  intros ρ [e | e | e] h; unravel in *; auto.
Qed.

Local Hint Resolve rename_arg_lifted_arg : core.

Lemma lift_args_lifted_args : forall args args' le up,
    lift_args up args = (le, args') ->
    Forall lifted_rexpr le /\ Forall lifted_arg args'.
Proof.
  intro args; induction args as [| arg args ih];
    intros args' le up h; unravel in *.
  - pair_destr; auto.
  - destruct (lift_arg up arg) as [larg arg'] eqn:eqlarg.
    destruct (lift_args (length larg + up) args) as [largs args''] eqn:eqlargs.
    pair_destr. rewrite Forall_app.
    apply lift_arg_lifted_arg in eqlarg as [? ?].
    apply ih in eqlargs as [? ?]; auto.
Qed.

Local Hint Resolve lift_args_lifted_args : core.
Local Hint Constructors lifted_parser_expr : core.

Lemma lift_trans_lifted_parser_expr : forall e e' le up,
    lift_trans up e = (le, e') ->
    Forall lifted_rexpr le /\ lifted_parser_expr e'.
Proof.
  intros e e' le up h; destruct e;
    unravel in *; try lift_e_destr_hyp;
    pair_destr; auto.
  apply lift_e_lifted_expr in Heqp as [? ?]; auto.
Qed.

Local Hint Constructors lifted_fun_kind : core.
Local Hint Constructors predop : core.

Lemma lift_fun_kind_lifted_fun_kind : forall fk fk' up le,
    lift_fun_kind up fk = (le, fk') ->
    Forall lifted_rexpr le /\ lifted_fun_kind fk'.
Proof.
  intros fk fk' up le h; destruct fk; unravel in *.
  - destruct returns as [e |]; try lift_e_destr_hyp; pair_destr; auto.
    apply lift_e_lifted_expr in Heqp as [? ?]; auto.
  - destruct (lift_e_list up control_plane_args) as [les es'] eqn:eqles.
    pair_destr; apply lift_e_list_lifted_expr in eqles as [? ?]; auto.
  - destruct returns as [e |]; try lift_e_destr_hyp; pair_destr; auto.
    apply lift_e_lifted_expr in Heqp as [? ?]; auto.
Qed.

Lemma rename_fun_kind_lifted_fun_kind : forall ρ fk,
    lifted_fun_kind fk ->
    lifted_fun_kind (rename_fun_kind ρ fk).
Proof.
  intros ρ fk h; inv h; unravel.
  - constructor; destruct oe; unravel; inv H; auto.
  - constructor.
    rewrite sublist.Forall_map; unravel.
    rewrite Forall_forall in *; eauto.
  - constructor; destruct oe; unravel; inv H; auto.
Qed.

Local Hint Resolve rename_fun_kind_lifted_fun_kind : core.

Local Hint Constructors lifted_stmt : core.

Lemma unwind_vars_lifted : forall le s,
    Forall lifted_rexpr le ->
    lifted_stmt s ->
    lifted_stmt (unwind_vars le s).
Proof.
  intro le; induction le as [| e le ih];
    intros s hle hs; inv hle; unravel; auto.
Qed.

Local Hint Resolve unwind_vars_lifted : core.

Lemma lift_s_lifted_stmt : forall s up, lifted_stmt (lift_s up s).
Proof.
  intro s; induction s; intro up; unravel; auto.
  - destruct e as [e |]; auto.
    lift_e_destr; apply lift_e_lifted_expr in Heqp.
    intuition.
  - destruct (lift_trans up e) as [le e'] eqn:eqle.
    apply lift_trans_lifted_parser_expr in eqle as [? ?].
    intuition.
  - do 2 lift_e_destr.
    apply lift_e_lifted_expr in Heqp as [? ?], Heqp0 as [? ?].
    apply unwind_vars_lifted; auto.
    rewrite Forall_app; auto.
  - destruct (lift_fun_kind up call) as [lfk fk'] eqn:eqfk.
    destruct (lift_args (length lfk + up) args) as [largs args'] eqn:eqargs.
    apply lift_fun_kind_lifted_fun_kind in eqfk as [? ?].
    apply lift_args_lifted_args in eqargs as [? ?].
    apply unwind_vars_lifted; auto.
    rewrite Forall_app; auto.
  - destruct (lift_e_list up key) as [le es] eqn:eqle.
    apply lift_e_list_lifted_expr in eqle as [hle hes]; eauto.
  - destruct (lift_args up args) as [largs args'] eqn:eqargs.
    apply lift_args_lifted_args in eqargs as [? ?]; auto.
  - destruct expr as [t | e]; auto.
    lift_e_destr. apply lift_e_lifted_expr in Heqp as [? ?]; auto.
  - lift_e_destr. apply lift_e_lifted_expr in Heqp as [? ?]; auto.
Qed.

Local Hint Resolve lift_s_lifted_stmt : core.

Ltac hyp_f_equal Heqp func:= 
  apply f_equal with (f := fst) in Heqp; apply f_equal with (f := func) in Heqp; simpl in Heqp;
  rewrite <- Heqp; auto.

Ltac hyp_f_equal_fst Heqp:= 
  apply f_equal with (f := fst) in Heqp; apply f_equal with (f := fst) in Heqp; simpl in Heqp;
  rewrite <- Heqp; auto.

Ltac hyp_f_equal_snd Heqp:= 
  apply f_equal with (f := fst) in Heqp; apply f_equal with (f := snd) in Heqp; simpl in Heqp;
  rewrite <- Heqp; auto.

Local Hint Constructors lifted_control_Decl : core.

Lemma lift_control_decl_lifted_control_Decl : forall cd,
    lifted_control_Decl (lift_control_decl cd).
Proof.
  intros cd; destruct cd; unravel; auto.
Qed.

Local Hint Resolve lift_control_decl_lifted_control_Decl : core.
Local Hint Constructors lifted_top_Decl : core.

Lemma lift_top_decl_lifted_top_Decl : forall td,
    lifted_top_Decl (lift_top_decl td).
Proof.
  intro td; destruct td; unravel in *; auto.
  - constructor; auto.
    rewrite Forall_forall.
    intros cd hcd.
    rewrite in_map_iff in hcd.
    destruct hcd as (d & hd & hin); subst; auto.
  - constructor; auto.
    rewrite sublist.Forall_map; unravel.
    rewrite Forall_forall in *; eauto.
Qed.
