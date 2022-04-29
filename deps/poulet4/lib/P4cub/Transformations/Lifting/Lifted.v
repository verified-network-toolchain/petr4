Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Syntax.Shift
        Poulet4.P4cub.Transformations.Lifting.Statementize
        Coq.Numbers.DecimalString
        Coq.Strings.Ascii Coq.Strings.String.
Import AllCubNotations StringSyntax Field.FieldTactics.

Ltac pair_destr :=
  match goal with
  | h: (_,_) = (_,_) |- _ => inv h
  end.

(*
Ltac translateParserExpr_destr :=
  match goal with 
  | |- context [TranslateParserExpr ?e ?env]
    => destruct (TranslateParserExpr e env) as [? ?] eqn:?; simpl in *
  end.

Ltac translateCases'_destr :=
  match goal with 
  | |- context [TranslateCases' ?c ?env ?i]
    => destruct (TranslateCases' c env i) as [[? ?] ?] eqn:?; simpl in *
  end.
 *)
(*
Ltac translateStmt_destr :=
  match goal with
  | |- context [TranslateStatement ?s ?env]
    => destruct (TranslateStatement s env) as [? ?] eqn:?; simpl in *
  end.
 *)
(*
Ltac translateArrowE_destr :=
  match goal with
  | |- context [TranslateArrowE ?args ?env ?i]
    => destruct (TranslateArrowE args env i) as [[? ?] ?] eqn:?; simpl in *
  end.

Ltac translateArgs_destr :=
  match goal with
  | |- context [TranslateArgs ?args ?env ?i]
    => destruct (TranslateArgs args env i) as [[? ?] ?] eqn:?; simpl in *
  end.
*)

Ltac lift_e_destr :=
  match goal with
  | |- context [lift_e ?up ?e]
    => destruct (lift_e up e) as [? ?] eqn:?; simpl in *
  end.

(*
Ltac translateControlDecl_destr := 
  match goal with
  | |- context [TranslateControlDecl ?cd ?env]
    => destruct (TranslateControlDecl cd env) as [[? ?] ?] eqn:?; simpl in *
  end.

Ltac translateTable_destr := 
  match goal with
  | |- context [TranslateTable ?body ?env ?i]
    => destruct (TranslateTable body env i) as [[? ?] ?] eqn:?; simpl in *
  end.

Ltac translateTopDecl_destr := 
  match goal with
  | |- context [TranslateTopDecl ?td ?env]
    => destruct (TranslateTopDecl td env) as [? ?] eqn:?; simpl in *
  end.
*)
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
| lifted_member τ e x :
  lifted_expr e ->
  lifted_expr (Expr.Member τ x e)
| lifted_error err :
  lifted_expr (Expr.Error err).

Definition lifted_args (args : Expr.args) : Prop :=
  Forall (pred_paramarg_same lifted_expr) args.

Variant lifted_lexpr : Expr.e -> Prop :=
  | lifted_lifted_expr e :
    lifted_expr e ->
    lifted_lexpr e
  | lifted_bit w n :
    lifted_lexpr (Expr.Bit w n)
  | lifted_int w z :
    lifted_lexpr (Expr.Int w z)
  | lifted_slice e hi lo :
    lifted_expr e ->
    lifted_lexpr (Expr.Slice e hi lo)
  | lifted_cast τ e :
    lifted_expr e ->
    lifted_lexpr (Expr.Cast τ e)
  | lifted_uop τ op e :
    lifted_expr e ->
    lifted_lexpr (Expr.Uop τ op e)
  | lifted_bop τ op e₁ e₂ :
    lifted_expr e₁ ->
    lifted_expr e₂ ->
    lifted_lexpr (Expr.Bop τ op e₁ e₂)
  | lifted_struct es ob :
    Forall lifted_expr es ->
    lifted_lexpr (Expr.Struct es ob).

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
    lifted_parser_expr (Parser.Goto st)
  | lifted_select exp default cases : 
    lifted_expr exp ->
    lifted_parser_expr (Parser.Select exp default cases).

Inductive lifted_stmt : Stmt.s -> Prop :=
| lifted_skip :
  lifted_stmt Stmt.Skip
| lifted_vardecl te s :
  match te with
  | inl t => True
  | inr e => lifted_lexpr e
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
  lifted_args args ->
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
| lifted_invoke t :
  lifted_stmt (Stmt.Invoke t)
| lifted_apply x ext_args args :
  lifted_args args ->
  lifted_stmt (Stmt.Apply x ext_args args).

Variant lifted_control_Decl : Control.d -> Prop :=
  | lifted_Decl_Action act cps dps body :
    lifted_stmt body ->
    lifted_control_Decl (Control.Action act cps dps body)
  | lifted_Table table_name key actions :
    Forall lifted_expr (map fst key) ->
    lifted_control_Decl (Control.Table table_name key actions).

Inductive lifted_top_Decl : TopDecl.d -> Prop :=
| lifted_Instantiate c_name type_args cargs :
  lifted_top_Decl (TopDecl.Instantiate c_name type_args cargs)
| lifted_Extern e_name type_params c_params methods : 
  lifted_top_Decl (TopDecl.Extern e_name type_params c_params methods)
| lifted_Control c cparams eps params body apply_blk :
  Forall lifted_control_Decl body -> lifted_stmt apply_blk ->
  lifted_top_Decl (TopDecl.Control c cparams eps params body apply_blk)
| lifted_Parser p cparams eps params start_state states :
  lifted_stmt start_state -> Forall lifted_stmt states ->
  lifted_top_Decl (TopDecl.Parser p cparams eps params start_state states)
| lifted_Function f tparams signature body :
  lifted_stmt body -> lifted_top_Decl (TopDecl.Funct f tparams signature body).

Local Hint Constructors lifted_expr : core.
Local Hint Constructors lifted_lexpr : core.
Local Hint Constructors lifted_parser_expr : core.

Lemma rename_e_lifted_expr : forall ρ e,
    lifted_expr e -> lifted_expr (rename_e ρ e).
Proof.
  intros ρ e h; induction h; unravel; auto.
Qed.

Local Hint Resolve rename_e_lifted_expr : core.

Lemma rename_e_lifted_lexpr : forall ρ e,
    lifted_lexpr e -> lifted_lexpr (rename_e ρ e).
Proof.
  intros ρ e h; inv h; unravel; auto.
  apply lifted_struct.
  rewrite sublist.Forall_map.
  rewrite Forall_forall in *; unravel; auto.
Qed.

Local Hint Resolve rename_e_lifted_lexpr : core.

Lemma lift_e_lifted_expr : forall e E l up,
    lift_e up e = (l, E) ->
    Forall lifted_lexpr l /\ lifted_expr E.
Proof.
  intro e; induction e using custom_e_ind;
    intros E l up h; unravel in *;
    repeat lift_e_destr;
    try lift_e_destr_hyp;
    repeat pair_destr; auto.
  - apply IHe in Heqp as [? ?]; auto.
  - apply IHe in Heqp as [? ?]; auto.
  - apply IHe in Heqp as [? ?]; auto.
  - destruct (lift_e (List.length l0 + up) e2) as [l2  e2'] eqn:eql2.
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
                 end) up fields)
      as [l' E'] eqn:eql; inv h.
    split; auto.
    assert (yes: Forall lifted_lexpr l' /\ Forall lifted_expr E').
    { generalize dependent l';
        generalize dependent E';
        generalize dependent up; clear valid.
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
  - apply IHe in Heqp as [? ?]; auto.
Qed.

Local Hint Constructors lifted_stmt : core.

  Ltac seq_lift :=
    match goal with
    | |- lifted_stmt (_; _ @ _ }-
      => apply lifted_seq
    end.

  Local Hint Resolve TransformExpr_lifted_expr : core.

  Lemma TransformExprList'_TransformExpr_lifted_expr : forall es env i,
      Forall
        lifted_expr
        (snd
           (fst
              (TransformExprList'
                 TransformExpr es env i))).
  Proof.
    auto.
  Qed.

  Local Hint Resolve TransformExprList'_TransformExpr_lifted_expr : core.
  
  Lemma TransformFields'_TransformExpr_lifted_expr : forall es env i,
      F.predfs_data
        lifted_expr
        (snd (fst (TransformFields' TransformExpr es env i))).
  Proof.
    auto.
  Qed.

  Local Hint Resolve TransformFields'_TransformExpr_lifted_expr : core.

  Lemma TransformExprList'_lifted_stmt_Forall :
    forall es,
      Forall
        (fun e => forall env,
             lifted_stmt (fst (fst (lift_e up e)))) es ->
      forall env i,
        lifted_stmt (fst (fst (TransformExprList' TransformExpr es env i))).
  Proof.
    unfold TransformExprList';
      intros es H; ind_list_Forall;
        intros env i; simpl in *; auto.
    intuition; fold_destr.
    specialize H with env i.
    rewrite Hfoldl in H; simpl in *; clear Hfoldl.
    specialize H2 with t. transformExpr_destr.
    auto.
  Qed.

  Local Hint Resolve TransformExprList'_lifted_stmt_Forall : core.

  Lemma TransformFields'_lifted_stmt_Forall :
    forall fields,
      F.predfs_data
        (fun e => forall env,
             lifted_stmt (fst (fst (lift_e up e)))) fields ->
      forall env i,
        lifted_stmt (fst (fst (TransformFields' TransformExpr fields env i))).
  Proof.
    unfold TransformFields', Field.fold;
      intros es H; ind_list_predfs;
        intros env i; simpl in *; auto.
    intuition. fold_destr.
    specialize H with env i.
    rewrite Hfoldl in H; simpl in *; clear Hfoldl.
    specialize H2 with t. transformExpr_destr.
    auto.
  Qed.

  Local Hint Resolve TransformFields'_lifted_stmt_Forall : core.
  
  Lemma TransformExpr_lifted_stmt : forall e env,
      lifted_stmt (fst (fst (lift_e up e))).
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
        apply f_equal with (f:= snd ∘ fst) in Heqp;
        apply f_equal with (f:= snd ∘ fst) in Heqp0.
      unravel in *; rewrite <- Heqp, <- Heqp0; auto.
    - apply f_equal with (f := fst ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - apply lifted_tuple.
      apply f_equal with (f := snd ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - apply f_equal with (f := fst ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - apply lifted_struct.
      apply f_equal with (f := snd ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - apply f_equal with (f := fst ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - apply f_equal with (f := fst ∘ fst) in Heqp0; unravel in *.
      rewrite <- Heqp0; auto.
    - apply lifted_header.
      + apply f_equal with (f := snd ∘ fst) in Heqp0; unravel in *.
        rewrite <- Heqp0; auto.
      + apply f_equal with (f := snd ∘ fst) in Heqp; unravel in *.
        rewrite <- Heqp; auto.
    - apply f_equal with (f := fst ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - apply lifted_stack.
      apply f_equal with (f:=snd ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
  Qed.

  Local Hint Resolve TransformExpr_lifted_stmt : core.

  Ltac hyp_f_equal Heqp func:= 
    apply f_equal with (f := fst) in Heqp; apply f_equal with (f := func) in Heqp; simpl in Heqp;
      rewrite <- Heqp; auto.
  
  Ltac hyp_f_equal_fst Heqp:= 
    apply f_equal with (f := fst) in Heqp; apply f_equal with (f := fst) in Heqp; simpl in Heqp;
      rewrite <- Heqp; auto.
  
  Ltac hyp_f_equal_snd Heqp:= 
    apply f_equal with (f := fst) in Heqp; apply f_equal with (f := snd) in Heqp; simpl in Heqp;
      rewrite <- Heqp; auto.

  Lemma TranslateArgs_lifted_stmt : forall (a : Expr.args ) env i,
  lifted_stmt (fst (fst (TranslateArgs a env i))).
  Proof.
    intros a i. induction a;
      intro env; simpl.
      - constructor.
      - destruct a. destruct (TranslateArgs a0 i env) eqn:Hs2. destruct p0. transformExpr_destr. 
        constructor.
        + hyp_f_equal_fst Hs2.
        + hyp_f_equal_fst Heqp0.
  Qed.

  Local Hint Resolve TranslateArgs_lifted_stmt : core.

  Lemma TranslateArrowE_lifted_stmt : forall (args : Expr.arrowE ) env i, 
  lifted_stmt (fst (fst (TranslateArrowE args env i))).
  Proof.
    intros [pas returns] i env; simpl.
    destruct (TranslateArgs pas i env) eqn:Hs1. destruct p. destruct returns.
    - transformExpr_destr. constructor.
      + hyp_f_equal_fst Hs1.
      + hyp_f_equal_fst Heqp.
    - simpl. hyp_f_equal_fst Hs1. 
  Qed.

  Local Hint Resolve TranslateArrowE_lifted_stmt : core.

  Lemma TranslateArgs_lifted_expr : forall pas env i,
      Field.predfs_data (pred_paramarg_same lifted_expr) (snd (fst (TranslateArgs pas i env))).
  Proof.
    intros pas i. induction pas; intro env; simpl.
    - constructor.
    - destruct a. translateArgs_destr. transformExpr_destr.
      destruct p; unfold F.predfs_data, F.predf_data in *; 
    unravel in *; rewrite Forall_app; split; try hyp_f_equal_snd Heqp0; repeat constructor;
    simpl; unfold pred_paramarg_same, pred_paramarg; hyp_f_equal_snd Heqp1.
  Qed.

  Local Hint Resolve TranslateArgs_lifted_expr : core.

  Local Hint Constructors predop : core.

  Lemma TransformExpr_lifted_args : forall pas i (e:Expr.e ) t env,
      lifted_args {|paramargs:=snd (fst (TranslateArgs pas i env));
                    rtrns:=Some (snd (fst (TransformExpr e t)))|}.
  Proof.
    unfold lifted_args.
    intros pas i e t env; simpl; auto.
  Qed.

  Local Hint Resolve TransformExpr_lifted_args : core.
   
  Lemma TranslateArrowE_lifted_args : forall (args : Expr.arrowE ) env i, 
  lifted_args (snd (fst (TranslateArrowE args env i))).
  Proof.
    intros [pas returns] i env; simpl.
    destruct (TranslateArgs pas i env) eqn:Hs1;
      destruct p eqn:Hs2; destruct returns eqn:Hs3; cbn.
    - transformExpr_destr. hyp_f_equal_snd Heqp0. hyp_f_equal_snd Hs1.
    - hyp_f_equal_snd Hs1. unfold lifted_args; split; cbn; auto.
  Qed.

  Local Hint Resolve TranslateArrowE_lifted_args : core.

  Lemma TranslateStmt_lifted_stmt : forall (s : Stmt.s ) (env:VarNameGen.t),
  lifted_stmt (fst (TranslateStatement s env)).
  Proof.
  intros s. induction s; intros env; try simpl; auto; repeat transformExpr_destr.
  - destruct expr.
    + simpl. auto.
    + transformExpr_destr. constructor. 
      * hyp_f_equal_fst Heqp. 
      * constructor. hyp_f_equal_snd Heqp.
  - repeat constructor. 
    + hyp_f_equal_fst Heqp.
    + hyp_f_equal_fst Heqp0.
    + hyp_f_equal_snd Heqp.   
    + hyp_f_equal_snd Heqp0.
  - repeat translateStmt_destr. constructor.
    + hyp_f_equal_fst Heqp.
    + constructor. 
      * hyp_f_equal_snd Heqp. 
      * hyp_f_equal Heqp0 (fun x:(Stmt.s ) => x).
      * hyp_f_equal Heqp1 (fun x:(Stmt.s ) => x). 
  - repeat translateStmt_destr. constructor. 
    + hyp_f_equal Heqp (fun x:(Stmt.s ) => x).
    + hyp_f_equal Heqp0 (fun x:(Stmt.s ) => x). 
  - translateStmt_destr. constructor. hyp_f_equal Heqp (fun x:(Stmt.s ) => x).
  - translateArrowE_destr. constructor.
    + hyp_f_equal_fst Heqp.
    + constructor. hyp_f_equal_snd Heqp. 
  - translateArrowE_destr. constructor.
    + hyp_f_equal_fst Heqp.
    + hyp_f_equal_snd Heqp.
  - translateArgs_destr. constructor.
    + hyp_f_equal_fst Heqp. 
    + hyp_f_equal_snd Heqp. 
  - destruct e.
    + transformExpr_destr. constructor.
      * hyp_f_equal_fst Heqp.
      * hyp_f_equal_snd Heqp.
    + simpl. auto.
  - translateArgs_destr. constructor.
    + hyp_f_equal_fst Heqp.
    + hyp_f_equal_snd Heqp. 
  - repeat constructor.
    + hyp_f_equal_fst Heqp.
    + hyp_f_equal_snd Heqp.
  Qed.

  Local Hint Resolve TranslateStmt_lifted_stmt : core.


  Lemma TranslateCases_lifted_stmt : forall (translateParserE : Parser.e  -> VarNameGen.t -> (Stmt.s ) * Parser.e  * VarNameGen.t)
  (cases: Field.fs Parser.pat (Parser.e )),
  F.predfs_data (fun pe => forall env, lifted_stmt (fst (fst (translateParserE pe env)))) cases -> 
  forall (env: VarNameGen.t) (: ), 
  lifted_stmt (fst (fst (TranslateCases' translateParserE cases env i))).
  Proof.
  intros translateParserE cases Hpte; ind_list_predfs; intros. 
  - simpl. auto.
  - simpl. translateCases'_destr. destruct (translateParserE e t) eqn: HS1.
  destruct p0. simpl. constructor.
    + hyp_f_equal_fst Heqp0.
    + hyp_f_equal_fst HS1.
  Qed.

  Local Hint Resolve TranslateCases_lifted_stmt : core.

  Lemma TranslateParserExpr_lifted_stmt : forall (e : Parser.e ) (env:VarNameGen.t),
  lifted_stmt (fst (fst (TranslateParserExpr e env))).
  Proof.
  intros e. induction e using pe_ind; intro env; try simpl; auto.
  transformExpr_destr. translateParserExpr_destr. destruct p eqn:Hs0. destruct (TranslateCases' TranslateParserExpr cases t0 i) eqn:Hs1.
  destruct p0 eqn: Hs2. simpl. repeat constructor; auto. 
  - hyp_f_equal_fst Heqp.
  - hyp_f_equal_fst Heqp0.
  - hyp_f_equal_fst Hs1.
  Qed. 

  Local Hint Resolve TranslateParserExpr_lifted_stmt : core.

  Lemma TranslateCases_lifted_expr : forall (translateParserE : Parser.e  -> VarNameGen.t -> (Stmt.s ) * Parser.e  * VarNameGen.t)
  (cases: Field.fs Parser.pat (Parser.e )),
  F.predfs_data (fun pe => forall env, lifted_parser_expr (snd (fst (translateParserE pe env)))) cases -> 
  forall (env: VarNameGen.t) (: ), 
  F.predfs_data lifted_parser_expr (snd (fst (TranslateCases' translateParserE cases env i))).
  Proof.
  intros translateParserE cases Hpte; ind_list_predfs; intros; unfold F.predfs_data in *; 
  unfold F.predf_data in *; unravel in *; auto.
  translateCases'_destr. destruct (translateParserE e t) eqn: HS1.
  destruct p0. simpl. rewrite Forall_app. split.
    + hyp_f_equal_snd Heqp0.
    + constructor; auto. simpl. hyp_f_equal_snd HS1.
  Qed.

  Local Hint Resolve TranslateCases_lifted_expr : core.

  Lemma TranslateParserExpr_lifted_parser_expr : forall (e : Parser.e ) (env:VarNameGen.t),
  lifted_parser_expr (snd (fst (TranslateParserExpr e env))).
  Proof.
  intros e. induction e using pe_ind; intro env; try simpl; auto.
  transformExpr_destr. translateParserExpr_destr. destruct p.
  translateCases'_destr. constructor.
  - hyp_f_equal_snd Heqp.
  - hyp_f_equal_snd Heqp0.
  - hyp_f_equal_snd Heqp1.   
  Qed. 

  Local Hint Resolve TranslateParserExpr_lifted_parser_expr : core.

  Lemma TranslateParserState_lifted_stmt :
    forall (parser_state: Parser.state_block ) (env : VarNameGen.t),
      lifted_parser_state (fst (TranslateParserState parser_state env)).
  Proof.
    intros [s e] env; simpl; translateStmt_destr; translateParserExpr_destr.
    destruct p. simpl. unfold lifted_parser_state; split; cbn; try constructor.
    - hyp_f_equal Heqp (fun x:(Stmt.s ) => x).
    - hyp_f_equal_fst Heqp0.
    - hyp_f_equal_snd Heqp0.
  Qed.

  Local Hint Resolve TranslateParserState_lifted_stmt : core.

  Lemma TranslateParserStates_lifted_stmt :
    forall (parser_states: Field.fs string (Parser.state_block )) (env : VarNameGen.t),
      lifted_parser_states (fst (TranslateParserStates parser_states env)).
  Proof.
    induction parser_states; intros; simpl in *.
    - constructor.
    - destruct a.
      unfold lifted_parser_states, F.predfs_data.
      destruct (TranslateParserStates parser_states env) as [prev_states env_prev] eqn:?.
      destruct (TranslateParserState s0 env_prev) as [s' env_state] eqn:?.
      apply Forall_app; split.
      + apply (f_equal fst) in Heqp.
        simpl (fst _) in Heqp.
        rewrite <- Heqp.
        apply IHparser_states.
      + constructor; auto.
        unfold F.predf_data.
        change _ with (lifted_parser_state s').
        apply (f_equal fst) in Heqp0.
        simpl (fst _) in Heqp0.
        rewrite <- Heqp0.
        auto.
  Qed.

  Local Hint Resolve TranslateParserStates_lifted_stmt : core.

  Lemma TranslateTable_lifted_stmt :
    forall (t: Control.table ) (env: VarNameGen.t) (: ),
      lifted_stmt (fst (fst (TranslateTable t env i))).
  Proof.
    intros [ky acts] env i; cbn; fold_destr; clear acts.
    hyp_f_equal_fst Hfoldl.
    clear Hfoldl l t s.
    generalize dependent env.
    induction ky as [| [e mk] ky IHky]; intros env; simpl in *; auto.
    fold_destr; transformExpr_destr.
    specialize IHky with env.
    rewrite Hfoldl in IHky; simpl in *.
    hyp_f_equal_fst Heqp.
  Qed.

  Local Hint Resolve TranslateTable_lifted_stmt : core.

  Lemma TranslateTable_lifted_table :
    forall (t: Control.table ) (env: VarNameGen.t) (: ),
      lifted_table (snd (fst (TranslateTable t env i))).
  Proof.
    intros [ky acts] env i; cbn; fold_destr.
    hyp_f_equal_snd Hfoldl.
    clear Hfoldl l t s.
    generalize dependent env.
    induction ky as [| [e mk] ky IHky]; intros env; simpl in *.
    - constructor.
    - fold_destr; transformExpr_destr.
      specialize IHky with env.
      rewrite Hfoldl in IHky; simpl in *.
      constructor.
      + hyp_f_equal_snd Heqp.
      + inversion IHky; simpl in *; subst l; auto.
  Qed.

  Local Hint Resolve TranslateTable_lifted_table : core.

  Lemma TranslateControlDecl_lifted_stmt : forall (cd : Control.d ) (env : VarNameGen.t),
      lifted_stmt (fst (fst (TranslateControlDecl cd env))).
  Proof.
    intro cd. induction cd; intro env; simpl; auto.  
    - translateStmt_destr. auto. 
    - simpl. translateTable_destr. hyp_f_equal_fst Heqp.
    - repeat translateControlDecl_destr. constructor.
      + hyp_f_equal_fst Heqp.
      + hyp_f_equal_fst Heqp0.
  Qed.  

  Local Hint Resolve TranslateControlDecl_lifted_stmt : core.

  Lemma TranslateControlDecl_lifted_decl : forall (cd : Control.d ) (env : VarNameGen.t),
      lifted_control_Decl (snd (fst (TranslateControlDecl cd env))).
  Proof.
    intro cd. induction cd; intro env; simpl; auto.  
    - translateStmt_destr. 
      constructor.
      replace s with (fst (TranslateStatement body env))
        by (rewrite Heqp; exact eq_refl).
      eauto.
    - translateTable_destr.
      constructor.
      hyp_f_equal_snd Heqp.
    - repeat translateControlDecl_destr. constructor.
      + hyp_f_equal_snd Heqp.
      + hyp_f_equal_snd Heqp0.
  Qed.  
  
  Local Hint Resolve TranslateControlDecl_lifted_decl : core.

  Lemma TranslateTopDecl_lifted_top_Decl : forall (td : TopDecl.d ) (env : VarNameGen.t),
      lifted_top_Decl (fst (TranslateTopDecl td env)).
  Proof.
    induction td; intros; simpl; try solve [constructor].
    - translateControlDecl_destr.
      translateStmt_destr.
      constructor.
      + hyp_f_equal_snd Heqp.
      + constructor.
        * hyp_f_equal_fst Heqp.
        * replace s0 with (fst (TranslateStatement apply_blk t))
            by (rewrite Heqp0; exact eq_refl).
          auto.
    - (* annoying--can't write (... start env) here because start gets
      grabbed by some notation and then fails to parse *)
      destruct (TranslateParserState _ env) as [start' env_start] eqn:?.
      destruct (TranslateParserStates states env_start) as [states' env_states] eqn:?.
      constructor.
      + apply (f_equal fst) in Heqp.
        simpl (fst _) in Heqp.
        rewrite <- Heqp.
        auto.
      + apply (f_equal fst) in Heqp0.
        simpl (fst _) in Heqp0.
        rewrite <- Heqp0.
        eauto.
    - translateStmt_destr.
      constructor; auto.
      replace s with (fst (TranslateStatement body env))
        by (rewrite Heqp; exact eq_refl).
      auto.
    - translateTopDecl_destr.
      translateTopDecl_destr.
      replace d with (fst (TranslateTopDecl td1 env))
        by (rewrite Heqp; exact eq_refl).
      replace d0 with (fst (TranslateTopDecl td2 t))
        by (rewrite Heqp0; exact eq_refl).
      constructor; auto.
  Qed.

  Local Hint Resolve TranslateTopDecl_lifted_top_Decl : core.

  Lemma TranslateProgram_lifted_top_Decl : forall (prog: TopDecl.d ),
      lifted_top_Decl (TranslateProgram prog).
  Proof.
    unfold TranslateProgram.
    auto.
  Qed.

End Lifted.
