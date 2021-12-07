Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Transformations.Lifting.Statementize
        Coq.Numbers.DecimalString
        Coq.Strings.Ascii Coq.Strings.String.
Import AllCubNotations StringSyntax Field.FieldTactics.

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

Ltac translateStmt_destr :=
  match goal with
  | |- context [TranslateStatement ?s ?env]
    => destruct (TranslateStatement s env) as [? ?] eqn:?; simpl in *
  end.

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

Ltac transformExpr_destr :=
  match goal with
  | |- context [TransformExpr ?e ?env]
    => destruct (TransformExpr e env) as [[? ?] ?] eqn:?; simpl in *
  | |- context [TransformExprList' ?f ?e ?env ?i]
    => destruct (TransformExprList' f e env i) as [[? ?] ?] eqn:?; simpl in *
  | |- context [TransformFields' ?f ?e ?env ?i]
    => destruct (TransformFields' f e env i) as [[? ?] ?] eqn:?; simpl in *
  end.

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

Ltac transformExpr_destr_hyp :=
  match goal with
  | H: context [TransformExpr ?e ?env] |- _
    => destruct (TransformExpr e env)
      as [[? ?] ?] eqn:?; simpl in *
  end.

Ltac transformExpr_destr_hyp_rewrite :=
  match goal with
  | H: TransformExpr ?e ?env = (_,_,_),
       Hy : context [TransformExpr ?e ?env]
    |- _ => rewrite H in Hy; simpl in *
  end.


(*Ltac quantify_varNameGen :=
  match goal with
        | env: VarNameGen.t, H: (forall _: VarNameGen.t, _)
      |-   _ => specialize H with env
    end.*) 

Ltac fold_destr :=
  match goal with
  | |- context [fold_left ?f ?l ?acc]
    => destruct (fold_left f l acc) as [[? ?] ?] eqn:Hfoldl; simpl in *
  | |- context [fold_right ?f ?acc ?l]
    => destruct (fold_right f acc l) as [[? ?] ?] eqn:Hfoldl; simpl in *
  end.

Section Lifted.
  Arguments String.append : simpl never.
  
  Context {tags_t : Type}.
  
  Inductive lifted_expr : Expr.e tags_t -> Prop :=
  | lifted_bool b i :
      lifted_expr <{ BOOL b @ i }>
  | lifted_var x τ i :
      lifted_expr <{ Var x:τ @ i }>
  | lifted_member τ e x i :
      lifted_expr e ->
      lifted_expr <{ Mem e dot x : τ @ i }>
  | lifted_error err i :
      lifted_expr <{ Error err @ i }>
  | lifted_matchkind mk i :
      lifted_expr <{ Matchkind mk @ i }>
  | lifted_access ts e z i :
      lifted_expr e ->
      lifted_expr <{ Access e[z] : ts @ i }>.

  Definition lifted_args (args : Expr.arrowE tags_t) : Prop :=
    F.predfs_data (pred_paramarg_same lifted_expr) (paramargs args) /\
    predop lifted_expr (rtrns args).
  
  Inductive lifted_stmt : Stmt.s tags_t -> Prop :=
  | lifted_skip i :
      lifted_stmt -{ skip @ i }-
  | lifted_vardecl x te i :
      match te with
      | inl t => True
      | inr e => lifted_expr e
      end ->
      lifted_stmt -{ var x with te @ i }-
  | lifted_assign e1 e2 i :
      lifted_expr e1 ->
      lifted_expr e2 ->
      lifted_stmt -{ asgn e1 := e2 @ i }-
  | lifted_bit x w n i iw :
      lifted_stmt -{ init x := w W n @ iw @ i }-
  | lifted_int x w z i iw :
      lifted_stmt -{ init x := w S z @ iw @ i }-
  | lifted_uop τ op x e i ie :
      lifted_expr e ->
      lifted_stmt -{ init x := UOP op e : τ @ ie @ i}-
  | lifted_bop τ op x e1 e2 i ie1e2 :
      lifted_expr e1 ->
      lifted_expr e2 ->
      lifted_stmt -{ init x := BOP e1 op e2 : τ @ ie1e2 @ i }-
  | lifted_slice x e hi lo i ie :
      lifted_expr e ->
      lifted_stmt -{ init x := Slice e [hi:lo] @ ie @ i }-
  | lifted_cast x e τe i ie :
      lifted_expr e ->
      lifted_stmt -{ init x := Cast e:τe @ ie @ i }-
  | lifted_tuple x es i ies :
      Forall lifted_expr es ->
      lifted_stmt -{ init x := tup es @ ies @ i }-
  | lifted_struct x es i ies :
      F.predfs_data lifted_expr es ->
      lifted_stmt -{ init x := struct { es } @ ies @ i }-
  | lifted_header x e es i ies :
      lifted_expr e ->
      F.predfs_data lifted_expr es ->
      lifted_stmt -{ init x := hdr { es } valid:=e @ ies @ i }-
  | lifted_stack x es ni τs i ies :
      Forall lifted_expr es ->
      lifted_stmt -{ init x := Stack es:τs nextIndex:=ni @ ies @ i }-
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
      lifted_stmt (Stmt.SExternMethodCall e f targs args i)
  | lifted_fun_call f targs args i :
      lifted_args args ->
      lifted_stmt (Stmt.SFunCall f targs args i)
  | lifted_act_call a args i :
      F.predfs_data (pred_paramarg_same lifted_expr) args ->
      lifted_stmt -{ calling a with args @ i }-
  | lifted_return eo i :
      match eo with
      | Some e => lifted_expr e
      | None   => True
      end ->
      lifted_stmt -{ return eo @ i }-
  | lifted_exit i :
      lifted_stmt -{ exit @ i }-
  | lifted_invoke t i :
      lifted_stmt -{ invoke t @ i }-
  | lifted_apply x ext_args args i :
      F.predfs_data (pred_paramarg_same lifted_expr) args ->
      lifted_stmt -{ apply x with ext_args & args @ i }-
  | lifted_headerStackOp hdr_stk_name op n i : 
      lifted_stmt (Stmt.SHeaderStackOp hdr_stk_name op n i)
  | lifted_setValidity e validity i : 
      lifted_expr e -> lifted_stmt (Stmt.SSetValidity e validity i).
  
  Local Hint Constructors lifted_expr : core.

  Inductive lifted_parser_expr : Parser.e tags_t -> Prop :=
  | lifted_goto st i : 
      lifted_parser_expr (Parser.PGoto st i)
  | lifted_select exp default cases i: 
      lifted_expr exp -> lifted_parser_expr default -> 
      Field.predfs_data lifted_parser_expr cases ->
      lifted_parser_expr (Parser.PSelect exp default cases i).

  Local Hint Constructors lifted_parser_expr : core.
  
  Definition lifted_parser_state (stblk : Parser.state_block tags_t) : Prop :=
    lifted_stmt (Parser.stmt stblk) /\ lifted_parser_expr (Parser.trans stblk).
  
  Definition lifted_parser_states (states: F.fs string (Parser.state_block tags_t)) : Prop := 
    F.predfs_data lifted_parser_state states.

  (*Check lifted_parser_states.*)
  Definition lifted_table (tbl : Control.table tags_t) : Prop :=
    Forall (fun '(e, _) => lifted_expr e) (Control.table_key tbl).
  
  Inductive lifted_control_Decl : Control.d tags_t -> Prop :=
  | lifted_CDAction act sig body i :
      lifted_stmt body ->
      lifted_control_Decl (Control.CDAction act sig body i)
  | lifted_CDTable table_name body i :
      lifted_table body ->
      lifted_control_Decl (Control.CDTable table_name body i)
  | lifted_CDSeq d1 d2 i :
      lifted_control_Decl d1 -> lifted_control_Decl d2 ->
      lifted_control_Decl (Control.CDSeq d1 d2 i).

  Inductive lifted_top_Decl : TopDecl.d tags_t -> Prop :=
  | lifted_TPInstantiate c_name i_name type_args cargs i :
      lifted_top_Decl (TopDecl.TPInstantiate c_name i_name type_args cargs i)
  | lifted_TPExtern e_name type_params c_params methods i : 
      lifted_top_Decl (TopDecl.TPExtern e_name type_params c_params methods i)
  | lifted_TPControl c cparams eps params body apply_blk i :
      lifted_control_Decl body -> lifted_stmt apply_blk ->
      lifted_top_Decl (TopDecl.TPControl c cparams eps params body apply_blk i)
  | lifted_TPParser p cparams eps params start_state states i :
      lifted_parser_state start_state -> lifted_parser_states states ->
      lifted_top_Decl (TopDecl.TPParser p cparams eps params start_state states i)
  | lifted_TPFunction f tparams signature body i :
      lifted_stmt body -> lifted_top_Decl (TopDecl.TPFunction f tparams signature body i)
  | lifted_TPSeq d1 d2 i :
      lifted_top_Decl d1 -> lifted_top_Decl d2 ->
      lifted_top_Decl (TopDecl.TPSeq d1 d2 i).

  Section HelperLemmas.
    Variable f :
      Expr.e tags_t -> VarNameGen.t ->
      Stmt.s tags_t * Expr.e tags_t * VarNameGen.t.
      
    Section General.
      Hypothesis Hf : forall e env, lifted_expr (snd (fst (f e env))).
      
      Lemma TransformExprList'_lifted_expr :
        forall es env i,
          Forall
            lifted_expr
            (snd (fst (TransformExprList' f es env i))).
      Proof.
        unfold TransformExprList'.
        intro es; induction es as [| e es IHes];
          intros env i; simpl; auto.
        fold_destr. destruct (f e t) as [[s' e'] env'] eqn:Heqfet.
        constructor.
        - apply f_equal with (f:=snd ∘ fst) in Heqfet; unravel in *.
          rewrite <- Heqfet; auto.
        - specialize IHes with env i.
          rewrite Hfoldl in IHes; auto.
      Qed.
      
      Lemma TransformFields'_lifted_expr :
        forall es env i,
          F.predfs_data
            lifted_expr
            (snd (fst (TransformFields' f es env i))).
      Proof.
        unfold TransformFields', Field.fold.
        intro es; induction es as [| (x & e) es IHes];
          intros env i; unfold F.predfs_data, F.predf_data in *;
            unravel in *; auto; fold_destr.
        destruct (f e t) as [[s' e'] env'] eqn:Heqfet; unravel.
        constructor; unravel.
        - apply f_equal with (f:=snd ∘ fst) in Heqfet;
            unravel in *. rewrite <- Heqfet; auto.
        - specialize IHes with env i.
          rewrite Hfoldl in IHes; auto.
      Qed.
    End General.
  End HelperLemmas.

  Local Hint Resolve TransformExprList'_lifted_expr : core.
  Local Hint Resolve TransformFields'_lifted_expr : core.
  
  Lemma TransformExpr_lifted_expr : forall e env,
      lifted_expr (snd (fst (TransformExpr e env))).
  Proof.
    intro e; induction e using custom_e_ind;
      intro env; unravel in *;
        repeat transformExpr_destr; auto;
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
             lifted_stmt (fst (fst (TransformExpr e env)))) es ->
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
             lifted_stmt (fst (fst (TransformExpr e env)))) fields ->
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
      lifted_stmt (fst (fst (TransformExpr e env))).
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

  Lemma TranslateArgs_lifted_stmt : forall (a : Expr.args tags_t) env i,
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

  Lemma TranslateArrowE_lifted_stmt : forall (args : Expr.arrowE tags_t) env i, 
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

  Lemma TransformExpr_lifted_args : forall pas i (e:Expr.e tags_t) t env,
      lifted_args {|paramargs:=snd (fst (TranslateArgs pas i env));
                    rtrns:=Some (snd (fst (TransformExpr e t)))|}.
  Proof.
    unfold lifted_args.
    intros pas i e t env; simpl; auto.
  Qed.

  Local Hint Resolve TransformExpr_lifted_args : core.
   
  Lemma TranslateArrowE_lifted_args : forall (args : Expr.arrowE tags_t) env i, 
  lifted_args (snd (fst (TranslateArrowE args env i))).
  Proof.
    intros [pas returns] i env; simpl.
    destruct (TranslateArgs pas i env) eqn:Hs1;
      destruct p eqn:Hs2; destruct returns eqn:Hs3; cbn.
    - transformExpr_destr. hyp_f_equal_snd Heqp0. hyp_f_equal_snd Hs1.
    - hyp_f_equal_snd Hs1. unfold lifted_args; split; cbn; auto.
  Qed.

  Local Hint Resolve TranslateArrowE_lifted_args : core.

  Lemma TranslateStmt_lifted_stmt : forall (s : Stmt.s tags_t) (env:VarNameGen.t),
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
      * hyp_f_equal Heqp0 (fun x:(Stmt.s tags_t) => x).
      * hyp_f_equal Heqp1 (fun x:(Stmt.s tags_t) => x). 
  - repeat translateStmt_destr. constructor. 
    + hyp_f_equal Heqp (fun x:(Stmt.s tags_t) => x).
    + hyp_f_equal Heqp0 (fun x:(Stmt.s tags_t) => x). 
  - translateStmt_destr. constructor. hyp_f_equal Heqp (fun x:(Stmt.s tags_t) => x).
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


  Lemma TranslateCases_lifted_stmt : forall (translateParserE : Parser.e tags_t -> VarNameGen.t -> (Stmt.s tags_t) * Parser.e tags_t * VarNameGen.t)
  (cases: Field.fs Parser.pat (Parser.e tags_t)),
  F.predfs_data (fun pe => forall env, lifted_stmt (fst (fst (translateParserE pe env)))) cases -> 
  forall (env: VarNameGen.t) (i : tags_t), 
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

  Lemma TranslateParserExpr_lifted_stmt : forall (e : Parser.e tags_t) (env:VarNameGen.t),
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

  Lemma TranslateCases_lifted_expr : forall (translateParserE : Parser.e tags_t -> VarNameGen.t -> (Stmt.s tags_t) * Parser.e tags_t * VarNameGen.t)
  (cases: Field.fs Parser.pat (Parser.e tags_t)),
  F.predfs_data (fun pe => forall env, lifted_parser_expr (snd (fst (translateParserE pe env)))) cases -> 
  forall (env: VarNameGen.t) (i : tags_t), 
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

  Lemma TranslateParserExpr_lifted_parser_expr : forall (e : Parser.e tags_t) (env:VarNameGen.t),
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
    forall (parser_state: Parser.state_block tags_t) (env : VarNameGen.t),
      lifted_parser_state (fst (TranslateParserState parser_state env)).
  Proof.
    intros [s e] env; simpl; translateStmt_destr; translateParserExpr_destr.
    destruct p. simpl. unfold lifted_parser_state; split; cbn; try constructor.
    - hyp_f_equal Heqp (fun x:(Stmt.s tags_t) => x).
    - hyp_f_equal_fst Heqp0.
    - hyp_f_equal_snd Heqp0.
  Qed.

  Local Hint Resolve TranslateParserState_lifted_stmt : core.

  Lemma TranslateTable_lifted_stmt :
    forall (t: Control.table tags_t) (env: VarNameGen.t) (i : tags_t),
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

  Lemma TranslateControlDecl_lifted_stmt : forall (cd : Control.d tags_t) (env : VarNameGen.t),
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

  (* Not Done, unsure how to write lemma with monad
  Lemma TranslateTopDecl_lifted_stmt : forall (td : TopDecl.d tags_t) (env : VarNameGen.t),
      lifted_ *)

End Lifted.
