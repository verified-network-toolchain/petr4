From Poulet4 Require Import
    P4light.Semantics.Typing.ValueTyping 
    P4light.Syntax.Syntax
    P4light.Semantics.Semantics
    Utils.Util.Utiliser
    Utils.Envn
    AListUtil
    Monads.State.Pure
    Monads.Option.


Import Envn Typed P4Int.

Require Import String.
Open Scope string_scope.

Section InlineConstants.

  (** AST tags *)
  Context {tags_t : Type}.

  Definition Env : Type := Env.t string (@Expression tags_t).

  Section ConstantEnv.
    
    (** Environment mapping identifiers to the value to be substituted, if any *)
    Variable env : Env.

    (** [subst_name d x] is the expression bound to [x] in [env], if any, or [d]
        if [x] is unbound in [env] *)
    Definition subst_name (d : @Expression tags_t) (x : @P4String.t tags_t) : @Expression tags_t :=
      let bound_value := Env.find x.(P4String.str) env in
      default d bound_value.

    (** [subst_expr e] is [e] with every identifier bound in [emv] substituted
        for its bound value *)
    Fixpoint subst_expr (e : @Expression tags_t) : @Expression tags_t :=
      let 'MkExpression i e_pre type dir := e in
      match e_pre with
      | ExpName (BareName x) _ => subst_name e x
      | _ =>
        let e_pre' := subst_expr_pre e_pre in
        MkExpression i e_pre' type dir
      end

    with subst_expr_pre (e : @ExpressionPreT tags_t) : @ExpressionPreT tags_t :=
      let subst_exprs := List.map subst_expr in
      match e with
      | ExpBool _ 
      | ExpInt _ 
      | ExpString _ 
      | ExpName _ _
      | ExpTypeMember _ _
      | ExpErrorMember _
      | ExpDontCare => e
      | ExpArrayAccess array idx => ExpArrayAccess (subst_expr array) (subst_expr idx)
      | ExpBitStringAccess bits lo hi =>
        ExpBitStringAccess (subst_expr bits) lo hi
      | ExpList es => ExpList (subst_exprs es)
      | ExpRecord entries => ExpRecord (map_values subst_expr entries)
      | ExpUnaryOp op e => ExpUnaryOp op (subst_expr e)
      | ExpBinaryOp op e1 e2 => ExpBinaryOp op (subst_expr e1) (subst_expr e2)
      | ExpCast type e => ExpCast type (subst_expr e)
      | ExpExpressionMember e name => ExpExpressionMember (subst_expr e) name
      | ExpTernary e1 e2 e3 =>
        ExpTernary (subst_expr e1) (subst_expr e2) (subst_expr e3)
      | ExpFunctionCall e types args =>
        let e' := subst_expr e in
        let args' := List.map (option_map subst_expr) args in
        ExpFunctionCall e' types args'
      | ExpNamelessInstantiation type args =>
        ExpNamelessInstantiation type (subst_exprs args)
      end.

    (** [subst_expr_opt None] is [None], and [subst_expr_opt (Some e)] is 
        [Some (subst_expr e)] *)
    Definition subst_expr_opt := option_map subst_expr.

    (** Maps [subst_expr_opt] over a list of optional expressions *)
    Definition subst_expr_opts := List.map subst_expr_opt.

    (** Maps [subst_expr] over a list of expressions *)
    Definition subst_exprs : list (@Expression tags_t) -> list (@Expression tags_t) :=
      List.map subst_expr.

    (** Maps [subst_expr] over a [MatchPreT] *)
    Definition subst_match_pre (match_pre : @MatchPreT tags_t) :  @MatchPreT tags_t :=
      match match_pre with
      | MatchDontCare => MatchDontCare
      | MatchMask e mask => MatchMask (subst_expr e) (subst_expr mask)
      | MatchRange lo hi => MatchRange (subst_expr lo) (subst_expr hi)
      | MatchCast type expr => MatchCast type (subst_expr expr)
      end.

    (** Maps [subst_expr] over a [Match] *)
    Definition subst_match (mtch : @Match tags_t) : @Match tags_t :=
      let 'MkMatch tags e type := mtch in
      MkMatch tags (subst_match_pre e) type.

    (** Maps [subst_expr] over a list of [Match]es *)
    Definition subst_matches : list (@Match tags_t) -> list (@Match tags_t) := 
      List.map subst_match.

    (** Maps [subst_expr] over a [ParserCase] *)
    Definition subst_parser_case (case : @ParserCase tags_t) : @ParserCase tags_t :=
      let 'MkParserCase tags matches next := case in
      let matches' := subst_matches matches in
      MkParserCase tags matches' next.

    (** Maps [subst_expr] over a [ParserTransition] *)
    Definition subst_parser_transition (trans : @ParserTransition tags_t) : @ParserTransition tags_t :=
      match trans with
      | ParserDirect _ _ => trans
      | ParserSelect tags es cases =>
        let es' := subst_exprs es in
        let cases' := List.map subst_parser_case cases in
        ParserSelect tags es' cases'
      end.

    (** [subst_method_call fn types args] maps [subst_expr] over
        [StatMethodCall fn types args] *)
    Definition subst_method_call fn types args :=
      StatMethodCall (subst_expr fn) types (subst_expr_opts args).

    (** [subst_assignment e1 e2] maps [subst_expr] over [StatAssignment e1 e2] *)
    Definition subst_assignment e1 e2 :=
      StatAssignment (subst_expr e1) (subst_expr e2).

    (** [subst_direct_application t1 t2 args] maps [subst_expr] over
        [StatDirectApplication t1 t2 args] *)
    Definition subst_direct_application t1 t2 args :=
      StatDirectApplication t1 t2 (subst_expr_opts args).

    (** [subst_return e] maps [subst_expr] over [StatReturn e] *)
    Definition subst_return e := StatReturn (subst_expr_opt e).

    (** [subst_constant_stmt type name value loc] maps [subst_expr] over
        [StatConstant type name value loc] *)
    Definition subst_constant_stmt type name value loc :=
      StatConstant type name (subst_expr value) loc.

    (** [subst_variable_stmt type name init loc] maps [subst_expr] over
        [StatVariable type name init loc] *)
    Definition subst_variable_stmt type name init loc :=
      StatVariable type name (subst_expr_opt init) loc.

    (** [subst_variable_decl tags type name init] maps [subst_expr] over
        [DeclVariable tags type name init] *)
    Definition subst_variable_decl tags type name init :=
      let init' := subst_expr_opt init in
      DeclVariable tags type name init'.

    (** [subst_table_pre_action_ref (MkTablePreActionRef name args)] maps
        [subst_expr] over [MkTablePreActionRef name args] *)
    Definition subst_table_pre_action_ref action :=
      let 'MkTablePreActionRef name args := action in
      MkTablePreActionRef name (subst_expr_opts args).

    (** [subst_table_action_ref (MkTableActionRef tags action type)] maps
        [subst_expr] over [MkTableActionRef tags action type] *)
    Definition subst_table_action_ref ref :=
      let 'MkTableActionRef tags action type := ref in
      let action' := subst_table_pre_action_ref action in
      MkTableActionRef tags action' type.

    (** [subst_table_key (MkTableKey tags key kind)] maps [subst_expr] over
        [MkTableKey tags key kind] *)
    Definition subst_table_key tbl_key :=
      let 'MkTableKey tags key kind := tbl_key in
      let key' := subst_expr key in
      MkTableKey tags key' kind.

    (** [subst_table_entry (MkTableEntry tags matches action)] maps [subst_expr]
        over [MkTableEntry tags matches action] *)
    Definition subst_table_entry entry :=
      let 'MkTableEntry tags matches action := entry in
      let matches' := subst_matches matches in
      let action' := subst_table_action_ref action in
      MkTableEntry tags matches' action'.

    (** [subst_table_property (MkTableProperty tags const name value)] maps
        [subst_expr] over [MkTableProperty tags const name value] *)
    Definition subst_table_property prop :=
      let 'MkTableProperty tags const name value := prop in
      let value' := subst_expr value in
      MkTableProperty tags const name value'.

    (** [subst_table tags name keys actions entries default size props] maps
        [subst_expr] over [DeclTable tags name keys actions entries default size props] *)
    Definition subst_table tags name keys actions entries default size props :=
      let keys' := List.map subst_table_key keys in
      let actions' := List.map subst_table_action_ref actions in
      let entries' := option_map (List.map subst_table_entry) entries in
      let default' := option_map subst_table_action_ref default in
      let props' := List.map subst_table_property props in
      DeclTable tags name keys' actions' entries' default' size props'.

    (** [subst_serializable_enum tags type name members] maps [subst_expr] over
        [DeclSerializableEnum tahs type name members] *)
    Definition subst_serializable_enum tags type name members :=
      let members' := map_values subst_expr members in
      DeclSerializableEnum tags type name members'.

  End ConstantEnv.

  (** [update_env env stmt] is [env] with any variables or constants declared
      in [stmt] removed *)
  Definition update_env (env : Env) (stmt : @Statement tags_t) : Env :=
    let 'MkStatement _ stmt _ := stmt in
    match stmt with
    | StatVariable _ name _ _
    | StatConstant _ name _ _ => Env.remove name.(P4String.str) env
    | _ => env
    end.

  (** [subst_stmt env stmt] maps [subst_expr env] over [stmt] *)
  Fixpoint subst_stmt (env : Env) (stmt : @Statement tags_t) : @Statement tags_t :=
    let 'MkStatement tags stmt type := stmt in
    MkStatement tags (subst_stmt_pre env stmt) type

  with subst_stmt_pre (env : Env) (stmt : @StatementPreT tags_t) : @StatementPreT tags_t :=
    let subst_expr := subst_expr env in
    let subst_stmt := subst_stmt env in
    match stmt with
    | StatMethodCall fn types args => subst_method_call env fn types args
    | StatAssignment e1 e2 => subst_assignment env e1 e2
    | StatDirectApplication t1 t2 args =>
      subst_direct_application env t1 t2 args
    | StatConditional e s1 s2 =>
      StatConditional (subst_expr e) (subst_stmt s1) (option_map subst_stmt s2)
    | StatBlock block => StatBlock (subst_block env block)
    | StatExit | StatEmpty => stmt
    | StatReturn e => subst_return env e
    | StatSwitch e cases =>
      let cases' := List.map (subst_switch_case env) cases in
      StatSwitch (subst_expr e) cases'
    | StatConstant type name value loc =>
      subst_constant_stmt env type name value loc
    | StatVariable type name init loc =>
      subst_variable_stmt env type name init loc
    | StatInstantiation type args name inits =>
      let args' := List.map subst_expr args in
      let inits' := List.map (subst_initializer env) inits in
      StatInstantiation type args' name inits'
    end

  (** [subst_block env block] maps [subst_stmt env] over [block] *)
  with subst_block (env : Env) (block : Block) : Block :=
    match block with
    | BlockEmpty _ => block
    | BlockCons stmt stmts =>
      let stmt := subst_stmt env stmt in
      let env := update_env env stmt in
      BlockCons stmt (subst_block env stmts)
    end

  (** [subst_switch_case env case] maps [subst_stmt env] over the switch case [case] *)
  with subst_switch_case (env : Env) (case : StatementSwitchCase) : StatementSwitchCase :=
    match case with
    | StatSwCaseFallThrough _ _ => case
    | StatSwCaseAction tags label code =>
      let code' := subst_block env code in
      StatSwCaseAction tags label code'
    end

  (** [subst_initializer env init] maps [subst_stmt env] over the initializer
      [init] *)
  with subst_initializer (env : Env) (init : Initializer) : Initializer :=
    match init with
    | InitFunction tags ret name types params body =>
      let body' := subst_block env body in
      InitFunction tags ret name types params body'
    | InitInstantiation tags types args name inits =>
      let args' := subst_exprs env args in
      let inits' := List.map (subst_initializer env) inits in
      InitInstantiation tags types args' name inits'
    end.

  (** A list of statements *)
  Definition Statements : Type := list (@Statement tags_t).

  (** [subst_stmts_state stmts] is a state monad that threads an environment
      sequentially through [stmts], updating it with variable declarations
      at every statement *)
  Definition subst_stmts_state : Statements -> State Env Statements :=
    map_monad
      ( fun stmt =>
          let* env := get_state in
          let stmt' := subst_stmt env stmt in
          put_state (update_env env stmt) ;;
          mret stmt'
      ).

  (** [subst_parser_state env state] maps [subst_expr env] over the parser state
      [state] *)
  Definition subst_parser_state (env : Env) (state : @ParserState tags_t) : @ParserState tags_t :=
    let 'MkParserState tags name stmts trans := state in
    let stmts_state := subst_stmts_state stmts in
    let (stmts', env') := run_state stmts_state env in
    let trans' := subst_parser_transition env' trans in
    MkParserState tags name stmts' trans'.

  (** Maps [subst_parser_state] over a list of parser states *)
  Definition subst_parser_states (env : Env) : list (@ParserState tags_t) -> list (@ParserState tags_t) :=
    List.map (subst_parser_state env).

  (** [update_toplevel_env env decl] is [env] with any constants declared in
      [decl] added to it *)
  Definition update_toplevel_env (env : Env) (d : @Declaration tags_t) : Env :=
    match d with
    | DeclConstant _ _ x e => Env.bind x.(P4String.str) e env
    | _ => env
    end.

  (** Would be nice to declare this as mutually recursive with [subst_decl].
      Unfortuntely, this would not be structurally recursive. *)
  Section SubstDecls.

    (** A function such that [subst_decl env decl] is [decl] with any
        identifiers bound in [env] substituted for their bound value *)
    Variable subst_decl : Env -> @Declaration tags_t -> @Declaration tags_t.

    (** A list of declarations *)
    Definition Declarations := list (@Declaration tags_t).

    (** [subst_decls_state decls] is a state monad that threads an environment'
        sequentially through [decls], updating it with declared constants
        every step *)
    Definition subst_decls_state : Declarations -> State Env Declarations :=
      map_monad 
        ( fun decl =>
            let* env := get_state in
            let decl' := subst_decl env decl in
            put_state (update_toplevel_env env decl) ;;
            mret decl'
        ).

    (** [subst_decls env decls] is the result of threading [decls] through
        [subst_decls_state] with intial environment [env] *)
    Definition subst_decls (env : Env) (decls : Declarations) : Declarations :=
      eval_state (subst_decls_state decls) env.

    (** [subst_decls_env env decls] is a pair [(decls' env')] where [decls'] is
        [subst_Decls env decls] and [env'] is the final updated environment
        resulting from threading initial environment [env] through [decls] *)
    Definition subst_decls_env (env : Env) (decls : Declarations) : Declarations * Env :=
      run_state (subst_decls_state decls) env.

  End SubstDecls.

  (** [subst_function env tags ret name types params body] is
      the function declaration [DeclFunction tags ret name types params body]
      with its body mapped by [subst_block env] *)
  Definition subst_function env tags ret name types params body :=
    let body' := subst_block env body in
    DeclFunction tags ret name types params body'.

  (** [subst_action env tags name dparams cparams body] is the action
      declaration [DeclAction tags name dparams cparams body] with its body
      mapped by [subst_block env] *)
  Definition subst_action env tags name dparams cparams body :=
    let body' := subst_block env body in
    DeclAction tags name dparams cparams body'.

  (** [subst_decl env decl] is [decl] with all identifiers bound in [env]
      substituted by their bound value *)
  Fixpoint subst_decl (env : Env) (decl : @Declaration tags_t) : @Declaration tags_t :=
    let subst_decls := subst_decls subst_decl env in
    let subst_decls_env := subst_decls_env subst_decl env in
    match decl with
    | DeclConstant tags type name value =>
      DeclConstant tags type name (subst_expr env value)
    | DeclInstantiation tags type args name init =>
      let args' := subst_exprs env args in
      let init' := subst_decls init in
      DeclInstantiation tags type args' name init'
    | DeclParser tags name types params cparams locals states =>
      let (locals', env') := subst_decls_env locals in
      let states' := subst_parser_states env' states in
      DeclParser tags name types params cparams locals' states'
    | DeclControl tags name types params cparams locals apply =>
      let (locals', env') := subst_decls_env locals in
      let apply' := subst_block env' apply in
      DeclControl tags name types params cparams locals' apply'
    | DeclFunction tags ret name types params body =>
      subst_function env tags ret name types params body
    | DeclVariable tags type name init =>
      subst_variable_decl env tags type name init
    | DeclAction tags name dparams cparams body =>
      subst_action env tags name dparams cparams body
    | DeclTable tags name keys actions entries default size props =>
      subst_table env tags name keys actions entries default size props
    | DeclSerializableEnum tags type name members =>
      subst_serializable_enum env tags type name members
    | DeclTypeDef tags name (inr decl) =>
      let decl' := subst_decl env decl in
      DeclTypeDef tags name (inr decl')
    | DeclNewType tags name (inr decl) =>
      let decl' := subst_decl env decl in
      DeclNewType tags name (inr decl')
    | DeclExternFunction _ _ _ _ _
    | DeclValueSet _ _ _ _
    | DeclHeader _ _ _
    | DeclHeaderUnion _ _ _
    | DeclStruct _ _ _
    | DeclError _ _
    | DeclMatchKind _ _
    | DeclEnum _ _ _
    | DeclExternObject _ _ _ _
    | DeclTypeDef _ _ (inl _)
    | DeclNewType _ _ (inl _)
    | DeclControlType _ _ _ _
    | DeclParserType _ _ _ _
    | DeclPackageType _ _ _ _ => decl
    end.

    Check exec_expr.

  (** [inline_constants prog] is [prog] with all references to constants
      inlined with their value *)
  Definition inline_constants (prog : @program tags_t) : @program tags_t :=
    let 'Program decls := prog in
    let state := subst_decls_state subst_decl decls in
    Program (eval_state state []).

End InlineConstants.

Section InlineProof.

  Variables 
    (tags_t : Type)
    (target : Target)
    (g : @genv tags_t target)
    (read_one_bit : option bool -> bool -> Prop)
    (p : list string) 
    (st : state).

  Definition exec_expr := exec_expr g read_one_bit p st.

  Definition Sval := @ValueBase (option bool).

  Definition Val := @ValueBase bool.

  Definition exec_val := exec_val read_one_bit.

  Hypotheses (read_one_bit_def : forall b b', read_one_bit (Some b) b' <-> b = b')
             (read_one_bit_reads : read_one_bit_reads read_one_bit).

  Local Hint Constructors exec_expr_det : core.

  Definition exec_expr_det := exec_expr_det g read_one_bit p st.

  Lemma exec_record_ndet :
    forall e ndet_fields name sv v,
    exec_expr e (ValBaseStruct ndet_fields) ->
    AList.get ndet_fields name = Some sv ->
    exec_val sv v ->
    exists fields,
    exec_val (ValBaseStruct ndet_fields) (ValBaseStruct fields) /\
    AList.get fields name = Some v.
  Proof.
  Admitted.

  Lemma expr_inline_correct :
    forall
      (e : Expression)
      (v : Val)
      (env : Env),
      exec_expr_det (subst_expr env e) v -> exec_expr_det e v.
  Proof.
    induction e using expr_ind; auto.
    - admit.
    - admit.
    - admit.
    - induction vs. auto. intros. inv H0. inv H1. inv H9. inv H2. inv H1. inv H.
      assert (exec_expr_det (subst_expr env a) y0).
      { econstructor; eauto. }
      apply H2 in H. inv H. eapply IHvs with (v := ValBaseTuple l'0) in H6 as IH.
      + inv IH. inv H. inv H8. econstructor; econstructor; econstructor; eauto.
      + econstructor; constructor; eauto. 
    - induction es. auto. intros. inv H.
      inv H0. inv H. inv H10.
      inv H1. inv H0. destruct H2 as [? ?]. destruct H5 as [? ?].
      destruct a as [x e]. destruct y as [xsv' sv']. destruct y0 as [xv v].
      simpl in *. subst.
      assert (exec_expr_det (subst_expr env e) v).
      { econstructor; eauto. }
      apply H3 in H. inv H.
      eapply IHes with (v := ValBaseStruct l'0) in H4 as IH.
      + inv IH. inv H. inv H7. econstructor.
        * constructor. apply Forall2_cons with (y := (P4String.str x, sv)); eauto.
        * constructor. constructor; auto.
      + econstructor; constructor; eauto.
    - intros. inv H. inv H0.
      assert (H12' := H12).
      apply val_to_sval_iff in H12. subst.
      eapply sval_to_val_eval_val_to_sval_iff in read_one_bit_def as ?.
      apply H in H1. clear H. subst.
      assert (exec_expr_det (subst_expr env e) argv).
      { econstructor; eauto. }
      assert (exec_expr_det e argv) by eauto. inv H0.
      assert (exec_expr (MkExpression t (ExpUnaryOp op e) typ dir) (eval_val_to_sval v)).
      { econstructor; eauto. }
      econstructor; eauto.
      apply sval_to_val_eval_val_to_sval.
      intros. apply read_one_bit_def. reflexivity.
    - intros. inv H. inv H0.
      assert (H15' := H15).
      apply val_to_sval_iff in H15. subst.
      eapply sval_to_val_eval_val_to_sval_iff in read_one_bit_def as ?.
      apply H in H1. clear H. subst.
      assert (exec_expr_det (subst_expr env e1) largv).
      { econstructor; eauto. }
      assert (exec_expr_det (subst_expr env e2) rargv).
      { econstructor; eauto. }
      assert (exec_expr_det e1 largv) by eauto. inv H1.
      assert (exec_expr_det e2 rargv) by eauto. inv H1.
      assert (exec_expr (MkExpression t (ExpBinaryOp op e1 e2) typ dir) (eval_val_to_sval v)).
      { econstructor; eauto. }
      econstructor; eauto.
      apply sval_to_val_eval_val_to_sval.
      intros. apply read_one_bit_def. reflexivity.
    - intros. inv H. inv H0.
      assert (H13' := H13).
      apply val_to_sval_iff in H13. subst.
      eapply sval_to_val_eval_val_to_sval_iff in read_one_bit_def as ?.
      apply H in H1. clear H. subst.
      assert (exec_expr_det (subst_expr env e) oldv).
      { econstructor; eauto. }
      assert (exec_expr_det e oldv) by eauto. inv H0.
      assert (exec_expr (MkExpression t (ExpCast typ e) typ1 dir) (eval_val_to_sval v)).
      { econstructor; eauto. }
      econstructor; eauto.
      apply sval_to_val_eval_val_to_sval.
      intros. apply read_one_bit_def. reflexivity.
  Admitted.

  Lemma expr_inline_sound :
    forall
      (e : Expression)
      (sv : Sval)
      (env : Env),
      exec_expr (subst_expr env e) sv -> exec_expr e sv.
  Proof.
    induction e using expr_ind; auto.
    - intros. destruct n eqn:E; auto.
      unfold subst_expr in H. unfold subst_name in H.
      destruct (Env.find (P4String.str name) env) eqn:E'; simpl in *; auto.
      admit.
    - intros. inv H. apply IHe1 in H11. apply IHe2 in H5. econstructor; eauto.
    - intros. inv H. apply IHe in H9. econstructor; eauto.
    - induction vs. auto. intros. inv H. inv H0. inv H9.
      repeat constructor.
      + apply H3 in H1. assumption.
      + eapply IHvs with (sv := ValBaseTuple l') in H4.
        * inv H4. assumption.
        * constructor. eauto.
    - induction es. auto. intros. inv H. inv H0. inv H9.
      destruct a as [x e]. destruct y as [xv v]. destruct H1 as [? ?]. 
      simpl in *. subst. apply H3 in H0.
      eapply IHes with (sv := ValBaseStruct l') in H4 as ?.
      + inv H. constructor. constructor; eauto.
      + econstructor. eauto. 
    - intros. inv H. apply val_to_sval_iff in H11 as ?. subst.
      apply IHe in H8. econstructor; eauto.
    - intros. inv H.
      apply val_to_sval_iff in H14 as ?. subst.
      apply IHe1 in H8. apply IHe2 in H10.
      econstructor; eauto.
    - intros. inv H. apply val_to_sval_iff in H12 as ?. subst.
      apply IHe in H7.
      econstructor; eauto.
    - intros. inv H. apply IHe in H8. inv H9; 
      econstructor; eauto; try (constructor; auto).
      + replace (P4String.str name) with "size". constructor.
      + replace (P4String.str name) with "lastIndex". econstructor; eauto.
    - intros. inv H. apply IHe1 in H9. destruct b.
      + apply IHe2 in H11. econstructor; eauto.
      + apply IHe3 in H11. econstructor; eauto.
    - intros. inv H0.
    - intros. inv H0.
  Admitted.

End InlineProof.
