From Poulet4 Require Import
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

  Print nth.

  (* Hypothesis read_one_bit_def : forall (b b' : bool), read_one_bit (Some b) b' <-> b = b'. *)

  Lemma expr_inline_correct :
    forall
      (e : Expression)
      (sv sv' : Sval)
      (v : Val)
      (env : Env),
      exec_expr e sv ->
      exec_expr (subst_expr env e) sv' ->
      exec_val sv v <-> exec_val sv' v.
  Proof.
    induction e using expr_ind.
    - intros. inv H. inv H0. reflexivity.
    - intros. inv H. inv H0. reflexivity.
    - intros. inv H. inv H0. reflexivity.
    - admit.
    - (* Show  e1[e2] ==> v -> [[ e1[e2] ]] ==> v' -> v = v' *)
      (* We know there exists v1, v1', v2, v2' 
        for which e1 ==> v1, [[ e1 ]] ==> v1', *)
      intros. inv H. inv H0.
      (* eapply IHe1 in H12 as [? ?]; eauto.
      eapply IHe2 in H6  as [? ?]; eauto. *)
      split; intros; admit.
      (* apply H in H7.
      apply H6 in H8.
      apply H
      intuition.
      + inv H3 econstructor. 
      + inv H. constructor.
      assert (ValBaseStack headers next = ValBaseStack headers0 next0) by eauto.
      assert (idxsv = idxsv0) by eauto.
      clear H5 H6 H12 H17 IHe1 IHe2.
      assert (rtyp0 = rtyp).
      { rewrite H18 in H13. injection H13. trivial. }
      clear H13 H18.
      injection H as ?. subst.
      assert (default_header = default_header0).
      { rewrite H19 in H14. injection H14. auto. }
      clear H14 H19.
      subst. f_equal.
      inv H7; inv H8; try discriminate; try congruence;
      try (injection H10 as ?; injection H15 as ?); subst.
      + admit. 
      + admit.
      + admit. *)
    - admit.
    - (* Case e = ExpList es. Proof: induction on es *)
      split; generalize dependent sv; generalize dependent sv'; generalize dependent v.
      + induction vs; intros.
        * inv H. inv H0. inv H9. inv H1. inv H8. assumption.
        * inv H0. inv H1.
          inv H10. inv H9.
          inv H. inv H2. inv H0. 
          apply IHvs with
            (sv := ValBaseTuple l') 
            (sv' := ValBaseTuple l'0) 
            (v := ValBaseTuple l'1) in H8 as IH.
          { inv IH. constructor. constructor; auto. 
            eapply H6 in H3 as [? ?]; eauto. eapply H in H2. auto. }
          { constructor. assumption. }
          { constructor. assumption. }
          { constructor. assumption. }
      + induction vs; intros.
        * inv H. inv H0. inv H9. inv H1. inv H8. assumption.
        * inv H0. inv H1.
          inv H10. inv H9.
          inv H. inv H2. inv H0. 
          apply IHvs with 
            (sv := ValBaseTuple l') 
            (sv' := ValBaseTuple l'0) 
            (v := ValBaseTuple l'1) in H8 as IH.
          { inv IH. constructor. constructor; auto. 
            eapply H6 in H3 as [? ?]; eauto. eapply H0 in H2. auto. }
          { constructor. assumption. }
          { constructor. assumption. }
          { constructor. assumption. }
    - split; generalize dependent sv; generalize dependent sv'; generalize dependent v.
      + induction es; intros.
        * inv H. inv H1. inv H9. inv H0. inv H8. assumption.
        * inv H0. inv H10. destruct H4 as [? ?].
          destruct a as [x e] eqn:?.
          destruct y as [xsv sv] eqn:?.
          simpl in *. subst.
          inv H1. inv H11. inv H2.
          destruct y as [x' e'] eqn:?.
          inv H1. destruct y0 as [xsv' sv'] eqn:?.
          simpl in *. subst. inv H.
          destruct H4 as [? ?].
          destruct H5 as [? ?].
          apply IHes with 
            (sv := ValBaseStruct l') 
            (sv' := ValBaseStruct l'0) 
            (v := ValBaseStruct l'1) in H8 as IH.
          { inv IH. constructor. constructor; auto. split; auto. simpl.
            eapply H2 in H3 as [? ?]; eauto. eapply H in H4. auto. }
          { constructor. assumption. }
          { constructor. assumption. }
          { constructor. assumption. }
      + induction es; intros.
        * inv H. inv H1. inv H9. inv H0. inv H8. assumption.
        * inv H0. inv H10. destruct H4 as [? ?].
          destruct a as [x e] eqn:?.
          destruct y as [xsv sv] eqn:?.
          simpl in *. subst.
          inv H1. inv H11. inv H2.
          destruct y as [x' e'] eqn:?.
          inv H1. destruct y0 as [xsv' sv'] eqn:?.
          simpl in *. subst. inv H.
          destruct H4 as [? ?].
          destruct H5 as [? ?].
          apply IHes with 
            (sv := ValBaseStruct l') 
            (sv' := ValBaseStruct l'0) 
            (v := ValBaseStruct l'1) in H8 as IH.
          { inv IH. constructor. constructor; auto. split; auto. simpl.
            eapply H2 in H3 as [? ?]; eauto. eapply H1 in H4. auto. }
          { constructor. assumption. }
          { constructor. assumption. }
          { constructor. assumption. }
    - admit.
  Admitted.

End InlineProof.
