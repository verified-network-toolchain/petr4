Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Transformations.Statementize
        Coq.Numbers.DecimalString
        Coq.Strings.Ascii Coq.Strings.String.
Import AllCubNotations StringSyntax Field.FieldTactics.

Ltac transformExpr_destr :=
  match goal with
  | |- context [TransformExpr ?e ?env]
    => destruct (TransformExpr e env) as [[? ?] ?] eqn:?; simpl in *
  | |- context [TransformExprList' ?f ?e ?env ?i]
    => destruct (TransformExprList' f e env i) as [[? ?] ?] eqn:?; simpl in *
  | |- context [TransformFields' ?f ?e ?env ?i]
    => destruct (TransformFields' f e env i) as [[? ?] ?] eqn:?; simpl in *
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

  Inductive lifted_args : Expr.arrowE tags_t -> Prop :=
  | lifted_args_arrow tes teo :
      F.predfs_data (pred_paramarg_same lifted_expr) tes ->
      predop lifted_expr teo ->
      lifted_args (Arrow tes teo).
  
  Inductive lifted_stmt : Stmt.s tags_t -> Prop :=
  | lifted_skip i :
      lifted_stmt -{ skip @ i }-
  | lifted_vardecl x te i :
      match te with
      | Left t => True
      | Right e => lifted_expr e
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
      lifted_stmt -{ apply x with ext_args & args @ i }-.
  
  Local Hint Constructors lifted_expr : core.
  Section HelperLemmas.
    Variable f :
      Expr.e tags_t -> VarNameGen.t ->
      Stmt.s tags_t * Expr.e tags_t * VarNameGen.t.

    (*Lemma TransformExprList'_lifted_expr :
      forall es env i,
        
        Forall
          lifted_expr
          (snd (fst (TransformExprList' f es env i))).*)
      
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
        apply f_equal with (f:= (snd ∘ fst)) in Heqp;
        apply f_equal with (f:= (snd ∘ fst)) in Heqp0.
      unravel in *; rewrite <- Heqp, <- Heqp0; auto.
    - admit.
    - apply lifted_tuple.
      apply f_equal with (f := snd ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - admit.
    - apply lifted_struct.
      apply f_equal with (f := snd ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto.
    - admit.
      (*
    - apply lifted_header.
      + apply f_equal with (f := snd ∘ fst) in Heqp; unravel in *.
        rewrite <- Heqp; auto.
      + apply f_equal with (f := snd ∘ fst) in Heqp0; unravel in *.
        rewrite <- Heqp0; auto.
    - admit.
    - apply lifted_stack.
      apply f_equal with (f := snd ∘ fst) in Heqp; unravel in *.
      rewrite <- Heqp; auto. *)
  Admitted.
End Lifted.
