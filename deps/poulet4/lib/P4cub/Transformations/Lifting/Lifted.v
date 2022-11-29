Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Syntax.Shift
        Poulet4.P4cub.Transformations.Lifting.Statementize.
Require Import Poulet4.Utils.ForallMap.
Import AllCubNotations.

Ltac pair_destr :=
  match goal with
  | h: (_,_) = (_,_) |- _ => inv h
  end.

Ltac lift_e_destr :=
  match goal with
  | |- context [lift_e ?e]
    => destruct (lift_e e) as [? ?] eqn:?; simpl in *
  end.

Ltac lift_e_destr_hyp :=
  match goal with
  | H: context [lift_e ?e] |- _
    => destruct (lift_e e)
      as [? ?] eqn:?; simpl in *
  end.

Ltac lift_e_destr_hyp_rewrite :=
  match goal with
  | H: lift_e ?e = (_,_),
      Hy : context [lift_e ?e]
    |- _ => rewrite H in Hy; simpl in *
  end.

Inductive lifted_expr : Expr.e -> Prop :=
| lifted_bool (b : bool) :
  lifted_expr b
| lifted_var τ og x :
  lifted_expr (Expr.Var τ og x)
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

Variant lifted_parser_expr : Parser.trns -> Prop :=
  | lifted_goto st : 
    lifted_parser_expr (Parser.Direct st)
  | lifted_select exp default cases : 
    lifted_expr exp ->
    lifted_parser_expr (Parser.Select exp default cases).

Inductive lifted_stmt : Stmt.s -> Prop :=
| lifted_skip :
  lifted_stmt Stmt.Skip
| lifted_vardecl og te s :
  match te with
  | inl t => True
  | inr e => lifted_rexpr e
  end ->
  lifted_stmt s ->
  lifted_stmt (Stmt.Var og te s)
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
| lifted_invoke t :
  lifted_stmt (Stmt.Invoke t)
| lifted_apply x ext_args args :
  Forall lifted_arg args ->
  lifted_stmt (Stmt.Apply x ext_args args).

Variant lifted_control_Decl : Control.d -> Prop :=
  | lifted_control_Var x te :
    match te with
    | inl t => True
    | inr e => lifted_rexpr e
    end ->
    lifted_control_Decl (Control.Var x te)
  | lifted_control_Action act cps dps body :
    lifted_stmt body ->
    lifted_control_Decl (Control.Action act cps dps body)
  | lifted_control_Table table_name key actions :
    Forall lifted_expr (map fst key) ->
    Forall (Forall lifted_arg) (map snd actions) ->
    lifted_control_Decl (Control.Table table_name key actions).

Variant lifted_top_Decl : TopDecl.d -> Prop :=
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

Lemma shift_lifted_expr : forall sh e,
    lifted_expr e -> lifted_expr (shift_e sh e).
Proof.
  intros sh e h; induction h; unravel; auto.
Qed.

Local Hint Resolve shift_lifted_expr : core.

Lemma rename_e_lifted_rexpr : forall ρ e,
    lifted_rexpr e -> lifted_rexpr (rename_e ρ e).
Proof.
  intros ρ e h; inv h; unravel; auto;
    constructor; rewrite sublist.Forall_map;
    rewrite Forall_forall in *; unravel; auto.
Qed.

Local Hint Resolve rename_e_lifted_rexpr : core.

Lemma shift_lifted_rexpr : forall sh e,
    lifted_rexpr e -> lifted_rexpr (shift_e sh e).
Proof.
  intros sh e h; inv h; unravel; auto;
    constructor; rewrite sublist.Forall_map;
    rewrite Forall_forall in *; unravel; auto.
Qed.

Local Hint Resolve shift_lifted_rexpr : core.

Lemma shift_list_lifted_rexpr : forall sh es,
    Forall lifted_rexpr es ->
    Forall lifted_rexpr (shift_list shift_e sh es).
Proof.
  intros sh es h; induction h; unravel; auto.
Qed.

Local Hint Resolve shift_list_lifted_rexpr : core.

Section LiftList.
  Context {U : Set}.
  Variable shift_u : shifter -> U -> U.
  Variable lifted_u : U -> Prop.

  Hypothesis shift_lifted_u : forall sh u,
      lifted_u u -> lifted_u (shift_u sh u).
  
  Lemma shift_pairs_lifted : forall us,
    Forall
      (fun ues => Forall lifted_rexpr (snd ues)
               /\ lifted_u (fst ues)) us ->
    Forall
      (fun ues => Forall lifted_rexpr (snd ues)
               /\ lifted_u (fst ues))
      (shift_pairs shift_u us).
  Proof using U lifted_u shift_lifted_u shift_u.
    intros us h.
    induction h as [| [u es] us [hu hes] hus ih]; unravel in *; auto.
    constructor; cbn.
    - split; auto.
    - clear dependent u. clear hus hu.
      rewrite Forall_conj in *.
      rewrite <- Forall_map with (f:=fst) in *.
      rewrite <- Forall_map with (f:=snd) in *.
      rewrite map_fst_map, map_snd_map, map_id.
      destruct ih as [h2 h1].
      split; auto. clear h2.
      rewrite Forall_forall in *.
      intros u' hu'.
      rewrite in_map_iff in hu'.
      destruct hu' as (u & hu & hin); subst.
      auto.
  Qed.
End LiftList.

Local Hint Resolve shift_pairs_lifted : core.
  
(*Lemma lift_list_lifted_expr : forall es l Es up,
    lift_list lift_e rename_e up es = (l, Es) ->
    Forall
        (fun e : Expr.e =>
         forall (E : Expr.e) (le : list Expr.e) (u : nat),
           lift_e u e = (le, E) ->
           Forall lifted_rexpr le /\ lifted_expr E) es ->
    Forall lifted_rexpr l /\ Forall lifted_expr Es.
Proof.
  intro es; induction es as [| e es ih];
    intros l [| E Es] up h H; cbn in *; inv H.
  - inv h. auto.
  - inv h.
  - destruct (lift_e up e) as [le' E'] eqn:he.
    destruct (lift_list lift_e rename_e (length le' + up) es)
      as [les' Es'] eqn:hes. inv h.
  - destruct (lift_e up e) as [le' E'] eqn:he.
    destruct (lift_list lift_e rename_e (length le' + up) es)
      as [les' Es'] eqn:hes. inv h.
    pose proof ih _ _ _ hes H3 as [hles' hEs].
    pose proof H2 _ _ _ he as [hle' hE'].
    rewrite Forall_app. repeat split; eauto.
Qed.

Local Hint Resolve lift_list_lifted_expr : core.*)

Lemma lift_e_lifted_expr : forall e E l,
    lift_e e = (E, l) ->
    Forall lifted_rexpr l /\ lifted_expr E.
Proof.
  intro e; induction e using custom_e_ind;
    intros E ll h; unravel in *;
    repeat lift_e_destr;
    try lift_e_destr_hyp;
    repeat pair_destr; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
  - destruct (lift_e e2) as [e2' l2] eqn:eql2.
    pose proof IHe1 _ _ eq_refl as [? ?]; clear IHe1.
    pose proof IHe2 _ _ eq_refl as [? ?]; clear IHe2.
    pair_destr.
    split; auto.
    constructor.
    + apply lifted_bop; auto.
    + rewrite Forall_app; eauto.
  - destruct (split (shift_pairs shift_e (map lift_e exps)))
      as [es les] eqn:hexps; inv h.
    split; auto.
    assert (Forall
              (fun ees : Expr.e * list Expr.e =>
                 Forall lifted_rexpr (snd ees)
                 /\ lifted_expr (fst ees)) (map lift_e exps)) as h.
    { clear dependent les. clear es.
      repeat rewrite Forall_forall in *.
      intros [e' es] h; cbn.
      rewrite in_map_iff in h.
      destruct h as (e & hlift & hin); cbn in *; subst.
      eauto. }
    clear H.
    rewrite split_map in hexps. inv hexps.
    pose proof shift_pairs_lifted
      _ _ shift_lifted_expr _ h as H.
    clear h.
    rewrite Forall_conj in H.
    destruct H as [h2 h1].
    rewrite <- Forall_map with (f:=snd),
        <- Forall_concat in h2.
    rewrite <- Forall_map with (f:=fst) in h1.
    auto.
  - destruct (lift_e e2) as [e2' l2] eqn:eql2.
    pose proof IHe1 _ _ eq_refl as [? ?].
    pose proof IHe2 _ _ eq_refl as [? ?].
    pair_destr.
    split; auto; rewrite Forall_app; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
Qed.

Local Hint Resolve lift_e_lifted_expr : core.

Lemma lift_e_list_lifted_expr : forall es es' le,
    lift_e_list es = (es', le) ->
    Forall lifted_rexpr le /\ Forall lifted_expr es'.
Proof.
  intros es es' le h.
  unfold lift_e_list in h.
  destruct (split (shift_pairs shift_e $ map lift_e es))
    as [es'' les] eqn:hsplit.
  rewrite split_map in hsplit.
  unravel in *.
  do 2 pair_destr.
  rewrite Forall_concat.
  rewrite Forall_map with (f:=snd).
  rewrite Forall_map with (f:=fst).
  rewrite <- Forall_conj.
  apply shift_pairs_lifted; eauto.
  rewrite Forall_forall.
  intros [e' le] hin.
  rewrite in_map_iff in hin.
  destruct hin as (e & hlift & hin); cbn.
  eauto.
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
Proof. eauto. Qed.

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
  - destruct (lift_trans up trns) as [le e'] eqn:eqle.
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

Lemma lift_control_decl_lifted_control_Decl : forall cd cds up n,
    lift_control_decl up cd = (n, cds) ->
    Forall lifted_control_Decl cds.
Proof.
  intros cd cds up n h; destruct cd; unravel in *; auto.
  - destruct expr.
    + inv h. auto.
    + lift_e_destr_hyp. inv h.
      apply lift_e_lifted_expr in Heqp as [hl he0].
      rewrite Forall_app, Forall_map.
      split; eauto using Forall_impl.
  - inv h. auto.
  - destruct (split key) as [es mks] eqn:hkey.
    destruct (split actions) as [acts argss] eqn:hactions.
    destruct (lift_e_list up es) as [ees es'] eqn:hes.
    destruct (lift_list lift_args (fun ρ => map (rename_arg ρ)) (length ees + up) argss)
      as [argsss argss'] eqn:hargss. inv h.
    pose proof lift_e_list_lifted_expr _ _ _ _ hes as [hees hes'].
    assert (Forall lifted_rexpr argsss /\ Forall (Forall lifted_arg) argss') as [hargsss hargs'].
    { eapply lift_list_lifted; eauto.
      intros r args hargs. unravel.
      rewrite Forall_map. eauto using Forall_impl. }
    repeat rewrite Forall_app. repeat rewrite Forall_map.
    repeat split; eauto using Forall_impl.
    constructor; auto. constructor.
    + rewrite map_fst_combine; auto.
      pose proof f_equal fst hkey as hfst.
      pose proof f_equal snd hkey as hsnd.
      apply f_equal with (f:=length (A:=Expr.e)) in hfst.
      apply f_equal with (f:=length (A:=String.string)) in hsnd.
      rewrite split_length_l in hfst.
      rewrite split_length_r in hsnd. cbn in *.
      rewrite hfst in hsnd.
      apply lift_list_length in hes.
      rewrite <- hes. assumption.
    + rewrite map_snd_combine; auto.
      pose proof f_equal fst hactions as hfst.
      pose proof f_equal snd hactions as hsnd.
      apply f_equal with (f:=length (A:=String.string)) in hfst.
      apply f_equal with (f:=length (A:=Expr.args)) in hsnd.
      rewrite split_length_l in hfst.
      rewrite split_length_r in hsnd. cbn in *.
      rewrite hfst in hsnd.
      apply lift_list_length in hargss.
      rewrite <- hargss. assumption.
Qed.

Local Hint Resolve lift_control_decl_lifted_control_Decl : core.

Lemma lift_control_decls_lifted_control_Decls : forall cds cds' up n,
    lift_control_decls up cds = (n, cds') ->
    Forall lifted_control_Decl cds'.
Proof.
  intro cds; induction cds as [| cd cds ih];
    intros cds' up n h; unravel in *; auto.
  - inv h. auto.
  - destruct (lift_control_decl up cd) as [cdn cdd] eqn:hcd.
    destruct (lift_control_decls (cdn + up) cds) as [cdsn cdsd] eqn:hcds.
    inv h. rewrite Forall_app. split; eauto.
Qed.

Local Hint Resolve lift_control_decls_lifted_control_Decls : core.
Local Hint Constructors lifted_top_Decl : core.

Lemma lift_top_decl_lifted_top_Decl : forall td,
    lifted_top_Decl (lift_top_decl td).
Proof.
  intro td; destruct td; unravel in *; auto.
  - destruct (lift_control_decls 0 body) as [? ?] eqn:?.
    constructor; eauto.
  - constructor; auto.
    rewrite sublist.Forall_map; unravel.
    rewrite Forall_forall in *; eauto.
Qed.
