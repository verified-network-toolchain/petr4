Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Syntax.Shift
        Poulet4.P4cub.Transformations.Lifting.Statementize.
Require Import Poulet4.Utils.ForallMap.

Ltac pair_destr :=
  match goal with
  | h: (_,_) = (_,_) |- _ => inv h
  end.

Ltac lift_exp_destr :=
  match goal with
  | |- context [lift_exp ?e]
    => destruct (lift_exp e) as [? ?] eqn:?; simpl in *
  end.

Ltac lift_exp_destr_hyp :=
  match goal with
  | H: context [lift_exp ?e] |- _
    => destruct (lift_exp e)
      as [? ?] eqn:?; simpl in *
  end.

Ltac lift_exp_destr_hyp_rewrite :=
  match goal with
  | H: lift_exp ?e = (_,_),
      Hy : context [lift_exp ?e]
    |- _ => rewrite H in Hy; simpl in *
  end.

Inductive lifted_exp : Exp.t -> Prop :=
| lifted_bool (b : bool) :
  lifted_exp (Exp.Bool b)
| lifted_var τ og x :
  lifted_exp (Exp.Var τ og x)
| lifted_index τ e₁ e₂ :
  lifted_exp e₁ ->
  lifted_exp e₂ ->
  lifted_exp (Exp.Index τ e₁ e₂)
| lifted_member τ e x :
  lifted_exp e ->
  lifted_exp (Exp.Member τ x e)
| lifted_error err :
  lifted_exp (Exp.Error err).

Definition lifted_arg : paramarg Exp.t Exp.t -> Prop :=
  pred_paramarg_same lifted_exp.

Variant lifted_rexp : Exp.t -> Prop :=
  | lifted_lifted_exp e :
    lifted_exp e ->
    lifted_rexp e
  | lifted_bit w n :
    lifted_rexp (Exp.Bit w n)
  | lifted_int w z :
    lifted_rexp (Exp.Int w z)
  | lifted_varbit m w n :
    lifted_rexp (Exp.VarBit m w n)
  | lifted_slice hi lo e :
    lifted_exp e ->
    lifted_rexp (Exp.Slice hi lo e)
  | lifted_cast τ e :
    lifted_exp e ->
    lifted_rexp (Exp.Cast τ e)
  | lifted_uop τ op e :
    lifted_exp e ->
    lifted_rexp (Exp.Uop τ op e)
  | lifted_bop τ op e₁ e₂ :
    lifted_exp e₁ ->
    lifted_exp e₂ ->
    lifted_rexp (Exp.Bop τ op e₁ e₂)
  | lifted_lists ls es :
    Forall lifted_exp es ->
    lifted_rexp (Exp.Lists ls es).

Variant lifted_call : Call.t -> Prop :=
  | lifted_Funct x τs oe :
    predop lifted_exp oe ->
    lifted_call (Call.Funct x τs oe)
  | lifted_Action x es :
    Forall lifted_exp es ->
    lifted_call (Call.Action x es)
  | lifted_Method x m τs oe :
    predop lifted_exp oe ->
    lifted_call (Call.Method x m τs oe)
  | lifted_Inst x es :
    lifted_call (Call.Inst x es).

Variant lifted_trns : Trns.t -> Prop :=
  | lifted_goto st : 
    lifted_trns (Trns.Direct st)
  | lifted_select exp default cases : 
    lifted_exp exp ->
    lifted_trns (Trns.Select exp default cases).

Inductive lifted_stm : Stm.t -> Prop :=
| lifted_skip :
  lifted_stm Stm.Skip
| lifted_vardecl og te s :
  SumForall
    (fun _ => True)
    lifted_rexp te ->
  lifted_stm s ->
  lifted_stm (`let og := te `in s)%stm
| lifted_asgn e1 e2 :
  lifted_exp e1 ->
  lifted_exp e2 ->
  lifted_stm (e1 `:= e2)%stm
| lifted_cond e s1 s2 :
  lifted_exp e ->
  lifted_stm s1 ->
  lifted_stm s2 ->
  lifted_stm (`if e `then s1 `else s2)%stm
| lifted_seq s1 s2 :
  lifted_stm s1 ->
  lifted_stm s2 ->
  lifted_stm (Stm.Seq s1 s2)
| lifted_app fk args :
  lifted_call fk ->
  Forall lifted_arg args ->
  lifted_stm (Stm.App fk args)
| lifted_ret eo :
  predop lifted_exp eo ->
  lifted_stm (Stm.Ret eo)
| lifted_exit :
  lifted_stm Stm.Exit
| lifted_trans e :
  lifted_trns e ->
  lifted_stm (Stm.Trans e)
| lifted_invoke eo t :
  predop lifted_rexp eo ->
  lifted_stm (Stm.Invoke eo t).

Variant lifted_ctrl : Ctrl.t -> Prop :=
  | lifted_control_Var x te :
    SumForall
      (fun _ => True)
      lifted_rexp te ->
    lifted_ctrl (Ctrl.Var x te)
  | lifted_control_Action act cps dps body :
    lifted_stm body ->
    lifted_ctrl (Ctrl.Action act cps dps body)
  | lifted_control_Table table_name key actions def :
    Forall lifted_exp (map fst key) ->
    Forall (Forall lifted_arg) (map snd actions) ->
    predop (fun '(_,es) => Forall lifted_exp es) def ->
    lifted_ctrl (Ctrl.Table table_name key actions def).

Variant lifted_top : Top.t -> Prop :=
| lifted_Instantiate c_name i_name type_args cargs expr_cargs :
  lifted_top (Top.Instantiate c_name i_name type_args cargs expr_cargs)
| lifted_Extern e_name type_params c_params expr_c_params methods : 
  lifted_top (Top.Extern e_name type_params c_params expr_c_params methods)
| lifted_Control c cparams expr_cparams eps params body apply_blk :
  Forall lifted_ctrl body -> lifted_stm apply_blk ->
  lifted_top (Top.Control c cparams expr_cparams eps params body apply_blk)
| lifted_Parser p cparams expr_cparams eps params start_state states :
  lifted_stm start_state -> Forall lifted_stm states ->
  lifted_top (Top.Parser p cparams expr_cparams eps params start_state states)
| lifted_Function f tparams signature body :
  lifted_stm body -> lifted_top (Top.Funct f tparams signature body).

Local Hint Constructors lifted_exp : core.
Local Hint Constructors lifted_rexp : core.
Local Hint Constructors lifted_trns : core.

Lemma rename_exp_lifted_exp : forall ρ e,
    lifted_exp e -> lifted_exp (rename_exp ρ e).
Proof.
  intros ρ e h; induction h; unravel; auto.
Qed.

Local Hint Resolve rename_exp_lifted_exp : core.

Lemma shift_lifted_exp : forall sh e,
    lifted_exp e -> lifted_exp (shift_exp sh e).
Proof.
  intros sh e h; induction h; unravel; auto.
Qed.

Local Hint Resolve shift_lifted_exp : core.

Lemma rename_exp_lifted_rexp : forall ρ e,
    lifted_rexp e -> lifted_rexp (rename_exp ρ e).
Proof.
  intros ρ e h; inv h; unravel; auto;
    constructor; rewrite sublist.Forall_map;
    rewrite Forall_forall in *; unravel; auto.
Qed.

Local Hint Resolve rename_exp_lifted_rexp : core.

Lemma shift_lifted_rexp : forall sh e,
    lifted_rexp e -> lifted_rexp (shift_exp sh e).
Proof.
  intros sh e h; inv h; unravel; auto;
    constructor; rewrite sublist.Forall_map;
    rewrite Forall_forall in *; unravel; auto.
Qed.

Local Hint Resolve shift_lifted_rexp : core.

Lemma shift_list_lifted_rexp : forall sh es,
    Forall lifted_rexp es ->
    Forall lifted_rexp (shift_list shift_exp sh es).
Proof.
  intros sh es h; induction h; unravel; auto.
Qed.

Local Hint Resolve shift_list_lifted_rexp : core.

Section LiftList.
  Context {U : Set}.
  Variable shift_u : shifter -> U -> U.
  Variable lifted_u : U -> Prop.

  Hypothesis shift_lifted_u : forall sh u,
      lifted_u u -> lifted_u (shift_u sh u).
  
  Lemma shift_pairs_lifted : forall us,
    Forall
      (fun ues => Forall lifted_rexp (snd ues)
               /\ lifted_u (fst ues)) us ->
    Forall
      (fun ues => Forall lifted_rexp (snd ues)
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
  
(*Lemma lift_list_lifted_exp : forall es l Es up,
    lift_list lift_exp rename_exp up es = (l, Es) ->
    Forall
        (fun e : Exp.t =>
         forall (E : Exp.t) (le : list Exp.t) (u : nat),
           lift_exp u e = (le, E) ->
           Forall lifted_rexp le /\ lifted_exp E) es ->
    Forall lifted_rexp l /\ Forall lifted_exp Es.
Proof.
  intro es; induction es as [| e es ih];
    intros l [| E Es] up h H; cbn in *; inv H.
  - inv h. auto.
  - inv h.
  - destruct (lift_exp up e) as [le' E'] eqn:he.
    destruct (lift_list lift_exp rename_exp (length le' + up) es)
      as [les' Es'] eqn:hes. inv h.
  - destruct (lift_exp up e) as [le' E'] eqn:he.
    destruct (lift_list lift_exp rename_exp (length le' + up) es)
      as [les' Es'] eqn:hes. inv h.
    pose proof ih _ _ _ hes H3 as [hles' hEs].
    pose proof H2 _ _ _ he as [hle' hE'].
    rewrite Forall_app. repeat split; eauto.
Qed.

Local Hint Resolve lift_list_lifted_exp : core.*)

Lemma lift_exp_lifted_exp : forall e E l,
    lift_exp e = (E, l) ->
    Forall lifted_rexp l /\ lifted_exp E.
Proof.
  intro e; induction e using custom_exp_ind;
    intros E ll h; unravel in *;
    repeat lift_exp_destr;
    try lift_exp_destr_hyp;
    repeat pair_destr; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
  - destruct (lift_exp e2) as [e2' l2] eqn:eql2.
    pose proof IHe1 _ _ eq_refl as [? ?]; clear IHe1.
    pose proof IHe2 _ _ eq_refl as [? ?]; clear IHe2.
    pair_destr.
    split; auto.
    constructor.
    + apply lifted_bop; auto.
    + rewrite Forall_app; eauto.
  - destruct (split (shift_pairs shift_exp (map lift_exp es)))
      as [es' les] eqn:hexps; inv h.
    split; auto.
    assert (Forall
              (fun ees : Exp.t * list Exp.t =>
                 Forall lifted_rexp (snd ees)
                 /\ lifted_exp (fst ees)) (map lift_exp es)) as h.
    { clear dependent les. clear es'.
      repeat rewrite Forall_forall in *.
      intros [e' es'] h; cbn.
      rewrite in_map_iff in h.
      destruct h as (e & hlift & hin); cbn in *; subst.
      eauto. }
    clear H.
    rewrite split_map in hexps. inv hexps.
    pose proof shift_pairs_lifted
      _ _ shift_lifted_exp _ h as H.
    clear h.
    rewrite Forall_conj in H.
    destruct H as [h2 h1].
    rewrite <- Forall_map with (f:=snd),
        <- Forall_concat in h2.
    rewrite <- Forall_map with (f:=fst) in h1.
    auto.
  - destruct (lift_exp e2) as [e2' l2] eqn:eql2.
    pose proof IHe1 _ _ eq_refl as [? ?].
    pose proof IHe2 _ _ eq_refl as [? ?].
    pair_destr.
    split; auto; rewrite Forall_app; auto.
  - pose proof IHe _ _ eq_refl as [? ?]; auto.
Qed.

Local Hint Resolve lift_exp_lifted_exp : core.

Lemma lift_exp_list_lifted_exp : forall es es' le,
    lift_exp_list es = (es', le) ->
    Forall lifted_rexp le /\ Forall lifted_exp es'.
Proof.
  intros es es' le h.
  unfold lift_exp_list in h.
  destruct (split (shift_pairs shift_exp $ map lift_exp es))
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

Local Hint Resolve lift_exp_list_lifted_exp : core.
Local Hint Constructors pred_paramarg : core.

Lemma lift_arg_lifted_arg : forall arg arg' le,
    lift_arg arg = (arg', le) ->
    Forall lifted_rexp le /\ lifted_arg arg'.
Proof.
  unfold lifted_arg,pred_paramarg_same.
  intros arg arg' le h;
    destruct arg as [e | e | e]; unravel in *;
    lift_exp_destr_hyp; pair_destr;
    match goal with
    | h: lift_exp _ = (_, _)
      |- _ => apply lift_exp_lifted_exp in h as [? ?]; eauto
    end.
Qed.
  
Local Hint Resolve lift_arg_lifted_arg : core.

Lemma rename_arg_lifted_arg : forall ρ arg,
    lifted_arg arg -> lifted_arg (rename_arg ρ arg).
Proof.
  unfold lifted_arg,pred_paramarg_same.
  intros ρ e h; inv h; unravel in *; auto.
Qed.

Local Hint Resolve rename_arg_lifted_arg : core.

Lemma shift_lifted_arg : forall sh arg,
    lifted_arg arg -> lifted_arg (shift_arg sh arg).
Proof.
  unfold lifted_arg,pred_paramarg_same.
  intros sh e h; inv h; unravel in *; auto.
Qed.

Local Hint Resolve shift_lifted_arg : core.

Lemma lift_args_lifted_args : forall args args' le,
    lift_args args = (args', le) ->
    Forall lifted_rexp le /\ Forall lifted_arg args'.
Proof.
  intros args args' le h.
  unfold lift_args in h.
  destruct (split (shift_pairs shift_arg $ map lift_arg args))
    as [args'' les] eqn:hsplit.
  rewrite split_map in hsplit.
  unravel in *.
  do 2 pair_destr.
  rewrite Forall_concat.
  rewrite Forall_map with (f:=snd).
  rewrite Forall_map with (f:=fst).
  rewrite <- Forall_conj.
  apply shift_pairs_lifted; auto.
  rewrite Forall_forall.
  intros [arg' es] hin; cbn.
  rewrite in_map_iff in hin.
  destruct hin as (arg & hlift & hin).
  eauto.
Qed.

Local Hint Resolve lift_args_lifted_args : core.
Local Hint Constructors lifted_trns : core.

Lemma shift_lifted_trns : forall sh e,
    lifted_trns e ->
    lifted_trns (shift_trns sh e).
Proof.
  intros sh [] h; inv h; unravel; auto.
Qed.

Local Hint Resolve shift_lifted_trns : core.

Lemma lift_trns_lifted_trns : forall e e' le,
    lift_trns e = (e', le) ->
    Forall lifted_rexp le /\ lifted_trns e'.
Proof.
  intros e e' le h; destruct e;
    unravel in *; try lift_exp_destr_hyp;
    pair_destr; auto.
  apply lift_exp_lifted_exp in Heqp as [? ?]; auto.
Qed.

Local Hint Constructors lifted_call : core.
Local Hint Constructors predop : core.

Lemma lift_call_lifted_call : forall fk fk' le,
    lift_call fk = (fk', le) ->
    Forall lifted_rexp le /\ lifted_call fk'.
Proof.
  intros fk fk' le h; destruct fk; unravel in *.
  - destruct returns as [e |]; try lift_exp_destr_hyp; pair_destr; auto.
    apply lift_exp_lifted_exp in Heqp as [? ?]; auto.
  - destruct (lift_exp_list control_plane_args) as [les es'] eqn:eqles.
    pair_destr; apply lift_exp_list_lifted_exp in eqles as [? ?]; auto.
  - destruct returns as [e |]; try lift_exp_destr_hyp; pair_destr; auto.
    apply lift_exp_lifted_exp in Heqp as [? ?]; auto.
  - inv h. auto.
Qed.

Lemma rename_call_lifted_call : forall ρ fk,
    lifted_call fk ->
    lifted_call (rename_call ρ fk).
Proof.
  intros ρ fk h; inv h; unravel; auto.
  - constructor; destruct oe; unravel; inv H; auto.
  - constructor.
    rewrite sublist.Forall_map; unravel.
    rewrite Forall_forall in *; eauto.
  - constructor; destruct oe; unravel; inv H; auto.
Qed.

Local Hint Resolve rename_call_lifted_call : core.

Lemma shift_lifted_call : forall sh fk,
    lifted_call fk ->
    lifted_call (shift_call sh fk).
Proof.
  intros sh fk h; inv h; unravel; auto.
  - constructor; destruct oe; unravel; inv H; auto.
  - constructor.
    rewrite sublist.Forall_map; unravel.
    rewrite Forall_forall in *; eauto.
  - constructor; destruct oe; unravel; inv H; auto.
Qed.

Local Hint Resolve shift_lifted_call : core.

Local Hint Constructors lifted_stm : core.
Local Hint Constructors SumForall : core.
Local Hint Constructors predop : core.

Lemma shift_lifted_stm : forall s,
    lifted_stm s -> forall sh, lifted_stm (shift_stm sh s).
Proof.
  intros s h; induction h; intro sh; unravel; auto.
  - destruct te as [t | e]; inv H; unravel; auto.
  - constructor; auto.
    rewrite Forall_forall in *.
    intros arg' hin.
    rewrite in_map_iff in hin.
    destruct hin as (arg & hlift & hin); subst.
    auto.
  - destruct eo; inv H; cbn; auto.
  - inv H; cbn; auto.
Qed.

Local Hint Resolve shift_lifted_stm : core.

Lemma Unwind_lifted : forall le s,
    Forall lifted_rexp le ->
    lifted_stm s ->
    lifted_stm (Unwind le s).
Proof.
  intro le; induction le as [| e le ih];
    intros s hle hs; inv hle; unravel; auto.
Qed.

Local Hint Resolve Unwind_lifted : core.

Lemma lift_stm_lifted_stm : forall s, lifted_stm (lift_stm s).
Proof.
  intro s; induction s; unravel; auto.
  - destruct e as [e |]; auto.
    lift_exp_destr; apply lift_exp_lifted_exp in Heqp.
    intuition.
  - destruct (lift_trns trns) as [e' le] eqn:eqle.
    apply lift_trns_lifted_trns in eqle as [? ?].
    intuition.
  - do 2 lift_exp_destr.
    apply lift_exp_lifted_exp in Heqp as [? ?], Heqp0 as [? ?].
    apply Unwind_lifted; auto.
    rewrite Forall_app; auto.
  - destruct (lift_call call) as [fk' lfk] eqn:eqfk.
    destruct (lift_args args) as [args' largs] eqn:eqargs.
    apply lift_call_lifted_call in eqfk as [? ?].
    apply lift_args_lifted_args in eqargs as [? ?].
    apply Unwind_lifted; auto.
    + rewrite Forall_app; auto.
    + constructor; auto.
      rewrite Forall_forall in H2 |- *.
      intros pa' hin.
      rewrite in_map_iff in hin.
      destruct hin as (pa & hlift & hin); subst. eauto.
  - destruct lhs; try lift_exp_destr;
      try apply lift_exp_lifted_exp in Heqp as [? ?]; auto.
  - destruct init as [t | e]; auto.
    lift_exp_destr.
    apply lift_exp_lifted_exp in Heqp as [? ?]; auto 6.
  - lift_exp_destr. apply lift_exp_lifted_exp in Heqp as [? ?]; auto.
Qed.

Local Hint Resolve lift_stm_lifted_stm : core.

Ltac hyp_f_equal Heqp func:= 
  apply f_equal with (f := fst) in Heqp; apply f_equal with (f := func) in Heqp; simpl in Heqp;
  rewrite <- Heqp; auto.

Ltac hyp_f_equal_fst Heqp:= 
  apply f_equal with (f := fst) in Heqp; apply f_equal with (f := fst) in Heqp; simpl in Heqp;
  rewrite <- Heqp; auto.

Ltac hyp_f_equal_snd Heqp:= 
  apply f_equal with (f := fst) in Heqp; apply f_equal with (f := snd) in Heqp; simpl in Heqp;
  rewrite <- Heqp; auto.

Lemma lift_args_list_lifted : forall argss argss' le,
    lift_args_list argss = (argss', le) ->
    Forall lifted_rexp le /\ Forall (Forall lifted_arg) argss'.
Proof.
  intros argss argss' le h.
  unfold lift_args_list in h.
  destruct (split (shift_pairs (shift_list shift_arg) $ map lift_args argss))
    as [argss'' es'] eqn:hsplit.
  rewrite split_map in hsplit.
  unravel in *. do 2 pair_destr.
  rewrite Forall_concat.
  rewrite Forall_map with (f:=snd).
  rewrite Forall_map with (f:=fst).
  rewrite <- Forall_conj.
  apply shift_pairs_lifted.
  - intros sh args h.
    induction h; constructor; auto.
  - rewrite Forall_forall.
    intros [args' es] hin.
    rewrite in_map_iff in hin.
    destruct hin as (args & hlift & hin); cbn.
    eauto.
Qed.

Local Hint Constructors lifted_ctrl : core.

Lemma lift_ctrl_lifted_ctrl : forall cd cds n,
    lift_ctrl cd = (cds, n) ->
    Forall lifted_ctrl cds.
Proof.
  intros cd cds n h; destruct cd; unravel in *; auto.
  - destruct expr.
    + inv h. auto.
    + lift_exp_destr_hyp. inv h.
      apply lift_exp_lifted_exp in Heqp as [hl he0].
      rewrite Forall_app, Forall_map.
      split; eauto using Forall_impl.
  - inv h. auto.
  - destruct (split key) as [es mks] eqn:hkey.
    destruct (split actions) as [acts argss] eqn:hactions.
    destruct (lift_exp_list es) as [es' ees] eqn:hes.
    destruct (lift_args_list argss)
      as [argss' argsss] eqn:hargss.
    destruct (omap_effect [] (fun '(a, es) => map_fst (pair a) (lift_exp_list es)) default_action)
      as [def' defes] eqn:eqdef. inv h.
    pose proof lift_exp_list_lifted_exp _ _ _ hes as [hees hes'].
    pose proof lift_args_list_lifted _ _ _ hargss as [hargss' hargsss].
    repeat rewrite Forall_app. repeat rewrite Forall_map.
    repeat split; eauto using Forall_impl.
    + destruct default_action as [[a des] |]; cbn in *.
      * destruct (map_fst (pair a) (lift_exp_list des))
          as [[a' des'] ?] eqn:eqdesfst; inv eqdef.
        destruct (lift_exp_list des) as [? ?] eqn:eqdes; cbn in *; inv eqdesfst.
        pose proof lift_exp_list_lifted_exp _ _ _ eqdes as [hdes1 hdes2].
        rewrite Forall_forall in hdes1 |- *.
        intros e hein.
        constructor. eauto.
      * inv eqdef. auto.
    + constructor; auto. constructor.
      * rewrite map_fst_combine.
         -- clear dependent es.
            clear dependent acts.
            clear dependent argss'.
            rewrite Forall_forall in hes' |- *.
            intros e' hin.
            rewrite in_map_iff in hin.
            destruct hin as (e & ? & hin); subst.
            rewrite in_map_iff in hin.
            destruct hin as (? & ? & ?); subst.
            auto.
         -- pose proof f_equal fst hkey as hfst.
            pose proof f_equal snd hkey as hsnd.
            apply f_equal with (f:=length (A:=Exp.t)) in hfst.
            apply f_equal with (f:=length (A:=String.string)) in hsnd.
            rewrite split_length_l in hfst.
            rewrite split_length_r in hsnd. cbn in *.
            rewrite hfst in hsnd.
            rewrite map_length.
            unfold lift_exp_list in hes.
            destruct (split (shift_pairs shift_exp $ map lift_exp es))
              as [es'' les] eqn:hsplit.
            rewrite split_map in hsplit.
            do 2 pair_destr. unravel in *.
            do 2 rewrite map_length.
            rewrite shift_pairs_length, map_length.
            assumption.
      * rewrite map_snd_combine.
        --  clear dependent es.
            clear dependent es'.
            clear dependent mks.
            clear dependent acts.
            clear dependent argss.
            clear dependent argsss.
            clear dependent def'.
            clear actions table_name key hees.
            induction argss'; inv hargsss;
              constructor; auto.
            clear dependent argss'.
            induction a; inv H1; constructor; auto.
        --  pose proof f_equal fst hactions as hfst.
            pose proof f_equal snd hactions as hsnd.
            apply f_equal with (f:=length (A:=String.string)) in hfst.
            apply f_equal with (f:=length (A:=Exp.args)) in hsnd.
            rewrite split_length_l in hfst.
            rewrite split_length_r in hsnd. cbn in *.
            rewrite hfst in hsnd.
            rewrite map_length.
            unfold lift_args_list in hargss.
            destruct (split (shift_pairs (shift_list shift_arg) $ map lift_args argss))
              as [argss'' argsss'] eqn:hsplit.
            rewrite split_map in hsplit.
            unravel in *. do 2 pair_destr.
            rewrite map_length, shift_pairs_length, map_length.
            assumption.
      * destruct default_action as [[a des] |]; cbn in *.
        -- destruct (map_fst (pair a) (lift_exp_list des))
          as [[a' des'] ?] eqn:eqdesfst; inv eqdef.
           destruct (lift_exp_list des) as [? ?] eqn:eqdes; cbn in *; inv eqdesfst.
           pose proof lift_exp_list_lifted_exp _ _ _ eqdes as [hdes1 hdes2].
           constructor.
           rewrite Forall_forall in hdes2 |- *.
           intros e hein.
           rewrite in_map_iff in hein.
           destruct hein as (? & ? & ?); subst.
           eauto.
        -- inv eqdef. constructor.
Qed.

Local Hint Resolve lift_ctrl_lifted_ctrl : core.
Local Hint Constructors predop : core.

Lemma shift_lifted_ctrl : forall sh cd,
    lifted_ctrl cd ->
    lifted_ctrl (shift_ctrl sh cd).
Proof.
  intros sh ch h; inv h; unravel; auto.
  - inv H; unravel; auto.
  - constructor.
    + rewrite map_fst_map.
      rewrite Forall_forall in H |- *.
      intros e' hin.
      rewrite in_map_iff in hin.
      destruct hin as (e & ? & hin); subst; auto.
    + rewrite map_snd_map.
      rewrite Forall_forall in H0 |- *.
      intros args' hin.
      rewrite in_map_iff in hin.
      destruct hin as (args & ? & hin); subst.
      pose proof H0 _ hin as h.
      clear dependent actions.
      clear dependent key. clear table_name.
      rewrite Forall_forall in *.
      intros arg' hin.
      rewrite in_map_iff in hin.
      destruct hin as (arg & ? & hin); subst; auto.
    + destruct def as [[da des] |];
        inv H1; constructor.
      rewrite Forall_forall in H3 |- *.
      intros e hein.
      rewrite in_map_iff in hein.
      destruct hein as (? & ? & ?); subst; auto.
Qed.

Local Hint Resolve shift_lifted_ctrl : core.

Lemma shift_ctrls_lifted_ctrl : forall cds,
    Forall lifted_ctrl cds -> forall sh,
      Forall lifted_ctrl (shift_ctrls sh cds).
Proof.
  intro cds; induction cds as [| [] cds ih];
    intros h sh; inv h; constructor; auto.
Qed.

Local Hint Resolve shift_ctrls_lifted_ctrl : core.

Lemma lift_ctrls_lifted_ctrls : forall cds cds' n,
    lift_ctrls cds = (cds', n) ->
    Forall lifted_ctrl cds'.
Proof.
  intro cds; induction cds as [| cd cds ih];
    intros cds' n h; unravel in *.
  - inv h. auto.
  - destruct (lift_ctrl cd) as [cdd cdn] eqn:hcd.
    destruct (lift_ctrls cds) as [cdsd cdsn] eqn:hcds.
    inv h. rewrite Forall_app. split; eauto.
Qed.

Local Hint Resolve lift_ctrls_lifted_ctrls : core.
Local Hint Constructors lifted_top : core.

Lemma lift_top_lifted_top : forall td,
    lifted_top (lift_top td).
Proof.
  intro td; destruct td; unravel in *; auto.
  - destruct (lift_ctrls body) as [? ?] eqn:?.
    constructor; eauto.
  - constructor; auto.
    rewrite sublist.Forall_map; unravel.
    rewrite Forall_forall in *; eauto.
Qed.
