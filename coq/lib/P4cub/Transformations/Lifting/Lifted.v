Require Export Poulet4.P4cub.Syntax.Syntax
        Poulet4.P4cub.Syntax.Shift
        Poulet4.P4cub.Transformations.Lifting.Statementize.
Require Import Poulet4.Utils.ForallMap Poulet4.Utils.VecUtil.
From Equations Require Import Equations.

Ltac pair_destr :=
  match goal with
  | h: (_,_) = (_,_) |- _ => inv h
  end.

Ltac conj_destr :=
  match goal with
    h: _ /\ _ |- _ => destruct h as [? ?]
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

Ltac shift_couple_destr :=
  lazymatch goal with
  | H: context [shift_couple ?fa ?fb ?a ?b ?la ?lb]
    |- _ => destruct (shift_couple fa fb a b la lb) as [[? ?] ?] eqn:?; simpl in *
  | |- context [shift_couple ?fa ?fb ?a ?b ?la ?lb]
    => destruct (shift_couple fa fb a b la lb) as [[? ?] ?] eqn:?; simpl in *
  end.

Ltac pair_fst_snd_eqns :=
  lazymatch goal with
  | H: ?trm = (?a, ?b) |- _
    => pose proof f_equal fst H
      as ?; pose proof f_equal snd H
        as ?; clear H; unravel in *
  end.

Ltac triple_fst_snd_eqns :=
  lazymatch goal with
  | H: ?trm = (?a, ?b, ?c) |- _
    => pose proof f_equal (fst ∘ fst) H
      as ?; pose proof f_equal (snd ∘ fst) H
        as ?; pose proof f_equal snd H
          as ?; clear H; unravel in *
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

Lemma shift_lifted_exp : forall c a e,
    lifted_exp e -> lifted_exp (shift_exp c a e).
Proof.
  intros c a e h; induction h; unravel; auto.
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

Lemma shift_lifted_rexp : forall c a e,
    lifted_rexp e -> lifted_rexp (shift_exp c a e).
Proof.
  intros c a e h; inv h; unravel; auto;
    constructor; rewrite sublist.Forall_map;
    rewrite Forall_forall in *; unravel; auto.
Qed.

Local Hint Resolve shift_lifted_rexp : core.

Lemma shift_list_lifted_rexp : forall c a es,
    Forall lifted_rexp es ->
    Forall lifted_rexp (shift_list shift_exp c a es).
Proof.
  intros c a es h; induction h; unravel; auto.
Qed.

Local Hint Resolve shift_list_lifted_rexp : core.
Local Hint Rewrite Forall_concat : core.

Section LiftProd.
  Import ProdN.ProdNNotations.
  Import Vec.VectorNotations.
  Local Open Scope prodn_scope.
  
  Polymorphic Universes a.

  Local Hint Constructors Vec.Forall : core.
  Local Hint Constructors ProdN.each : core.
  
  Polymorphic Lemma prodn_shift_pairs_lifted :
    forall {n : nat} {AS : Vec.t Type@{a} n}
      (lifteds : ProdN.t (Vec.map (fun A => A -> Prop) AS))
      (shifts : ProdN.t (Vec.map shifter AS)),
      (forall pas, ProdN.each lifteds pas ->
              forall cutoff amt, ProdN.each lifteds (ProdN.map_uni2 cutoff amt shifts pas)) ->
      forall (p : ProdN.t AS) (v : Vec.t (list Exp.t) n),
        ProdN.each lifteds p ->
        Vec.Forall (Forall lifted_rexp) v ->
        ProdN.each lifteds (fst (prodn_shift_pairs shifts p v))
        /\ Vec.Forall (Forall lifted_rexp) (snd (prodn_shift_pairs shifts p v)).
  Proof using.
    intros n AS lifteds shifts hyp p v p_lifted v_lifted.
    funelim (prodn_shift_pairs shifts p v); auto.
    cbn in lifteds.
    depelim lifteds. rename a0 into lifted.
    depelim p_lifted. depelim v_lifted.
    rename H0 into ha. rename H1 into hes.
    assert
      (forall pas,
          ProdN.each lifteds pas ->
          forall cutoff amt,
            ProdN.each lifteds (ProdN.map_uni2 cutoff amt fs pas))
      as hyp'.
    { intros pas hpas c amt.
      pose proof hyp
        (a :: pas)
        (ProdN.each_cons _ _ _ _ ha hpas) c amt as hyp'.
      rewrite ProdN.map_uni2_equation_2 with
        (A0:=A) (f:=f) (fs:=fs) in hyp'.
      depelim hyp'. assumption. }
    rewrite prodn_shift_pairs_equation_2.
    unravel; cbn.
    pose proof H lifteds hyp' p_lifted v_lifted
      as [ihp ihv]; clear H hyp'.
    destruct (prodn_shift_pairs fs p ess) as [p' v'] eqn:hpsp.
    cbn in *.
    split; auto.
    pose proof hyp (a :: p')
      (ProdN.each_cons _ _ _ _ ha ihp) as h.
    constructor.
    - specialize h with
        (length es)
        (vec_sum (Vec.map (length (A:=Exp.t)) ess)).
      rewrite ProdN.map_uni2_equation_2
        with (A0:=A) (f:=f) (fs:=fs) in h.
      depelim h. assumption.
    - specialize h with 0 (length es).
      rewrite ProdN.map_uni2_equation_2
        with (A0:=A) (f:=f) (fs:=fs) in h.
      depelim h. assumption.
  Qed.

  Polymorphic Context {A : Type@{a}}.
  Variable shifta : shifter A.
  Variable lifteda : A -> Prop.
  Hypothesis shifta_lifteda : forall c amt a,
      lifteda a -> lifteda (shifta c amt a).
  Local Hint Resolve shifta_lifteda : core.

  Polymorphic Lemma shift_list_lifted_list :
    forall c amt (l : list A),
      Forall lifteda l -> Forall lifteda (shift_list shifta c amt l).
  Proof using A lifteda shifta shifta_lifteda.
    intros c a l h.
    induction h; unravel; auto.
  Qed.
  
  Polymorphic Remark prodn_shifta_lifteda :
    forall {n : nat} (p : ProdN.t (vec_rep n A)),
      ProdN.each (ProdN.rep_param lifteda n) p ->
      forall cutoff amt,
        ProdN.each
          (ProdN.rep_param lifteda n)
          (ProdN.map_uni2 cutoff amt (ProdN.rep_param shifta n) p).
  Proof using A lifteda shifta shifta_lifteda.
    intro n.
    induction n as [| n ih];
      intros p h c amt; unravel in *; depelim h; auto.
    rewrite ProdN.map_uni2_equation_2 with (f:=shifta).
    auto.
  Qed.

  Local Hint Resolve ProdN.Forall_each : core.
  Local Hint Resolve ProdN.each_Forall : core.
  
  Polymorphic Lemma vec_shift_pairs_lifted :
    forall {n : nat} (v : Vec.t A n) (ess : Vec.t (list Exp.t) n),
      Vec.Forall lifteda v ->
      Vec.Forall (Forall lifted_rexp) ess ->
      Vec.Forall lifteda (fst (vec_shift_pairs shifta v ess))
      /\ Vec.Forall
          (Forall lifted_rexp)
          (snd (vec_shift_pairs shifta v ess)).
  Proof using A lifteda shifta shifta_lifteda.
    intros n v ess hb hess.
    unfold vec_shift_pairs. unravel.
    pose proof prodn_shift_pairs_lifted (AS:=vec_rep n A)
      (ProdN.rep_param (B:=fun A => A -> Prop) lifteda n)
      (ProdN.rep_param (B:=shifter) shifta n)
      prodn_shifta_lifteda as h.
    specialize h with (ProdN.of_vec v) ess.
    assert (ProdN.each (ProdN.rep_param lifteda n) (ProdN.of_vec v))
      as hv by eauto.
    destruct
      (prodn_shift_pairs
         (ProdN.rep_param shifta n)
         (ProdN.of_vec v) ess)
      as [p' ess'] eqn:hpsp.
    cbn in *. intuition.
  Qed.

  Local Hint Resolve list_Forall_vec : core.
  Local Hint Resolve vec_Forall_list : core.

  Polymorphic Lemma shift_pairs_lifted : forall l,
      Forall
        (fun aes => lifteda (fst aes)
                 /\ Forall lifted_rexp (snd aes)) l ->
      Forall
        lifteda
        (fst (shift_pairs shifta l))
      /\ Forall
        (Forall lifted_rexp)
        (snd (shift_pairs shifta l)).
  Proof using A lifteda shifta shifta_lifteda.
    intros l hl.
    unfold shift_pairs; unravel.
    destruct (vec_unzip (Vec.of_list l)) as [v ess] eqn:hlv.
    rewrite Forall_conj in hl.
    rewrite <- Forall_map with (f:=fst) in hl.
    rewrite <- Forall_map with (f:=snd) in hl.
    destruct hl as [has hrs].
    apply list_Forall_vec, Forall_of_list_map in has,hrs.
    rewrite vec_unzip_correct in hlv. inv hlv.
    pose proof vec_shift_pairs_lifted _ _ has hrs as [hva hes].
    destruct
      (vec_shift_pairs shifta (Vec.map fst (Vec.of_list l)) (Vec.map snd (Vec.of_list l)))
      as [va ves] eqn:hvsp. unravel in *.
    pair_fst_snd_eqns; subst. auto.
  Qed.

  Polymorphic Variable lifta : A -> A * list Exp.t.
  Polymorphic Hypothesis lifta_lifteda : forall a,
      lifteda (fst (lifta a)) /\ Forall lifted_rexp (snd (lifta a)).

  Polymorphic Remark  map_lifta_lifted : forall (l : list A),
      Forall
        (fun aes => lifteda (fst aes)
                 /\ Forall lifted_rexp (snd aes)) (map lifta l).
  Proof using A lifta lifta_lifteda lifteda.
    intro l. rewrite Forall_map, Forall_forall. auto.
  Qed.
  
  Polymorphic Lemma lift_A_list_lifted : forall (l : list A),
      Forall lifteda (fst (lift_A_list shifta lifta l))
      /\ Forall lifted_rexp (snd (lift_A_list shifta lifta l)).
  Proof using A lifta lifta_lifteda lifteda shifta shifta_lifteda.
    intro l.
    unfold lift_A_list. unravel.
    pose proof map_lifta_lifted l as h.
    apply shift_pairs_lifted in h.
    rewrite fst_prod_map_snd, snd_prod_map_snd.
    autorewrite with core. assumption.
  Qed.

  Polymorphic Context {B : Type@{a}}.
  Variable shiftb : shifter B.
  Variable liftedb : B -> Prop.
  Hypothesis shiftb_liftedb : forall c amt b,
      liftedb b -> liftedb (shiftb c amt b).
  Local Hint Resolve shiftb_liftedb : core.

  Polymorphic Lemma shift_couple_lifted
    : forall a b esa esb,
      lifteda a -> liftedb b ->
      Forall lifted_rexp esa -> Forall lifted_rexp esb ->
      lifteda (fst (fst (shift_couple shifta shiftb a b esa esb)))
      /\ liftedb (snd (fst (shift_couple shifta shiftb a b esa esb)))
      /\ Forall lifted_rexp (snd (shift_couple shifta shiftb a b esa esb)).
  Proof using A B lifteda liftedb shifta shifta_lifteda shiftb shiftb_liftedb.
    intros a b esa esb ha hb hesa hesb.
    unfold shift_couple.
    do 2 rewrite prodn_shift_pairs_equation_2.
    rewrite prodn_shift_pairs_equation_1. cbn.
    rewrite ProdN.map_uni2_equation_2 with (f:=shifta).
    rewrite ProdN.map_uni2_equation_1. cbn.
    rewrite ProdN.nth_equation_2, ProdN.nth_equation_1, ProdN.hd_equation_1.
    cbn. auto.
  Qed.

  Polymorphic Context {C : Type@{a}}.
  Variable shiftc : shifter C.
  Variable liftedc : C -> Prop.
  Hypothesis shiftc_liftedc : forall ct amt c,
      liftedc c -> liftedc (shiftc ct amt c).
  Local Hint Resolve shiftc_liftedc : core.

  Polymorphic Lemma shift_triple_lifted :
    forall a b c esa esb esc,
      lifteda a -> liftedb b -> liftedc c ->
      Forall lifted_rexp esa -> Forall lifted_rexp esb -> Forall lifted_rexp esc ->
      lifteda (fst (fst (fst (fst (shift_triple shifta shiftb shiftc a b c esa esb esc)))))
      /\ liftedb (snd (fst (fst (fst (shift_triple shifta shiftb shiftc a b c esa esb esc)))))
      /\ liftedc (snd (fst (fst ((shift_triple shifta shiftb shiftc a b c esa esb esc)))))
      /\ Forall lifted_rexp (snd (fst (shift_triple shifta shiftb shiftc a b c esa esb esc)))
      /\ Forall lifted_rexp (snd (shift_triple shifta shiftb shiftc a b c esa esb esc)).
  Proof using A B C lifteda liftedb liftedc shifta shifta_lifteda shiftb shiftb_liftedb shiftc shiftc_liftedc.
    intros a b c esa esb esc ha hb hc hesa hesb hesc.
    unfold shift_triple.
    do 3 rewrite prodn_shift_pairs_equation_2.
    rewrite prodn_shift_pairs_equation_1. cbn.
    rewrite ProdN.map_uni2_equation_2 with (f:=shiftb).
    do 2 rewrite ProdN.map_uni2_equation_2 with (f:=shifta).
    rewrite ProdN.map_uni2_equation_1. cbn. unravel.
    do 3 rewrite ProdN.nth_equation_2.
    do 2 rewrite ProdN.nth_equation_1.
    rewrite ProdN.hd_equation_1.
    auto 6.
  Qed.
End LiftProd.

Local Hint Resolve lift_A_list_lifted : core.
Local Hint Resolve shift_pairs_lifted : core.
Local Hint Resolve shift_couple_lifted : core.
Local Hint Resolve shift_triple_lifted : core.
Local Hint Constructors Forall : core.
Local Hint Rewrite Forall_app : core.

Ltac shift_couple_lifted_solve thm1 thm2 :=
  lazymatch goal with
    Ha : ?la (fst (?f ?a)), Hb : ?lb (fst (?f ?b)),
    Hla : Forall ?lr (snd (?f ?a)), Hlb : Forall ?lr (snd (?f ?b))
    |- _ => pose proof shift_couple_lifted _ _ thm1 _ _ thm2
            _ _ _ _ Ha Hb Hla Hlb as [? [? ?]]
  end.

Local Hint Extern 5 => shift_couple_lifted_solve shift_lifted_exp shift_lifted_exp : core.

Lemma lift_exp_lifted_exp : forall e,
    lifted_exp (fst (lift_exp e))
    /\ Forall lifted_rexp (snd (lift_exp e)).
Proof.
  intro e; induction e using custom_exp_ind;
    unravel in *;
    repeat lift_exp_destr;
    repeat pair_fst_snd_eqns; subst;
    repeat conj_destr; auto.
  - shift_couple_destr.
    triple_fst_snd_eqns; subst.
    constructor; auto.
    constructor; auto.
    autorewrite with core. auto.
  - rewrite <- Forall_map with
      (f:=lift_exp)
      (P:=fun ees => lifted_exp (fst ees) /\ Forall lifted_rexp (snd ees))
      in H.
    destruct
      (shift_pairs shift_exp (map lift_exp es))
      as [es' ess] eqn:hsp.
    pair_fst_snd_eqns; subst.
    eapply shift_pairs_lifted in H as [hfst hsnd]; eauto.
    constructor; auto.
    constructor; auto.
    autorewrite with core. assumption.
  - shift_couple_destr.
    triple_fst_snd_eqns; subst.
    constructor; auto.
    autorewrite with core. auto.
Qed.

Local Hint Resolve lift_exp_lifted_exp : core.

Lemma lift_exp_list_lifted_exp : forall es,
    Forall lifted_exp (fst (lift_exp_list es))
    /\ Forall lifted_rexp (snd (lift_exp_list es)).
Proof.
  intro es.
  unfold lift_exp_list. auto.
Qed.

Local Hint Resolve lift_exp_list_lifted_exp : core.

Lemma map_shift_exp_lifted : forall c amt es,
    Forall lifted_exp es -> Forall lifted_exp (map (shift_exp c amt) es).
Proof.
  intros c a es h.
  rewrite Forall_map.
  rewrite Forall_forall in *. auto.
Qed.

Local Hint Constructors predop : core.

Lemma option_map_snd_shift_exp_lifted :
  forall {A:Set} c a (oe : option (A * list Exp.t)),
    predop (Forall lifted_exp ∘ snd) oe ->
    predop
      (Forall lifted_exp ∘ snd)
      (option_map (prod_map_snd (map (shift_exp c a))) oe).
Proof.
  intros A c amt [[a es] |] h; inv h; unravel in *;
    constructor; cbn; auto using map_shift_exp_lifted.
Qed.

Local Hint Constructors pred_paramarg : core.

Lemma lift_arg_lifted_arg : forall arg,
    lifted_arg (fst (lift_arg arg))
    /\ Forall lifted_rexp (snd (lift_arg arg)).
Proof.
  unfold lifted_arg,pred_paramarg_same.
  intros arg;
    destruct arg as [e | e | e]; unravel in *;
    lift_exp_destr; pair_fst_snd_eqns; subst;
    pose proof lift_exp_lifted_exp e as [? ?]; auto.
Qed.
  
Local Hint Resolve lift_arg_lifted_arg : core.

Lemma rename_arg_lifted_arg : forall ρ arg,
    lifted_arg arg -> lifted_arg (rename_arg ρ arg).
Proof.
  unfold lifted_arg,pred_paramarg_same.
  intros ρ e h; inv h; unravel in *; auto.
Qed.

Local Hint Resolve rename_arg_lifted_arg : core.

Lemma shift_lifted_arg : forall c a arg,
    lifted_arg arg -> lifted_arg (shift_arg c a arg).
Proof.
  unfold lifted_arg,pred_paramarg_same.
  intros c a e h; inv h; unravel in *; auto.
Qed.

Local Hint Resolve shift_lifted_arg : core.

Lemma map_shift_arg_lifted : forall c amt args,
    Forall lifted_arg args -> Forall lifted_arg (map (shift_arg c amt) args).
Proof.
  intros c a args h.
  rewrite Forall_map.
  rewrite Forall_forall in *. auto.
Qed.

Local Hint Resolve map_shift_arg_lifted : core.

Lemma map_shift_args_lifted : forall c a argss,
    Forall (Forall lifted_arg) argss ->
    Forall (Forall lifted_arg) (map (map (shift_arg c a)) argss).
Proof.
  intros c a argss h.
  rewrite Forall_map.
  rewrite Forall_forall in *. auto.
Qed.

Lemma lift_args_lifted_args : forall args,
    Forall lifted_arg (fst (lift_args args))
    /\ Forall lifted_rexp (snd (lift_args args)).
Proof.
  intros args.
  unfold lift_args.
  apply lift_A_list_lifted; auto.
Qed.

Local Hint Resolve lift_args_lifted_args : core.
Local Hint Constructors lifted_trns : core.

Lemma shift_lifted_trns : forall c a e,
    lifted_trns e ->
    lifted_trns (shift_trns c a e).
Proof.
  intros c a [] h; inv h; unravel; auto.
Qed.

Local Hint Resolve shift_lifted_trns : core.

Lemma lift_trns_lifted_trns : forall t,
    lifted_trns (fst (lift_trns t))
    /\ Forall lifted_rexp (snd (lift_trns t)).
Proof.
  intros [| e]; unravel in *; auto.
  lift_exp_destr. pair_fst_snd_eqns; subst.
  pose proof lift_exp_lifted_exp e as [? ?]; auto.
Qed.

Local Hint Constructors lifted_call : core.
Local Hint Constructors predop : core.

Lemma lift_call_lifted_call : forall c,
    lifted_call (fst (lift_call c))
    /\ Forall lifted_rexp (snd (lift_call c)).
Proof.
  intros [f ts [e |] | a es | ex m ts [e |] | i exs]; unravel in *;
    try lift_exp_destr; try pair_fst_snd_eqns; subst;
    try pose proof lift_exp_lifted_exp e as [? ?]; auto.
  destruct (lift_exp_list es) as [? ?] eqn:h.
  pair_fst_snd_eqns; subst.
  pose proof lift_exp_list_lifted_exp es as [? ?]; auto.
Qed.

Lemma rename_call_lifted_call : forall ρ c,
    lifted_call c ->
    lifted_call (rename_call ρ c).
Proof.
  intros ρ c h; inv h; unravel; auto.
  - constructor; destruct oe; unravel; inv H; auto.
  - constructor.
    rewrite sublist.Forall_map; unravel.
    rewrite Forall_forall in *; eauto.
  - constructor; destruct oe; unravel; inv H; auto.
Qed.

Local Hint Resolve rename_call_lifted_call : core.

Lemma shift_lifted_call : forall ct amt c,
    lifted_call c ->
    lifted_call (shift_call ct amt c).
Proof.
  intros ct amt c h; inv h; unravel; auto.
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
    lifted_stm s -> forall c a, lifted_stm (shift_stm c a s).
Proof.
  intros s h; induction h; intros c a; unravel; auto.
  - destruct te as [t | e]; inv H; unravel; auto.
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
    lift_exp_destr.
    pair_fst_snd_eqns; subst.
    pose proof lift_exp_lifted_exp e as [? ?]; auto.
  - destruct (lift_trns trns) as [e' le] eqn:eqle;
      pair_fst_snd_eqns; subst.
    pose proof lift_trns_lifted_trns trns as [? ?]; auto.
  - do 2 lift_exp_destr.
    do 2 pair_fst_snd_eqns; subst.
    shift_couple_destr.
    triple_fst_snd_eqns; subst.
    pose proof lift_exp_lifted_exp lhs as [? ?].
    pose proof lift_exp_lifted_exp rhs as [? ?].
    shift_couple_lifted_solve shift_lifted_exp shift_lifted_exp.
    apply Unwind_lifted; auto.
    autorewrite with core. auto.
  - destruct (lift_call call) as [call' lcall] eqn:eqcall.
    destruct (lift_args args) as [args' largs] eqn:eqargs.
    do 2 pair_fst_snd_eqns; subst.
    pose proof lift_call_lifted_call call as [hc1 hc2].
    pose proof lift_args_lifted_args args as [ha1 ha2].
    shift_couple_destr.
    triple_fst_snd_eqns; subst.
    pose proof shift_couple_lifted
      _ _ map_shift_arg_lifted _ _ shift_lifted_call
      _ _ _ _ ha1 hc1 ha2 hc2 as [? [? ?]].
    apply Unwind_lifted; auto.
    autorewrite with core. auto.
  - destruct lhs; auto; try lift_exp_destr; try pair_fst_snd_eqns; subst.
    pose proof lift_exp_lifted_exp t as [? ?]; auto.
  - destruct init as [t | e]; auto.
    lift_exp_destr; pair_fst_snd_eqns; subst.
    pose proof lift_exp_lifted_exp e as [? ?]; auto.
  - lift_exp_destr. pair_fst_snd_eqns; subst.
    pose proof lift_exp_lifted_exp guard as [? ?].
    auto.
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

Lemma lift_args_list_lifted : forall argss,
    Forall (Forall lifted_arg) (fst (lift_args_list argss))
    /\ Forall lifted_rexp (snd (lift_args_list argss)).
Proof.
  intro argss.
  unfold lift_args_list.
  apply lift_A_list_lifted; auto.
  apply shift_list_lifted_list; auto.
Qed.

Local Hint Constructors lifted_ctrl : core.

Lemma lift_ctrl_lifted_ctrl : forall cd,
    Forall lifted_ctrl (fst (lift_ctrl cd)).
Proof.
  intros cd; destruct cd; unravel in *; auto.
  - destruct expr as [t | e]; cbn; auto.
    lift_exp_destr.
    pair_fst_snd_eqns; subst.
    pose proof lift_exp_lifted_exp e as [? ?].
    rewrite Forall_app, Forall_map.
    split; eauto using Forall_impl.
  - destruct (split key) as [es mks] eqn:hkey.
    destruct (split actions) as [acts argss] eqn:hactions.
    destruct (lift_exp_list es) as [es' ees] eqn:hes.
    destruct (lift_args_list argss)
      as [argss' argsss] eqn:hargss.
    destruct (omap_effect
                [] (fun '(a, es) =>
                      prod_map_fst (pair a) (lift_exp_list es)) default_action)
      as [def' defes] eqn:eqdef.
    do 5 pair_fst_snd_eqns; subst.
    assert
      (predop
         (Forall lifted_exp ∘ snd)
         (fst (omap_effect
               []
               (fun '(a, es) =>
                  prod_map_fst (pair a) (lift_exp_list es)) default_action))
       /\ Forall
           lifted_rexp
           (snd
              (omap_effect
                 []
                 (fun '(a, es) =>
                    prod_map_fst (pair a) (lift_exp_list es)) default_action)))
      as [ho1 ho2].
    { destruct default_action as [[a es] |]; unravel; auto.
      destruct (lift_exp_list es) as [es' ess] eqn:hleles.
      pair_fst_snd_eqns; subst.
      pose proof lift_exp_list_lifted_exp es as [? ?]. auto. }
    pose proof lift_args_list_lifted (snd (split actions)) as [ha1 ha2].
    pose proof lift_exp_list_lifted_exp (fst (split key)) as [he1 he2].
    pose proof shift_triple_lifted
      _ _ (option_map_snd_shift_exp_lifted (A:=String.string))
      _ _ map_shift_exp_lifted
      _ _ map_shift_args_lifted
      _ _ _ _ _ _ ho1 he1 ha1 ho2 he2 ha2
      as h.
    rewrite <- eta_expansion with
      (f := (fun c a : nat => option_map (prod_map_snd (map (shift_exp c a))))) in h.
    assert ((fun c amt es => map (shift_exp c amt) es)
            = (fun c a : nat => map (shift_exp c a))) as hea by reflexivity.
    rewrite hea in h; clear hea.
    assert ((fun c a argss => map (map (shift_arg c a)) argss)
            = (fun c a : nat => map (map (shift_arg c a)))) as hea by reflexivity.
    rewrite hea in h; clear hea.
    destruct h as (ho' & hes' & hargss' & hess' & hargsss').
    destruct
      (shift_triple
         (fun c a => option_map (prod_map_snd (map (shift_exp c a))))
         (fun c a => map (shift_exp c a))
         (fun c a => map (map (shift_arg c a)))
         (fst (omap_effect [] (fun '(a, es) => prod_map_fst (pair a) (lift_exp_list es)) default_action))
         (fst (lift_exp_list (fst (split key))))
         (fst (lift_args_list (snd (split actions))))
         (snd (omap_effect [] (fun '(a, es) => prod_map_fst (pair a) (lift_exp_list es)) default_action))
         (snd (lift_exp_list (fst (split key)))) (snd (lift_args_list (snd (split actions)))))
      as [[[[? ?] ?] ?] ?] eqn:hst.
    pose proof f_equal (fst ∘ fst ∘ fst ∘ fst) hst as ?; unravel in *.
    pose proof f_equal (snd ∘ fst ∘ fst ∘ fst) hst as ?; unravel in *.
    pose proof f_equal (snd ∘ fst ∘ fst) hst as ?; unravel in *.
    pose proof f_equal (snd ∘ fst) hst as ?; unravel in *.
    pose proof f_equal snd hst as ?; unravel in *.
    clear hst; subst.
    autorewrite with core. repeat rewrite Forall_map.
    repeat split; eauto using Forall_impl.
    constructor; auto.
    (*pose proof shift_triple_lengths
      (fun c a => option_map (prod_map_snd (map (shift_exp c a))))
      (fun c a => map (shift_exp c a))
      (fun c a => map (map (shift_arg c a)))
      (fst (omap_effect [] (fun '(a, es) => prod_map_fst (pair a) (lift_exp_list es)) default_action))
      (fst (lift_exp_list (fst (split key))))
      (fst (lift_args_list (snd (split actions))))
      (snd (omap_effect [] (fun '(a, es) => prod_map_fst (pair a) (lift_exp_list es)) default_action))
      (snd (lift_exp_list (fst (split key)))) (snd (lift_args_list (snd (split actions)))) as [hlen1 hlen2].*)
    constructor.
    + rewrite map_fst_combine; auto.
      clear hargss' hargsss' ho' hes' hess' ho1 ho2 ha1 ha2 he1 he2.
      unfold shift_triple.
      do 3 rewrite prodn_shift_pairs_equation_2.
      rewrite prodn_shift_pairs_equation_1. unravel.
      rewrite ProdN.nth_equation_2.
      rewrite ProdN.map_uni2_equation_2 with (f:= (fun c a : nat => map (shift_exp c a))).
      rewrite ProdN.nth_equation_1.
      do 2 rewrite map_length.
      unfold lift_exp_list.
      rewrite lift_A_list_length.
      rewrite split_length_l, split_length_r.
      reflexivity.
    + rewrite map_snd_combine; auto.
      clear hargss' hargsss' ho' hes' hess' ho1 ho2 ha1 ha2 he1 he2.
      unfold shift_triple.
      do 3 rewrite prodn_shift_pairs_equation_2.
      rewrite prodn_shift_pairs_equation_1. unravel.
      rewrite ProdN.hd_equation_1.
      rewrite map_length.
      unfold lift_args_list.
      rewrite lift_A_list_length.
      rewrite split_length_l, split_length_r.
      reflexivity.
    + rewrite predop_pat_snd. assumption.
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
