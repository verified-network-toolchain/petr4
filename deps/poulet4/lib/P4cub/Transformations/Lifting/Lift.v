From Coq Require Import Strings.String
  NArith.BinNat Arith.PeanoNat.
From Poulet4 Require Import
     P4cub.Syntax.AST P4cub.Syntax.Auxiliary
     P4cub.Syntax.CubNotations P4cub.Syntax.Shift
     P4cub.Syntax.IndPrincip
     P4cub.Semantics.Dynamic.BigStep.Semantics
     P4cub.Semantics.Dynamic.BigStep.IndPrincip
     P4cub.Semantics.Dynamic.BigStep.Properties.
Import ListNotations AllCubNotations Nat.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Open Scope nat_scope.
Open Scope string_scope.
Open Scope list_scope.

Ltac len_app :=
  match goal with
| hlen: length ?l1 = length ?l2, happ: ?l1 ++ _ = ?l2 ++ _
  |- _ => pose proof sublist.app_eq_len_eq happ hlen as [? ?]; subst
  end.

Local Hint Extern 1 => len_app : core.

Lemma shift_e_0 : forall e c, shift_e (Shifter c 0) e = e.
Proof.
  intros e c.
  induction e using custom_e_ind; unravel;
    f_equal; auto.
  - unfold shift_var.
    destruct_if; reflexivity.
  - apply map_ext_Forall in H.
    rewrite H, map_id; reflexivity.
Qed.

Local Hint Rewrite shift_e_0 : core.

Lemma shift_e_0_map : forall es c,
    map (shift_e (Shifter c 0)) es = es.
Proof.
  intros es c;
    induction es as [| e es ih]; unravel;
    autorewrite with core; f_equal; auto.
Qed.

Local Hint Rewrite shift_e_0_map : core.

Lemma shift_arg_0 : forall arg c, shift_arg (Shifter c 0) arg = arg.
Proof.
  intros [] c; unravel;
    autorewrite with core; reflexivity.
Qed.

Local Hint Rewrite shift_arg_0 : core.

Lemma shift_arg_0_map : forall args c,
    map (shift_arg (Shifter c 0)) args = args.
Proof.
  intros args c;
    induction args as [| arg args ih];
    unravel; autorewrite with core;
    f_equal; auto.
Qed.

Local Hint Rewrite shift_arg_0_map : core.

Lemma shift_trans_0 : forall p c, shift_transition (Shifter c 0) p = p.
Proof.
  intros [] c; unravel;
    autorewrite with core; reflexivity.
Qed.

Local Hint Rewrite shift_trans_0 : core.

Lemma shift_s_0 : forall s c, shift_s (Shifter c 0) s = s.
Proof.
  intro s;
    induction s;
    intro c; unravel;
    autorewrite with core;
    unfold sext, smother, RecordSet.set; unravel;
    f_equal; auto.
  - destruct e; unravel;
      autorewrite with core; reflexivity.
  - destruct expr; unravel;
      autorewrite with core; reflexivity.
Qed.

Local Hint Constructors expr_big_step : core.

Lemma shift_e_eval : forall us vs ϵ e v,
    ⟨ us ++ ϵ, e ⟩ ⇓ v ->
    ⟨ us ++ vs ++ ϵ,
      shift_e
        (Shifter (length us) (length vs)) e ⟩ ⇓ v.
Proof.
  intros us vs ϵ e v h.
  remember (us ++ ϵ) as usϵ eqn:husϵ.
  generalize dependent ϵ.
  generalize dependent us.
  induction h using custom_expr_big_step_ind;
    intros us eps huseps; subst;
    unravel; eauto.
  - unfold shift_var. unravel.
    constructor. destruct_if.
    + rewrite nth_error_app2 in * by lia.
      rewrite <- Nat.add_sub_assoc by lia.
      rewrite nth_error_app3.
      assumption.
    + rewrite nth_error_app1 in * by lia.
      assumption.
  - rewrite Forall2_forall_nth_error in H0.
    destruct H0 as [Hlen HF2].
    pose proof
      (conj Hlen
         (fun n e v he hv =>
            HF2 n e v he hv us eps Logic.eq_refl))
      as HF2'.
    rewrite <- Forall2_forall_nth_error in HF2'.
    clear HF2 Hlen.
    constructor.
    rewrite sublist.Forall2_map1.
    assumption.
Qed.

Local Hint Resolve shift_e_eval : core.
Local Hint Constructors parser_expr_big_step : core.

Lemma shift_trans_eval : forall us ϵ p st,
    p⟨ us ++ ϵ , p ⟩ ⇓ st -> forall vs,
      p⟨ us ++ vs ++ ϵ , shift_transition (Shifter (length us) (length vs)) p ⟩ ⇓ st.
Proof.
  intros us eps p st h vs.
  inv h; unravel; auto.
Qed.

Local Hint Resolve shift_trans_eval : core.

Fixpoint shift_lv (sh : shifter) (lv : Val.lv) : Val.lv :=
  match lv with
  | Val.Var x => Val.Var $ shift_var sh x
  | Val.Slice hi lo lv => Val.Slice hi lo $ shift_lv sh lv
  | Val.Member x lv => Val.Member x $ shift_lv sh lv
  | Val.Index n lv => Val.Index n $ shift_lv sh lv
  end.

Lemma shift_lv_0_add : forall lv m n,
    shift_lv (Shifter 0 (m + n)) lv = shift_lv (Shifter 0 m) (shift_lv (Shifter 0 n) lv).
Proof.
  intro lv; induction lv; intros m n; unravel; f_equal; auto.
  unfold shift_var; cbn. lia.
Qed.

Lemma shift_lv_0 : forall lv c, shift_lv (Shifter c 0) lv = lv.
Proof.
  intros lv c; induction lv; unravel; f_equal; auto.
  unfold shift_var. destruct_if; reflexivity.
Qed.

Local Hint Constructors lexpr_big_step : core.

Lemma shift_lv_eval : forall us vs ϵ e lv,
    l⟨ us ++ ϵ, e ⟩ ⇓ lv ->
    l⟨ us ++ vs ++ ϵ,
        shift_e
          (Shifter (length us) (length vs)) e ⟩
      ⇓ shift_lv (Shifter (length us) (length vs)) lv.
Proof.
  intros us vs eps e lv h.
  remember (us ++ eps) as useps eqn:huseps.
  generalize dependent eps.
  generalize dependent us.
  induction h; intros; subst; unravel; eauto.
Qed.

Local Hint Resolve shift_lv_eval : core.

Lemma nth_update_app1 : forall {A : Set} n (a : A) l1 l2,
    length l1 <= n ->
    nth_update n a (l1 ++ l2) = l1 ++ nth_update (n - length l1) a l2.
Proof.
  intros A n a;
    induction n as [| n ih];
    intros [| a1 l1] l2 h; cbn in *;
    lia || (f_equal; auto).
  apply ih. lia.
Qed.

Lemma nth_update_app2 : forall {A : Set} n (a : A) l1 l2,
    n < length l1 ->
    nth_update n a (l1 ++ l2) = nth_update n a l1 ++ l2.
Proof.
  intros A n a;
    induction n as [| n ih];
    intros [| a1 l1] l2 h; cbn in *;
    lia || (f_equal; auto).
  apply ih. lia.
Qed.

Lemma nth_update_app3 : forall {A : Set} n (a : A) l1 l2,
    nth_update (length l1 + n) a (l1 ++ l2) = l1 ++ nth_update n a l2.
Proof.
  intros.
  rewrite nth_update_app1 by lia.
  f_equal. f_equal. lia.
Qed.

Lemma shift_lv_lookup : forall lv rs us ϵ,
    lv_lookup (rs ++ us ++ ϵ) (shift_lv (Shifter (length rs) (length us)) lv)
    = lv_lookup (rs ++ ϵ) lv.
Proof.
  intro lv; induction lv; intros; unravel.
  - unfold shift_var, cutoff,amt.
    destruct_if.
    + rewrite nth_error_app2
        with (n := x) by assumption.
      rewrite nth_error_app2
        with (n := length us + x) by lia.
      replace (length us + x - length rs)
        with (length us + (x - length rs)) by lia.
      rewrite nth_error_app3.
      reflexivity.
    + rewrite nth_error_app1 by lia.
      rewrite nth_error_app1 by assumption.
      reflexivity.
  - rewrite IHlv. reflexivity.
  - rewrite IHlv. reflexivity.
  - rewrite IHlv. reflexivity.
Qed.

Local Hint Rewrite shift_lv_lookup : core.

Lemma shift_lv_update : forall lv v rs ϵ rs' ϵ',
    length rs = length rs' ->
    lv_update lv v (rs ++ ϵ) = rs' ++ ϵ' -> forall us,
      lv_update (shift_lv (Shifter (length rs) (length us)) lv) v (rs ++ us ++ ϵ)
      = rs' ++ us ++ ϵ'.
Proof.
  intro lv; induction lv;
    intros v rs eps rs' eps' hrs hlv us;
    unravel in *; autorewrite with core.
  - unfold shift_var, cutoff, amt.
    destruct_if.
    + rewrite nth_update_app1 in * by lia.
      replace (length us + x - length rs)
        with (length us + (x - length rs)) by lia.
      rewrite nth_update_app3.
      pose proof sublist.app_eq_len_eq hlv hrs as [hrs' heps]; subst.
      reflexivity.
    + rewrite nth_update_app2 in * by lia.
      assert (length (nth_update x v rs) = length rs') as hup.
      { rewrite nth_update_length. assumption. }
      pose proof sublist.app_eq_len_eq hlv hup as [hrs' heps]; subst.
      reflexivity.
  - destruct v; auto.
    destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
  - destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
    destruct ls; eauto.
  - destruct (lv_lookup (rs ++ eps) lv) as [[] |]; auto.
    destruct ls; eauto.
Qed.
    
Inductive eval_decl_list
  (ϵ : list Val.v)
  : list Expr.e -> list Val.v -> Prop :=
| eval_decl_nil :
  eval_decl_list ϵ [] []
| eval_decl_cons h hv t tv :
  ⟨ tv ++ ϵ, h ⟩ ⇓ hv ->
  eval_decl_list ϵ t tv ->
  eval_decl_list ϵ (h :: t) (hv :: tv).

Local Hint Constructors stmt_big_step : core.
Local Hint Constructors eval_decl_list : core.
Local Hint Constructors relop : core.

Lemma eval_decl_list_append : forall ϵ vs1 vs2 l1 l2,
    eval_decl_list ϵ l1 vs1 ->
    eval_decl_list (vs1 ++ ϵ) l2 vs2 ->
    eval_decl_list ϵ (l2 ++ l1) (vs2 ++ vs1).
Proof.
  intros ϵ vs1 vs2.
  generalize dependent vs1.
  induction vs2 as [| v2 vs2 ih];
    intros vs1 l1 [| e2 l2] h1 h2; inv h2; cbn; auto.
  constructor; eauto.
  rewrite <- app_assoc; assumption.
Qed.

Local Hint Resolve eval_decl_list_append : core.

Lemma eval_decl_list_length : forall ϵ l vs,
    eval_decl_list ϵ l vs -> length l = length vs.
Proof.
  intros ϵ l vs h; induction h; cbn; auto.
Qed.

Local Hint Resolve eval_decl_list_length : core.

Fixpoint shift_elist (sh : shifter) (es : list Expr.e) : list Expr.e :=
  match es with
  | [] => []
  | e :: es => shift_e (smother sh (length es)) e :: shift_elist sh es
  end.

Lemma eval_decl_list_app : forall ϵ es1 es2 vs1 vs2,
    eval_decl_list ϵ es1 vs1 ->
    eval_decl_list ϵ es2 vs2 ->
    eval_decl_list ϵ (shift_elist (Shifter 0 (length es1)) es2 ++ es1) (vs2 ++ vs1).
Proof.
  intros eps es1 es2 vs1 vs2 h1 h2.
  generalize dependent vs1.
  generalize dependent es1.
  induction h2; intros es1 vs1 h1; cbn; auto.
  unfold smother, RecordSet.set; cbn.
  rewrite add_0_r.
  constructor; auto. rewrite <- app_assoc.
  rewrite (eval_decl_list_length _ _ _ h1).
  rewrite (eval_decl_list_length _ _ _ h2).
  eauto.
Qed.

Local Hint Resolve eval_decl_list_app : core.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Inductive Lift_e
  : Expr.e -> Expr.e -> list Expr.e -> Prop :=
| Lift_e_bool (b : bool) :
  Lift_e b b []
| Lift_e_bit w n :
  Lift_e (w `W n) (Expr.Var (Expr.TBit w) "" 0) [w `W n]
| Lift_e_var t og x :
  Lift_e (Expr.Var t og x) (Expr.Var t og x) []
| Lift_e_member t x e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Member t x e) (Expr.Member t x e') es
| Lift_e_uop t o e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Uop t o e) (Expr.Var t "" 0) (Expr.Uop t o e' :: es)
| Lift_e_index t e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Index t e1 e2)
    (Expr.Index
       t
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2'))
    (shift_elist (Shifter 0 (length es1)) es2 ++ es1)
| Lift_e_bop t o e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Bop t o e1 e2)
    (Expr.Var t "" 0)
    (Expr.Bop
       t o
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2')
       :: shift_elist (Shifter 0 (length es1)) es2 ++ es1).

Lemma Lift_e_good : forall ϵ e v,
    ⟨ ϵ, e ⟩ ⇓ v -> forall e' es,
      Lift_e e e' es -> exists vs,
        eval_decl_list ϵ es vs /\ ⟨ vs ++ ϵ, e' ⟩ ⇓ v.
Proof.
  intros eps e v hev;
    induction hev using custom_expr_big_step_ind;
    intros E Es hn; inv hn; eauto.
  - pose proof IHhev _ _ H5 as (vs & hvs & hv).
    exists (v' :: vs). split; eauto.
  - pose proof IHhev1 _ _ H6 as (vs1 & hvs1 & hv1); clear IHhev1.
    pose proof IHhev2 _ _ H7 as (vs2 & hvs2 & hv2); clear IHhev2.
    exists (v :: vs2 ++ vs1). split; eauto.
    constructor; eauto.
    rewrite <- app_assoc.
    rewrite (eval_decl_list_length _ _ _ hvs2).
    rewrite (eval_decl_list_length _ _ _ hvs1).
    econstructor; eauto.
    eapply shift_e_eval with (us := []); assumption.
  - firstorder eauto.
  - pose proof IHhev1 _ _ H5 as (vs1 & hvs1 & hv1); clear IHhev1.
    pose proof IHhev2 _ _ H6 as (vs2 & hvs2 & hv2); clear IHhev2.
    exists (vs2 ++ vs1). rewrite <- app_assoc.
    split; eauto.
    rewrite (eval_decl_list_length _ _ _ hvs1).
    rewrite (eval_decl_list_length _ _ _ hvs2).
    econstructor; eauto.
    eapply shift_e_eval with (us := []); eassumption.
Qed.

Lemma Lift_e_good_lv : forall ϵ e lv,
    l⟨ ϵ, e ⟩ ⇓ lv -> forall e' es,
      Lift_e e e' es -> exists vs,
        eval_decl_list ϵ es vs /\ l⟨ vs ++ ϵ, e' ⟩ ⇓ shift_lv (Shifter 0 (length vs)) lv.
Proof.
  intros eps e lv H; induction H;
    intros e' es h; inv h; unravel.
  - unfold shift_var; cbn. eexists; eauto.
  - pose proof IHlexpr_big_step _ _ H5 as (vs & hvs & ih); clear IHlexpr_big_step.
    eexists; eauto.
  - pose proof IHlexpr_big_step _ _ H6 as (vs1 & hvs1 & ih); clear IHlexpr_big_step.
    pose proof Lift_e_good _ _ _ H _ _ H7 as (vs2 & hvs2 & hv2).
    exists (vs2 ++ vs1). split; auto.
    rewrite <- app_assoc.
    rewrite (eval_decl_list_length _ _ _ hvs1).
    rewrite (eval_decl_list_length _ _ _ hvs2).
    econstructor; eauto.
    rewrite app_length.
    rewrite shift_lv_0_add.
    apply shift_lv_eval with (us := []); auto.
Qed.

Fixpoint Unwind (es : list Expr.e) (s : Stmt.s) : Stmt.s :=
  match es with
  | [] => s
  | e :: es => Unwind es (Stmt.Var "" (inr e) s)
  end.

Inductive Lift_s : Stmt.s -> Stmt.s -> Prop :=
| Lift_s_skip :
  Lift_s Stmt.Skip Stmt.Skip
| Lift_s_return_some e e' es :
  Lift_e e e' es ->
  Lift_s
    (Stmt.Return (Some e))
    (Unwind es (Stmt.Return (Some e')))
| Lift_s_asgn e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_s
    (e1 `:= e2)
    (Unwind
       (shift_elist (Shifter 0 (length es1)) es2 ++ es1)
       (shift_e (Shifter 0 (length es2)) e1'
          `:= shift_e (Shifter (length es2) (length es1)) e2'))
| Lift_s_seq s1 s2 s1' s2' :
  Lift_s s1 s1' ->
  Lift_s s2 s2' ->
  Lift_s (s1 `; s2) (s1' `; s2')
| Lift_s_if e e' s1 s2 s1' s2' es :
  Lift_e e e' es ->
  Lift_s s1 s1' ->
  Lift_s s2 s2' ->
  Lift_s
    (If e Then s1 Else s2)
    (Unwind
       es
       (If e'
          Then shift_s (Shifter 0 (length es)) s1'
          Else shift_s (Shifter 0 (length es)) s2'))
| Lift_s_var_typ og t s s' :
  Lift_s s s' ->
  Lift_s (Stmt.Var og (inl t) s) (Stmt.Var og (inl t) s')
| Lift_s_var_exp og e e' s s' es :
  Lift_e e e' es ->
  Lift_s s s' ->
  Lift_s
    (Stmt.Var og (inr e) s)
    (Unwind
       es
       (Stmt.Var og (inr e') (shift_s (Shifter 1 (length es)) s'))).

Variant ctx_cuttoff (m : nat) : ctx -> Prop :=
  | ctx_cuttoff_action aa :
    ctx_cuttoff m (CAction aa)
  | ctx_cuttoff_function :
    ctx_cuttoff m CFunction
  | ctx_cuttoff_applyblock ts aa ac :
    ctx_cuttoff m (CApplyBlock ts aa ac)
  | ctx_cuttoff_parserstate n strt sts ap :
    n <= m ->
    ctx_cuttoff m (CParserState n strt sts ap).

Local Hint Constructors ctx_cuttoff : core.

Lemma ctx_cuttoff_le : forall l m c,
    m <= l ->
    ctx_cuttoff m c ->
    ctx_cuttoff l c.
Proof.
  intros l m c hml hc; inv hc; auto.
  constructor. lia.
Qed.

Local Hint Resolve ctx_cuttoff_le : core.

Section StatementLifting.
  Context `{ext_sem : Extern_Sem}.

  Local Hint Constructors stmt_big_step : core.

  (** Specification of [unwind_vars]. *)
  Lemma eval_decl_list_Unwind : forall ϵ es vs,
      eval_decl_list ϵ es vs ->
      forall vs' ϵ' c Ψ s sig ψ,
        length vs = length vs' ->
        ⧼ Ψ, vs ++ ϵ, c, s ⧽ ⤋ ⧼ vs' ++ ϵ', sig, ψ ⧽ ->
        ⧼ Ψ, ϵ, c, Unwind es s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
  Proof using.
    intros eps es vs h;
      induction h; intros; unravel in *.
    - symmetry in H.
      rewrite length_zero_iff_nil in H.
      subst; assumption.
    - destruct vs' as [| h' vs']; cbn in *; try lia.
      inv H0. eauto.
  Qed.

  Local Hint Resolve eval_decl_list_Unwind : core.
  
  Lemma shift_s_eval : forall Ψ us us' ϵ ϵ' c s sig ψ,
      length us = length us' ->
      ctx_cuttoff (length ϵ) c ->
      ⧼ Ψ , us ++ ϵ , c , s ⧽ ⤋ ⧼ us' ++ ϵ' , sig , ψ ⧽ -> forall vs,
          ⧼ Ψ , us ++ vs ++ ϵ , c ,
            shift_s (Shifter (length us) (length vs)) s ⧽
            ⤋ ⧼ us' ++ vs ++ ϵ' , sig , ψ ⧽.
  Proof using.
    intros Psi us us' eps eps' c s sig psi hus hc hs.
    remember (us ++ eps) as useps eqn:huseps.
    remember (us' ++ eps') as useps' eqn:huseps'.
    generalize dependent eps'.
    generalize dependent us'.
    generalize dependent eps.
    generalize dependent us.
    induction hs; intros; unravel; subst; eauto.
    - inv H; unravel; auto.
    - pose proof sbs_length _ _ _ _ _ _ _ hs as hlen.
      pose proof app_eq_app _ _ _ _ huseps as [l2 heps2].
      pose proof app_eq_app _ _ _ _ huseps' as [l3 heps3].
      inv hc.
      destruct heps2 as [[hl2 heps2] | [hl2 hesp2]];
        destruct heps3 as [[hl3 heps3] | [hl3 hesp3]]; subst.
      + rewrite <- app_assoc in huseps,  huseps'.
        pose proof sublist.app_eq_len_eq huseps' hus as [huseq heps]; subst.
        rewrite app_inv_head_iff in hl3, huseps'; subst.
        do 4 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc in H1.
        do 2 rewrite <- app_assoc.
        eauto.
      + rewrite <- app_assoc in hus.
        repeat rewrite app_length in *.
        assert (hlen2 : length l2 = 0) by lia.
        assert (hlen3 : length l3 = 0) by lia.
        rewrite length_zero_iff_nil in hlen2.
        rewrite length_zero_iff_nil in hlen3.
        subst; cbn in *.
        repeat rewrite <- app_assoc in *; cbn in *.
        do 2 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc.
        eauto.
      + rewrite <- app_assoc in hus.
        repeat rewrite app_length in *.
        assert (hlen2 : length l2 = 0) by lia.
        assert (hlen3 : length l3 = 0) by lia.
        rewrite length_zero_iff_nil in hlen2.
        rewrite length_zero_iff_nil in hlen3.
        subst; cbn in *.
        repeat rewrite <- app_assoc in *; cbn in *.
        do 2 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc.
        do 2 rewrite add_0_r.
        eauto.
      + repeat rewrite app_length in * |-.
        assert (hl23 : length l2 = length l3) by lia.
        assert (hepslen : length eps = length eps') by lia.
        assert (hlen2 : length l2 = 0) by lia.
        rewrite length_zero_iff_nil in hlen2.
        subst; cbn in *.
        symmetry in hl23.
        rewrite length_zero_iff_nil in hl23.
        subst; cbn in *.
        repeat rewrite app_nil_r.
        do 2 rewrite app_assoc.
        econstructor; eauto.
        rewrite <- app_assoc. auto.
    - pose proof shift_lv_update _ _ _ _ _ _ hus huseps' vs as hvs.
      rewrite <- hvs.
      constructor; auto.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - destruct te as [t | e]; unravel; unfold sext,smother,RecordSet.set; cbn.
      + apply sbs_var with (v := v) (v' := v'); auto.
        replace (v :: us ++ vs ++ eps)
          with ((v :: us) ++ vs ++ eps) by reflexivity.
        replace (v' :: us' ++ vs ++ eps')
          with ((v' :: us') ++ vs ++ eps') by reflexivity.
        replace (S (length us)) with (length (v :: us)) by reflexivity.
        apply IHhs; cbn; auto.
      + apply sbs_var with (v := v) (v' := v'); auto.
        replace (v :: us ++ vs ++ eps)
          with ((v :: us) ++ vs ++ eps) by reflexivity.
        replace (v' :: us' ++ vs ++ eps')
          with ((v' :: us') ++ vs ++ eps') by reflexivity.
        replace (S (length us)) with (length (v :: us)) by reflexivity.
        apply IHhs; cbn; auto.
    - assert (hϵ' : length (us ++ eps) = length ϵ') by
        eauto using sbs_length.
      rewrite app_length in hϵ'.
      eapply sbs_seq_cont with (ϵ' := firstn (length us) ϵ' ++ vs ++ skipn (length us) ϵ'); eauto.
      + eapply IHhs1; eauto.
        * rewrite firstn_length. lia.
        * rewrite firstn_skipn. reflexivity.
      + replace (length us) with
          (length (firstn (length us) ϵ')) at 3
          by (rewrite firstn_length; lia).
        eapply IHhs2; eauto.
        * rewrite skipn_length, <- hϵ'.
          replace (length us + length eps - length us) with (length eps) by lia.
          assumption.
        * rewrite firstn_skipn. reflexivity.
        * rewrite firstn_length; lia.
    - econstructor; eauto.
      destruct b; auto.
  Admitted.

  Local Hint Resolve shift_s_eval : core.
  
  Lemma Lift_E_good : forall Ψ ϵ ϵ' c s sig ψ,
      ctx_cuttoff (length ϵ) c ->
      ⧼ Ψ, ϵ, c, s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽ -> forall s',
          Lift_s s s' ->
          ⧼ Ψ, ϵ, c, s' ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
  Proof using.
    intros Psi eps eps' c s sg psi hc hs;
      induction hs; intros σ hσ; inv hσ; eauto.
    - inv H.
      pose proof Lift_e_good _ _ _ H2 _ _ H1 as (vs & hvs & hv).
      eauto.
    - pose proof Lift_e_good_lv _ _ _ H _ _ H3 as (vs1 & hvs1 & hv1).
      pose proof Lift_e_good _ _ _ H0 _ _ H5 as (vs2 & hvs2 & hv2).
      eapply eval_decl_list_Unwind; eauto. admit.
    - econstructor; eauto.
      eapply IHhs; cbn; eauto.
    - pose proof Lift_e_good _ _ _ H _ _ H4 as (vs & hvs & hv).
      eapply eval_decl_list_Unwind; eauto.
      apply sbs_var with (v := v) (v' := v'); auto.
      replace (v :: vs ++ ϵ) with ([v] ++ vs ++ ϵ) by reflexivity.
      replace (v' :: vs ++ ϵ') with ([v'] ++ vs ++ ϵ') by reflexivity.
      replace 1 with (length [v]) by reflexivity.
      rewrite (eval_decl_list_length _ _ _ hvs). 
      eapply shift_s_eval; cbn; eauto.
      apply IHhs; cbn; eauto.
    - eapply sbs_seq_cont; eauto.
      apply IHhs2; auto.
      erewrite <- sbs_length by eauto; assumption.
    - pose proof Lift_e_good _ _ _ H _ _ H3 as (vs & hvs & hv).
      rewrite (eval_decl_list_length _ _ _ hvs).
      eapply eval_decl_list_Unwind; eauto.
      econstructor; eauto.
      replace 0 with (@length Val.v []) by reflexivity.
      replace (vs ++ ϵ) with ([] ++ vs ++ ϵ) by reflexivity.
      replace (vs ++ ϵ') with ([] ++ vs ++ ϵ') by reflexivity.
      destruct b; eauto.
  Admitted.
End StatementLifting.
