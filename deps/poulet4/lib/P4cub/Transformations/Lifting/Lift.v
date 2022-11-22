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
Local Hint Resolve shift_e_eval : core.

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

Fixpoint shift_pairs (ess : list (Expr.e * list Expr.e)) : list (Expr.e * list Expr.e) :=
  match ess with
  | [] => []
  | (e,es) :: ess
    => let n := list_sum $ map (@length _) $ map snd ess in
      (shift_e (Shifter (length es) n) e,
        shift_elist (Shifter 0 n) es) ::
        map (fun '(e,es') => (shift_e (Shifter 0 $ length es) e, es')) (shift_pairs ess)
  end.

Lemma shift_one_pair : forall e es,
    shift_pairs [(e,es)] = [(e,es)].
Proof.
  intros; cbn; rewrite shift_e_0 , shift_elist_0. reflexivity.
Qed.

Lemma shift_two_pairs : forall e1 e2 es1 es2,
    shift_pairs [(e2,es2);(e1,es1)]
    = [(shift_e (Shifter (length es2) (length es1)) e2,
         shift_elist (Shifter 0 (length es1)) es2);
       (shift_e (Shifter 0 (length es2)) e1, es1)].
Proof.
  intros; unravel.
  rewrite add_0_r, shift_elist_0, shift_e_0.
  reflexivity.
Qed.

Lemma shift_three_pairs : forall e1 e2 e3 es1 es2 es3,
    shift_pairs [(e3,es3);(e2,es2);(e1,es1)]
    = [(shift_e (Shifter (length es3) (length es2 + length es1)) e3,
            shift_elist (Shifter 0 (length es2 + length es1)) es3);
       (shift_e (Shifter 0 (length es3)) (shift_e (Shifter (length es2) (length es1)) e2),
         shift_elist (Shifter 0 (length es1)) es2);
       (shift_e (Shifter 0 (length es3 + length es2)) e1, es1)].
Proof.
  intros; unravel.
  rewrite add_0_r, shift_elist_0, shift_e_0, shift_e_add.
  reflexivity.
Qed.
       
Inductive Lift_e
  : Expr.e -> Expr.e -> list Expr.e -> Prop :=
| Lift_bool (b : bool) :
  Lift_e b b []
| Lift_var t og x :
  Lift_e (Expr.Var t og x) (Expr.Var t og x) []
| Lift_bit w n :
  Lift_e (w `W n) (Expr.Var (Expr.TBit w) "" 0) [w `W n]
| Lift_int w z :
  Lift_e (w `S z) (Expr.Var (Expr.TInt w) "" 0) [w `S z]
| Lift_member t x e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Member t x e) (Expr.Member t x e') es
| Lift_uop t o e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Uop t o e) (Expr.Var t "" 0) (Expr.Uop t o e' :: es)
| Lift_slice hi lo e e' es :
  Lift_e e e' es ->
  Lift_e
    (Expr.Slice hi lo e)
    (Expr.Var (Expr.TBit (Npos hi - Npos lo + 1)%N) "" 0)
    (Expr.Slice hi lo e' :: es)
| Lift_cast t e e' es :
  Lift_e e e' es ->
  Lift_e (Expr.Cast t e) (Expr.Var t "" 0) (Expr.Cast t e' :: es)
| Lift_index t e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Index t e1 e2)
    (Expr.Index
       t
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2'))
    (shift_elist (Shifter 0 (length es1)) es2 ++ es1)
| Lift_bop t o e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_e
    (Expr.Bop t o e1 e2)
    (Expr.Var t "" 0)
    (Expr.Bop
       t o
       (shift_e (Shifter 0 (length es2)) e1')
       (shift_e (Shifter (length es2) (length es1)) e2')
       :: shift_elist (Shifter 0 (length es1)) es2 ++ es1)
| Lift_lists ls es es' ess :
  Forall3 Lift_e es es' ess ->
  Lift_e
    (Expr.Lists ls es)
    (Expr.Var (t_of_lists ls es) "" 0)
    (Expr.Lists ls es' :: concat ess).

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
| Lift_skip :
  Lift_s Stmt.Skip Stmt.Skip
| Lift_return_some e e' es :
  Lift_e e e' es ->
  Lift_s
    (Stmt.Return (Some e))
    (Unwind es (Stmt.Return (Some e')))
| Lift_asgn e1 e2 e1' e2' es1 es2 :
  Lift_e e1 e1' es1 ->
  Lift_e e2 e2' es2 ->
  Lift_s
    (e1 `:= e2)
    (Unwind
       (shift_elist (Shifter 0 (length es1)) es2 ++ es1)
       (shift_e (Shifter 0 (length es2)) e1'
          `:= shift_e (Shifter (length es2) (length es1)) e2'))
| Lift_seq s1 s2 s1' s2' :
  Lift_s s1 s1' ->
  Lift_s s2 s2' ->
  Lift_s (s1 `; s2) (s1' `; s2')
| Lift_if e e' s1 s2 s1' s2' es :
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
| Lift_var_typ og t s s' :
  Lift_s s s' ->
  Lift_s (Stmt.Var og (inl t) s) (Stmt.Var og (inl t) s')
| Lift_var_exp og e e' s s' es :
  Lift_e e e' es ->
  Lift_s s s' ->
  Lift_s
    (Stmt.Var og (inr e) s)
    (Unwind
       es
       (Stmt.Var og (inr e') (shift_s (Shifter 1 (length es)) s'))).

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
  Local Hint Resolve shift_s_eval : core.
  
  Lemma Lift_s_good : forall Ψ ϵ ϵ' c s sig ψ,
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
