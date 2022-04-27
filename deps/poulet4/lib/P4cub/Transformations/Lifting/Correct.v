Require Export Coq.micromega.Lia Poulet4.P4cub.Syntax.Syntax.
From Poulet4.P4cub Require Export Semantics.Dynamic.BigStep.BigStep
     Transformations.Lifting.Statementize
     (*Transformations.Lifting.Lifted*).
Import AllCubNotations Clmt.Notations Val.ValueNotations.

Inductive eval_decl_list (ϵ : list Val.v) : list Expr.e -> list Val.v -> Prop :=
| eval_decl_nil :
  eval_decl_list ϵ [] []
| eval_decl_cons h hv t tv :
  ⟨ tv ++ ϵ, h ⟩ ⇓ hv ->
  eval_decl_list ϵ t tv ->
  eval_decl_list ϵ (h :: t) (hv :: tv).

Ltac if_destr :=
  match goal with
    |- context [if ?trm then _ else _]
    => destruct trm as [? | ?] eqn:?
  end; unfold "===" in *; try contradiction; auto.

Local Hint Constructors expr_big_step : core.
Local Hint Constructors stmt_big_step : core.
Local Hint Constructors lexpr_big_step : core.
Local Hint Resolve Clmt.bind_sound : core.
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

Lemma shift_eval : forall vs vs' ϵ e v,
    ⟨ vs ++ ϵ, e ⟩ ⇓ v ->
      ⟨ vs' ++ vs ++ ϵ, Shift.rename_e (Nat.add $ length vs') e ⟩ ⇓ v.
Proof.
  intros vs vs' ϵ e v h; induction h using custom_expr_big_step_ind;
    unravel; eauto.
  - constructor.
    rewrite nth_error_app2 by lia.
    rewrite Minus.minus_plus; assumption.
  - constructor.
    rewrite <- ForallMap.Forall2_map_l; assumption.
Qed.

Lemma eval_decl_list_length : forall ϵ l vs,
    eval_decl_list ϵ l vs -> length l = length vs.
Proof.
  intros ϵ l vs h; induction h; cbn; auto.
Qed.

Goal forall e ϵ v,
    ⟨ ϵ, e ⟩ ⇓ v ->
    forall us l e',
      lift_e (length us) e = (l, e') ->
      exists vs, eval_decl_list (us ++ ϵ) l vs /\ ⟨ vs ++ us ++ ϵ, e' ⟩ ⇓ v.
Proof.
  intros e ϵ v h; induction h using custom_expr_big_step_ind;
    intros us l e' heq; cbn in *; inv heq; eauto.
  - eexists; split; eauto; cbn.
    constructor.
    rewrite nth_error_app2 by lia.
    replace (length us + x - length us) with x by lia;
      assumption.
  - destruct (lift_e (length us) e) as [l' e''] eqn:eql. inv H1.
    pose proof IHh _ _ _ eql as (vs & ih & ihv); clear IHh.
    eexists; eauto.
  - destruct (lift_e (length us) e) as [l' e''] eqn:eql. inv H1.
    pose proof IHh _ _ _ eql as (vs & ih & ihv); clear IHh.
    eexists; eauto.
  - destruct (lift_e (length us) e) as [l' e''] eqn:eql. inv H1.
    pose proof IHh _ _ _ eql as (vs & ih & ihv); clear IHh.
    eexists; eauto.
  - destruct (lift_e (length us) e1) as [l₁ e₁] eqn:eql1.
    destruct (lift_e (length l₁ + length us) e2) as [l₂ e₂] eqn:eql2; inv H1.
    pose proof IHh1 _ _ _ eql1 as (vs1 & ih1 & ihv1); clear IHh1.
    assert (Hl1: length l₁ = length vs1) by eauto using eval_decl_list_length.
    rewrite Hl1, <- app_length in eql2.
    pose proof IHh2 _ _ _ eql2 as (vs2 & ih2 & ihv2); clear IHh2.
    exists (v :: vs2 ++ vs1); split; eauto.
    rewrite <- app_assoc in ihv2.
    rewrite <- app_assoc in ih2.
    constructor; eauto using eval_decl_list_append.
    econstructor; eauto;
      rewrite <- app_assoc; auto.
    apply eval_decl_list_length in ih2.
    rewrite ih2.
    auto using shift_eval.
  - destruct (lift_e (length us) e) as [l' e''] eqn:eql; inv H1.
    pose proof IHh _ _ _ eql as (vs' & ih & ihv); clear IHh.
    eexists; eauto.
  - destruct ((fix lift_e_list (up : nat) (es : list Expr.e)
                : list Expr.e * list Expr.e :=
                 match es with
                 | [] => ([], [])
                 | e :: es0 =>
                     let '(le, e') := lift_e up e in
                     let '(les, es') := lift_e_list (length le + up) es0 in
                     (les ++ le, Shift.rename_e (Nat.add $ length les) e' :: es')
                 end) (length us) es)
      as [les es'] eqn:eql; inv H2.
    assert (help: exists vs',
               eval_decl_list (us ++ ϵ) les vs'
               /\ Forall2 (expr_big_step (vs' ++ us ++ ϵ)) es' vs).
    { generalize dependent les;
      generalize dependent es';
        generalize dependent us.
      induction H as [| e v es vs hev hesvs ihesvs]; inv H0;
        intros us ES l h; cbn.
      + inv h; cbn; eexists; eauto.
      + destruct (lift_e (length us) e) as [le E] eqn:eqle.
        destruct ((fix lift_e_list (up : nat) (es : list Expr.e) {struct es}
                    : list Expr.e * list Expr.e :=
                     match es with
                     | [] => ([], [])
                     | e :: es0 =>
                         let '(le, e') := lift_e up e in
                         let '(les, es') := lift_e_list (length le + up) es0 in
                         (les ++ le, Shift.rename_e (Nat.add $ length les) e' :: es')
                     end) (length le + length us) es)
          as [les Es] eqn:eqles; inv h.
        pose proof H3 _ _ _ eqle as (levs & hlevs & ihE); clear H3.
        assert (hlen: length le = length levs)
          by eauto using eval_decl_list_length.
        rewrite hlen, <- app_length in eqles.
        pose proof ihesvs H5 _ _ _ eqles as (lesvs & hlesvs & ihEs); clear ihesvs.
        rewrite <- app_assoc in hlesvs, ihEs.
        exists (lesvs ++ levs); split; auto using eval_decl_list_append.
        apply eval_decl_list_length in hlesvs.
        rewrite hlesvs.
        constructor; rewrite <- app_assoc; auto using shift_eval. }
    destruct help as (vs' & hvs' & h); eexists; eauto.
Qed.
