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

Lemma eval_decl_list : forall l1 l2 vs1 vs2 ϵ,
    eval_decl_list ϵ l1 vs1 ->
    eval_decl_list ϵ l2 vs2 ->
    eval_decl_list ϵ (l1 ++ l2) (vs1 ++ vs2).
Proof.
  intros l1 l2 vs1 vs2 ϵ h1.
  generalize dependent vs2.
  generalize dependent l2.
  induction h1; intros l2 vs2 h2; cbn; auto.
  constructor; eauto.
  admit (* uh oh *).
Abort.

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
    + clear H1 H2. inv H; inv H0; unravel in *; auto.
      constructor.
      destruct ob; cbn in *; repeat some_inv;
        try discriminate; auto.
    + rewrite <- ForallMap.Forall2_map_l; assumption.
Qed.

Lemma eval_decl_list_length : forall ϵ l vs,
    eval_decl_list ϵ l vs -> length l = length vs.
Proof.
  intros ϵ l vs h; induction h; cbn; auto.
Qed.

Goal forall e ϵ v,
    ⟨ ϵ, e ⟩ ⇓ v ->
    forall l e',
      lift_e e = (l, e') ->
      exists vs, eval_decl_list ϵ l vs /\ ⟨ vs ++ ϵ, e' ⟩ ⇓ v.
Proof.
  intros e ϵ v h; induction h using custom_expr_big_step_ind;
    intros l e' heq; cbn in *; inv heq; eauto.
  - destruct (lift_e e) as [l' e'']. inv H1.
    pose proof IHh _ _ eq_refl as (vs & ih & ihv); clear IHh.
    eexists; eauto.
  - destruct (lift_e e) as [l' e'']. inv H1.
    pose proof IHh _ _ eq_refl as (vs & ih & ihv); clear IHh.
    eexists; eauto.
  - destruct (lift_e e) as [l' e'']. inv H1.
    pose proof IHh _ _ eq_refl as (vs & ih & ihv); clear IHh.
    eexists; eauto.
  - destruct (lift_e e1) as [l₁ e₁].
    destruct (lift_e e2) as [l₂ e₂].
    inv H1.
    pose proof IHh1 _ _ eq_refl as (vs1 & ih1 & ihv1); clear IHh1.
    pose proof IHh2 _ _ eq_refl as (vs2 & ih2 & ihv2); clear IHh2.
    exists (v :: vs2 ++ vs1); split; eauto.
    constructor.
    + econstructor; eauto.
      * rewrite <- app_assoc.
        apply eval_decl_list_length in ih2.
        rewrite ih2.
        auto using shift_eval.
      * admit (* sketcky case. *).
    + admit (*not true, need to shift a list?.*).
  - destruct (lift_e e) as [l' e'']; inv H1.
    pose proof IHh _ _ eq_refl as (vs' & ih & ihv); clear IHh.
    eexists; eauto.
  - (* generalization of [Bop] case. *)
Abort.
