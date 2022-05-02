Require Export Coq.micromega.Lia Poulet4.P4cub.Syntax.Syntax.
From Poulet4.P4cub Require Export Semantics.Dynamic.BigStep.BigStep
     Transformations.Lifting.Statementize
     (*Transformations.Lifting.Lifted*).
Import AllCubNotations Clmt.Notations Val.ValueNotations.

(** Big-step evaluation specification for lifting in [Statementize.v] *)

Inductive eval_decl_list (ϵ : list Val.v) : list Expr.e -> list Val.v -> Prop :=
| eval_decl_nil :
  eval_decl_list ϵ [] []
| eval_decl_cons h hv t tv :
  ⟨ tv ++ ϵ, h ⟩ ⇓ hv ->
  eval_decl_list ϵ t tv ->
  eval_decl_list ϵ (h :: t) (hv :: tv).

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

Local Hint Resolve eval_decl_list_append : core.

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

Local Hint Resolve shift_eval : core.

Lemma eval_decl_list_length : forall ϵ l vs,
    eval_decl_list ϵ l vs -> length l = length vs.
Proof.
  intros ϵ l vs h; induction h; cbn; auto.
Qed.

Local Hint Resolve eval_decl_list_length : core.

Theorem lift_e_expr_big_step : forall e ϵ v,
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

Local Hint Resolve lift_e_expr_big_step : core.

Lemma lift_e_list_expr_big_step : forall es vs ϵ,
    Forall2 (expr_big_step ϵ) es vs ->
    forall us les es',
      lift_e_list (length us) es = (les, es') ->
      exists vs',
        eval_decl_list (us ++ ϵ) les vs'
        /\ Forall2 (expr_big_step (vs' ++ us ++ ϵ)) es' vs.
Proof.
  intros es vs ϵ h;
    induction h as [| e v es vs hev hesvs ihesvs];
    intros us les es' h; unravel in *.
  - inv h; eauto.
  - destruct (lift_e (length us) e) as [l' e'] eqn:eql.
    destruct (lift_e_list (length l' + length us) es)
      as [les' es''] eqn:eqles; inv h.
    eapply lift_e_expr_big_step in eql as (evs & hevs & ihevs); eauto.
    assert (hl'evs : length l' = length evs)
      by eauto using eval_decl_list_length.
    rewrite hl'evs, <- app_length in eqles.
    apply ihesvs in eqles as (esvs & h & ih).
    repeat rewrite <- app_assoc in *.
    exists (esvs ++ evs). rewrite <- app_assoc.
    assert (hles'esvs : length les' = length esvs) by eauto.
    rewrite hles'esvs; split; eauto.
Qed.

(* TODO: need better lemma for l-expressions. *)
Theorem lift_e_lexpr_big_step : forall e lv,
    e ⇓ₗ lv ->
    forall us l e',
      lift_e (length us) e = (l, e') ->
      exists lv', e' ⇓ₗ lv' /\ forall ϵ, exists vs,
          eval_decl_list (us ++ ϵ) l vs /\
            lv_lookup ϵ lv = lv_lookup (vs ++ us ++ ϵ) lv'.
Proof.
  intros e lv helv; induction helv;
    intros us l e' h; unravel in *.
  - inv h. exists (Val.Var (length us + x)); split; unravel; auto.
    intro ϵ. exists []; cbn; split; auto.
    rewrite ForallMap.nth_error_app3; reflexivity.
  - destruct (lift_e (length us) e) as [le e''] eqn:eqle; inv h.
    apply IHhelv in eqle as (lv' & he'lev' & ih); clear IHhelv.
    eexists; split; eauto. intro ϵ.
    specialize ih with ϵ.
    destruct ih as (vs & hvs & ih).
    (* TODO: don't have enough evidence
       that [e] may be evaluated under [ϵ].
       Perhaps typing needs to be an assumption
       then use progress? *)
    admit.
  - destruct (lift_e (length us) e) as [le e''] eqn:eqle; cbn in *; inv h.
    rename e'' into e'.
    apply IHhelv in eqle as (lv' & he'lv' & ih).
    eexists; split; eauto.
    intro ϵ. specialize ih with ϵ.
    destruct ih as (vs & hvs & ih).
    eexists; split; eauto; unravel.
    rewrite ih; reflexivity.
Abort.

(* TODO: need better lemma for l-expressions. *)
Lemma lift_arg_big_step : forall arg varg ϵ,
    rel_paramarg (expr_big_step ϵ) lexpr_big_step arg varg ->
    forall us l arg',
      lift_arg (length us) arg = (l, arg') ->
      exists vs, eval_decl_list (us ++ ϵ) l vs /\ exists varg',
          rel_paramarg
            (expr_big_step (vs ++ us ++ ϵ))
            lexpr_big_step arg' varg' /\
            rel_paramarg
              eq (fun lv lv' =>
                    lv_lookup ϵ lv = lv_lookup (vs ++ us ++ ϵ) lv')
              varg varg'.
Proof.
  intros [e | e | e] [v | lv | lv] ϵ heval us l [e' | e' | e'] h;
    unravel in *; try contradiction;
    destruct (lift_e (length us) e) as [le ?] eqn:eqle; inv h.
  - eapply lift_e_expr_big_step in eqle as (vs & hvs & ih); eauto.
    eexists; split; eauto. exists (PAIn v); auto.
  - Fail eapply lift_e_lexpr_big_step in eqle; eauto.
  (* destruct eqle as (lv' & he'lv' & ih).
    specialize ih with ϵ.
    destruct ih as (vs & hvs & ih).
    eexists; split; eauto.
    exists (PAOut lv'); auto. *) admit.
  - Fail eapply lift_e_lexpr_big_step in eqle; eauto.
  (* destruct eqle as (lv' & he'lv' & ih).
    specialize ih with ϵ.
    destruct ih as (vs & hvs & ih).
    eexists; split; eauto.
    exists (PAInOut lv'); auto. *) admit.
Abort.

(* TODO: need better lemma for l-expressions. *)
Lemma lift_args_big_step : forall args vargs ϵ,
    Forall2
      (rel_paramarg
         (expr_big_step ϵ)
         lexpr_big_step)
      args vargs ->
    forall us largs args',
      lift_args (length us) args = (largs, args') ->
      exists vs,
        eval_decl_list (us ++ ϵ) largs vs /\ exists vargs',
          Forall2
            (rel_paramarg
               (expr_big_step (vs ++ us ++ ϵ))
               lexpr_big_step) args' vargs'
          /\ Forall2
              (rel_paramarg
                 eq (fun lv lv' =>
                       lv_lookup ϵ lv = lv_lookup (vs ++ us ++ ϵ) lv'))
              vargs vargs'.
Proof.
  intros args vargs ϵ h;
    induction h as [| arg varg args vargs harg hargs ih];
    intros us largs args' h; unravel in h.
  - inv h; eexists; split; eauto.
  - destruct (lift_arg (length us) arg) as [larg arg'] eqn:eqlarg.
    destruct (lift_args (length larg + length us) args)
      as [largs'' args''] eqn:eqlargs; inv h.
    rename largs'' into largs; rename args'' into args'.
    Fail eapply lift_arg_big_step in eqlarg; eauto.
  (* destruct eqlarg as (argvs & hargvs & varg' & hvarg' & ihvarg').
    assert (hlargargvs : length larg = length argvs) by eauto.
    rewrite hlargargvs, <- app_length in eqlargs.
    apply ih in eqlargs as (argsvs & hargsvs & vargs' & hvargs' & ihvargs').
    assert (hlargsargsvs : length largs = length argsvs) by eauto.
    rewrite <- app_assoc in *; eexists; split; eauto.
    rewrite <- app_assoc. rewrite hlargsargsvs.
    exists (varg' :: vargs'); split.
    + constructor; auto. (* TODO: helper lemma. *) admit.
    + constructor; auto. *)
Abort.

Local Hint Constructors parser_expr_big_step : core.

Lemma lift_trans_parser_expr_big_step : forall ϵ e st,
    p⟨ ϵ, e ⟩ ⇓ st ->
    forall us l e',
      lift_trans (length us) e = (l, e') ->
      exists vs, eval_decl_list (us ++ ϵ) l vs /\ p⟨ vs ++ us ++ ϵ, e' ⟩ ⇓ st.
Proof.
  intros ϵ e st hp us l e' h; inv hp; unravel in *.
  - inv h; eexists; split; eauto.
  - rename e0 into e.
    destruct (lift_e (length us) e) as [le ee'] eqn:eqle.
    eapply lift_e_expr_big_step in eqle as (vs & hvs & ihvs); eauto; inv h.
    eexists; split; eauto.
Qed.

(** Specification of [unwind_vars]. *)
Lemma eval_decl_list_unwind_vars : forall es vs ϵ,
    eval_decl_list ϵ es vs ->
    forall vs' ϵ' Ψ s sig ψ,
      length vs = length vs' ->
      ⧼ Ψ, vs ++ ϵ, s ⧽ ⤋ ⧼ vs' ++ ϵ', sig, ψ ⧽ ->
      ⧼ Ψ, ϵ, unwind_vars es s ⧽ ⤋ ⧼ ϵ', sig, ψ ⧽.
Proof.
  unfold unwind_vars.
  intros es vs ϵ hedl; induction hedl;
    intros [| v' vs'] ϵ' Ψ s sig ψ hvs hs;
    cbn in *; try discriminate; auto.
  inv hvs; eapply IHhedl; eauto.
Qed.

Local Hint Resolve eval_decl_list_unwind_vars : core.

Lemma lift_s_stmt_big_step : forall Ψ ϵ ϵ' s sig ψ,
    ⧼ Ψ , ϵ , s ⧽ ⤋ ⧼ ϵ' , sig , ψ ⧽ -> forall us,
      ⧼ Ψ , us ++ ϵ , lift_s (length us) s ⧽ ⤋ ⧼ us ++ ϵ' , sig , ψ ⧽.
Proof.
  intros Ψ ϵ ϵ' s sig ψ hs; induction hs;
    intro us; unravel; eauto.
  - destruct eo as [e |]; inv H; auto.
    destruct (lift_e (length us) e) as [le e'] eqn:eqle.
    eapply lift_e_expr_big_step in eqle as (levs & hlevs & ihlevs); eauto.
  - destruct (lift_e (length us) e₁) as [l₁ e₁'] eqn:eql1.
    destruct (lift_e (length l₁ + length us) e₂) as [l₂ e₂'] eqn:eql2.
    (* TODO: need l-expression lemma for lifting. *) admit.
  - (* TODO: lemma for fun kind. *) admit.
  - (* TODO: need l-expression lemma for lifting. *) admit.
  - destruct te as [τ | e].
    + specialize IHhs with us.
      (* TODO: lemma for stmt evaluation
         that [length ϵ = length ϵ']. *) admit.
    + destruct (lift_e (length us) e) as [le e'] eqn:eqle.
      eapply lift_e_expr_big_step in eqle
          as (vs & hvs & he'); eauto.
      (* TODO: lemma for stmt evaluation
         that [length ϵ = length ϵ']. *) admit.
  - destruct (lift_e (length us) e) as [le e'] eqn:eqle.
      eapply lift_e_expr_big_step in eqle
          as (vs & hvs & he'); eauto.
      assert (hlevs : length le = length vs) by eauto.
      rewrite hlevs, <- app_length.
      specialize IHhs with (us := vs ++ us).
      do 2 rewrite <- app_assoc in IHhs.
      rewrite ssrbool.fun_if in IHhs.
      eapply eval_decl_list_unwind_vars; eauto.
Admitted.
