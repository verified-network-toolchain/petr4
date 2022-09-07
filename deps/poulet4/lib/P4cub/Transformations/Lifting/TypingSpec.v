Require Export Coq.micromega.Lia
        Poulet4.P4cub.Syntax.Syntax
        Poulet4.Utils.ForallMap.
From Poulet4.P4cub Require Export Semantics.Static.Static
     Semantics.Static.Auxiliary
     Transformations.Lifting.Statementize.
Import AllCubNotations.

(** Typing specification for lifting in [Statementize.v] *)

Inductive type_decl_list (Δ : nat) (Γ : list Expr.t)
  : list Expr.e -> list Expr.t -> Prop :=
| type_decl_nil :
  type_decl_list Δ Γ [] []
| type_decl_cons h hτ t tτ :
  {|type_vars:=Δ;types:=tτ ++ Γ|} ⊢ₑ h ∈ hτ ->
  type_decl_list Δ Γ t tτ ->
  type_decl_list Δ Γ (h :: t) (hτ :: tτ).

Local Hint Constructors type_decl_list : core.

Lemma type_decl_list_length : forall Δ Γ l τs,
    type_decl_list Δ Γ l τs -> length l = length τs.
Proof.
  intros Δ Γ l τs h; induction h; cbn; auto.
Qed.

Local Hint Resolve type_decl_list_length : core.

Lemma type_decl_list_append : forall Δ Γ τs1 τs2 l1 l2,
    type_decl_list Δ Γ l1 τs1 ->
    type_decl_list Δ (τs1 ++ Γ) l2 τs2 ->
    type_decl_list Δ Γ (l2 ++ l1) (τs2 ++ τs1).
Proof.
  intros Δ Γ ts1 ts2.
  generalize dependent ts1.
  induction ts2 as [| t2 ts2 ih];
    intros ts1 l1 [| e2 l2] h1 h2; inv h2; cbn; auto.
  constructor; eauto.
  rewrite <- app_assoc; assumption.
Qed.

Local Hint Resolve type_decl_list_append : core.
Local Hint Constructors type_expr : core.

Lemma shift_type : forall τs Γ e τ,
    Γ ⊢ₑ e ∈ τ ->
    {|type_vars:=type_vars Γ;types:=τs ++ types Γ|}
      ⊢ₑ Shift.rename_e (Nat.add (length τs)) e ∈ τ.
Proof.
  intros ts Γ e t het.
  induction het using custom_type_expr_ind; unravel in *; eauto.
  - constructor; auto; unravel.
    rewrite nth_error_app3; assumption.
  - econstructor; eauto.
  - econstructor; eauto.
    rewrite <- Forall2_map_l; unravel; assumption.
Qed.

Local Hint Resolve shift_type : core.

Lemma shift_type' : forall Δ τs Γ e τ,
    {|type_vars:=Δ;types:=Γ|} ⊢ₑ e ∈ τ ->
    {|type_vars:=Δ;types:=τs ++ Γ|}
      ⊢ₑ Shift.rename_e (Nat.add (length τs)) e ∈ τ.
Proof.
  intros Δ ts Γ e t; apply shift_type.
Qed.

Local Hint Resolve shift_type' : core.
Local Hint Constructors relop : core.
Local Hint Constructors t_ok : core.
Local Hint Resolve type_array : core.
Local Hint Resolve type_struct : core.
Local Hint Resolve type_header : core.
Local Hint Constructors type_lists_ok : core.
Local Hint Constructors t_ok_lists : core.

Theorem lift_e_type_expr : forall Γ e τ,
    Forall (t_ok (type_vars Γ)) (types Γ) ->
    Γ ⊢ₑ e ∈ τ -> forall us l e',
      lift_e (length us) e = (l, e') -> exists τs,
        type_decl_list (type_vars Γ) (us ++ types Γ) l τs
        /\ {| type_vars := type_vars Γ
          ;  types     := τs ++ us ++ types Γ
          |} ⊢ₑ e' ∈ τ.
Proof.
  intros Γ e t hΓ het;
    induction het using custom_type_expr_ind;
    intros us l e' h; unravel in *.
  - inv h; eauto.
  - inv h; unravel; eauto 6.
  - inv h; unravel; eauto 6.
  - inv h; unravel.
    eexists; split; eauto; unravel.
    constructor; unravel; auto.
    rewrite nth_error_app3; assumption.
  - destruct (lift_e (length us) e) as [le eₛ] eqn:eqle; inv h.
    apply IHhet in eqle as (ts & hts & ih); auto; clear IHhet.
    eexists; split; eauto.
  - destruct (lift_e (length us) e) as [le eₛ] eqn:eqle; inv h.
    apply IHhet in eqle as (ts & hts & ih); auto; clear IHhet.
    eexists; split; eauto.
  - destruct (lift_e (length us) e) as [le eₛ] eqn:eqle; inv h.
    apply IHhet in eqle as (ts & hts & ih); auto; clear IHhet.
    eexists; split; eauto.
  - destruct (lift_e (length us) e₁) as [l1 e1] eqn:eql1.
    destruct (lift_e (length l1 + length us) e₂) as [l2 e2] eqn:eql2; inv h.
    apply IHhet1 in eql1 as (ts1 & hts1 & ih1); auto; clear IHhet1.
    assert (hl1ts1 : length l1 = length ts1) by eauto.
    rewrite hl1ts1, <- app_length in eql2.
    apply IHhet2 in eql2 as (ts2 & hts2 & ih2); auto; clear IHhet2.
    rewrite <- app_assoc in *.
    assert (hl2ts2 : length l2 = length ts2) by eauto.
    rewrite hl2ts2.
    exists (τ :: ts2 ++ ts1); split; auto.
    constructor; eauto; rewrite <- app_assoc; eauto.
  - destruct (lift_e (length us) e₁) as [l1 e1] eqn:eql1.
    destruct (lift_e (length l1 + length us) e₂) as [l2 e2] eqn:eql2; inv h.
    apply IHhet1 in eql1 as (ts1 & hts1 & ih1); auto; clear IHhet1.
    assert (hl1ts1 : length l1 = length ts1) by eauto.
    rewrite hl1ts1, <- app_length in eql2.
    apply IHhet2 in eql2 as (ts2 & hts2 & ih2); auto; clear IHhet2.
    rewrite <- app_assoc in *.
    assert (hl2ts2 : length l2 = length ts2) by eauto.
    rewrite hl2ts2.
    exists (ts2 ++ ts1); split; auto.
    econstructor; eauto; rewrite <- app_assoc; eauto.
  - destruct (lift_e (length us) e) as [le eₛ] eqn:eqle; inv h.
    apply IHhet in eqle as (ts & hts & ih); auto; clear IHhet.
    eexists; split; eauto.
  - destruct
      (lift_list lift_e Shift.rename_e (length us) es)
      as [les es'] eqn:eqles; inv h.
    assert (bruh : exists τs',
               type_decl_list (type_vars Γ) (us ++ types Γ) les τs'
               /\ Forall2
                   (type_expr
               {| type_vars:=type_vars Γ
               ;  types := (τs' ++ us ++ types Γ) |})
                   es' τs).
    { clear dependent ls.
      generalize dependent es';
        generalize dependent les;
        generalize dependent us.
      induction H1 as [| e t es τs heτ hesτs ihesτs];
        inv H2; intros us les es' h; unravel in *.
      - inv h; eauto.
      - destruct (lift_e (length us) e) as [le e'] eqn:eqle.
        destruct
          (lift_list lift_e Shift.rename_e (length le + length us) es)
          as [les' es''] eqn:eqles; inv h.
        rename les' into les. rename es'' into es'.
        apply H3 in eqle as (ets & hets & ihets); auto; clear H3.
        assert (hleets : length le = length ets) by eauto.
        rewrite hleets, <- app_length in eqles.
        eapply ihesτs in eqles as (ts' & hts' & ih); eauto; clear ihesτs.
        rewrite <- app_assoc in *.
        exists (ts' ++ ets); split; eauto.
        assert (hlests' : length les = length ts') by eauto.
        rewrite hlests'.
        constructor; rewrite <- app_assoc; eauto. }
    destruct bruh as (τs' & htτs' & ih).
    eexists; split; eauto; unravel.
    assert (hok: t_ok (type_vars Γ) (Expr.TStruct false τs))
      by eauto using type_expr_t_ok; inv hok.
    assert (bruh : map t_of_e es = τs).
    { rewrite Forall2_forall in H1.
      pose proof conj
           (proj1 H1)
           (fun e τ hin => t_of_e_correct Γ e τ (proj2 H1 e τ hin)) as duh.
      rewrite <- Forall2_forall in duh; clear H1.
      rewrite ForallMap.Forall2_map_l,Forall2_eq in duh; assumption. }
    rewrite bruh.
    inv H; inv H0; unravel in *; try contradiction; eauto.
    apply f_equal with (f := @List.length _) in H.
    rewrite map_length, repeat_length in H.
    rewrite <- H, Nnat.N2Nat.id; eauto.
  - inv h; eauto.
Qed.

Lemma lift_e_list_type_expr : forall Γ es τs,
    Forall (t_ok (type_vars Γ)) (types Γ) ->
    Forall2 (type_expr Γ) es τs -> forall us les es',
      lift_e_list (length us) es = (les, es') -> exists τs',
        type_decl_list (type_vars Γ) (us ++ types Γ) les τs'
        /\ Forall2
            (type_expr
               {| type_vars:=type_vars Γ
               ;  types := (τs' ++ us ++ types Γ) |})
            es' τs.
Proof.
  intros G es ts hG hets;
    induction hets as [| e t es ts het hests ih];
    intros us les es' h; unravel in *.
  - inv h; eauto.
  - destruct (lift_e (length us) e) as [le e'] eqn:eqle.
    destruct (lift_e_list (length le + length us) es)
      as [les'' es''] eqn:eqles; inv h.
    rename les'' into les; rename es'' into es'.
    eapply lift_e_type_expr in eqle as (ets & hets & he); eauto.
    assert (hleets : length le = length ets) by eauto.
    rewrite hleets, <- app_length in eqles.
    apply ih in eqles as (τs & hτs & ihτs); clear ih.
    rewrite <- app_assoc in *.
    exists (τs ++ ets); split; eauto.
    assert (hlesτs : length les = length τs) by eauto.
    rewrite hlesτs.
    constructor; rewrite <- app_assoc; eauto.
Qed.
