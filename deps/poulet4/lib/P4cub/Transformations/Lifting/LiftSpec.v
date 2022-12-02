Require Export Coq.Lists.List
  Coq.Arith.PeanoNat
  Poulet4.Utils.ForallMap
  Poulet4.P4cub.Syntax.Syntax
  Poulet4.P4cub.Syntax.Shift
  Poulet4.P4cub.Transformations.Lifting.Statementize.
Import ListNotations Nat.

Section RelateDeclList.
  Polymorphic Universes a b.
  
  Polymorphic Context {A : Type@{a}} {B : Type@{b}}.
  Polymorphic Variable R : list A -> B -> A -> Prop.
  Polymorphic Variable l : list A.
  
  Polymorphic Inductive relate_decl_list : list B -> list A -> Prop :=
  | relate_decl_list_nil :
    relate_decl_list [] []
  | relate_decl_list_cons hb ha tb ta :
    R (ta ++ l) hb ha ->
    relate_decl_list tb ta ->
    relate_decl_list (hb :: tb) (ha :: ta).

  Polymorphic Lemma relate_decl_list_length : forall lb la,
      relate_decl_list lb la -> length lb = length la.
  Proof using.
    intros lb la h; induction h; cbn; auto.
  Qed.
End RelateDeclList.

Section RelateExprDeclList.
  Polymorphic Universe a.
  Polymorphic Context {A : Type@{a}}.
  Polymorphic Variable R : list A -> Expr.e -> A -> Prop.
  Polymorphic Variable l : list A.

  Polymorphic Hypothesis shift_e_preserves_R : forall as1 as2 as3 a e,
      R (as1 ++ as3) e a ->
      R (as1 ++ as2 ++ as3) (shift_e (Shifter (length as1) (length as2)) e) a.

  Local Hint Constructors relate_decl_list : core.
  
  Polymorphic Lemma relate_decl_list_app : forall es1 es2 as1 as2,
      relate_decl_list R l es1 as1 ->
      relate_decl_list R l es2 as2 ->
      relate_decl_list R l (shift_list shift_e (Shifter 0 (length es1)) es2 ++ es1) (as2 ++ as1).
  Proof using A R l shift_e_preserves_R.
    intros es1 es2 as1 as2 h1 h2.
    generalize dependent as1.
    generalize dependent es1.
    induction h2; intros es1 as1 h1; cbn; auto.
    unfold smother, RecordSet.set; cbn.
    rewrite add_0_r.
    constructor; auto. rewrite <- app_assoc.
    rewrite (relate_decl_list_length _ _ _ _ h1).
    rewrite (relate_decl_list_length _ _ _ _ h2).
    eauto.
  Qed.

  Local Hint Resolve relate_decl_list_app : core.
  
  Polymorphic Lemma shift_pairs_relate_snd : forall ess ass,
      Forall2 (relate_decl_list R l) (map snd ess) ass ->
      relate_decl_list R l
        (concat (map snd (shift_pairs shift_e ess)))
        (concat ass).
  Proof using A R l shift_e_preserves_R.
    intros ess vss h.
    remember (map snd ess) as sess eqn:hess.
    generalize dependent ess.
    induction h; intros [| [e es] ess] hess; inv hess;
      unravel in *; auto.
    pose proof IHh ess ltac:(auto) as ih; clear IHh.
    rewrite map_snd_map, map_id.
    assert (list_sum (map (length (A:=Expr.e)) (map snd ess))
            = length (concat (map snd (shift_pairs shift_e ess)))) as hlen.
    { unfold list_sum.
      rewrite sublist.length_concat.
      rewrite shift_pairs_inner_length.
      reflexivity. }
    rewrite hlen. auto.
  Qed.

  Polymorphic Lemma shift_pairs_relate_fst : forall es ess vs vss,
      length es = length ess ->
      Forall3 (fun vs e v => R (vs ++ l) e v) vss es vs ->
      Forall2 (relate_decl_list R l) ess vss ->
      Forall2
        (R (concat vss ++ l))
        (map fst (shift_pairs shift_e (combine es ess))) vs.
  Proof using A R l shift_e_preserves_R.
    intros es ess vs vss hl hF3.
    generalize dependent ess.
    induction hF3; intros [| E ess] hl hF2;
      inv hF2; unravel in *; auto; try discriminate.
    inv hl.
    rewrite <- app_assoc.
    rewrite map_snd_combine by assumption.
    rewrite map_fst_map.
    unfold list_sum.
    rewrite <- sublist.length_concat.
    assert (hlen : length (concat ess) = length (concat ts)).
    { rewrite <- map_snd_combine with (us := us) (vs := ess)
        in H5 by assumption.
      apply shift_pairs_relate_snd in H5.
      apply relate_decl_list_length in H5.
      rewrite sublist.length_concat in H5 at 1.
      rewrite shift_pairs_inner_length in H5.
      rewrite <- sublist.length_concat in H5.
      rewrite <- H5.
      rewrite map_snd_combine by eauto.
      reflexivity. }
    rewrite hlen.
    rewrite (relate_decl_list_length _ _ _ _ H3).
    constructor; auto using shift_e_preserves_R.
    pose proof IHhF3 _ H1 H5 as ih; clear IHhF3.
    clear dependent v.
    clear dependent E.
    clear dependent u.
    clear hlen H5 hF3.
    rewrite Forall2_forall_nth_error in *.
    destruct ih as [hlen ih].
    split.
    - repeat rewrite map_length in *.
      assumption.
    - intros n e v he hv.
      rewrite nth_error_map in he.
      destruct (nth_error (map fst (shift_pairs shift_e (combine us ess))) n)
        as [se |] eqn:hse;
        cbn in *;
        try discriminate.
      inv he.
      pose proof ih _ _ _ hse hv as h.
      pose proof shift_e_preserves_R [] t0 _ _ _ h as H;
        cbn in H.
      assumption.
  Qed.
End RelateExprDeclList.
