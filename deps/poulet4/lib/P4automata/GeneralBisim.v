Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.

Section GeneralBisim.
  Variables (Q A: Type).

  Record automaton :=
    { o: Q -> Prop;
      d: Q -> A -> Q; }.

  Variable (aut: automaton).

  Notation rel := (relation Q).

  Definition sat_rels (l: list rel) (q1 q2: Q) :=
    forall C, In C l -> C q1 q2
  .

  CoInductive bisimilar : rel :=
  | Bisimilar:
      forall q1 q2,
        (o aut q1 <-> o aut q2) ->
        (forall a, bisimilar (d aut q1 a) (d aut q2 a)) ->
        bisimilar q1 q2
  .

  Fixpoint follow (q: Q) (w: list A) :=
    match w with
    | nil => q
    | a :: w =>
      follow (d aut q a) w
    end
  .

  Definition lang_equiv (q1 q2: Q): Prop :=
    forall (w : list A), o aut (follow q1 w) <-> o aut (follow q2 w)
  .

  Lemma lang_equiv_implies_bisimilar :
    forall q1 q2, lang_equiv q1 q2 -> bisimilar q1 q2
  .
  Proof.
    cofix R.
    intros.
    apply Bisimilar.
    - apply (H nil).
    - intros.
      apply R.
      intro w.
      change (follow (d aut q1 a) w) with (follow q1 (a :: w)).
      change (follow (d aut q2 a) w) with (follow q2 (a :: w)).
      apply H.
  Qed.

  Lemma bisimilar_implies_lang_equiv :
    forall q1 q2, bisimilar q1 q2 -> lang_equiv q1 q2
  .
  Proof.
    intros.
    intro w.
    revert q1 q2 H.
    induction w; intros.
    - inversion H.
      simpl.
      apply H0.
    - simpl.
      apply IHw.
      inversion H.
      apply H1.
  Qed.

  Inductive pre_bisimulation : list rel -> list rel -> rel :=
  | PreBisimulationClose:
      forall R q1 q2,
        sat_rels R q1 q2 ->
        pre_bisimulation R nil q1 q2
  | PreBisimulationSkip:
      forall (R T: list rel) (C: rel) q1 q2,
        pre_bisimulation R T q1 q2 ->
        (forall q1 q2, sat_rels R q1 q2 -> C q1 q2) ->
        pre_bisimulation R (C :: T) q1 q2
  | PreBisimulationExtend:
      forall (R T E: list (Q -> Q -> Prop)) (C: Q -> Q -> Prop) q1 q2,
        pre_bisimulation (C :: R) (T ++ E) q1 q2 ->
        (forall q1 q2, sat_rels E q1 q2 -> (forall a, C (d aut q1 a) (d aut q2 a))) ->
        pre_bisimulation R (C :: T) q1 q2
  .

  Lemma pre_bisimulation_implies_bisimulation :
    forall R T,
      (forall q1 q2, sat_rels (R ++ T) q1 q2 -> o aut q1 <-> o aut q2) ->
      (forall q1 q2, sat_rels (R ++ T) q1 q2 -> forall a, sat_rels R (d aut q1 a) (d aut q2 a)) ->
      forall q1 q2,
        pre_bisimulation R T q1 q2 ->
        bisimilar q1 q2
  .
  Proof.
    intros.
    induction H1.
    - revert q1 q2 H1.
      cofix CH; intros.
      apply Bisimilar.
      + apply H.
        rewrite app_nil_r.
        apply H1.
      + intros.
        apply CH.
        apply H0.
        rewrite app_nil_r.
        apply H1.
    - apply IHpre_bisimulation.
      + intros.
        apply H.
        intros ? ?.
        apply in_app_or in H4.
        destruct H4.
        * apply H3.
          apply in_app_iff.
          left.
          apply H4.
        * destruct H4.
          -- subst.
             apply H2.
             intros ? ?.
             apply H3.
             apply in_app_iff.
             left.
             apply H4.
          -- apply H3.
             apply in_app_iff.
             right.
             apply H4.
      + intros.
        apply H0.
        intros ? ?.
        apply in_app_or in H4.
        destruct H4.
        * apply H3.
          apply in_app_iff.
          left.
          apply H4.
        * destruct H4.
          -- subst.
             apply H2.
             intros ? ?.
             apply H3.
             apply in_app_iff.
             left.
             apply H4.
          -- apply H3.
             apply in_app_iff.
             right.
             apply H4.
    - apply IHpre_bisimulation.
      + intros.
        apply H.
        intros ? ?.
        apply H3.
        rewrite in_app_iff in H4.
        destruct H4.
        * apply in_app_iff.
          left.
          right.
          apply H4.
        * destruct H4.
          -- subst.
             apply in_app_iff.
             left.
             left.
             reflexivity.
          -- apply in_app_iff.
             right.
             apply in_app_iff.
             left.
             apply H4.
      + intros.
        intros ? ?.
        destruct H4.
        * subst.
          apply H2.
          intros ? ?.
          apply H3.
          apply in_app_iff; right.
          apply in_app_iff; right.
          apply H4.
        * apply H0; auto.
          intros ? ?.
          apply in_app_iff in H5.
          destruct H5.
          -- apply H3.
             apply in_app_iff.
             left.
             right.
             apply H5.
          -- destruct H5.
             ++ subst.
                apply H3.
                apply in_app_iff.
                left.
                left.
                reflexivity.
             ++ apply H3.
                apply in_app_iff.
                right.
                apply in_app_iff.
                left.
                apply H5.
  Qed.

  Lemma pre_bisimulation_implies_bisimulation' :
    forall q1 q2,
      pre_bisimulation nil ((fun q1 q2 => o aut q1 <-> o aut q2) :: nil) q1 q2 ->
      bisimilar q1 q2
  .
  Proof.
    apply pre_bisimulation_implies_bisimulation.
    - intros.
      apply H.
      simpl.
      auto.
    - intros.
      intros ? ?.
      destruct H0.
  Qed.

  Lemma bisimulation_implies_pre_bisimulation :
    forall q1 q2,
      bisimilar q1 q2 ->
      pre_bisimulation nil (bisimilar :: nil) q1 q2
  .
  Proof.
    intros.
    apply PreBisimulationExtend with (E := (bisimilar :: nil)).
    - apply PreBisimulationSkip.
      + apply PreBisimulationClose.
        intros ? ?.
        destruct H0; subst; easy.
      + intros.
        apply H0.
        left.
        reflexivity.
    - intros.
      specialize (H0 (bisimilar)).
      destruct H0.
      + now left.
      + apply H1.
  Qed.

End GeneralBisim.

Module BisimExample.
  Inductive Q' :=
  | Qleft
  | Qright
  | Qaccept.

  Inductive A' :=
  | Zero
  | One.

  Definition aut : automaton Q' A' :=
    {| o := fun q => q = Qaccept;
       d := fun q a => Qaccept |}.

  Definition R0 x y := (x = Qaccept <-> y = Qaccept).
  Hint Unfold R0.
  Definition R x y := (x = Qaccept <-> y = Qaccept) \/ x = Qleft /\ y = Qright.
  Hint Unfold R.
  Notation rr := (R0 :: R :: nil).

  Lemma prebisim_example:
    bisimilar _ _ aut Qleft Qright.
  Proof.
    assert (pre_bisimulation Q' A' aut rr nil Qleft Qright).
    {
      eapply PreBisimulationClose.
      unfold sat_rels; intros.
      invlist In; subst.
      - firstorder congruence.
      - firstorder.
    }
    eapply pre_bisimulation_implies_bisimulation; eauto.
    - intros.
      simpl in H0.
      unfold sat_rels in H0.
      assert (R q1 q2).
      { eapply H0; eauto with datatypes. }
      unfold R in H1.
      intuition congruence.
    - simpl (_ ++ _).
      intros.
      simpl in *.
      unfold sat_rels; intros.
      invlist In; subst.
      + intuition.
      + intuition.
  Qed.

End BisimExample.
