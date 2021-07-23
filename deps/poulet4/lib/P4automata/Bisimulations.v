Require Import Coq.micromega.Lia.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Import List.ListNotations.

Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Import Poulet4.Relations.
Require Poulet4.P4automata.WP.
Require Poulet4.P4automata.WPSymBit.
Require Poulet4.P4automata.WPSymLeap.
Require Poulet4.P4automata.Reachability.
Require Poulet4.P4cub.Util.Utiliser.

Module SemBisim.
  Section SemBisim.
    Variable (a: p4automaton).
    Notation conf := (configuration a).

    Definition bisimulation (R: rel conf) :=
      forall q1 q2,
        R q1 q2 ->
        (accepting q1 <-> accepting q2) /\
        forall b, R (step q1 b) (step q2 b).

    Definition bisimilar q1 q2 :=
      exists R, bisimulation R /\ R q1 q2.

    Lemma bisimilar_implies_equiv :
      forall (c1 c2: conf),
        bisimilar c1 c2 ->
        lang_equiv c1 c2.
    Proof.
      intros.
      unfold lang_equiv.
      intros; revert c1 c2 H.
      induction input; intros.
      - unfold accepted.
        simpl.
        unfold bisimilar in H.
        destruct H as [R [? ?]].
        now apply H in H0.
      - unfold accepted.
        repeat rewrite follow_cons.
        apply IHinput.
        unfold bisimilar in H.
        destruct H as [R [? ?]].
        exists R.
        apply H in H0.
        easy.
    Qed.

    Lemma lang_equiv_is_bisimulation :
        bisimulation lang_equiv
    .
    Proof.
      unfold bisimulation; intros.
      split.
      - apply (H nil).
      - intros.
        unfold lang_equiv.
        intros.
        unfold accepted.
        repeat rewrite <- follow_cons.
        apply H.
    Qed.

    Lemma equiv_implies_bisimilar
          (c1 c2: conf)
      :
        lang_equiv c1 c2 -> bisimilar c1 c2
    .
    Proof.
      intros.
      exists lang_equiv.
      split; try easy.
      apply lang_equiv_is_bisimulation.
    Qed.

    Theorem bisimilar_iff_lang_equiv
            (c1 c2: conf)
      :
        lang_equiv c1 c2 <-> bisimilar c1 c2
    .
    Proof.
      split.
      - apply equiv_implies_bisimilar.
      - apply bisimilar_implies_equiv.
    Qed.

  End SemBisim.
End SemBisim.

Module SemBisimCoalg.
  Section SemBisimCoalg.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    CoInductive bisimilar : rel conf :=
    | Bisimilar:
        forall q1 q2,
          (accepting q1 <-> accepting q2) ->
          (forall b, bisimilar (step q1 b) (step q2 b)) ->
          bisimilar q1 q2
    .

    Lemma bisimilar_coalg_implies_sem_bisim:
      forall q1 q2,
        bisimilar q1 q2 ->
        SemBisim.bisimilar a q1 q2.
    Proof.
      intros.
      exists bisimilar.
      split.
      - unfold SemBisim.bisimulation.
        intros.
        inversion H0; firstorder.
      - tauto.
    Qed.

    Lemma sem_bisim_implies_bisimilar_coalg:
      forall q1 q2,
        SemBisim.bisimilar a q1 q2 ->
        bisimilar q1 q2.
    Proof.
      cofix C.
      intros.
      constructor.
      - unfold SemBisim.bisimulation in *.
        firstorder.
      - intros.
        eapply C.
        unfold SemBisim.bisimilar, SemBisim.bisimulation in *.
        firstorder.
    Qed.

  End SemBisimCoalg.
End SemBisimCoalg.

Module SemBisimUpto.
  Section SemBisimUpto.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    Definition bisimulation_upto
               (f: rel conf -> rel conf)
               (R: rel conf)
      :=
        forall c1 c2,
          R c1 c2 ->
          (accepting c1 <-> accepting c2) /\
          forall b, f R (step c1 b) (step c2 b)
    .

    Definition bisimilar_upto
               (f: rel conf -> rel conf)
               (c1 c2: conf)
      :=
        exists R, bisimulation_upto f R /\ R c1 c2
    .

    Definition closure_extends
               (close: rel conf -> rel conf)
      :=
        forall (R: rel conf) c1 c2,
          R c1 c2 -> close R c1 c2
    .

    Definition closure_preserves_accept
               (close: rel conf -> rel conf)
      :=
        forall (R: rel conf),
          (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
          (forall c1 c2, close R c1 c2 -> accepting c1 <-> accepting c2)
    .

    Definition closure_preserves_transition
               (close: rel conf -> rel conf)
      :=
        forall (R: rel conf),
          (forall c1 c2, R c1 c2 ->
                    forall b, close R (step c1 b) (step c2 b)) ->
          (forall c1 c2, close R c1 c2 ->
                    forall b, close R (step c1 b) (step c2 b))
    .

    Definition closure_mono
               (close: rel conf -> rel conf)
      :=
        forall (R R': rel conf),
          (forall c1 c2, R c1 c2 -> R' c1 c2) ->
          (forall c1 c2, close R c1 c2 -> close R' c1 c2)
    .

    Class SoundClosure
          (f: rel conf -> rel conf)
      := {
      closure_sound_extends: closure_extends f;
      closure_sound_preserves_accept: closure_preserves_accept f;
      closure_sound_preserves_transition: closure_preserves_transition f;
      closure_sound_mono: closure_mono f;
        }.

    Lemma bisimilar_implies_bisimilar_upto
          (f: rel conf -> rel conf)
      :
        SoundClosure f ->
        forall c1 c2,
          SemBisim.bisimilar a c1 c2 ->
          bisimilar_upto f c1 c2
    .
    Proof.
      intros.
      destruct H0 as [R [? ?]].
      exists R; split; auto.
      intros c1' c2' ?; split.
      - now apply H0.
      - intros.
        now apply H, H0.
    Qed.

    Lemma bisimilar_upto_implies_bisimilar
          (f: rel conf -> rel conf)
      :
        SoundClosure f ->
        forall c1 c2,
          bisimilar_upto f c1 c2 ->
          SemBisim.bisimilar a c1 c2
    .
    Proof.
      intros.
      destruct H0 as [R [? ?]].
      exists (f R); split.
      - intros c1' c2' ?; split.
        + revert c1' c2' H2.
          now apply H, H0.
        + revert c1' c2' H2.
          now apply H, H0.
      - now apply closure_sound_extends.
    Qed.

    (* Sanity check: the identity function is a valid closure. *)
    Definition close_id (R: rel conf) := R.

    Program Instance close_id_sound
      : SoundClosure close_id
    .
    Solve Obligations with firstorder.

  End SemBisimUpto.
End SemBisimUpto.

Module SemBisimLeaps.
  Section SemBisimLeaps.
    Variable (a: p4automaton).
    Notation conf := (configuration a).

    Inductive close_interpolate (R: rel conf) : rel conf :=
      | InterpolateBase:
          forall c1 c2,
            R c1 c2 -> close_interpolate _ c1 c2
      | InterpolateStep:
          forall s1 st1 buf1 s2 st2 buf2 b,
            close_interpolate R (inl s1, st1, buf1)
                                (inl s2, st2, buf2) ->
            length buf1 + 1 < size a s1 ->
            length buf2 + 1 < size a s2 ->
            (forall buf,
                length buf = min (size a s1 - length buf1)
                                 (size a s2 - length buf2) ->
                R (follow (inl s1, st1, buf1) buf)
                  (follow (inl s2, st2, buf2) buf)) ->
            close_interpolate R (inl s1, st1, buf1 ++ b :: nil)
                                (inl s2, st2, buf2 ++ b :: nil)
    .

    Program Instance close_interpolate_sound
      : SemBisimUpto.SoundClosure a close_interpolate
    .
    Next Obligation.
      eauto using InterpolateBase.
    Qed.
    Next Obligation.
      induction H0; firstorder.
    Qed.
    Next Obligation.
      revert b.
      induction H0; intros; eauto.
      repeat rewrite <- step_with_space; auto.
      destruct (le_lt_dec (Nat.min (size a s1 - length buf1)
                                   (size a s2 - length buf2)) 2).
      - apply InterpolateBase.
        rewrite <- follow_nil.
        rewrite <- follow_nil at 1.
        repeat rewrite <- follow_cons.
        apply H3.
        simpl length.
        lia.
      - repeat rewrite step_with_space;
          repeat rewrite app_length;
          simpl length;
          try lia.
        apply InterpolateStep;
          repeat rewrite app_length;
          simpl length;
          try lia.
        + repeat rewrite <- step_with_space; eauto.
        + intros.
          repeat rewrite <- follow_with_space; try lia.
          apply H3.
          simpl length.
          lia.
    Qed.
    Next Obligation.
      induction H0.
      - eauto using InterpolateBase.
      - eauto using InterpolateStep.
    Qed.

    Definition bisimulation_with_leaps
               (R: rel conf)
      :=
        forall c1 c2,
          R c1 c2 ->
          (accepting c1 <-> accepting c2) /\
          forall buf,
            length buf = min (min_step c1) (min_step c2) ->
            R (follow c1 buf) (follow c2 buf)
    .

    Definition bisimilar_with_leaps (c1 c2: conf) :=
      exists R,
        R c1 c2 /\ bisimulation_with_leaps R
    .
    
    Lemma bisimilar_with_leaps_implies_bisimilar_upto
          (c1 c2: conf)
      :
        bisimilar_with_leaps c1 c2 ->
        SemBisimUpto.bisimilar_upto a close_interpolate c1 c2
    .
    Proof.
      intros.
      destruct H as [R [? ?]].
      exists R.
      split; auto.
      intros c1' c2' ?; split.
      - now apply H0.
      - intros.
        rewrite <- follow_nil.
        rewrite <- follow_nil at 1.
        repeat rewrite <- follow_cons.
        destruct c1' as (([s1' | h1'], st1'), buf1'),
                        c2' as (([s2' | h2'], st2'), buf2').
        + destruct (Compare_dec.le_lt_dec 2 (min (min_step (inl s1', st1', buf1'))
                                                 (min_step (inl s2', st2', buf2')))).
          * repeat rewrite follow_with_space.
            all: unfold min_step; simpl in l; try lia.
            apply InterpolateStep; try lia.
            now apply InterpolateBase.
            intros.
            apply H0; auto.
            simpl min_step.
            lia.
          * apply InterpolateBase, H0; auto.
            simpl min_step in *.
            simpl length.
            lia.
        + apply InterpolateBase, H0; auto.
          simpl min_step in *.
          simpl length.
          lia.
        + apply InterpolateBase, H0; auto.
          simpl min_step in *.
          simpl length.
          lia.
        + apply InterpolateBase.
          apply H0; auto.
    Qed.

    Lemma bisimilar_implies_bisimilar_with_leaps
          (c1 c2: conf)
      :
        SemBisim.bisimilar a c1 c2 ->
        bisimilar_with_leaps c1 c2
    .
    Proof.
      intros.
      destruct H as [R [? ?]].
      exists R.
      split; auto.
      intros c1' c2' ?; split.
      - now apply H.
      - intros.
        clear H2.
        induction buf using rev_ind.
        + now repeat rewrite follow_nil.
        + unfold follow.
          repeat rewrite fold_left_app.
          fold (follow c1' buf).
          fold (follow c2' buf).
          simpl fold_left.
          now apply H.
    Qed.

    Theorem bisimilar_iff_bisimilar_with_leaps
            (c1 c2: conf)
      :
        SemBisim.bisimilar a c1 c2 <->
        bisimilar_with_leaps c1 c2
    .
    Proof.
      split; intro.
      - now apply bisimilar_implies_bisimilar_with_leaps.
      - apply SemBisimUpto.bisimilar_upto_implies_bisimilar with (f := close_interpolate).
        + apply close_interpolate_sound.
        + now apply bisimilar_with_leaps_implies_bisimilar_upto.
    Qed.

  End SemBisimLeaps.
End SemBisimLeaps.

Module SemPre.
  Section SemPre.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    Variable (i: rel conf).
    Variable (i_closed: forall x y b, i x y -> i (step x b) (step y b)). 

    Notation "⟦ x ⟧" := (interp_rels i x).
    Notation "R ⊨ S" := (forall q1 q2,
                            ⟦R⟧ q1 q2 ->
                            S q1 q2)
                          (at level 40).

    Reserved Notation "R ⇝ S" (at level 10).
    Inductive pre_bisimulation : rels conf -> rels conf -> rel conf :=
    | PreBisimulationClose:
        forall R q1 q2,
          ⟦R⟧ q1 q2 ->
          R ⇝ [] q1 q2
    | PreBisimulationSkip:
        forall R T (C: relation conf) q1 q2,
          R ⊨ C ->
          R ⇝ T q1 q2 ->
          R ⇝ (C :: T) q1 q2
    | PreBisimulationExtend:
        forall R T C W q1 q2,
          (C :: R) ⇝ (W ++ T) q1 q2 ->
          (forall q1 q2, ⟦W⟧ q1 q2 -> (forall bit, C (step q1 bit) (step q2 bit))) ->
          R ⇝ (C :: T) q1 q2
    where "R ⇝ S" := (pre_bisimulation R S).

    Lemma interp_rels_i:
      forall R x y,
        ⟦R⟧ x y ->
        i x y.
    Proof.
      induction R.
      - simpl in *.
        eauto.
      - simpl in *.
        firstorder.
    Qed.

    Lemma sem_pre_implies_sem_bisim' :
      forall R T,
        (forall q1 q2, ⟦R ++ T⟧ q1 q2 -> accepting q1 <-> accepting q2) ->
        (forall q1 q2, ⟦R ++ T⟧ q1 q2 -> forall b, ⟦R⟧ (step q1 b) (step q2 b)) ->
        forall q1 q2,
          pre_bisimulation R T q1 q2 ->
          SemBisimCoalg.bisimilar a q1 q2
    .
    Proof.
      intros.
      induction H1.
      - revert q1 q2 H1.
        cofix CH; intros.
        apply SemBisimCoalg.Bisimilar.
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
          eapply in_interp_rels; eauto using interp_rels_i.
          intros.
          apply in_app_or in H4.
          destruct H4.
          * eapply interp_rels_in in H3; eauto with datatypes.
          * destruct H4; subst.
            -- eapply H1.
               eauto using interp_rels_mono, interp_rels_i with datatypes.
            -- eapply interp_rels_in in H3; eauto with datatypes.
        + intros.
          apply H0.
          eapply in_interp_rels; eauto using interp_rels_i.
          intros.
          apply in_app_or in H4.
          destruct H4.
          * eapply interp_rels_in in H3; eauto with datatypes.
          * destruct H4; subst.
            -- eapply H1.
               eauto using interp_rels_mono, interp_rels_i with datatypes.
            -- eapply interp_rels_in in H3; eauto with datatypes.
      - apply IHpre_bisimulation.
        + intros.
          apply H.
          apply in_interp_rels; eauto using interp_rels_i.
          intros ? ?.
          eapply interp_rels_in in H3; eauto with datatypes.
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
               right.
               apply H4.
        + intros.
          eapply in_interp_rels;
            eauto using i_closed, interp_rels_i.
          intros ? ?.
          destruct H4.
          * subst.
            apply H2.
            eapply in_interp_rels;
              eauto using i_closed, interp_rels_i.
            intros ? ?.
            eapply interp_rels_in in H3; eauto with datatypes.
          * eapply interp_rels_in; try eassumption.
            eapply H0; auto.
            eapply in_interp_rels;
              eauto using i_closed, interp_rels_i.
            intros ? ?.
            eapply interp_rels_in in H3; eauto.
            apply in_app_iff in H5.
            destruct H5; eauto with datatypes.
            destruct H5; subst; eauto with datatypes.
    Qed.

    Lemma sem_pre_implies_sem_bisim :
      forall T,
        (forall q1 q2, ⟦T⟧ q1 q2 -> accepting q1 <-> accepting q2) ->
        forall q1 q2,
          pre_bisimulation [] T q1 q2 ->
          SemBisimCoalg.bisimilar a q1 q2.
    Proof.
      intros.
      eapply sem_pre_implies_sem_bisim' with (R:=[]) (T:=T); eauto.
      intros.
      apply i_closed.
      eauto using interp_rels_i.
    Qed.

  End SemPre.
End SemPre.

Module SemPreLeaps.
  Section SemPreLeaps.
    Variable (a: p4automaton).
    Notation conf := (configuration a).
    Variable (i: rel conf).
    Variable (i_closed: forall x y b, i x y -> i (step x b) (step y b)). 

    Notation "⟦ x ⟧" := (interp_rels i x).
    Notation "R ⊨ S" := (forall q1 q2,
                            ⟦R⟧ q1 q2 ->
                            S q1 q2)
                          (at level 40).

    Reserved Notation "R ⇝ S" (at level 10).
    Inductive pre_bisimulation : rels conf -> rels conf -> rel conf :=
    | PreBisimulationClose:
        forall R q1 q2,
          ⟦R⟧ q1 q2 ->
          R ⇝ [] q1 q2
    | PreBisimulationSkip:
        forall R T (C: relation conf) q1 q2,
          R ⊨ C ->
          R ⇝ T q1 q2 ->
          R ⇝ (C :: T) q1 q2
    | PreBisimulationExtend:
        forall R T C W q1 q2,
          (C :: R) ⇝ (W ++ T) q1 q2 ->
          (forall q1 q2, ⟦W⟧ q1 q2 -> (forall bit, C (step q1 bit) (step q2 bit))) ->
          R ⇝ (C :: T) q1 q2
    where "R ⇝ S" := (pre_bisimulation R S).

  End SemPreLeaps.
End SemPreLeaps.


Module SynPreSynWP.
  Section SynPreSynWP.

    (* State identifiers. *)
    Variable (S1: Type).
    Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
    Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

    Variable (S2: Type).
    Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
    Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

    Notation S := ((S1 + S2)%type).

    (* Header identifiers. *)
    Variable (H: Type).
    Context `{H_eq_dec: EquivDec.EqDec H eq}.
    Context `{H_finite: @Finite H _ H_eq_dec}.

    Variable (a: P4A.t S H).

    Variable (wp: P4A.t S H ->
                  conf_rel S H ->
                  list (conf_rel S H)).

    Notation conf := (configuration (P4A.interp a)).

    Variable (i: rel conf).
    Variable (i_closed: forall x y b, i x y -> i (step x b) (step y b)). 

    Notation "⟦ x ⟧" := (interp_crel i x).
    Notation "⦇ x ⦈" := (interp_conf_rel (a:=a) x).
    Notation "R ⊨ q1 q2" := (⟦R⟧ q1 q2) (at level 40).
    Notation "R ⊨ S" := (forall q1 q2, ⟦R⟧ q1 q2 -> ⦇S⦈ q1 q2) (at level 40).
    Notation δ := step.

    Reserved Notation "R ⇝ S" (at level 10).
    Inductive pre_bisimulation : crel S H -> crel S H -> relation conf :=
    | PreBisimulationClose:
        forall R q1 q2,
          ⟦R⟧ q1 q2 ->
          R ⇝ [] q1 q2
    | PreBisimulationSkip:
        forall (R T: crel S H) (C: conf_rel S H) q1 q2,
          R ⊨ C ->
          R ⇝ T q1 q2 ->
          R ⇝ (C :: T) q1 q2
    | PreBisimulationExtend:
        forall (R T: crel S H) (C: conf_rel S H) (W: crel S H) q1 q2,
          W = wp a C ->
          (C :: R) ⇝ (W ++ T) q1 q2 ->
          R ⇝ (C :: T) q1 q2
    where "R ⇝ S" := (pre_bisimulation R S).

    Fixpoint range (n: nat) :=
      match n with
      | 0 => []
      | Datatypes.S n => range n ++ [n]
      end.

    Definition not_accept1 (a: P4A.t S H) (s: S) : crel S H := 
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inr true; st_buf_len := 0 |};
                                 cs_st2 := {| st_state := inl s;    st_buf_len := n |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a s)).

    Definition not_accept2 (a: P4A.t S H) (s: S) : crel S H := 
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inl s;    st_buf_len := n |};
                                 cs_st2 := {| st_state := inr true; st_buf_len := 0 |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a s)).

    Definition init_rel (a: P4A.t S H) : crel S H := 
      List.concat (List.map (not_accept1 a) (enum S) ++
                            List.map (not_accept2 a) (enum S)).
    

    Definition sum_not_accept1 (a: P4A.t (S1 + S2) H) (s: S1) : crel (S1 + S2) H := 
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inl (inl s); st_buf_len := n |};
                                 cs_st2 := {| st_state := inr true;    st_buf_len := 0 |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a (inl s))).

    Definition sum_not_accept2 (a: P4A.t (S1 + S2) H) (s: S2) : crel (S1 + S2) H := 
      List.map (fun n =>
                  {| cr_st := {| cs_st1 := {| st_state := inr true;    st_buf_len := 0 |};
                                 cs_st2 := {| st_state := inl (inr s); st_buf_len := n |} |};
                     cr_rel := BRFalse _ BCEmp |})
               (range (P4A.size a (inr s))).

    Definition sum_init_rel (a: P4A.t (S1 + S2) H) : crel (S1 + S2) H := 
      List.concat (List.map (sum_not_accept1 a) (enum S1)
                            ++ List.map (sum_not_accept2 a) (enum S2)).
    Notation "ctx , ⟨ s1 , n1 ⟩ ⟨ s2 , n2 ⟩ ⊢ b" :=
      ({| cr_st :=
            {| cs_st1 := {| st_state := s1; st_buf_len := n1 |};
               cs_st2 := {| st_state := s2; st_buf_len := n2 |}; |};
          cr_ctx := ctx;
          cr_rel := b|}) (at level 10).
    Notation btrue := (BRTrue _ _).
    Notation bfalse := (BRFalse _ _).
    Notation "a ⇒ b" := (BRImpl a b) (at level 40).

    Definition reachable_pair_to_partition '((s1, s2): Reachability.state_pair _ _)
      : crel (S1 + S2) H :=
      match s1.(st_state) with
      | inl st =>
        [BCEmp, ⟨inl st, s1.(st_buf_len)⟩ ⟨inr true, 0⟩ ⊢ bfalse]
      | inr st =>
        []
      end
        ++
        match s2.(st_state) with
        | inl st =>
          [BCEmp, ⟨inr true, 0⟩ ⟨inl st, s2.(st_buf_len)⟩ ⊢ bfalse]
        | inr st =>
          []
        end.

    Definition reachable_pairs_to_partition (r: Reachability.state_pairs _ _)
      : crel (S1 + S2) H :=
      List.concat (List.map reachable_pair_to_partition r).

    Definition mk_init (n: nat) (a: P4A.t (S1 + S2) H) s1 s2 :=
      let s := ({| st_state := inl (inl s1); st_buf_len := 0 |}, 
                {| st_state := inl (inr s2); st_buf_len := 0 |}) in
      List.nodup (@conf_rel_eq_dec _ _ _ _ _ _)
                 (reachable_pairs_to_partition
                    (Reachability.reachable_states a n [s])).

    Definition lift_l {X Y A} (f: X -> A) (x: X + Y) : A + Y :=
      match x with
      | inl x => inl (f x)
      | inr y => inr y
      end.

    Definition separated (q1 q2: conf) : Prop :=
      match q1 with
      | (inl (inl _), _, _) => True
      | (inl (inr _), _, _) => False
      | (inr _, _, _) => True
      end /\
      match q2 with
      | (inl (inr _), _, _) => True
      | (inl (inl _), _, _) => False
      | (inr _, _, _) => True
      end.

    Definition ibdd (C: rel conf) : Prop :=
      forall q1 q2,
        C q1 q2 ->
        i q1 q2.

    Definition cibdd (C: crel S H) : Prop :=
      forall r,
        In r C ->
        ibdd ⦇r⦈.

    Lemma cibbd_ibdd:
      forall R,
        cibdd R ->
        ibdd ⟦R⟧.
    Proof.
      unfold cibdd, ibdd.
      induction R; simpl; intros.
      - assumption.
      - inversion H1.
        eauto.
    Qed.

    Lemma cibdd_app:
      forall C T,
        cibdd C ->
        cibdd T ->
        cibdd (C ++ T).
    Proof.
      unfold cibdd.
      intros.
      rewrite in_app_iff in *.
      intuition.
    Qed.

    Lemma ibdd_mono:
      forall (R S: rel conf),
        (forall x y, R x y -> S x y) ->
        ibdd S ->
        ibdd R.
    Proof.
      unfold ibdd.
      firstorder.
    Qed.

    Definition safe_wp_1bit : Prop :=
      forall C (q1 q2: conf),
        i q1 q2 ->
        ⟦wp a C⟧ q1 q2 ->
        forall bit,
          ⦇C⦈ (δ q1 bit) (δ q2 bit).

    Definition wp_bdd :=
      forall a C,
        ibdd ⦇C⦈ ->
        cibdd (wp a C).

    Lemma syn_pre_implies_sem_pre:
      forall R S q1 q2,
        R ⇝ S q1 q2 ->
        cibdd R ->
        cibdd S ->
        safe_wp_1bit ->
        wp_bdd ->
        SemPre.pre_bisimulation (P4A.interp a)
                                i
                                (map interp_conf_rel R)
                                (map interp_conf_rel S)
                                q1 q2.
    Proof.
      intros R S q1 q2 Hstep.
      induction Hstep.
      - simpl.
        constructor.
        eauto.
      - simpl.
        constructor 2; eauto.
        eapply IHHstep; eauto.
        unfold cibdd; intros.
        eauto with datatypes.
      - rewrite map_app in IHHstep.
        subst.
        intros.
        econstructor 3.
        eapply IHHstep; eauto.
        + unfold cibdd in *.
          intros.
          simpl (In _ _) in *.
          intuition.
        + eapply cibdd_app.
          * eapply H3.
            eapply H1.
            eauto with datatypes.
          * unfold cibdd in *; simpl (In _ _ ) in *; eauto.
        + intros.
          eapply H2; eauto.
          eapply SemPre.interp_rels_i; eauto.
    Qed.

  End SynPreSynWP.
  Arguments pre_bisimulation {S1 S2 H equiv2 H_eq_dec} a wp.
End SynPreSynWP.

Module SynPreSynWP1bit.
  Section SynPreSynWP1bit.
    (* State identifiers. *)
    Variable (S1: Type).
    Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
    Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

    Variable (S2: Type).
    Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
    Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

    (* Header identifiers. *)
    Variable (H: Type).
    Context `{H_eq_dec: EquivDec.EqDec H eq}.
    Context `{H_finite: @Finite H _ H_eq_dec}.

    Variable (a: P4A.t (S1 + S2) H).

    Notation conf := (configuration (P4A.interp a)).

    Notation i := (SynPreSynWP.separated _ _ _ a).
    Lemma wp_concrete_bdd:
      SynPreSynWP.wp_bdd S1 S2 H a (WP.wp (H:=H)) i.
    Proof.
    Admitted.

    Lemma be_subst_hdr_left:
      forall c (valu: bval c) hdr exp phi s1 st1 buf1 c2 v,
          interp_bit_expr exp valu (s1, st1, buf1) c2 = v ->
          interp_bit_expr (a:=a) phi valu
                          (s1, P4A.assign hdr (P4A.VBits v) st1, buf1)
                          c2 =
          interp_bit_expr (WP.be_subst phi exp (BEHdr c Left hdr))
                          valu
                          (s1, st1, buf1)
                          c2.
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); simpl; congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          simpl.
          destruct hdr.
          unfold P4A.assign, P4A.find; simpl.
          change H_eq_dec with equiv_dec.
          rewrite EquivUtil.equiv_dec_refl.
          reflexivity.
        + simpl.
          unfold P4A.find, P4A.Env.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress simpl in *
                 end;
            congruence.
      - reflexivity.
      - simpl.
        admit.
        (* rewrite IHphi; eauto. *)
        (* admit. *)
      - simpl.
        rewrite IHphi1, IHphi2; auto.
    Admitted.

    Lemma be_subst_hdr_right:
      forall c (valu: bval c) hdr exp phi s2 st2 buf2 c1 v,
          interp_bit_expr exp valu c1 (s2, st2, buf2) = v ->
          interp_bit_expr (a:=a) phi valu
                          c1
                          (s2, P4A.assign hdr (P4A.VBits v) st2, buf2)
          =
          interp_bit_expr (WP.be_subst phi exp (BEHdr c Right hdr))
                          valu
                          c1
                          (s2, st2, buf2).
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); simpl; congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          simpl.
          destruct hdr.
          unfold P4A.assign, P4A.find; simpl.
          change H_eq_dec with equiv_dec.
          rewrite EquivUtil.equiv_dec_refl.
          reflexivity.
        + simpl.
          unfold P4A.find, P4A.Env.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress simpl in *
                 end;
            congruence.
      - reflexivity.
      - simpl.
        admit.
        (* rewrite IHphi; eauto. *)
        (* admit. *)
      - simpl.
        rewrite IHphi1, IHphi2; auto.
    Admitted.

    Lemma sr_subst_hdr_left:
      forall c (valu: bval c) hdr exp phi s1 st1 buf1 c2,
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEHdr c Left hdr))
          valu
          (s1, st1, buf1)
          c2 <->
        interp_store_rel
          (a:=a)
          phi
          valu
          (s1,
           P4A.assign hdr
                      (P4A.VBits (interp_bit_expr exp valu (s1, st1, buf1) c2))
                      st1,
           buf1)
          c2.
    Proof.
      unfold bror in *;
      unfold brand in *;
      induction phi; 
        
        simpl in *;
        unfold bror in *;
        unfold brand in *;
        repeat match goal with
        | |- forall _, _ => intro
        | |- _ /\ _ => split
        | |- _ <-> _ => split
        | H: _ /\ _ |- _ => destruct H
        | H: _ <-> _ |- _ => destruct H
        end;
          auto with *;
          unfold bror in *;
          unfold brand in *;
          try solve [erewrite !be_subst_hdr_left in *; eauto
                    |tauto
                    |intuition].
    Admitted.

    Lemma sr_subst_hdr_right:
      forall c (valu: bval c) hdr exp phi c1 s2 st2 buf2,
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEHdr c Right hdr))
          valu
          c1
          (s2, st2, buf2)
        <->
        interp_store_rel
          (a:=a)
          phi
          valu
          c1
          (s2,
           P4A.assign hdr
                      (P4A.VBits (interp_bit_expr exp valu c1 (s2, st2, buf2)))
                      st2,
           buf2).
    Proof.
      induction phi; simpl in *;
        repeat match goal with
        | |- forall _, _ => intro
        | |- _ /\ _ => split
        | |- _ <-> _ => split
        | H: _ /\ _ |- _ => destruct H
        | H: _ <-> _ |- _ => destruct H
        end;
          auto with *;
          try solve [erewrite !be_subst_hdr_right in *; eauto
                    |tauto
                    |intuition].
    Admitted.

    Lemma wp_op'_size:
      forall (c: bctx) si o n phi m phi',
        WP.wp_op' (c:=c) si o (P4A.op_size o + n, phi) = (m, phi') ->
        m = n.
    Proof.
      induction o; cbn; intros.
      - congruence.
      - destruct (WP.wp_op' si o2 (P4A.op_size o1 + P4A.op_size o2 + n, phi)) eqn:?.
        replace (P4A.op_size o1 + P4A.op_size o2 + n)
          with (P4A.op_size o2 + (P4A.op_size o1 + n))
          in *
          by Lia.lia.
        apply IHo2 in Heqp.
        subst.
        eauto.
      - replace (width + n - width) with n in * by Lia.lia.
        congruence.
      - congruence.
    Qed.

    Lemma wp_op'_seq:
      forall (c: bctx) o1 o2 si phi,
        WP.wp_op' (c:=c) si (P4A.OpSeq o1 o2) phi = WP.wp_op' si o1 (WP.wp_op' si o2 phi).
    Proof.
      induction o1; intros; simpl;
        repeat match goal with
               | H:context [match ?x with _ => _ end] |- _ => destruct x eqn:?; simpl
               | |- context [match ?x with _ => _ end] => destruct x eqn:?; simpl
               | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
               end.
      - reflexivity.
      - rewrite <- IHo1_1.
        reflexivity.
      - reflexivity.
      - reflexivity.
    Qed.

    Ltac break_match :=
      match goal with
      | |- context [match ?x with _ => _ end] =>
        destruct x eqn:?
      | H: context [match ?x with _ => _ end] |- _ =>
        destruct x eqn:?
      end.

    Lemma skipn_skipn:
      forall A (l: list A) m n,
        skipn n (skipn m l) = skipn (n + m) l.
    Proof.
      induction l; intros.
      - rewrite !skipn_nil.
        reflexivity.
      - destruct m.
        + simpl.
          rewrite <- plus_n_O.
          reflexivity.
        + rewrite skipn_cons.
          replace (n + S m) with (S (n + m))
            by eauto with *.
          rewrite skipn_cons.
          eauto.
    Qed.

    Lemma wp_op'_mono:
      forall (c: bctx) si o n phi,
        fst (WP.wp_op' (c:=c) si o (n, phi)) <= n.
    Proof.
      induction o; simpl.
      - Lia.lia.
      - intros.
        destruct (WP.wp_op' si o2 _) as [m psi] eqn:?.
        specialize (IHo2 n phi).
        specialize (IHo1 m psi).
        rewrite Heqp in *.
        simpl in *.
        Lia.lia.
      - Lia.lia.
      - Lia.lia.
    Qed.

    Lemma expr_to_bit_expr_sound:
      forall (c: bctx) si (valu: bval c) expr c1 c2,
        P4A.eval_expr (snd (fst match si with Left => c1 | Right => c2 end)) expr =
        P4A.VBits (interp_bit_expr (a:=a) (WP.expr_to_bit_expr si expr) valu c1 c2).
    Proof.
      assert (Hv: forall v, P4A.VBits match v with P4A.VBits v' => v' end = v).
      {
        intros.
        destruct v; reflexivity.
      }
      induction expr; intros; cbn; auto.
      - destruct (P4A.eval_expr (snd (fst _))) eqn:?.
        unfold P4A.slice.
        specialize (IHexpr c1 c2).
        simpl in IHexpr.
        rewrite -> IHexpr in Heqv.
        congruence.
    Qed.

    Notation "⟨ R , v ⟩ ⊨ c1 c2" := (interp_store_rel R v c1 c2) (at level 50).

    Lemma eval_op_size:
      forall op st n buf st' n',
        P4A.eval_op st n buf op = (st', n') ->
        n + P4A.op_size op = n'.
    Proof.
      induction op.
      - simpl.
        intros.
        inversion H0.
        Lia.lia.
      - intros.
        simpl in *.
        destruct (P4A.eval_op _ _ _ op1) eqn:?.
        destruct (P4A.eval_op _ _ _ op2) eqn:?.
        rewrite Plus.plus_assoc.
        inversion H0.
        erewrite IHop1; eauto.
        erewrite IHop2; eauto.
      - intros.
        simpl in *.
        inversion H0.
        exact eq_refl.
      - simpl.
        intros.
        inversion H0.
        Lia.lia.
    Qed.

    Lemma wp_op'_spec_l:
      forall c (valu: bval c) o n phi s1 st1 buf1 c2,
        P4A.nonempty o ->
        interp_store_rel (a:=a)
                         (snd (WP.wp_op' Left o (n + P4A.op_size o, phi)))
                         valu
                         (s1, st1, buf1)
                         c2 <->
        interp_store_rel (a:=a)
                         phi
                         valu
                         (s1,
                          fst (P4A.eval_op st1 n buf1 o),
                          buf1)
                         c2.
    Proof.
      induction o.
      - intros.
        simpl.
        reflexivity.
      - intros.
        destruct H0.
        simpl (P4A.eval_op _ _ _ _).
        destruct (P4A.eval_op st1 n buf1 o1) as [st1' n'] eqn:?.
        destruct (P4A.eval_op st1' n' buf1 o2) as [st2' n''] eqn:?.
        pose proof (eval_op_size o1 _ _ _ _ _ Heqp).
        pose proof (eval_op_size o2 _ _ _ _ _ Heqp0).
        simpl (WP.wp_op' _ _ _).
        destruct (WP.wp_op' Left o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)) as [wn' phi'] eqn:?.
        assert (wn' = P4A.op_size o1 + n).
        {
          replace (n + (P4A.op_size o1 + P4A.op_size o2))
            with (P4A.op_size o2 + (P4A.op_size o1 + n))
            in Heqp1
            by Lia.lia.
          eapply wp_op'_size.
          eauto.
        }
        subst wn'.
        replace (P4A.op_size o1 + n)
          with (n + P4A.op_size o1)
          by Lia.lia.
        erewrite IHo1 by eauto.
        rewrite Heqp; simpl.
        replace st2' with (fst (P4A.eval_op st1' n' buf1 o2))
          by (rewrite Heqp0; reflexivity).
        replace phi' with (snd (WP.wp_op' Left o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)))
          by (rewrite Heqp1; reflexivity).
        rewrite Plus.plus_assoc.
        erewrite IHo2 by eauto.
        subst n'.
        rewrite Heqp0.
        reflexivity.
      - simpl.
        intros.
        rewrite sr_subst_hdr_left.
        simpl.
        replace (n + width - width) with n by Lia.lia.
        simpl.
        unfold P4A.slice.
        replace (1 + (n + width - 1)) with (n + width)
          by Lia.lia.
        erewrite <- firstn_skipn_comm.
        reflexivity.
      - simpl.
        unfold WP.wp_op, WP.wp_op'.
        simpl.
        intros.
        destruct lhs.
        rewrite sr_subst_hdr_left.
        simpl.
        rewrite <- expr_to_bit_expr_sound.
        reflexivity.
    Qed.

    (* This is basically a copy-pasted version of wp_op'_spec_l with
        some things flipped around. *)
    Lemma wp_op'_spec_r:
      forall c (valu: bval c) o n phi s2 st2 buf2 c1,
        P4A.nonempty o ->
        interp_store_rel (a:=a)
                         (snd (WP.wp_op' Right o (n + P4A.op_size o, phi)))
                         valu
                         c1
                         (s2, st2, buf2)
        <->
        interp_store_rel (a:=a)
                         phi
                         valu
                         c1
                         (s2,
                          fst (P4A.eval_op st2 n buf2 o),
                          buf2).
    Proof.
      induction o.
      - intros.
        simpl.
        reflexivity.
      - intros.
        destruct H0.
        simpl (P4A.eval_op _ _ _ _).
        destruct (P4A.eval_op st2 n buf2 o1) as [st2' n'] eqn:?.
        destruct (P4A.eval_op st2' n' buf2 o2) as [st2'' n''] eqn:?.
        pose proof (eval_op_size o1 _ _ _ _ _ Heqp).
        pose proof (eval_op_size o2 _ _ _ _ _ Heqp0).
        simpl (WP.wp_op' _ _ _).
        destruct (WP.wp_op' Right o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)) as [wn' phi'] eqn:?.
        assert (wn' = P4A.op_size o1 + n).
        {
          replace (n + (P4A.op_size o1 + P4A.op_size o2))
            with (P4A.op_size o2 + (P4A.op_size o1 + n))
            in Heqp1
            by Lia.lia.
          eapply wp_op'_size.
          eauto.
        }
        subst wn'.
        replace (P4A.op_size o1 + n)
          with (n + P4A.op_size o1)
          by Lia.lia.
        erewrite IHo1 by eauto.
        rewrite Heqp; simpl.
        replace st2'' with (fst (P4A.eval_op st2' n' buf2 o2))
          by (rewrite Heqp0; reflexivity).
        replace phi' with (snd (WP.wp_op' Right o2 (n + (P4A.op_size o1 + P4A.op_size o2), phi)))
          by (rewrite Heqp1; reflexivity).
        rewrite Plus.plus_assoc.
        erewrite IHo2 by eauto.
        subst n'.
        rewrite Heqp0.
        reflexivity.
      - simpl.
        intros.
        rewrite sr_subst_hdr_right.
        simpl.
        replace (n + width - width) with n by Lia.lia.
        simpl.
        unfold P4A.slice.
        replace (1 + (n + width - 1)) with (n + width)
          by Lia.lia.
        erewrite <- firstn_skipn_comm.
        reflexivity.
      - simpl.
        unfold WP.wp_op, WP.wp_op'.
        simpl.
        intros.
        destruct lhs.
        rewrite sr_subst_hdr_right.
        simpl.
        rewrite <- expr_to_bit_expr_sound.
        reflexivity.
    Qed.

    Definition pred_i {c} (p1 p2: WP.pred S1 S2 H c) : Prop :=
      forall q1 q2,
        match p1 with
        | WP.PredRead _ _ st =>
          interp_state_template st q1
        | WP.PredJump phi s =>
          fst (fst q1) = s
        end ->
        match p2 with
        | WP.PredRead _ _ st =>
          interp_state_template st q2
        | WP.PredJump phi s =>
          fst (fst q2) = s
        end ->
        i q1 q2.

    Lemma wp_pred_pair_step :
      forall C u v,
        SynPreSynWP.ibdd _ _ _ a i (interp_conf_rel C) ->
        (forall sl sr,
            pred_i sl sr ->
            interp_crel (a:=a) i (WP.wp_pred_pair a C (sl, sr)) u v) ->
        (forall b, interp_conf_rel C (step u b) (step v b)).
    Proof.
      intros.
      unfold WP.wp_pred_pair in *.
      destruct u as [[us ust] ubuf].
      destruct v as [[vs vst] vbuf].
      unfold interp_crel, interp_conf_rel, interp_conf_state, interp_state_template in * |-.
      destruct C as [[[Cst1 Clen1] [Cst2 Cbuf2]] Cctx Crel].
      unfold interp_conf_rel, interp_conf_state, interp_state_template.
      intros.
      simpl (st_state _) in *.
      simpl (st_buf_len _) in *.
      simpl (PreBisimulationSyntax.cr_st _) in *.
      simpl (PreBisimulationSyntax.cr_ctx _) in *.
      simpl (PreBisimulationSyntax.cr_rel _) in *.
      destruct H2 as [[? ?] [? ?]].
      subst.
      unfold step; cbn.
      simpl in *.
      repeat match goal with
      | |- context [length (?x ++ [_])] =>
        replace (length (x ++ [_])) with (S (length x)) in *
          by (rewrite app_length; simpl; rewrite PeanoNat.Nat.add_comm; reflexivity)
      end.
      destruct vs as [vs | vs], us as [us | us]; simpl.
      simpl in * |-.
      destruct (equiv_dec (S (length ubuf)) (P4A.size a us)),
               (equiv_dec (S (length vbuf)) (P4A.size a vs)).
      - admit.
      - admit.
      - admit.
      - admit.
    Admitted.

    Lemma be_subst_buf_left:
      forall c (valu: bval c) exp phi c2 s1 st1 buf1 v,
        interp_bit_expr exp valu (s1, st1, buf1) c2 = v ->
        interp_bit_expr (a:=a) phi valu
                        (s1, st1, v)
                        c2
        =
        interp_bit_expr (WP.be_subst phi exp (BEBuf _ c Left))
                        valu
                        (s1, st1, buf1)
                        c2.
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          reflexivity.
        + simpl.
          unfold P4A.find, P4A.Env.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress simpl in *
                 end;
            congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); try congruence.
        simpl.
        destruct a0; simpl;
          destruct (P4A.find _ _);
          reflexivity.
      - simpl.
        eauto.
      - simpl.
        admit.
      - simpl.
        erewrite IHphi1, IHphi2; auto.
    Admitted.

    Lemma be_subst_buf_right:
      forall c (valu: bval c) exp phi c1 s2 st2 buf2 v,
        interp_bit_expr exp valu c1 (s2, st2, buf2) = v ->
        interp_bit_expr (a:=a) phi valu
                        c1
                        (s2, st2, v)
        =
        interp_bit_expr (WP.be_subst phi exp (BEBuf _ c Right))
                        valu
                        c1
                        (s2, st2, buf2).
    Proof.
      induction phi; intros.
      - tauto.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _).
        + inversion e; clear e; subst.
          reflexivity.
        + simpl.
          unfold P4A.find, P4A.Env.find, P4A.assign.
          repeat match goal with
                 | H: context[ match ?e with _ => _ end ] |- _ => destruct e eqn:?
                 | |- context[ match ?e with _ => _ end ] => destruct e eqn:?
                 | |- _ => progress simpl in *
                 end;
            congruence.
      - unfold WP.be_subst.
        destruct (bit_expr_eq_dec _ _); try congruence.
        simpl.
        destruct a0; simpl;
          destruct (P4A.find _ _);
          reflexivity.
      - simpl.
        eauto.
      - simpl.
        erewrite IHphi; eauto.
        admit.
      - simpl.
        erewrite IHphi1, IHphi2; auto.
        admit.
    Admitted.

    Lemma sr_subst_buf_left:
      forall c (valu: bval c) exp phi s1 st1 buf1 c2,
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEBuf _ c Left))
          valu
          (s1, st1, buf1)
          c2 <->
        interp_store_rel
          (a:=a)
          phi
          valu
          (s1,
           st1,
           interp_bit_expr exp valu (s1, st1, buf1) c2)
          c2.
    Proof.
      (*
      induction phi; simpl in *; try tauto; intuition eauto;
        try solve [erewrite <- !be_subst_buf_left in *;
                   eauto
                  |intuition].
       *)
    Admitted.

    Lemma sr_subst_buf_right:
      forall c (valu: bval c) exp phi c1 s2 st2 buf2,
        interp_store_rel
          (a:=a)
          (WP.sr_subst phi exp (BEBuf _ c Right))
          valu
          c1
          (s2, st2, buf2) <->
        interp_store_rel
          (a:=a)
          phi
          valu
          c1
          (s2,
           st2,
           interp_bit_expr exp valu c1 (s2, st2, buf2)).
    Proof.
      (*
      induction phi; simpl in *; try tauto; intuition eauto;
        try solve [erewrite <- !be_subst_buf_right in *;
                   eauto
                  |intuition].
       *)
    Admitted.

    Lemma interp_bit_expr_ignores_state:
      forall {c} (e: bit_expr H c) valu s1 st1 buf1 s2 st2 buf2 s1' s2',
        interp_bit_expr (a:=a) e valu (s1, st1, buf1) (s2, st2, buf2) =
        interp_bit_expr (a:=a) e valu (s1', st1, buf1) (s2', st2, buf2).
    Proof.
      induction e; intros.
      - reflexivity.
      - reflexivity.
      - simpl.
        destruct a0; simpl; reflexivity.
      - reflexivity.
      - simpl.
        erewrite IHe; eauto.
      - simpl.
        erewrite IHe1, IHe2; eauto.
    Qed.

    Lemma interp_store_rel_ignores_state:
      forall {c} (r: store_rel H c) valu s1 st1 buf1 s2 st2 buf2 s1' s2',
        interp_store_rel (a:=a) r valu (s1, st1, buf1) (s2, st2, buf2) ->
        interp_store_rel (a:=a) r valu (s1', st1, buf1) (s2', st2, buf2).
    Proof.
      induction r; intros; simpl in *; try solve [intuition eauto].
      erewrite (interp_bit_expr_ignores_state e1).
      erewrite (interp_bit_expr_ignores_state e2).
      eauto.
    Qed.

    Lemma wp_concrete_safe :
      SynPreSynWP.safe_wp_1bit _ _ _ a (WP.wp (H:=H)) i.
    Proof.
      unfold SynPreSynWP.safe_wp_1bit.
      intros.
      destruct q1 as [[st1 s1] buf1].
      destruct q2 as [[st2 s2] buf2].
      unfold WP.wp in * |-.
      destruct C.
      destruct a; simpl in * |-.
      destruct cr_st.
      unfold WP.wp in * |-.
      (*
either the step is a jump or a read on the left and on the right
so that's a total of 4 cases.
But in each case you need to massage the WP to line up with it,
because you're not branching on the same thing.
*)
      unfold step.
      unfold interp_conf_rel, interp_conf_state, interp_state_template; intros.
      simpl in *.
      intuition.
      simpl in *.
      repeat match goal with
      | |- context [length (?x ++ [_])] =>
        replace (length (x ++ [_])) with (S (length x)) in *
          by (rewrite app_length; simpl; rewrite PeanoNat.Nat.add_comm; reflexivity)
      end.
      destruct (equiv_dec (S (length buf1)) _), (equiv_dec (S (length buf2)) _);
        unfold "===" in *;
        simpl in *.
      - cbv in H0.
        destruct cs_st1 as [cst1 bl1] eqn:?, cs_st2 as [cst2 bl2] eqn:?.
        simpl in *.
        (* this is a real transition*)
        destruct st1 as [[st1 | ?] | st1], st2 as [[st2 | ?] | st2];
          try solve [cbv in H0; tauto].
        + simpl in *.
          subst bl2.
          subst bl1.
          simpl in *.
          admit.
        + admit.
        + admit.
        + simpl in *.
          subst cst1 cst2.
          cbn in *.
          pose (pred_l := WP.PredJump (S1:=S1) (S2:=S2) (BRTrue H cr_ctx) (inr st1)).
          pose (pred_r := WP.PredJump (S1:=S1) (S2:=S2) (BRTrue H cr_ctx) (inr st2)).
          pose (wp_lr :=
                  (WP.wp_pred_pair
                     {|
                       WPSymLeap.P4A.t_states := t_states;
                       WPSymLeap.P4A.t_nonempty := t_nonempty;
                       WPSymLeap.P4A.t_has_extract := t_has_extract
                     |}
                     {|
                       cr_st := {| cs_st1 := cs_st1; cs_st2 := cs_st2 |};
                       cr_ctx := cr_ctx;
                       cr_rel := cr_rel
                     |} (pred_l, pred_r))).
          assert (forall r, In r wp_lr ->
                       interp_conf_rel (a:=a) r (inr st1, s1, buf1) (inr st2, s2, buf2)).
          {
            intros.
            eapply interp_rels_in; eauto.
            rewrite in_map_iff.
            eexists; intuition eauto.
            rewrite in_concat.
            eexists wp_lr.
            split; auto.
            rewrite in_map_iff.
            exists (pred_l, pred_r).
            split; [reflexivity|].
            rewrite in_prod_iff.
            unfold WP.preds.
            simpl.
            subst bl1 bl2.
            simpl.
            destruct st1, st2;
              unfold pred_l, pred_r;
              simpl;
              tauto.
          }
          cbn in wp_lr.
          match goal with
          | wp_lr := ?a :: ?b :: nil : _ |- _ => pose (wp_lr' := (a, b))
          end.
          assert (Hfst:In (fst wp_lr') wp_lr /\
                       In (snd wp_lr') wp_lr)
            by (unfold wp_lr', wp_lr; simpl; tauto).
          destruct Hfst as [Hfst Hsnd].
          pose proof (H2 (fst wp_lr') Hfst) as Hf.
          cbn in Hf.
          unfold interp_conf_rel, interp_conf_state, interp_state_template in Hf.
          subst.
          cbn in Hf.
          (*
          specialize (Hf ltac:(intuition Lia.lia) valu I I).
          rewrite !sr_subst_buf_left, !sr_subst_buf_right in Hf.
          simpl in Hf.
          eapply interp_store_rel_ignores_state; eauto.
           *)
          admit.
      - admit.
      - admit.
      - (* this is a read*)
        cbn in *.
        unfold complement in *.
        rewrite app_length in *.
        simpl in *.
        replace (length buf2 + 1) with (S (length buf2)) in * by Lia.lia.
        replace (length buf1 + 1) with (S (length buf1)) in * by Lia.lia.
        destruct cs_st1 as [cst1 bl1] eqn:?, cs_st2 as [cst2 bl2] eqn:?; simpl in *.
        assert (Hsize: bl1 <> 0 /\ bl2 <> 0) by Lia.lia.
        destruct Hsize.
        pose (pred_l :=
                WP.PredRead H cr_ctx {| st_state := cst1; st_buf_len := bl1 - 1 |}).
        pose (pred_r :=
                WP.PredRead H cr_ctx {| st_state := cst2; st_buf_len := bl2 - 1 |}).
        pose (wp_lr :=
                (WP.wp_pred_pair
                   {|
                     WPSymLeap.P4A.t_states := t_states;
                     WPSymLeap.P4A.t_nonempty := t_nonempty;
                     WPSymLeap.P4A.t_has_extract := t_has_extract
                   |}
                   {|
                     cr_st := {| cs_st1 := cs_st1; cs_st2 := cs_st2 |};
                     cr_ctx := cr_ctx;
                     cr_rel := cr_rel
                   |} (pred_l, pred_r))).
        assert (forall r, In r wp_lr ->
                     interp_conf_rel (a:=a) r (st1, s1, buf1) (st2, s2, buf2)).
        {
          intros.
          eapply interp_rels_in; eauto.
          rewrite in_map_iff.
          eexists; intuition eauto.
          rewrite in_concat.
          eexists wp_lr.
          split; auto.
          rewrite in_map_iff.
          exists (pred_l, pred_r).
          split; [reflexivity|].
          rewrite in_prod_iff.
          unfold WP.preds.
          destruct (equiv_dec _ _), (equiv_dec _ _);
            try solve [exfalso; tauto].
          unfold pred_l, pred_r.
          split; eauto with datatypes.
        }
        simpl in wp_lr.
        match goal with
        | wp_lr := ?a :: ?b :: nil : _ |- _ => pose (wp_lr' := (a, b))
        end.
        assert (Hfst:In (fst wp_lr') wp_lr /\
                     In (snd wp_lr') wp_lr)
          by (unfold wp_lr', wp_lr; simpl; tauto).
        destruct Hfst as [Hfst Hsnd].
        destruct bit;
          [specialize (H8 (snd wp_lr') Hsnd)
          |specialize (H8 (fst wp_lr') Hfst)];
          simpl in H8.
        + unfold interp_conf_rel, interp_conf_state, interp_state_template in H8.
          subst.
          simpl in H8.
          specialize (H8 ltac:(intuition Lia.lia) valu).
          subst wp_lr wp_lr'.
          clear Hfst Hsnd.
          rewrite sr_subst_buf_left in H8.
          rewrite sr_subst_buf_right in H8.
          simpl in H8.
          eauto.
        + unfold interp_conf_rel, interp_conf_state, interp_state_template in H8.
          subst.
          simpl in H8.
          specialize (H8 ltac:(intuition Lia.lia) valu).
          subst wp_lr wp_lr'.
          clear Hfst Hsnd.
          rewrite sr_subst_buf_left in H8.
          rewrite sr_subst_buf_right in H8.
          simpl in H8.
          eauto.
    Admitted.

    Lemma syn_pre_1bit_concrete_implies_sem_pre:
    forall R S q1 q2,
      SynPreSynWP.cibdd _ _ _ a i R ->
      SynPreSynWP.cibdd _ _ _ a i S ->
      SynPreSynWP.pre_bisimulation a (WP.wp (H:=H)) i R S q1 q2 ->
      SemPre.pre_bisimulation (P4A.interp a)
                              i
                              (map interp_conf_rel R)
                              (map interp_conf_rel S)
                              q1 q2.
    Proof.
      eauto using wp_concrete_safe, wp_concrete_bdd, SynPreSynWP.syn_pre_implies_sem_pre.
    Qed.
  
  End SynPreSynWP1bit.
End SynPreSynWP1bit.

Module SynPreSynWPSym.
  Section SynPreSynWPSym.
    (* State identifiers. *)
    Variable (S1: Type).
    Context `{S1_eq_dec: EquivDec.EqDec S1 eq}.
    Context `{S1_finite: @Finite S1 _ S1_eq_dec}.

    Variable (S2: Type).
    Context `{S2_eq_dec: EquivDec.EqDec S2 eq}.
    Context `{S2_finite: @Finite S2 _ S2_eq_dec}.

    (* Header identifiers. *)
    Variable (H: Type).
    Context `{H_eq_dec: EquivDec.EqDec H eq}.
    Context `{H_finite: @Finite H _ H_eq_dec}.

    Variable (a: P4A.t (S1 + S2) H).

    Notation conf := (configuration (P4A.interp a)).
    Variable (i: rel conf).
    Variable (i_closed: forall x y b, i x y -> i (step x b) (step y b)). 

    Lemma wp_sym_safe :
      SynPreSynWP.safe_wp_1bit _ _ _ a (WPSymBit.wp (H:=H)) i.
    Proof.
      unfold SynPreSynWP.safe_wp_1bit.
      intros.
    Admitted.

    Lemma wp_sym_bdd :
      SynPreSynWP.wp_bdd S1 S2 H a (WPSymBit.wp (H:=H)) i.
    Proof.
    Admitted.

    Lemma syn_pre_1bit_sym_implies_sem_pre:
    forall R S q1 q2,
      SynPreSynWP.cibdd _ _ _ a i R ->
      SynPreSynWP.cibdd _ _ _ a i S ->
      SynPreSynWP.pre_bisimulation a (WPSymBit.wp (H:=H)) i R S q1 q2 ->
      SemPre.pre_bisimulation (P4A.interp a)
                              i
                              (map interp_conf_rel R)
                              (map interp_conf_rel S)
                              q1 q2.
    Proof.
      eauto using wp_sym_safe, wp_sym_bdd, SynPreSynWP.syn_pre_implies_sem_pre.
    Qed.
  End SynPreSynWPSym.
End SynPreSynWPSym.

Module SynPreSynWPLeap.
End SynPreSynWPLeap.
