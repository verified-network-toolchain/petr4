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

    Notation "⟦ x ⟧" := (interp_rels x).
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
          (C :: R) ⇝ (T ++ W) q1 q2 ->
          (forall q1 q2, ⟦W⟧ q1 q2 -> (forall bit, C (step q1 bit) (step q2 bit))) ->
          R ⇝ (C :: T) q1 q2
    where "R ⇝ S" := (pre_bisimulation R S).

    Lemma sem_pre_implies_sem_bisim :
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
          eapply in_interp_rels.
          intros.
          apply in_app_or in H4.
          destruct H4.
          * eapply interp_rels_in in H3; eauto with datatypes.
          * destruct H4; subst.
            -- eauto using interp_rels_mono with datatypes.
            -- eapply interp_rels_in in H3; eauto with datatypes.
        + intros.
          apply H0.
          eapply in_interp_rels.
          intros.
          apply in_app_or in H4.
          destruct H4.
          * eapply interp_rels_in in H3; eauto with datatypes.
          * destruct H4; subst.
            -- eauto using interp_rels_mono with datatypes.
            -- eapply interp_rels_in in H3; eauto with datatypes.
      - apply IHpre_bisimulation.
        + intros.
          apply H.
          apply in_interp_rels.
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
               left.
               apply H4.
        + intros.
          eapply in_interp_rels.
          intros ? ?.
          destruct H4.
          * subst.
            apply H2.
            eapply in_interp_rels.
            intros ? ?.
            eapply interp_rels_in in H3; eauto with datatypes.
          * eapply interp_rels_in; try eassumption.
            eapply H0; auto.
            apply in_interp_rels.
            intros ? ?.
            eapply interp_rels_in in H3; eauto.
            apply in_app_iff in H5.
            destruct H5; eauto with datatypes.
            destruct H5; subst; eauto with datatypes.
    Qed.

  End SemPre.
End SemPre.

Module SemPreLeaps.
  Section SemPreLeaps.
    Variable (a: p4automaton).
    Notation conf := (configuration a).

    Notation "⟦ x ⟧" := (interp_rels x).
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
          (C :: R) ⇝ (T ++ W) q1 q2 ->
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

    Definition S: Type := S1 + S2.

    (* Header identifiers. *)
    Variable (H: Type).
    Context `{H_eq_dec: EquivDec.EqDec H eq}.
    Context `{H_finite: @Finite H _ H_eq_dec}.

    Variable (a: P4A.t S H).

    Variable (wp: P4A.t S H ->
                  conf_rel S H ->
                  list (conf_rel S H)).

    Notation conf := (configuration (P4A.interp a)).

    Notation "⟦ x ⟧" := (interp_crel x).
    Notation "⦇ x ⦈" := (interp_conf_rel (a:=a) x).
    Notation "R ⊨ q1 q2" := (interp_crel R q1 q2) (at level 40).
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
        forall (R T: crel S H) (C: conf_rel S H) q1 q2,
          (C :: R) ⇝ (T ++ wp a C) q1 q2 ->
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
  End SynPreSynWP.
  Arguments pre_bisimulation {S1 S2 H equiv2 H_eq_dec} a wp.
End SynPreSynWP.
