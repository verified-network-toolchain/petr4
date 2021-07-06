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
      exact I.
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
        forall (R T: crel S H) (C: conf_rel S H) (W: crel S H) q1 q2,
          W = wp a C ->
          (C :: R) ⇝ (T ++ W) q1 q2 ->
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

    Definition safe_wp_1bit :=
      forall C q1 q2,
        ⟦wp a C⟧ q1 q2 ->
        forall bit, ⦇C⦈ (δ q1 bit) (δ q2 bit).
    
    Lemma syn_pre_implies_sem_pre:
      forall R S q1 q2,
        safe_wp_1bit ->
        R ⇝ S q1 q2 ->
        SemPre.pre_bisimulation (P4A.interp a)
                                (map interp_conf_rel R)
                                (map interp_conf_rel S)
                                q1 q2.
    Proof.
      intros.
      induction H1.
      - simpl.
        constructor.
        eauto.
      - simpl.
        constructor 2; eauto.
      - rewrite map_app in IHpre_bisimulation.
        subst.
        econstructor 3; eauto.
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
          rewrite Utiliser.equiv_dec_refl.
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
        rewrite IHphi; eauto.
      - simpl.
        rewrite IHphi1, IHphi2; auto.
    Qed.

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
          rewrite Utiliser.equiv_dec_refl.
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
        rewrite IHphi; eauto.
      - simpl.
        rewrite IHphi1, IHphi2; auto.
    Qed.

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
      induction phi; simpl in *;
        repeat match goal with
        | |- forall _, _ => intro
        | |- _ /\ _ => split
        | |- _ <-> _ => split
        | H: _ /\ _ |- _ => destruct H
        | H: _ <-> _ |- _ => destruct H
        end;
          auto with *;
          try solve [erewrite !be_subst_hdr_left in *; eauto
                    |tauto
                    |intuition].
    Qed.

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
    Qed.

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

    Lemma wp_pred_pair_step :
      forall C u v,
        (forall sl sr,
            interp_crel (a:=a) (WP.wp_pred_pair a C (sl, sr)) u v) ->
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
      destruct H1 as [[? ?] [? ?]].
      subst.
      unfold step; cbn.
      repeat match goal with
      | |- context [length (?x ++ [_])] =>
        replace (length (x ++ [_])) with (S (length x))
          by (rewrite app_length; simpl; rewrite PeanoNat.Nat.add_comm; reflexivity)
      end.
      destruct vs as [vs | vs], us as [us | us]; simpl.
      - destruct (equiv_dec (S (length ubuf)) (P4A.size a us)),
                 (equiv_dec (S (length vbuf)) (P4A.size a vs)).
        + simpl (states _) in *.
          set (sl := WP.PredJump (c:=Cctx)
                                 (WP.trans_cond Left
                                                (P4A.st_trans (P4A.t_states a us))
                                                (inl us))
                                 us).
          set (sr := WP.PredJump (c:=Cctx)
                                 (WP.trans_cond Right
                                                (P4A.st_trans (P4A.t_states a vs))
                                                (inl vs))
                                 vs).
          specialize (H0 sl sr).
          destruct H0 as [? [? ?]].
          cbn in * |-.
          unfold "===" in *.
          unfold WP.S in *.
          pose proof (P4A.t_has_extract a us).
          pose proof (P4A.t_has_extract a vs).
          repeat match goal with
          | H: context[P4A.state_size (P4A.t_states ?a ?s)] |- _ =>
            change (P4A.state_size (P4A.t_states a s)) with (P4A.size a s) in H
          end.
          repeat match goal with
          | H: ?pre -> forall _: bval _, _ |- _ =>
            let H' := fresh "H" in
            assert (H': pre) by (intuition eauto; Lia.lia);
              pose proof (H H' valu);
              clear H'; clear H
          end.
          unfold WP.wp_op in *; cbn in *.
          clear sl.
          clear sr.
          admit.
        + admit.
        + admit.
        + admit.
      - admit.
      - admit.
      - admit.
    Admitted.

    Lemma wp_concrete_safe :
      SynPreSynWP.safe_wp_1bit _ _ _ a (WP.wp (H:=H)).
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
      set (p1 := WP.preds _ _ _ _) in H0.
      set (p2 := WP.preds _ _ _ _) in H0.
      remember (list_prod p1 p2) as p.
      symmetry in Heqp.
      revert Heqp.
      induction p; intros.
      - unfold WP.wp_pred_pair in *.
        simpl in * |-.
        cbv in H0.
        assert (p1 = [] \/ p2 = []).
        {
          unfold list_prod in *.
          destruct p1, p2; try tauto.
          simpl in Heqp.
          congruence.
        }
        unfold WP.preds in *.
    Admitted.
      
    Lemma syn_pre_1bit_concrete_implies_sem_pre:
    forall R S q1 q2,
      SynPreSynWP.pre_bisimulation a (WP.wp (H:=H)) R S q1 q2 ->
      SemPre.pre_bisimulation (P4A.interp a)
                              (map interp_conf_rel R)
                              (map interp_conf_rel S)
                              q1 q2.
    Proof.
      eauto using wp_concrete_safe, SynPreSynWP.syn_pre_implies_sem_pre.
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

    Check WP.wp.
    Check (WP.wp a).
    Lemma wp_sym_safe :
      SynPreSynWP.safe_wp_1bit _ _ _ a (WPSymBit.wp (H:=H)).
    Proof.
      unfold SynPreSynWP.safe_wp_1bit.
      intros.
    Admitted.
      
    Lemma syn_pre_1bit_sym_implies_sem_pre:
    forall R S q1 q2,
      SynPreSynWP.pre_bisimulation a (WPSymBit.wp (H:=H)) R S q1 q2 ->
      SemPre.pre_bisimulation (P4A.interp a)
                              (map interp_conf_rel R)
                              (map interp_conf_rel S)
                              q1 q2.
    Proof.
      eauto using wp_sym_safe, SynPreSynWP.syn_pre_implies_sem_pre.
    Qed.
  End SynPreSynWPSym.
End SynPreSynWPSym.

Module SynPreSynWPLeap.
End SynPreSynWPLeap.
