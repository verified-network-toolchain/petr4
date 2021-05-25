Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.

Require Import Poulet4.P4automata.P4automaton.

Open Scope list_scope.

Definition chunked_relation
  (a1 a2: p4automaton)
:=
  list (
    configuration a1 ->
    configuration a2 ->
    Prop
  )
.

Inductive chunked_related
  {a1 a2: p4automaton}
  : chunked_relation a1 a2 ->
    configuration a1 ->
    configuration a2 ->
    Prop
:=
| ChunkedRelatedHead:
    forall c1 c2 (R: configuration a1 -> configuration a2 -> Prop) rel,
      R c1 c2 ->
      chunked_related (R :: rel) c1 c2
| ChunkedRelatedTail:
    forall c1 c2 R rel,
      chunked_related rel c1 c2 ->
      chunked_related (R :: rel) c1 c2
.

Lemma chunked_related_correct
  {a1 a2: p4automaton}
  (R: chunked_relation a1 a2)
  (c1: configuration a1)
  (c2: configuration a2)
:
  chunked_related R c1 c2 <->
  exists R', In R' R /\ R' c1 c2
.
Proof.
  split; intros.
  - induction H.
    repeat split; auto.
    + exists R.
      split; auto.
      apply in_eq.
    + firstorder.
  - induction R.
    + firstorder.
    + destruct H as [R' [? ?]].
      destruct H.
      * apply ChunkedRelatedHead; auto.
        congruence.
      * apply ChunkedRelatedTail.
        apply IHR.
        repeat split; auto.
        now exists R'.
Qed.

Lemma chunked_related_subset
  {a1 a2: p4automaton}
  (R1 R2: chunked_relation a1 a2)
  (c1: configuration a1)
  (c2: configuration a2)
:
  incl R1 R2 ->
  chunked_related R1 c1 c2 ->
  chunked_related R2 c1 c2
.
Proof.
  intros.
  apply chunked_related_correct.
  apply chunked_related_correct in H0.
  firstorder.
Qed.

Definition progresses
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
  (expanded: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
:=
  forall c1 c2 b,
    chunked_related expanded c1 c2 ->
    close (chunked_related (front ++ expanded)) (step c1 b) (step c2 b)
.

Definition acceptance_ok
  {a1 a2: p4automaton}
  (R: chunked_relation a1 a2)
:=
  forall c1 c2,
    chunked_related R c1 c2 ->
    accepting c1 <-> accepting c2
.

Definition pre_bisimulation
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
  (expanded: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
:=
  acceptance_ok expanded ->
  progresses close expanded front ->
  forall c1 c2,
    close (chunked_related (front ++ expanded)) c1 c2 ->
    bisimilar c1 c2
.


Lemma pre_bisimulation_intro
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  SoundClosure close ->
  pre_bisimulation close nil (R :: nil) ->
  (forall c1 c2, R c1 c2 -> bisimilar c1 c2)
.
Proof.
  intros.
  apply H0.
  - intros c1' c2' ?.
    inversion H2.
  - intros c1' c2' ? ?.
    inversion H2.
  - rewrite app_nil_r.
    apply H.
    now apply ChunkedRelatedHead.
Qed.

Lemma pre_bisimulation_leaf
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
  (checked: chunked_relation a1 a2)
:
  SoundClosure close ->
  pre_bisimulation close checked nil
.
Proof.
  intros ? ? ? ? ? ?.
  rewrite app_nil_l in *.
  exists (close (chunked_related checked)).
  split; auto.
  intros c1' c2' ?; split.
  - revert c1' c2' H3.
    apply H.
    apply H0.
  - revert c1' c2' H3.
    apply H.
    intros.
    now apply H1.
Qed.

Ltac solve_incl :=
  match goal with
  | |- incl ?l ?l  =>
    apply incl_refl
  | |- incl _ (_ :: _)  =>
    apply incl_tl; solve_incl
  | |- In ?x (_ ++ ?x :: _) =>
    apply in_elt
  | |- incl (_ ++ _) _  =>
    apply incl_app; solve_incl
  | |- incl (_ :: _) _  =>
    apply incl_cons; solve_incl
  | |- incl ?l1 (?l2 ++ ?l3) =>
    match l2 with
    | context [ l1 ] =>
      apply incl_appl; solve_incl
    | _ =>
      match l3 with
      | context [ l1 ] =>
        apply incl_appr; solve_incl
      end
    end
  end
.

Definition symbolic_step
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  (c1: configuration a1)
  (c2: configuration a2)
  : Prop
:=
  exists c1' c2' b,
    R c1' c2' /\ step c1' b = c1 /\ step c2' b = c2
.

Lemma pre_bisimulation_grow
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  SoundClosure close ->
  (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
  pre_bisimulation close (R :: checked) (symbolic_step R :: front) ->
  pre_bisimulation close checked (R :: front)
.
Proof.
  intros ? ? ? ? ? ? ? ?.
  apply H1.
  - intros c1' c2' ?.
    inversion H5; subst; auto.
  - intros c1' c2' ? ?.
    inversion_clear H5; subst.
    + apply H.
      rewrite <- app_comm_cons.
      apply ChunkedRelatedHead.
      exists c1', c2', b.
      easy.
    + apply (H3 _ _ b) in H6.
      eapply closure_sound_mono in H6.
      exact H6.
      intros.
      apply chunked_related_subset with (R1 := (R :: front) ++ checked); auto.
      solve_incl.
  - revert c1 c2 H4.
    apply H.
    intros.
    apply chunked_related_subset with (R1 := (R :: front) ++ checked); auto.
    solve_incl.
Qed.

Definition symbolic_leap
  {a1 a2: p4automaton}
  (R: rel a1 a2)
  (n: nat)
  (c1: configuration a1)
  (c2: configuration a2)
  : Prop
:=
  exists c1' c2' buf,
    length buf = n /\
    R c1' c2' /\
    follow c1' buf = c1 /\
    follow c2' buf = c2
.

Definition min_step_all
  {a1 a2: p4automaton}
  (R: rel a1 a2)
  (n: nat)
:=
  forall c1 c2,
    R c1 c2 ->
      n = min (min_step c1) (min_step c2)
.

Lemma pre_bisimulation_leap
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
  (n: nat)
:
  (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
  min_step_all R n ->
  pre_bisimulation close_interpolate (R :: checked) (symbolic_leap R n :: front) ->
  pre_bisimulation close_interpolate checked (R :: front)
.
Proof.
  intros ? ? ? ? ? ? ? ?.
  apply H1.
  - intros c1' c2' ?.
    inversion H5; subst; auto.
  - intros c1' c2' ? ?.
    inversion_clear H5; subst.
    + rewrite <- follow_nil.
      rewrite <- follow_nil at 1.
      repeat rewrite <- follow_cons.
      destruct c1' as (([s1' | h1'], st1'), buf1'),
               c2' as (([s2' | h2'], st2'), buf2').
      * destruct (Compare_dec.le_lt_dec 2 (min (min_step (inl s1', st1', buf1'))
                                               (min_step (inl s2', st2', buf2')))).
        -- repeat rewrite follow_with_space.
           all: simpl min_step in *; try lia.
           repeat rewrite follow_nil.
           apply InterpolateStep; try lia.
           ++ apply InterpolateBase.
              apply chunked_related_subset with (R1 := R :: checked).
              ** solve_incl.
              ** now apply ChunkedRelatedHead.
           ++ intros.
              rewrite <- app_comm_cons.
              apply ChunkedRelatedHead.
              repeat eexists; auto.
              rewrite (H0 _ _ H6).
              simpl min_step in *.
              lia.
        -- apply InterpolateBase.
           rewrite <- app_comm_cons.
           apply ChunkedRelatedHead.
           repeat eexists; auto.
           simpl length.
           rewrite (H0 _ _ H6).
           simpl min_step in *.
           lia.
      * apply InterpolateBase.
        rewrite <- app_comm_cons.
        apply ChunkedRelatedHead.
        repeat eexists; auto.
        simpl length.
        rewrite (H0 _ _ H6).
        simpl min_step.
        lia.
      * apply InterpolateBase.
        rewrite <- app_comm_cons.
        apply ChunkedRelatedHead.
        repeat eexists; auto.
        simpl length.
        rewrite (H0 _ _ H6).
        simpl min_step.
        lia.
      * apply InterpolateBase.
        rewrite <- app_comm_cons.
        apply ChunkedRelatedHead.
        repeat eexists; auto.
        simpl length.
        rewrite (H0 _ _ H6).
        simpl min_step.
        lia.
    + apply (H3 _ _ b) in H6.
      eapply closure_sound_mono in H6.
      exact H6.
      intros.
      apply chunked_related_subset with (R1 := (R :: front) ++ checked); auto.
      solve_incl.
  - revert c1 c2 H4.
    apply closure_sound_mono.
    intros.
    apply chunked_related_subset with (R1 := (R :: front) ++ checked); auto.
    solve_incl.
Qed.

Lemma pre_bisimulation_replace
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
  (R R': configuration a1 -> configuration a2 -> Prop)
  (checked front: chunked_relation a1 a2)
:
  SoundClosure close ->
  (forall c1 c2, R c1 c2 -> R' c1 c2) ->
  pre_bisimulation close checked (R' :: front) ->
  pre_bisimulation close checked (R :: front)
.
Proof.
  unfold pre_bisimulation; intros.
  apply H1; auto.
  - intros c1' c2' b ?.
    apply (H3 _ _ b) in H5.
    rewrite <- app_comm_cons in *.
    eapply closure_sound_mono in H5.
    exact H5.
    intros.
    inversion H6; subst.
    + now apply ChunkedRelatedHead, H0.
    + now apply ChunkedRelatedTail.
  - rewrite <- app_comm_cons in *.
    eapply closure_sound_mono in H4.
    exact H4.
    intros.
    inversion H5; subst.
    + now apply ChunkedRelatedHead, H0.
    + now apply ChunkedRelatedTail.
Qed.

Lemma pre_bisimulation_skip
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  SoundClosure close ->
  (forall c1 c2, R c1 c2 -> chunked_related checked c1 c2) ->
  pre_bisimulation close checked front ->
  pre_bisimulation close checked (R :: front)
.
Proof.
  do 8 intro.
  apply H1; auto.
  - intros c1' c2' ? ?.
    apply (H3 _ _ b) in H5.
    rewrite <- app_comm_cons in H5.
    eapply closure_sound_mono in H5.
    exact H5.
    intros.
    inversion H6; subst; auto.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
  - rewrite <- app_comm_cons in H4.
    eapply closure_sound_mono in H4.
    exact H4.
    intros.
    inversion H5; subst; auto.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
Qed.
