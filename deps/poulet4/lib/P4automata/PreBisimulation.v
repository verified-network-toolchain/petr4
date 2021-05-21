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

Definition rel (a1 a2: p4automaton) :=
  configuration a1 -> configuration a2 -> Prop
.

Definition closure_extends
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R: rel a1 a2) c1 c2,
    R c1 c2 -> close R c1 c2
.

Definition closure_preserves_accept
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R: rel a1 a2),
    (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
    (forall c1 c2, close R c1 c2 -> accepting c1 <-> accepting c2)
.

Definition closure_preserves_transition
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R: rel a1 a2),
    (forall c1 c2, R c1 c2 ->
     forall b, close R (step c1 b) (step c2 b)) ->
    (forall c1 c2, close R c1 c2 ->
     forall b, close R (step c1 b) (step c2 b))
.

Definition closure_mono
  {a1 a2: p4automaton}
  (close: rel a1 a2 -> rel a1 a2)
:=
  forall (R R': rel a1 a2),
    (forall c1 c2, R c1 c2 -> R' c1 c2) ->
    (forall c1 c2, close R c1 c2 -> close R' c1 c2)
.

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
  closure_extends close ->
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
  closure_preserves_accept close ->
  closure_preserves_transition close ->
  pre_bisimulation close checked nil
.
Proof.
  intros ? ? ? ? ? ? ?.
  rewrite app_nil_l in *.
  exists (close (chunked_related checked)).
  split; auto.
  intros c1' c2' ?; split.
  - revert c1' c2' H4.
    apply H.
    apply H1.
  - revert c1' c2' H4.
    apply H0.
    intros.
    now apply H2.
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
  closure_mono close ->
  closure_extends close ->
  closure_preserves_accept close ->
  (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
  pre_bisimulation close (R :: checked) (symbolic_step R :: front) ->
  pre_bisimulation close checked (R :: front)
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ?.
  apply H3.
  - intros c1' c2' ?.
    inversion H7; subst; auto.
  - intros c1' c2' ? ?.
    inversion_clear H7; subst.
    + apply H0.
      rewrite <- app_comm_cons.
      apply ChunkedRelatedHead.
      exists c1', c2', b.
      easy.
    + apply (H5 _ _ b) in H8.
      eapply H in H8.
      exact H8.
      intros.
      apply chunked_related_subset with (R1 := (R :: front) ++ checked); auto.
      solve_incl.
  - revert c1 c2 H6.
    apply H.
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
  closure_mono close ->
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
    eapply H in H5.
    exact H5.
    intros.
    inversion H6; subst.
    + now apply ChunkedRelatedHead, H0.
    + now apply ChunkedRelatedTail.
  - rewrite <- app_comm_cons in *.
    eapply H in H4.
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
  closure_mono close ->
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
    eapply H in H5.
    exact H5.
    intros.
    inversion H6; subst; auto.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
  - rewrite <- app_comm_cons in H4.
    eapply H in H4.
    exact H4.
    intros.
    inversion H5; subst; auto.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
Qed.

(* Sanity check: the identity function is a valid closure. *)
Definition close_id
  {a1 a2: p4automaton}
  (R: rel a1 a2)
:=
  R
.

Lemma close_id_preserves_accept
  {a1 a2: p4automaton}
:
  @closure_preserves_accept a1 a2 close_id
.
Proof.
  firstorder.
Qed.

Lemma close_id_preserves_transition
  {a1 a2: p4automaton}
:
  @closure_preserves_transition a1 a2 close_id
.
Proof.
  firstorder.
Qed.

Lemma close_id_mono
  {a1 a2: p4automaton}
:
  @closure_mono a1 a2 close_id
.
Proof.
  firstorder.
Qed.

Lemma close_id_extends
  {a1 a2: p4automaton}
:
  @closure_extends a1 a2 close_id
.
Proof.
  firstorder.
Qed.

Inductive close_interpolate
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  : configuration a1 -> configuration a2 -> Prop
:=
| InterpolateBase:
    forall c1 c2,
      R c1 c2 -> close_interpolate _ c1 c2
| InterpolateStep:
    forall s1 st1 buf1 s2 st2 buf2 b,
      close_interpolate _ (inl s1, st1, buf1)
                          (inl s2, st2, buf2) ->
      length buf1 + 1 < size a1 s1 ->
      length buf2 + 1 < size a2 s2 ->
      (forall buf,
         length buf = min (size a1 s1 - length buf1)
                          (size a2 s2 - length buf2) ->
         R (follow (inl s1, st1, buf1) buf)
           (follow (inl s2, st2, buf2) buf)) ->
      close_interpolate _ (inl s1, st1, buf1 ++ b :: nil)
                          (inl s2, st2, buf2 ++ b :: nil)
.

Lemma close_interpolate_preserves_accept
  {a1 a2: p4automaton}
:
  @closure_preserves_accept a1 a2 close_interpolate
.
Proof.
  intros ? ? ? ? ?.
  induction H0; firstorder.
Qed.

Lemma follow_nil
  {a: p4automaton}
  (c: configuration a)
:
  follow c nil = c
.
Proof.
  reflexivity.
Qed.

Lemma step_with_space
  {a: p4automaton}
  (s: states a)
  (st: store a)
  (buf: list bool)
  (b: bool)
:
  length buf + 1 < size a s ->
  step (inl s, st, buf) b = (inl s, st, buf ++ b :: nil)
.
Proof.
  intros; simpl.
  destruct (equiv_dec _ _); auto.
  unfold equiv in e.
  rewrite app_length in e.
  simpl length in e.
  lia.
Qed.

Lemma follow_with_space
  {a: p4automaton}
  (s: states a)
  (st: store a)
  (buf buf': list bool)
  (b: bool)
:
  length buf + 1 < size a s ->
  follow (inl s, st, buf) (b :: buf') =
  follow (inl s, st, buf ++ b :: nil) buf'
.
Proof.
  intros.
  rewrite follow_cons.
  f_equal.
  now apply step_with_space.
Qed.

Lemma close_interpolate_preserves_transition
  {a1 a2: p4automaton}
:
  @closure_preserves_transition a1 a2 close_interpolate
.
Proof.
  intros ? ? ? ? ?.
  induction H0; intros; eauto.
  repeat rewrite <- step_with_space; auto.
  destruct (Compare_dec.le_lt_dec (Nat.min (size a1 s1 - length buf1)
                                           (size a2 s2 - length buf2)) 2).
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
    + repeat rewrite <- step_with_space; auto.
    + intros.
       repeat rewrite <- follow_with_space; try lia.
       apply H3.
       simpl length.
       lia.
Qed.

Lemma close_interpolate_mono
  {a1 a2: p4automaton}
:
  @closure_mono a1 a2 close_interpolate
.
Proof.
  intros ? ? ? ? ? ?.
  induction H0.
  - eauto using InterpolateBase.
  - eauto using InterpolateStep.
Qed.

Lemma close_interpolate_extends
  {a1 a2: p4automaton}
:
  @closure_extends a1 a2 close_interpolate
.
Proof.
  intros ? ? ? ?.
  eauto using InterpolateBase.
Qed.
