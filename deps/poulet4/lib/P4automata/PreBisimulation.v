Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

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

Definition buffer_appended
  {a: p4automaton}
  (c c': configuration a)
  (b: bool)
  : Prop
:=
  let '(s, st, buf) := c in
  let '(s', st', buf') := c' in
  match s with
  | inl s => Datatypes.length buf + 1 < size a s
  | inr _ => True
  end ->
  buf' = buf ++ b :: nil
.

Definition buffer_filled
  {a: p4automaton}
  (c c': configuration a)
  (b: bool)
  : Prop
:=
  let '(s, st, buf) := c in
  let '(s', st', buf') := c' in
  match s with
  | inl s =>
    Datatypes.length buf + 1 = size a s /\
    buf' = nil /\
    st' = update a s (buf ++ b :: nil) st /\
    s' = transitions a s st'
  | inr _ => False
  end
.

Definition symbolic_step
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  : chunked_relation a1 a2
:=
  (* First case: neither buffer was filled. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_appended c1 c1' b /\
       buffer_appended c2 c2' b
  ) ::
  (* Second case: the left buffer was filled, but the right was not. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_filled c1 c1' b /\
       buffer_appended c2 c2' b
  ) ::
  (* Third case: the right buffer was filled, but the left was not. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_appended c1 c1' b /\
       buffer_filled c2 c2' b
  ) ::
  (* Fourth case: both buffers were filled. *)
  (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_filled c1 c1' b /\
       buffer_filled c2 c2' b
  ) ::
  nil
.

Lemma appended_or_filled
  {a: p4automaton}
  (c c': configuration a)
  (b: bool)
:

  buffer_appended c (step c b) b \/
  buffer_filled c (step c b) b
.
Proof.
  destruct c as ((s, st), buf).
  destruct s.
  - simpl step.
    rewrite app_length.
    simpl Datatypes.length.
    destruct (equiv_dec (Datatypes.length buf + 1) (size a s)).
    + right.
      unfold buffer_filled.
      easy.
    + left.
      simpl.
      intros.
      easy.
  - left.
    simpl step.
    unfold buffer_appended.
    easy.
Qed.

Lemma symbolic_step_correct
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  (c1: configuration a1)
  (c2: configuration a2)
  (b: bool)
:
  R c1 c2 ->
  exists R',
    List.In R' (symbolic_step R) /\
    R' (step c1 b) (step c2 b)
.
Proof.
  intros.
  unfold symbolic_step.
  destruct (appended_or_filled c1 (step c1 b) b),
           (appended_or_filled c2 (step c2 b) b).
  - eexists; split.
    + apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
  - eexists; split.
    + do 2 apply in_cons; apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
  - eexists; split.
    + apply in_cons; apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
  - eexists; split.
    + do 3 apply in_cons; apply in_eq.
    + simpl.
      exists c1, c2, b.
      easy.
Qed.



Definition pre_bisimulation
  {a1 a2: p4automaton}
  (expanded: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
:=
  (forall R c1 c2,
    List.In R expanded ->
    R c1 c2 ->
    (accepting c1 <-> accepting c2) /\
    forall b,
      exists R',
        List.In R' (front ++ expanded) /\
        R' (step c1 b) (step c2 b)) ->
  forall R c1 c2,
    (List.In R (front ++ expanded) ->
     R c1 c2 ->
     bisimilar c1 c2)
.

Lemma pre_bisimulation_intro
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
:
  pre_bisimulation nil (R :: nil) ->
  (forall c1 c2, R c1 c2 -> bisimilar c1 c2)
.
Proof.
  intros.
  eapply H.
  - firstorder.
  - apply in_eq.
  - easy.
Qed.

Lemma pre_bisimulation_leaf
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
:
  pre_bisimulation checked nil
.
Proof.
  unfold pre_bisimulation.
  intros.
  rewrite app_nil_l in *.
  exists (fun c1 c2 =>
    exists R',
      List.In R' checked /\
      R' c1 c2
  ).
  split.
  - intros c1' c2' ?.
    destruct H2 as [R' [? ?]].
    specialize (H R' c1' c2').
    now apply H.
  - exists R; easy.
Qed.

Lemma pre_bisimulation_valid
  {a1 a2: p4automaton}
  (c1: configuration a1)
  (c2: configuration a2)
  (checked front: chunked_relation a1 a2)
:
  (forall R c1 c2,
    List.In R checked ->
    R c1 c2 ->
    (accepting c1 <-> accepting c2) /\
    forall b,
      exists R',
        List.In R' (front ++ checked) /\
        R' (step c1 b) (step c2 b)) ->
  pre_bisimulation checked front ->
  (exists R, List.In R (front ++ checked) /\ R c1 c2) ->
  bisimilar c1 c2
.
Proof.
  intros.
  apply H0 in H.
  destruct H1 as [R [? ?]].
  now apply H with (R := R).
Qed.

Lemma pre_bisimulation_grow
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  (forall c1 c2, R c1 c2 -> accepting c1 <-> accepting c2) ->
  pre_bisimulation (R :: checked) (symbolic_step R ++ front) ->
  pre_bisimulation checked (R :: front)
.
Proof.
  intros; unfold pre_bisimulation; intros.
  eapply pre_bisimulation_valid.
  2: { exact H0. }
  - intros.
    specialize (H1 R1 c0 c3).
    destruct H4.
    + rewrite <- H4 in H5.
      clear H4.
      split.
      * now apply H.
      * intros.
        apply symbolic_step_correct with (b0 := b) in H5.
        destruct H5 as [R' [? ?]].
        exists R'.
        split; auto.
        rewrite <- app_assoc.
        now apply in_app_iff; left.
    + split.
      * now apply H1.
      * intros.
        specialize (H1 H4 H5).
        destruct H1.
        specialize (H6 b).
        destruct H6 as [R' [? ?]].
        exists R'.
        split; auto.
        rewrite <- app_assoc.
        repeat rewrite in_app_iff.
        repeat rewrite in_app_iff in H6.
        destruct H6.
        -- destruct H6.
           ++ right; right.
              rewrite H6.
              apply in_eq.
           ++ right; left; assumption.
        -- right; right.
           now apply in_cons.
  - exists R0.
    split; auto.
    repeat rewrite in_app_iff.
    repeat rewrite in_app_iff in H2.
    destruct H2.
    + destruct H2.
      * right.
        rewrite H2.
        apply in_eq.
      * left.
        right.
        assumption.
    + right.
      now apply in_cons.
Qed.

Lemma pre_bisimulation_skip
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  (forall c1 c2,
    R c1 c2 ->
    exists R',
      List.In R' checked /\
      R' c1 c2) ->
  pre_bisimulation checked front ->
  pre_bisimulation checked (R :: front)
.
Proof.
  intros; unfold pre_bisimulation; intros.
  eapply pre_bisimulation_valid.
  2: { exact H0. }
  - intros.
    specialize (H1 R1 c0 c3 H4 H5).
    split; try apply H1.
    intros.
    destruct H1.
    specialize (H6 b).
    destruct H6 as [R' [? ?]].
    rewrite <- app_comm_cons in H6.
    destruct H6.
    + rewrite <- H6 in H7.
      apply H in H7.
      destruct H7 as [R'' [? ?]].
      exists R''.
      split; auto.
      apply in_app_iff; now right.
    + exists R'.
      auto.
  - rewrite <- app_comm_cons in H2.
    destruct H2.
    + rewrite <- H2 in H3.
      clear H2.
      apply H in H3.
      destruct H3 as [R' [? ?]].
      exists R'.
      split; auto.
      apply in_app_iff; now right.
    + exists R0.
      auto.
Qed.
