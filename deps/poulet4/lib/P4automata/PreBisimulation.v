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

Definition buffer_appended
  {a: p4automaton}
  (c c': configuration a)
  (b: bool)
  : Prop
:=
  let '(s, st, buf) := c in
  let '(s', st', buf') := c' in
  buf' = buf ++ b :: nil /\
  s = s' /\
  st = st'
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

Definition buffer_sane
  {a: p4automaton}
  (c: configuration a)
  : Prop
:=
  let '(s, st, buf) := c in
  match s with
  | inl s => Datatypes.length buf < size a s
  | inr _ => True
  end
.

Definition build_chunk
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  (c1: configuration a1)
  (c2: configuration a2)
:=
  R c1 c2 /\
  buffer_sane c1 /\
  buffer_sane c2
.

Definition symbolic_step
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  : chunked_relation a1 a2
:=
  (* First case: neither buffer was filled. *)
  build_chunk (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_appended c1 c1' b /\
       buffer_appended c2 c2' b
  ) ::
  (* Second case: the left buffer was filled, but the right was not. *)
  build_chunk (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_filled c1 c1' b /\
       buffer_appended c2 c2' b
  ) ::
  (* Third case: the right buffer was filled, but the left was not. *)
  build_chunk (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_appended c1 c1' b /\
       buffer_filled c2 c2' b
  ) ::
  (* Fourth case: both buffers were filled. *)
  build_chunk (fun c1' c2' =>
     exists c1 c2 b,
       R c1 c2 /\
       buffer_filled c1 c1' b /\
       buffer_filled c2 c2' b
  ) ::
  nil
.

Lemma buffer_sane_preserved
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
:
  buffer_sane c ->
  buffer_sane (step c b)
.
Proof.
  unfold buffer_sane; intros.
  destruct c as ((s, st), buf).
  destruct s; auto.
  simpl step.
  destruct (equiv_dec _ _).
  destruct (transitions _ _ _); auto.
  - simpl length.
    apply a.
  - rewrite app_length in *.
    unfold "===", complement in *.
    simpl length in *.
    lia.
Qed.

Lemma appended_or_filled
  {a: p4automaton}
  (c: configuration a)
  (b: bool)
:
  buffer_sane c ->
  buffer_appended c (step c b) b \/
  buffer_filled c (step c b) b
.
Proof.
  intros.
  destruct c as ((s, st), buf).
  destruct s.
  - simpl step.
    rewrite app_length.
    simpl length.
    destruct (equiv_dec (length buf + 1) (size a s)).
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
      buffer_sane c1 ->
      buffer_sane c2 ->
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
  (buffer_sane c1 /\
   buffer_sane c2 /\
   exists R', In R' R /\ R' c1 c2)
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
    + destruct H as [? [? [R' [? ?]]]].
      destruct H1.
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

Lemma symbolic_step_correct
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
  (c1: configuration a1)
  (c2: configuration a2)
  (b: bool)
:
  buffer_sane c1 ->
  buffer_sane c2 ->
  R c1 c2 ->
  chunked_related (symbolic_step R) (step c1 b) (step c2 b)
.
Proof.
  intros.
  unfold symbolic_step.
  destruct (appended_or_filled c1 b H),
           (appended_or_filled c2 b H0).
  - apply ChunkedRelatedHead.
    unfold build_chunk; repeat split.
    exists c1, c2, b; easy.
    all: eauto using buffer_sane_preserved.
  - do 2 apply ChunkedRelatedTail; apply ChunkedRelatedHead.
    unfold build_chunk; repeat split.
    exists c1, c2, b; easy.
    all: eauto using buffer_sane_preserved.
  - do 1 apply ChunkedRelatedTail; apply ChunkedRelatedHead.
    unfold build_chunk; repeat split.
    exists c1, c2, b; easy.
    all: eauto using buffer_sane_preserved.
  - do 3 apply ChunkedRelatedTail; apply ChunkedRelatedHead.
    unfold build_chunk; repeat split.
    exists c1, c2, b; easy.
    all: eauto using buffer_sane_preserved.
Qed.

Definition progresses
  {a1 a2: p4automaton}
  (expanded: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
:=
  forall c1 c2 b,
    chunked_related expanded c1 c2 ->
    chunked_related (front ++ expanded)
                    (step c1 b)
                    (step c2 b)
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
  (expanded: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
:=
  acceptance_ok expanded ->
  progresses expanded front ->
  forall c1 c2,
    chunked_related (front ++ expanded) c1 c2 ->
    bisimilar c1 c2
.

Lemma pre_bisimulation_intro
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
:
  pre_bisimulation nil (R :: nil) ->
  (forall c1 c2,
    R c1 c2 ->
    buffer_sane c1 ->
    buffer_sane c2 ->
    bisimilar c1 c2)
.
Proof.
  intros.
  apply H.
  - intros c1' c2' ?.
    inversion H3.
  - intros c1' c2' ? ?.
    inversion H3.
  - rewrite app_nil_r.
    now constructor.
Qed.

Definition grows_to_bisimulation
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
:=
  forall c1 c2,
    build_chunk R c1 c2 ->
    bisimilar c1 c2
.

Lemma pre_bisimulation_intro'
  {a1 a2: p4automaton}
  (R: configuration a1 -> configuration a2 -> Prop)
:
  pre_bisimulation nil (R :: nil) ->
  grows_to_bisimulation R
.
Proof.
  intros.
  unfold grows_to_bisimulation.
  intros.
  destruct H0 as [? [? ?]].
  revert c1 c2 H0 H1 H2.
  now apply pre_bisimulation_intro.
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
  exists (chunked_related checked).
  firstorder.
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
  apply H0.
  - intros c1' c2' ?.
    inversion H4; subst; auto.
  - intros c1' c2' ? ?.
    inversion H4; subst.
    + apply symbolic_step_correct with (b0 := b) in H7; auto.
      apply chunked_related_subset with (R1 := symbolic_step R); auto.
      solve_incl.
    + apply chunked_related_subset with (R1 := (R :: front) ++ checked); auto.
      solve_incl.
  - apply chunked_related_subset with ((R :: front) ++ checked); auto.
    solve_incl.
Qed.

Lemma pre_bisimulation_replace
  {a1 a2: p4automaton}
  (R R': configuration a1 -> configuration a2 -> Prop)
  (checked front: chunked_relation a1 a2)
:
  (forall c1 c2, R c1 c2 -> R' c1 c2) ->
  pre_bisimulation checked (R' :: front) ->
  pre_bisimulation checked (R :: front)
.
Proof.
  unfold pre_bisimulation; intros.
  apply H0; auto.
  - intros c1' c2' b ?.
    apply (H2 _ _ b) in H4.
    rewrite <- app_comm_cons in *.
    inversion H4; subst.
    + apply H in H7.
      now apply ChunkedRelatedHead.
    + now apply ChunkedRelatedTail.
  - rewrite <- app_comm_cons in *.
    inversion H3; subst.
    + apply H in H6.
      now apply ChunkedRelatedHead.
    + now apply ChunkedRelatedTail.
Qed.

Lemma pre_bisimulation_skip
  {a1 a2: p4automaton}
  (checked: chunked_relation a1 a2)
  (front: chunked_relation a1 a2)
  (R: configuration a1 -> configuration a2 -> Prop)
:
  (forall c1 c2, R c1 c2 -> chunked_related checked c1 c2) ->
  pre_bisimulation checked front ->
  pre_bisimulation checked (R :: front)
.
Proof.
  do 7 intro.
  apply H0; auto.
  - intros c1' c2' ? ?.
    apply (H2 _ _ b) in H4.
    rewrite <- app_comm_cons in H4.
    inversion H4; subst; auto.
    apply H in H7.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
  - rewrite <- app_comm_cons in H3.
    inversion H3; subst; auto.
    apply H in H6.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
Qed.
