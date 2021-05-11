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
    + exists R.
      split; auto.
      apply in_eq.
    + firstorder.
  - induction R.
    + firstorder.
    + destruct H as [R' [? ?]].
      destruct H.
      * apply ChunkedRelatedHead.
        congruence.
      * apply ChunkedRelatedTail.
        apply IHR.
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
  R c1 c2 ->
  chunked_related (symbolic_step R) (step c1 b) (step c2 b)
.
Proof.
  intros.
  unfold symbolic_step.
  destruct (appended_or_filled c1 (step c1 b) b),
           (appended_or_filled c2 (step c2 b) b).
  - apply ChunkedRelatedHead.
    exists c1, c2, b; easy.
  - do 2 apply ChunkedRelatedTail; apply ChunkedRelatedHead.
    exists c1, c2, b; easy.
  - do 1 apply ChunkedRelatedTail; apply ChunkedRelatedHead.
    exists c1, c2, b; easy.
  - do 3 apply ChunkedRelatedTail; apply ChunkedRelatedHead.
    exists c1, c2, b; easy.
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
  (forall c1 c2, R c1 c2 -> bisimilar c1 c2)
.
Proof.
  intros.
  apply H.
  - intros c1' c2' ?.
    inversion H1.
  - intros c1' c2' ? ?.
    inversion H1.
  - rewrite app_nil_r.
    now constructor.
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
    + apply symbolic_step_correct with (b0 := b) in H9.
      apply chunked_related_subset with (R1 := symbolic_step R); auto.
      solve_incl.
    + apply chunked_related_subset with (R1 := (R :: front) ++ checked); auto.
      solve_incl.
  - apply chunked_related_subset with ((R :: front) ++ checked); auto.
    solve_incl.
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
    apply H in H9.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
  - rewrite <- app_comm_cons in H3.
    inversion H3; subst; auto.
    apply H in H8.
    apply chunked_related_subset with (R1 := checked); auto.
    solve_incl.
Qed.
