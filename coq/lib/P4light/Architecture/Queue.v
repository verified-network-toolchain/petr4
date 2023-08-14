Require Import Coq.Lists.List.
Import ListNotations.

Section Queue.

  Context {A : Type}.

  Definition double_stack := (list A * list A)%type.

  Definition wf_queue (ds: double_stack): Prop :=
    match ds with
    | ([], []) => True
    | (_, []) => False
    | (_, _) => True
    end.

  Definition queue := {x: double_stack | wf_queue x}.

  Definition empty_queue: queue := exist _ ([], []) I.

  Definition enque' (x: A) (ds: double_stack) :=
    match ds with
    | ([], []) => ([], [x])
    | (s1, s2) => (x :: s1, s2)
    end.

  Ltac break_match :=
    match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _ ] => destruct X eqn:?; simpl
    | [ |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?; simpl
    end.

  Lemma wf_enque': forall x q, wf_queue q -> wf_queue (enque' x q).
  Proof.
    intros. destruct q as [s1 s2]. simpl.
    repeat break_match; try reflexivity. inversion H.
  Qed.

  Definition enque (x: A) (que: queue): queue.
  Proof.
    destruct que as [q wfq].
    exists (enque' x q).
    apply wf_enque'. exact wfq.
  Defined.

  Definition front (que: queue): option A :=
    match que with
    | exist _ (_, []) _ => None
    | exist _ (_, x :: s) _ => Some x
    end.

  Definition is_empty (que: queue): bool :=
    match que with
    | exist _ (_, []) _ => true
    | _ => false
    end.

  Definition queue_rep_eq (que: queue) (l: list A) : Prop :=
    match que with
    | exist _ (s1, s2) _ => s2 ++ rev s1 = l
    end.

  Notation "q =ₖ l" := (queue_rep_eq q l) (at level 80, no associativity).

  Definition deque' (que: double_stack): double_stack :=
    match que with
    | (_, []) => ([], [])
    | (s, [x]) => ([], rev s)
    | (s1, x :: s2) => (s1, s2)
    end.

  Lemma wf_deque': forall q, wf_queue q -> wf_queue (deque' q).
  Proof.
    intros. destruct q as [s1 s2]. simpl.
    repeat break_match; try reflexivity.
  Qed.

  Definition deque (que: queue): queue.
  Proof.
    destruct que as [q wfq].
    exists (deque' q).
    apply wf_deque'. assumption.
  Defined.

  Lemma empty_queue_nil: empty_queue =ₖ [].
  Proof. reflexivity. Qed.

  Lemma queue_front_none: forall q, q =ₖ [] <-> front q = None.
  Proof.
    intros. destruct q as [[s1 s2] wfq]. simpl. split; intros.
    - apply app_eq_nil in H. destruct H. subst s2. reflexivity.
    - simpl in *. repeat break_match; try reflexivity; inversion H.
      exfalso; assumption.
  Qed.

  Lemma queue_front_some: forall q x l, q =ₖ x :: l -> front q = Some x.
  Proof.
    intros. destruct q as [[s1 s2] wfq]. simpl. red in H.
    destruct s1, s2; simpl in *.
    - inversion H.
    - inversion H. reflexivity.
    - exfalso; assumption.
    - inversion H. reflexivity.
  Qed.

  Lemma queue_front_some_iff: forall q x, front q = Some x <-> exists l, q =ₖ x :: l.
  Proof.
    intros; split; intros.
    - destruct q as [[s1 s2] wfq]. destruct s1, s2; simpl in *; inversion H.
      + exists s2. rewrite app_nil_r. reflexivity.
      + exists (s2 ++ rev s1 ++ [a]). reflexivity.
    - destruct H as [l H]. apply queue_front_some in H. assumption.
  Qed.

  Lemma enque_eq: forall q x l, q =ₖ l -> enque x q =ₖ l ++ [x].
  Proof.
    intros. destruct q as [[s1 s2] wfq]. destruct s1, s2; simpl in *.
    - subst. reflexivity.
    - subst. simpl. rewrite app_nil_r. reflexivity.
    - exfalso. assumption.
    - subst. simpl. rewrite app_assoc. reflexivity.
  Qed.

  Lemma deque_eq_nil: forall q, q =ₖ [] -> deque q =ₖ [].
  Proof.
    intros. destruct q as [[s1 s2] wfq]. simpl in H.
    apply app_eq_nil in H. destruct H.
    subst s2. reflexivity.
  Qed.

  Lemma deque_eq_cons: forall q x l, q =ₖ x :: l -> deque q =ₖ l.
  Proof.
    intros. destruct q as [[s1 s2] wfq]. destruct s1, s2; simpl in *.
    - inversion H.
    - rewrite app_nil_r in H. inversion H. destruct l; simpl; try reflexivity.
      rewrite app_nil_r. reflexivity.
    - exfalso; assumption.
    - inversion H. subst. repeat break_match; inversion Heqd; simpl.
      + rewrite app_nil_r. reflexivity.
      + reflexivity.
  Qed.

  Lemma is_empty_eq: forall q, is_empty q = true <-> q = empty_queue.
  Proof.
    intros; split; intros.
    - destruct q as [[s1 s2] wfq]. destruct s1, s2; simpl in *.
      + destruct wfq. reflexivity.
      + inversion H.
      + exfalso; assumption.
      + inversion H.
    - subst. reflexivity.
  Qed.

  Lemma empty_is_empty: is_empty empty_queue = true.
  Proof. reflexivity. Qed.

  Lemma empty_eq_nil: empty_queue =ₖ nil.
  Proof. reflexivity. Qed.

End Queue.

Arguments queue _ : clear implicits.

Notation "q =ₖ l" := (queue_rep_eq q l) (at level 80, no associativity).
