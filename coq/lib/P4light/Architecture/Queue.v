Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Section Queue.

  Context {A : Type}.

  Inductive queue := empty_queue | nonempty_queue: list A -> A -> list A -> queue.

  Definition enque (x: A) (que: queue): queue :=
    match que with
    | empty_queue => nonempty_queue [] x []
    | nonempty_queue front mid rear => nonempty_queue front mid (x :: rear)
    end.

  Definition front (que: queue): option A :=
    match que with
    | empty_queue => None
    | nonempty_queue [] mid _ => Some mid
    | nonempty_queue (v :: _) _ _ => Some v
    end.

  Fixpoint rev_aux (l: list A) (result: list A): list A :=
    match l with
    | [] => result
    | v :: rest => rev_aux rest (v :: result)
    end.

  (** A faster implementation of rev *)
  Definition rev' (l: list A) : list A := rev_aux l [].

  Definition deque (que: queue): queue :=
    match que with
    | empty_queue => empty_queue
    | nonempty_queue [] _ [] => empty_queue
    | nonempty_queue [] _ (v :: rear) => nonempty_queue (rev' rear) v []
    | nonempty_queue (_ :: front) mid rear => nonempty_queue front mid rear
    end.

  Definition is_empty (que: queue): bool :=
    match que with
    | empty_queue => true
    | _ => false
    end.

  Definition list_rep (que: queue): list A :=
    match que with
    | empty_queue => nil
    | nonempty_queue front mid rear => front ++ mid :: rev' rear
    end.

  Lemma empty_queue_rep_nil: list_rep empty_queue = [].
  Proof. reflexivity. Qed.

  Lemma is_empty_true_iff: forall q, is_empty q = true <-> q = empty_queue.
  Proof.
    intros; split; intros.
    - destruct q; auto. simpl in H. discriminate.
    - subst. reflexivity.
  Qed.

  Lemma queue_rep_nil_iff: forall q, list_rep q = [] <-> q = empty_queue.
  Proof.
    intros; split; intros.
    - destruct q; auto. simpl in H. symmetry in H.
      apply app_cons_not_nil in H. contradiction.
    - subst. reflexivity.
  Qed.

  Lemma queue_rep_is_empty_iff: forall q, is_empty q = true <-> list_rep q = [].
  Proof. intros. rewrite is_empty_true_iff. symmetry. apply queue_rep_nil_iff. Qed.

  Lemma queue_front_none: forall q, list_rep q = [] <-> front q = None.
  Proof.
    intros. rewrite queue_rep_nil_iff. split; intros.
    - subst. reflexivity.
    - destruct q as [|front mid rear]; auto. simpl in H.
      destruct front; discriminate.
  Qed.

  Lemma queue_front_some: forall q x l, list_rep q = x :: l -> front q = Some x.
  Proof.
    intros. destruct q as [|front mid rear]; simpl in H. discriminate. simpl.
    destruct front; simpl in H; inversion H; reflexivity.
  Qed.

  Lemma queue_front_some_iff: forall q x, front q = Some x <-> exists l, list_rep q = x :: l.
  Proof.
    intros; split; intros.
    - destruct q as [|front mid rear]; simpl in H. discriminate.
      destruct front as [|a front]; inversion H.
      + exists (rev' rear). reflexivity.
      + exists (front ++ mid :: rev' rear). reflexivity.
    - destruct H as [l H]. apply queue_front_some in H. assumption.
  Qed.

  Lemma rev_aux_inv: forall l1 l2, rev_aux l1 l2 = rev l1 ++ l2.
  Proof.
    induction l1; intros; simpl; auto.
    rewrite IHl1. rewrite <- app_assoc. simpl. reflexivity.
  Qed.

  Lemma rev'_eq_rev: forall l, rev' l = rev l.
  Proof. intros. unfold rev'. rewrite rev_aux_inv, app_nil_r. reflexivity. Qed.

  Lemma enque_eq: forall q x l, list_rep q = l -> list_rep (enque x q) = l ++ [x].
  Proof.
    intros. destruct q; simpl in *; subst.
    - reflexivity.
    - rewrite <- app_assoc, <- app_comm_cons, !rev'_eq_rev. reflexivity.
  Qed.

  Lemma deque_eq_nil: forall q, list_rep q = [] -> list_rep (deque q) = [].
  Proof. intros. rewrite queue_rep_nil_iff in H. subst. reflexivity. Qed.

  Lemma deque_eq_cons: forall q x l, list_rep q = x :: l -> list_rep (deque q) = l.
  Proof.
    intros. destruct q as [|front mid rear]; simpl in H. discriminate. simpl.
    destruct front, rear; simpl in H; inversion H;
      simpl in H; inversion H; rewrite !rev'_eq_rev; simpl;
      rewrite ?rev'_eq_rev; reflexivity.
  Qed.

  Lemma enque_preserves_list_rep: forall x q1 q2,
      list_rep q1 = list_rep q2 -> list_rep (enque x q1) = list_rep (enque x q2).
  Proof.
    intros. remember (list_rep q1) as l. remember (list_rep q2) as l2.
    subst l2. symmetry in Heql, H. erewrite !enque_eq; eauto.
  Qed.

  Lemma deque_preserves_list_rep: forall q1 q2,
      list_rep q1 = list_rep q2 -> list_rep (deque q1) = list_rep (deque q2).
  Proof.
    intros. remember (list_rep q1) as l. remember (list_rep q2) as l2.
    subst l2. symmetry in Heql, H. destruct l.
    - rewrite !deque_eq_nil; auto.
    - apply deque_eq_cons in Heql, H. rewrite Heql, H. reflexivity.
  Qed.

End Queue.

(** Test Begin

Definition test := Eval cbv in repeat 0 30000.

Time Compute (let s := (rev' test) in length s).
(* Finished transaction in 0.137 secs (0.135u,0.001s) (successful) *)

Time Compute (let s := (rev test) in length s).
(* Finished transaction in 8.533 secs (8.518u,0.015s) (successful) *)

Test End *)

Arguments queue _ : clear implicits.
