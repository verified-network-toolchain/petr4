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

  Definition list_enque (l: list A) (que: queue): queue :=
    fold_left (Basics.flip enque) l que.

  Definition list_to_queue (l: list A): queue := list_enque l empty_queue.

  Definition qlength (que: queue): nat :=
    match que with
    | empty_queue => O
    | nonempty_queue front _ rear => S (length front + length rear)
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

  Lemma queue_front: forall q, front q = hd_error (list_rep q).
  Proof. intros. destruct q; simpl; [|destruct l; simpl]; reflexivity. Qed.

  Lemma queue_front_some_iff: forall q x, front q = Some x <-> exists l, list_rep q = x :: l.
  Proof.
    intros; split; intros.
    - destruct q as [|front mid rear]; simpl in H. discriminate.
      destruct front as [|a front]; inversion H.
      + exists (rev' rear). reflexivity.
      + exists (front ++ mid :: rev' rear). reflexivity.
    - destruct H as [l H]. rewrite queue_front, H. reflexivity.
  Qed.

  Lemma rev_aux_inv: forall l1 l2, rev_aux l1 l2 = rev l1 ++ l2.
  Proof.
    induction l1; intros; simpl; auto.
    rewrite IHl1. rewrite <- app_assoc. simpl. reflexivity.
  Qed.

  Lemma rev'_eq: forall l, rev' l = rev l.
  Proof. intros. unfold rev'. rewrite rev_aux_inv, app_nil_r. reflexivity. Qed.

  Lemma enque_eq: forall q x, list_rep (enque x q) = list_rep q ++ [x].
  Proof.
    intros. destruct q; simpl in *.
    - reflexivity.
    - rewrite <- app_assoc, <- app_comm_cons, !rev'_eq. reflexivity.
  Qed.

  Lemma deque_eq: forall q, list_rep (deque q) = tl (list_rep q).
  Proof.
    intros. destruct q as [|front mid rear]; simpl; auto.
    destruct front, rear; simpl; rewrite !rev'_eq; reflexivity.
  Qed.

  Lemma list_enque_eq: forall l q,
      list_rep (list_enque l q) = list_rep q ++ l.
  Proof.
    induction l; intros; simpl.
    - rewrite app_nil_r. reflexivity.
    - rewrite IHl. unfold Basics.flip. rewrite enque_eq, <- app_assoc. reflexivity.
  Qed.

  Lemma list_to_queue_eq: forall l, list_rep (list_to_queue l) = l.
  Proof. intros. unfold list_to_queue. rewrite list_enque_eq. reflexivity. Qed.

  Lemma qlength_eq: forall que, qlength que = length (list_rep que).
  Proof.
    intros. destruct que as [|front mid rear]; simpl; auto.
    rewrite app_length. simpl. rewrite rev'_eq, rev_length. lia.
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

Definition qmap {A B: Type} (f: A -> B) (que: queue A) : queue B :=
  match que with
  | empty_queue => empty_queue
  | nonempty_queue front mid rear => nonempty_queue (map f front) (f mid) (map f rear)
  end.

Lemma qmap_map: forall {A B} (f: A -> B) (que: queue A),
    list_rep (qmap f que) = map f (list_rep que).
Proof.
  intros. destruct que; simpl; auto. rewrite !rev'_eq, map_app. simpl.
  rewrite map_rev. reflexivity.
Qed.
