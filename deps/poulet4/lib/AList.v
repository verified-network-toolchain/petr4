Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Classes.Morphisms.
Import ListNotations.

Definition AList
    (K V: Type)
    (R: Relation_Definitions.relation K)
    `{Equivalence K R} :=
  list (K * V)
.

Definition sublist {A} (l1 l2: list A): Prop := exists l3, Permutation (l1 ++ l3) l2.

Lemma sublist_cons: forall {A} (a: A) (l1 l2: list A),
    sublist (a :: l1) l2 -> sublist l1 l2.
Proof.
  unfold sublist. intros. destruct H as [l3 ?]. simpl in H.
  exists (a :: l3). apply perm_trans with (a :: l1 ++ l3); auto.
  symmetry. apply Permutation_middle.
Qed.

Section AList.
  Context {K V: Type}.
  Context {R: Relation_Definitions.relation K}.
  Context `{H: Equivalence K R}.
  Context {KEqDec: EqDec K R}.

  Definition get (l: AList K V R) (k: K) : option V :=
    let filter := fun '(k', _) =>
      if KEqDec k k' then true else false in
    match List.find filter l with
    | None => None
    | Some (k, v) => Some v
    end
  .

  Fixpoint set (l: AList K V R) (k: K) (v: V) : option (AList K V R) :=
    match l with
    | (k', v') :: l' =>
      if KEqDec k k'
      then Some ((k, v) :: l')
      else match set l' k v with
           | Some l'' => Some ((k', v') :: l'')
           | None => None
           end
    | nil =>
      None
    end.

  Fixpoint set_some (l: AList K V R) (k: K) (v: V) : (AList K V R) :=
    match l with
    | (k', v') :: l' =>
      if KEqDec k k'
      then ((k, v) :: l')
      else ((k', v') :: (set_some l' k v))
    | nil =>[(k, v)]
    end.

  Lemma get_neq_cons:
    forall (k' : K) (v' : V) (l : list (K * V)) (k : K),
      k =/= k' -> get ((k', v') :: l) k = get l k.
  Proof. intros. unfold get. simpl. destruct (KEqDec k k'); easy. Qed.

  Lemma get_eq_cons:
    forall (k' : K) (v' : V) (l : list (K * V)) (k : K),
      k === k' -> get ((k', v') :: l) k = Some v'.
  Proof.
    intros. unfold get. simpl. destruct (KEqDec k k'); auto.
    exfalso; now apply c.
  Qed.

  Lemma get_some_set: forall l k v1 v2,
                      get l k = Some v1 ->
                      set l k v2 = Some (set_some l k v2).
  Proof.
    induction l; intros.
    - unfold get in H0. simpl in H0. inversion H0.
    - simpl. destruct a as [k' v']. destruct (KEqDec k k'); auto.
      assert (get l k = Some v1) by now rewrite get_neq_cons in H0.
      destruct (set l k v2) eqn: ?.
      + rewrite (IHl _ v1) in Heqo; auto. inversion Heqo. easy.
      + exfalso. clear -H1 Heqo. rename Heqo into H2. induction l.
        * unfold get in H1. simpl in H1. inversion H1.
        * simpl in H2. destruct a as [k' v']. destruct (KEqDec k k'). 1: inversion H2.
          destruct (set l k v2). 1: inversion H2. apply IHl; auto.
          now rewrite get_neq_cons in H1.
  Qed.

  Lemma set_some_get: forall l k v, get (set_some l k v) k = Some v.
  Proof.
    induction l; intros.
    - simpl. unfold get. simpl. destruct (KEqDec k k); auto. exfalso. now apply c.
    - destruct a as [k' v']. simpl. destruct (KEqDec k k').
      + unfold get. simpl. destruct (KEqDec k k); auto. exfalso. now apply c.
      + rewrite get_neq_cons; auto.
  Qed.

  Fixpoint key_unique (l : AList K V R) : bool :=
    match l with
    | [] => true
    | (k, _) :: tl =>
      match get tl k with
      | Some _ => false
      | None => key_unique tl
      end
    end.

  Fixpoint filter (l : AList K V R) (f : K -> bool) : (AList K V R) :=
    match l with
    | [] => []
    | (k, v) :: tl =>
      if f k then (k, v) :: (filter tl f)
      else filter tl f
    end.

  Lemma filter_sublist: forall l f, sublist (filter l f) l.
  Proof.
    induction l; intros; simpl; unfold sublist in *.
    - exists []. now simpl.
    - destruct a as [k v]. destruct (IHl f) as [l4 ?]. destruct (f k).
      + exists l4. simpl. now constructor.
      + exists ((k, v) :: l4).
        pose proof (Permutation_middle (filter l f) l4 (k, v)).
        symmetry. apply perm_trans with ((k, v) :: filter l f ++ l4); auto.
        constructor. now symmetry.
  Qed.

  Lemma filter_set_some_false: forall l k v f,
      Proper (R ==> eq) f -> f k = false -> filter (set_some l k v) f = filter l f.
  Proof.
    intros. induction l; intros; simpl.
    - now rewrite H1.
    - destruct a as [k' v']. destruct (KEqDec k k'); simpl.
      + rewrite H1. rewrite <- e. now rewrite H1.
      + destruct (f k'); auto. now rewrite IHl.
  Qed.

  Instance get_proper: Proper (eq ==> R ==> eq) get.
  Proof.
    repeat intro. subst y. induction x.
    - unfold get. now simpl.
    - destruct a as [k v]. unfold get. simpl.
      destruct (KEqDec x0 k); destruct (KEqDec y0 k); auto; exfalso.
      + rewrite <- e in c. now apply c.
      + rewrite <- e in c. now apply c.
  Qed.

  Lemma get_filter_set_some_neq:
    forall (k : K) (l : list (K * V)) (f : K -> bool) (key : K) (val : V),
      Proper (R ==> eq) f ->
      key =/= k -> get (filter (set_some l key val) f) k = get (filter l f) k.
  Proof.
    intros. induction l; simpl.
    - destruct (f key); auto. unfold get. simpl.
      destruct (KEqDec k key); auto. exfalso. now apply H1.
    - destruct a as [k' v']. destruct (KEqDec key k'); simpl.
      + rewrite e. destruct (f k'); auto. unfold get. simpl.
        destruct (KEqDec k key); destruct (KEqDec k k'); auto; exfalso; intuition.
        rewrite <- e in e0. now apply c.
      + destruct (f k'); auto. destruct (KEqDec k k').
        * rewrite !get_eq_cons; auto.
        * rewrite !get_neq_cons; auto.
  Qed.

  Lemma key_unique_unrelated: forall l f key val,
      Proper (R ==> eq) f ->
      key_unique (filter (set_some l key val) f) = key_unique (filter l f).
  Proof.
    intros. induction l; simpl.
    - destruct (f key); now simpl.
    - destruct a as [k v]. destruct (KEqDec key k).
      + simpl. rewrite e. destruct (f k); auto. simpl. rewrite get_proper; eauto.
      + simpl. destruct (f k); auto. simpl. rewrite get_filter_set_some_neq; auto.
        destruct (get (filter l f) k); auto.
  Qed.

  Lemma get_in_not_none:
    forall (k' : K) (v' : V) (l : list (K * V)) (k : K),
      k === k' -> In (k', v') l -> get l k <> None.
  Proof.
    intros. induction l; intros; unfold get; simpl; auto.
    destruct a as [ka va]. destruct (KEqDec k ka).
    - intro. inversion H2.
    - simpl in H1. destruct H1.
      + inversion H1. subst. exfalso. now apply c.
      + now apply IHl.
  Qed.

  Lemma get_none_sublist: forall l1 l2 k,
      sublist l1 l2 -> get l2 k = None -> get l1 k = None.
  Proof.
    induction l1; intros; unfold get; simpl; auto. destruct a as [k' v'].
    destruct (KEqDec k k').
    - exfalso.
      assert (In (k', v') l2). {
        red in H0. destruct H0 as [l3 ?].
        eapply Permutation_in; eauto. simpl. now left. }
      eapply get_in_not_none; eauto.
    - apply IHl1 with l2; auto. now apply sublist_cons in H0.
  Qed.

  Lemma get_perm_none: forall l1 l2 k,
      Permutation l1 l2 -> get l1 k = None <-> get l2 k = None.
  Proof.
    intros. induction H0.
    - unfold get. simpl. tauto.
    - destruct x as [k' v]. destruct (KEqDec k k').
      + rewrite !get_eq_cons; tauto.
      + rewrite !get_neq_cons; auto.
    - destruct y as [k1 v1]; destruct x as [k2 v2].
      destruct (KEqDec k k1); destruct (KEqDec k k2).
      + rewrite !get_eq_cons; auto. split; intro S; inversion S.
      + rewrite get_eq_cons; auto. rewrite get_neq_cons; auto.
        rewrite get_eq_cons; auto. tauto.
      + rewrite get_neq_cons; auto. rewrite get_eq_cons; auto.
        rewrite get_eq_cons; auto. tauto.
      + rewrite !get_neq_cons; tauto.
    - etransitivity; eauto.
  Qed.

  Lemma key_unique_perm: forall l1 l2,
      Permutation l1 l2 -> key_unique l1 = key_unique l2.
  Proof.
    intros. induction H0.
    - now simpl.
    - simpl. destruct x as [k v].
      destruct (get l k) eqn: ?H; destruct (get l' k) eqn: ?H; auto.
      + symmetry in H0. rewrite get_perm_none in H2; eauto.
        rewrite H1 in H2. inversion H2.
      + rewrite get_perm_none in H1; eauto. rewrite H1 in H2; inversion H2.
    - simpl. destruct x as [k1 v1]; destruct y as [k2 v2]. destruct (KEqDec k1 k2).
      + rewrite !get_eq_cons; auto. now symmetry.
      + rewrite !get_neq_cons; auto. 2: now symmetry.
        destruct (get l k1); destruct (get l k2); auto.
    - etransitivity; eauto.
  Qed.

  Lemma get_app_some: forall l1 l2 k v,
      get l1 k = Some v -> get (l1 ++ l2) k = Some v.
  Proof.
    induction l1; intros.
    - unfold get in H0. simpl in H0. inversion H0.
    - simpl. destruct a as [k' v']. destruct (KEqDec k k').
      + rewrite get_eq_cons in *; auto.
      + rewrite get_neq_cons in *; auto.
  Qed.

  Lemma key_unique_sublist_true: forall l1 l2,
      sublist l1 l2 -> key_unique l2 = true -> key_unique l1 = true.
  Proof.
    induction l1; intros; simpl; auto. destruct a as [k v].
    destruct (get l1 k) eqn: ?H.
    - exfalso. destruct H0 as [l3 ?]. symmetry in H0.
      erewrite key_unique_perm in H1; eauto. simpl in H1.
      destruct (get (l1 ++ l3) k) eqn: ?H. 1: inversion H1.
      erewrite get_app_some in H3; eauto. inversion H3.
    - eapply IHl1; eauto. now apply sublist_cons in H0.
  Qed.

  Lemma key_unique_true_filter: forall l f,
      key_unique l = true -> key_unique (filter l f) = true.
  Proof. intros. apply key_unique_sublist_true with l; auto. apply filter_sublist. Qed.

End AList.
