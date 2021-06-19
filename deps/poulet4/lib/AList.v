Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Import ListNotations.

Definition AList
    (K V: Type)
    (R: Relation_Definitions.relation K)
    `{Equivalence K R} :=
  list (K * V)
.

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

End AList.
