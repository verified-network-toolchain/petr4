Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.

Set Universe Polymorphism.

Section HAList.
  Variable (K: Type).
  Context `{KEqDec: EqDec K eq}.

  Fixpoint alist_In {A} (k: K) (l: list (K * A)) :=
    match l with
    | (k0, x0) :: l =>
      if KEqDec k0 k
      then True
      else alist_In k l
    | [] => False
    end.

  Inductive alist_NoDup {A} : list (K * A) -> Prop :=
  | NoDupNil: alist_NoDup []
  | NoDupCons:
      forall k a l,
        ~ alist_In k l ->
        alist_NoDup ((k, a) :: l).

  Definition valid_key {A} (l: list (K * A)) :=
    {k: K | alist_In k l}.

  Lemma valid_key_nil:
    forall A (x: @valid_key A []), False.
  Proof.
    unfold valid_key.
    intros.
    destruct x.
    auto.
  Defined.
  Hint Resolve valid_key_nil: halist.

  Lemma valid_key_cons_In:
    forall {A} (l: list (K * A)) (x: valid_key l),
      alist_In (proj1_sig x) l.
  Proof.
    unfold valid_key.
    intros.
    destruct x.
    auto.
  Defined.
  Hint Resolve valid_key_cons_In: halist.

  Lemma valid_key_cons:
    forall {A} k (a: A) l x,
      alist_In x ((k, a)::l) ->
      (x === k) + alist_In x l.
  Proof.
    intros.
    simpl in *.
    destruct (KEqDec k x); intuition.
  Defined.
  Hint Resolve valid_key_cons: halist.

  (* This should be replaced with a library function. *)
  Fixpoint alist_get {A} (l: list (K * A)) (k: valid_key l) : A.
    destruct l.
    - exfalso.
      eauto with halist.
    - destruct k, p.
      assert (H:(x === k) + alist_In x l)
        by eauto with halist.
      destruct H.
      + exact a0.
      + eapply alist_get.
        exists x.
        exact a1.
  Defined.

  Definition signature := list (K * Type).
  Definition valid_signature (s: signature) := alist_NoDup s.

  Fixpoint t (fields: signature) : Type :=
    match fields as f return Type with
    | (field_name, field_type) :: rest =>
      field_type * t rest
    | [] => unit
    end.

  Lemma alist_get_hd:
    forall k (T: Type) fields a0,
      alist_get ((k, T) :: fields) (exist (fun k0 : K => alist_In k0 ((k, T) :: fields)) k a0) = T.
  Proof.
    intros.
    simpl.
    destruct (valid_key_cons k T fields k a0) eqn:?.
    - reflexivity.
    - exfalso.
      simpl in Heqs.
      unfold valid_key_cons in Heqs.
      simpl in a0.
      destruct (KEqDec k k); congruence.
  Defined.

  Lemma alist_In_unique:
    forall k A l (p q: @alist_In A k l),
      p = q.
  Proof.
    induction l as [|[k' v] l].
    - cbv; tauto.
    - intros.
      cbn in *.
      destruct (KEqDec k' k).
      + destruct p, q; reflexivity.
      + apply IHl.
  Defined.

  Lemma alist_get_cons:
    forall k (T: Type) fields x a0 (a1: alist_In x fields),
      k <> x ->
      alist_get ((k, T) :: fields) (exist (fun k0 : K => alist_In k0 ((k, T) :: fields)) x a0) = 
      alist_get fields (exist (fun k0 : K => alist_In k0 fields) x a1).
  Proof.
    intros.
    destruct (valid_key_cons k T fields x a0) eqn:?.
    - congruence.
    - simpl.
      rewrite Heqs.
      f_equal.
      f_equal.
      eapply alist_In_unique.
  Defined.

  Fixpoint get {signature} (l: t signature) (f: valid_key signature)
    : alist_get signature f.
    destruct signature as [|[k T] ?].
    - exfalso.
      eapply valid_key_nil.
      exact f.
    - destruct f.
      pose proof (g := a).
      simpl in g.
      destruct (KEqDec k x).
      + inversion e; subst.
        rewrite alist_get_hd.
        exact (fst l).
      + erewrite alist_get_cons with (a1:=g).
        * eapply get, l.
        * exact c.
  Defined.

  Definition set {signature} (l: t signature) (f: valid_key signature) (v: alist_get signature f)
    : t signature.
  Admitted.

End HAList.

