Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.

Section HAList.
  Parameter (K: Type).
  Context `{KEqDec: EqDec K eq}.

  Fixpoint alist_In {A} (k: K) (l: list (K * A)) :=
    match l with
    | (k0, x0) :: l =>
      if KEqDec k0 k
      then True
      else alist_In k l
    | [] => False
    end.

  Definition valid_key {A} (l: list (K * A)) :=
    {k: K | alist_In k l}.

  Lemma valid_key_nil:
    forall A (x: @valid_key A []), False.
  Proof.
    unfold valid_key.
    intros.
    destruct x.
    auto.
  Qed.
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
      {x === k} + {alist_In x l}.
  Proof.
    intros.
    simpl in *.
    destruct (KEqDec k x); intuition.
  Defined.
  Hint Resolve valid_key_cons: halist.

  (* This should be replaced with a library function. *)
  Fixpoint alist_get {A} (l: list (K * A)) (k: valid_key l) : A.
    induction l.
    - exfalso.
      eauto with halist.
    - destruct k, a.
      assert (H:{x === k} + {alist_In x l})
        by eauto with halist.
      destruct H.
      + exact a.
      + apply IHl.
        exists x.
        exact a1.
  Defined.

  Fixpoint t (field_types: list (K * Type)) : Type :=
    match field_types with
    | (field_name, field_type) :: rest =>
      ({k: K | k === field_name} * field_type) * t rest
    | [] => unit
    end.

  Lemma alist_get_hd:
    forall k (T: Type) signature x a0,
      alist_get ((k, T) :: signature) (exist (fun k0 : K => alist_In k0 ((k, T) :: signature)) x a0) = T.
  Proof.
    intros.
    simpl.
    destruct (valid_key_cons k T signature x a0) eqn:?.
    - reflexivity.
    - exfalso.
      unfold valid_key_cons in Heqs.
      set (e := KEqDec k x).
      change (KEqDec k x) with e in Heqs.
      revert Heqs.
      admit.
  Admitted.

  Definition get {signature} (l: t signature) (f: valid_key signature)
    : alist_get signature f.
    induction signature.
    - exfalso.
      eauto with halist.
    - destruct f, a.
      assert (H:{x === k} + {alist_In x signature})
        by eauto with halist.
      destruct H.
      + rewrite alist_get_hd.
        simpl in a0.
        destruct l.
        destruct p.
        exact t1.
      + destruct (KEqDec k x) eqn:?.
        * simpl.
          unfold valid_key_cons.
  Admitted.

End HAList.
