Require Import Coq.Lists.List.
Require Import Coq.Program.Program.
Import ListNotations.
Require Import Coq.Classes.EquivDec.

(* based roughly on stdpp.finite *)
Class Finite (A: Type) `{EqDec A Logic.eq} := {
  enum: list A;
  NoDup_enum: NoDup enum;
  elem_of_enum: forall (x: A), In x enum
}.
Global Arguments enum _ {_} {_} {_}.

Global Program Instance UnitFinite: Finite unit :=
  {| enum := [tt] |}.
Next Obligation.
  constructor; eauto.
  constructor.
Qed.
Next Obligation.
  destruct x.
  auto.
Qed.

Lemma NoDup_app :
  forall A (l l': list A),
    NoDup l ->
    NoDup l' ->
    (forall x, In x l -> ~ In x l') ->
    (forall x, In x l' -> ~ In x l) ->
    NoDup (l ++ l').
Proof.
  induction l; destruct l'; simpl; autorewrite with list; auto.
  intros.
  constructor.
  + intro.
    inversion H; subst.
    apply in_app_or in H3.
    destruct H3; auto.
    eapply H2; eauto with datatypes.
  + eapply IHl; eauto with datatypes.
    * inversion H; auto.
    * intuition eauto with datatypes.
Qed.

Lemma NoDup_map:
  forall A B (f: A -> B) l,
    (forall x y, f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros.
  induction l; simpl; constructor.
  - intro Hin.
    apply in_map_iff in Hin.
    destruct Hin as [x [Heq Hin]].
    apply H in Heq.
    subst.
    inversion H0.
    congruence.
  - inversion H0.
    eauto.
Qed.

Global Program Instance SumFinite A B `{Finite A} `{Finite B} : Finite (A + B) :=
  {| enum := List.map inl (enum A) ++ List.map inr (enum B) |}.
Next Obligation.
  eapply NoDup_app; eauto.
  - eapply NoDup_map; try congruence.
    apply NoDup_enum.
  - eapply NoDup_map; try congruence.
    apply NoDup_enum.
  - destruct x; intros Hin Hnin;
      apply in_map_iff in Hnin;
      apply in_map_iff in Hin;
      firstorder congruence.
  - destruct x; intros Hin Hnin;
      apply in_map_iff in Hnin;
      apply in_map_iff in Hin;
      firstorder congruence.
Qed.
Next Obligation.
  destruct x.
  - eapply in_or_app.
    left; eapply in_map; eapply elem_of_enum.
  - eapply in_or_app.
    right; eapply in_map; eapply elem_of_enum.
Qed.

