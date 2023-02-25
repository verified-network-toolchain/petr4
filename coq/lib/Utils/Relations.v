Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Export ListNotations.

Notation rel A := (relation A).
Definition rels A :=
  list (relation A).

Definition rel_true: forall {A}, relation A :=
  fun _ x y => True.

Notation "⊤" := rel_true.
Notation "x ⊓ y" := (relation_conjunction x y) (at level 40).

Definition interp_rels {A} (i: rel A) (R: rels A) : relation A :=
  List.fold_right relation_conjunction i R.

Local Program Instance f_Equivalence {A B} {equiv: rel B} `{Equivalence B equiv} (f: A -> B): Equivalence (fun x y => equiv (f x) (f y)).
Next Obligation.
  repeat intro.
  eapply Equivalence_Reflexive; eauto.
Qed.
Next Obligation.
  repeat intro.
  eapply Equivalence_Symmetric; eauto.
Qed.
Next Obligation.
  repeat intro.
  eapply Equivalence_Transitive; eauto.
Qed.

Definition rels_equiv {A} i (R S: rels A) : Prop :=
  relation_equivalence (interp_rels i R) (interp_rels i S).

Global Program Instance rels_Equivalence {A i}: Equivalence (@rels_equiv A i) :=
  ltac:(typeclasses eauto).

Lemma interp_rels_in:
  forall A (R: rels A) i,
    forall x y,
      interp_rels i R x y ->
      forall r, In r R -> r x y.
Proof.
  induction R; intros.
  - inversion H0.
  - inversion H0; subst; clear H0.
    + simpl in *.
      apply H.
    + destruct H; eapply IHR; eauto.
Qed.

Lemma in_interp_rels:
  forall A (i: rel A) (R: rels A),
    forall x y,
      i x y ->
      (forall r, In r R -> r x y) ->
      interp_rels i R x y.
Proof.
  induction R; intros.
  - eauto.
  - simpl in *.
    split.
    + eapply H0; eauto.
    + eapply IHR; eauto.
      firstorder.
Qed.

Lemma interp_rels_mono:
  forall A (i: rel A) (R S: rels A),
    forall x y,
      i x y ->
      interp_rels i S x y ->
      (forall r, In r R -> In r S) ->
      interp_rels i R x y.
Proof.
  induction R.
  - eauto.
  - unfold interp_rels in *.
    intros.
    simpl.
    split.
    + assert (In a (a :: R))
        by (eauto with datatypes).
      eapply interp_rels_in in H0; eauto.
    + eapply (IHR S); eauto.
      intros.
      eauto with datatypes.
Qed.

Lemma interp_rels_map:
  forall A B i (f: A -> rel B) l x y,
    interp_rels i (map f l) x y ->
    forall a,
      In a l -> f a x y.
Proof.
  intros.
  eapply interp_rels_in; eauto using in_map.
Qed.
