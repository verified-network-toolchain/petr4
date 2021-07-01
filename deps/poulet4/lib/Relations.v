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

Definition interp_rels {A} (R: rels A) : relation A :=
  List.fold_right relation_conjunction ⊤ R.

Notation "⟦ R ⟧" := (interp_rels R).

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

Definition rels_equiv {A} (R S: rels A) : Prop :=
  relation_equivalence ⟦R⟧ ⟦S⟧.

Global Program Instance rels_Equivalence {A}: Equivalence (@rels_equiv A) :=
  ltac:(typeclasses eauto).

Lemma interp_rels_in:
  forall A (R: rels A),
    forall x y,
      interp_rels R x y ->
      forall r, In r R -> r x y.
Proof.
  induction R; intros.
  - inversion H0.
  - inversion H0; subst; clear H0.
    + simpl in *.
      apply H.
    + destruct H; eapply IHR; auto.
Qed.

Lemma in_interp_rels:
  forall A (R: rels A),
    forall x y,
    (forall r, In r R -> r x y) ->
    interp_rels R x y.
Proof.
  induction R; intros.
  - exact I.
  - simpl; split.
    + apply H.
      eauto with datatypes. 
    + apply IHR; intros.
      eapply H.
      right.
      apply H0.
Qed.

Lemma interp_rels_mono:
  forall A (R S: rels A),
    forall x y,
      interp_rels S x y ->
      (forall r, In r R -> In r S) ->
      interp_rels R x y.
Proof.
  induction R.
  - intros.
    exact I.
  - unfold interp_rels in *.
    intros.
    simpl.
    split.
    + assert (In a (a :: R))
        by (eauto with datatypes).
      eapply interp_rels_in in H; eauto.
    + eapply (IHR S); eauto.
      intros.
      eauto with datatypes.
Qed.
