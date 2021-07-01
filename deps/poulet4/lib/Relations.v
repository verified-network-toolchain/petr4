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

Fixpoint interp_rels {A} (R: rels A) : relation A :=
  match R with
  | [] => ⊤
  | r :: R' => r ⊓ interp_rels R'
  end.
