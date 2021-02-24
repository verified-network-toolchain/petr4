Require Coq.Strings.String.
Module CoqString := Coq.Strings.String.
Require Import Coq.Classes.EquivDec.

(** Coq string type. *)
Definition string := CoqString.string.

Record t (tags_t: Type) :=
  { tags: tags_t;
    str: string }.
Arguments tags [tags_t] _.
Arguments str [tags_t] _.

Definition strip [tags_t: Type] (s: t tags_t) :=
  {| tags := tt; str := s.(str) |}.

Definition equiv [tags_t: Type] (s1 s2: t tags_t) : Prop :=
  s1.(str) = s2.(str).

Definition equivb [tags_t: Type] (s1 s2: t tags_t) :=
  String.eqb s1.(str) s2.(str).

Definition eq_const [tags_t: Type] (s1: t tags_t) (s2: string) :=
  String.eqb s1.(str) s2.

Instance EquivEquivalence (tags_t : Type) : Equivalence (@equiv tags_t).
Proof.
  constructor.
  - constructor.
  - intros [] [] H; unfold equiv in *; simpl in *; subst; auto.
  - intros [] [] [] H1 H2; unfold equiv in *; simpl in *; subst; auto.
Defined.

Instance P4StringEqDec (tags_t : Type) : EqDec (t tags_t) (@equiv tags_t).
Proof.
  intros [t1 s1] [t2 s2].
  unfold Equivalence.equiv; unfold complement; simpl; unfold equiv; simpl.
  apply String.string_dec.
Defined.
