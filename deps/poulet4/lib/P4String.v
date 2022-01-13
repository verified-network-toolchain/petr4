Require Import Coq.Strings.String.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Poulet4.AList.
Import ListNotations.

Instance StrEqDec:EqDec string eq.
Proof.
  unfold EqDec.
  apply string_dec.
Defined.

Record t (tags_t: Type) :=
  { tags: tags_t;
    str: string }.
Arguments tags {tags_t}.
Arguments str {tags_t}.

Definition empty_str [tags_t: Type] (tag : tags_t) :  (t tags_t) :=
  {| tags := tag; str := "" |}.

Definition strip [tags_t: Type] (s: t tags_t) :=
  {| tags := tt; str := s.(str) |}.

Definition equiv [tags_t: Type] (s1 s2: t tags_t) : Prop :=
  s1.(str) = s2.(str).

Definition equivb [tags_t: Type] (s1 s2: t tags_t) :=
  String.eqb s1.(str) s2.(str).

Definition nequivb [tags_t: Type] (s1 s2: t tags_t) :=
  negb (String.eqb s1.(str) s2.(str)).

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

Lemma equiv_reflect {tags_t : Type} : forall s1 s2 : t tags_t,
    reflect (equiv s1 s2) (equivb s1 s2).
Proof.
  intros [s1 t1] [s2 t2]. unfold equiv, equivb; simpl.
  apply Coq.Strings.String.eqb_spec.
Qed.

Section AList.
  Variables tags_t V : Type.

  Definition AList := AList.AList (t tags_t) V (@equiv tags_t).

  Definition clear_AList_tags : AList -> AList.StringAList V :=
    List.map (fun '(x, v) => (str x,v)).

  Lemma get_clear_AList_tags : forall vs x,
      AList.get vs x = AList.get (clear_AList_tags vs) (str x).
  Proof.
    unfold AList.get, clear_AList_tags;
      intros vs [t x]; induction vs as [| [[i y] v] vs IHvs];
        simpl in *; auto.
    destruct (string_dec x y) as [Hxy | Hxy];
      destruct (StrEqDec x y) as [Hxy' | Hxy'];
      unfold "=/=", "===" in *; subst; try contradiction; auto.
  Qed.
End AList.

Arguments clear_AList_tags {_} {_}.
