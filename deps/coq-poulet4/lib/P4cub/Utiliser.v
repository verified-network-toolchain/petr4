Require Export Coq.Classes.EquivDec.
Require Export Coq.Numbers.BinNums. (** Integers. *)
Require Coq.Strings.String.
Module Strings := Coq.Strings.String.
Require Petr4.P4String. (** Strings. *)
Require Petr4.Typed. (** Names. *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

(** * Useful Functions And Lemmas *)

(** Update position [n] of list [l],
    or return [l] if [n] is too large. *)
Fixpoint nth_update {A : Type} (n : nat) (a : A) (l : list A) : list A :=
  match n, l with
  | O, _::t   => a::t
  | S n, h::t => h :: nth_update n a t
  | O, []
  | S _, []  => []
  end.
(**[]*)

Lemma nth_error_exists : forall {A:Type} (l : list A) n,
    n < length l -> exists a, nth_error l n = Some a.
Proof.
  intros A l; induction l as [| h t IHt];
    intros [] Hnl; simpl in *; try lia.
  - exists h; reflexivity.
  - apply IHt; lia.
Qed.

Lemma Forall_nth_error : forall {A : Type} (P : A -> Prop) l n a,
    Forall P l -> nth_error l n = Some a -> P a.
Proof.
  intros A P l n a HPl Hnth.
  eapply Forall_forall in HPl; eauto.
  eapply nth_error_In; eauto.
Qed.

Lemma Forall2_length : forall {A B : Type} (R : A -> B -> Prop) l1 l2,
    Forall2 R l1 l2 -> length l1 = length l2.
Proof. intros A B R l1 l2 H; induction H; simpl; auto. Qed.

(** * Option Equivalence *)

Inductive relop {A : Type} (R : A -> A -> Prop) : option A -> option A -> Prop :=
| relop_none : relop R None None
| relop_some (a1 a2 : A) : R a1 a2 -> relop R (Some a1) (Some a2).

Instance OptionEquivalence
         (A : Type) (R : A -> A -> Prop)
         `{Equivalence A R} : Equivalence (relop R).
Proof.
  inversion H; constructor;
    unfold Reflexive, Symmetric, Transitive in *.
  - intros [a |]; constructor; auto.
  - intros [a1 |] [a2 |] H'; inversion H';
      subst; constructor; auto.
  - intros [a1 |] [a2 |] [a3 |] H12 H23;
      inversion H12; inversion H23;
        subst; constructor; eauto.
Defined.

Instance OptionEqDec
         (A : Type) (R : A -> A -> Prop)
         `{HR : EqDec A R} : EqDec (option A) (relop R).
Proof.
  unfold EqDec in *;
    unfold equiv, complement in *;
    intros [a1 |] [a2 |];
    try (specialize HR with a1 a2; destruct HR as [HR | HR]);
    try (right; intros H'; inversion H'; contradiction);
    try (left; constructor; auto).
Defined.

(** * Equivalence for Petr4 Base Data Types *)

Instance PositiveEqDec : EqDec positive eq := { equiv_dec := BinPos.Pos.eq_dec }.

Instance NEqDec : EqDec N eq := { equiv_dec := BinNat.N.eq_dec }.

Instance ZEqDec : EqDec Z eq := { equiv_dec := BinInt.Z.eq_dec }.

Instance StringEqDec : EqDec Strings.string eq := { equiv_dec := Strings.string_dec }.

Section TypeSynonyms.
  Variable (tags_t : Type).

  Definition string : Type := Petr4.P4String.t tags_t.

  Global Instance P4StringEqDec : EqDec string (@P4String.equiv tags_t) :=
    P4String.P4StringEqDec tags_t.
  (**[]*)

  Definition int : Type := Petr4.P4Int.t tags_t.

  Global Instance P4IntEquivalence : Equivalence (@P4Int.equiv tags_t) :=
    P4Int.IntEquivalence tags_t.
  (**[]*)

  Global Instance P4IntEqDec : EqDec int (P4Int.equiv) :=
    P4Int.IntEqDec tags_t.
  (**[]*)

  Definition name : Type := @Typed.name tags_t.

  Definition equivn (n1 n2 : name) : Prop :=
    match n1, n2 with
    | Typed.BareName x1,
      Typed.BareName x2          => P4String.equiv x1 x2
    | Typed.QualifiedName xs1 x1,
      Typed.QualifiedName xs2 x2 =>
        P4String.equiv x1 x2 /\
        List.Forall2 (@P4String.equiv tags_t) xs1 xs2
    | _, _ => False
    end.

  Lemma equivn_reflexive : Reflexive equivn.
  Proof.
    intros [x | xs x]; simpl.
    - reflexivity.
    - split; try reflexivity.
      induction xs as [| h xs IHxs];
        constructor; auto. reflexivity.
  Qed.

  Lemma equivn_symmetric : Symmetric equivn.
  Proof.
    intros [x | xs x] [y | ys y] H; simpl in *; auto.
    - symmetry. assumption.
    - destruct H as [Hxy H]. split; try (symmetry; assumption).
      generalize dependent ys; induction xs as [| hx xs IHxs];
        intros [| hy ys] H; inversion H; clear H; subst; auto;
      constructor; auto. symmetry. assumption.
  Qed.

  Lemma equivn_transitive : Transitive equivn.
  Proof.
    intros [x | xs x] [y | ys y] [z | zs z] Hxy Hyz;
      simpl in *; auto; try contradiction.
    - transitivity y; auto.
    - destruct Hxy as [Hxy Hxys]; destruct Hyz as [Hyz Hyzs]; split.
      + transitivity y; auto.
      + clear x y z Hxy Hyz.
        generalize dependent zs; generalize dependent ys.
        induction xs as [| x xs IHxs];
          intros [| y ys] Hxy [| z zs] Hyz;
          inversion Hxy; clear Hxy;
            inversion Hyz; clear Hyz; subst; auto.
        constructor.
        * transitivity y; auto.
        * apply IHxs with ys; auto.
  Qed.

  Global Instance NameEquivalence : Equivalence equivn.
  Proof.
    constructor; [ apply equivn_reflexive
                 | apply equivn_symmetric
                 | apply equivn_transitive].
  Defined.

  Definition equivn_dec : forall n1 n2 : name,
      { equivn n1 n2 } + { ~ equivn n1 n2 }.
  Proof.
    intros [x | xs x] [y | ys y]; simpl; auto.
    - pose proof equiv_dec x y; auto.
    - assert (H : {List.Forall2 (@P4String.equiv tags_t) xs ys} +
                  {~ List.Forall2 (@P4String.equiv tags_t) xs ys}).
      { clear x y; generalize dependent ys.
        induction xs as [| x xs IHxs]; intros [| y ys];
          try (right; intros H'; inversion H'; contradiction).
        - left; constructor.
        - pose proof equiv_dec x y as Hxy; specialize IHxs with ys;
            unfold equiv in *; unfold complement in *.
          destruct Hxy as [Hxy | Hxy]; destruct IHxs as [IH | IH];
            try (right; intros H'; inversion H'; contradiction).
          left. constructor; auto. }
      destruct (equiv_dec x y) as [Hxy | Hxy]; destruct H as [H | H];
        unfold equiv in *; unfold complement in *;
          try (right; intros [Hxy' H']; contradiction).
      left; auto.
  Defined.

  Global Instance NameEqDec : EqDec name equivn :=
    { equiv_dec := equivn_dec }.
  (**[]*)
End TypeSynonyms.

(** * Useful Operators *)

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := Basics.compose (at level 40, left associativity).

(** * Useful Tactics *)

Ltac inv H := inversion H; clear H; subst.
