Require Export Coq.Classes.EquivDec.
Require Export Coq.Numbers.BinNums. (** Integers. *)
Require Coq.Strings.String.
Module Strings := Coq.Strings.String.
Require Poulet4.P4String. (** Strings. *)
Require Poulet4.Typed. (** Names. *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

(** * Useful Operators *)

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := Basics.compose (at level 40, left associativity).

(** Haskell's [$] operator, Coq is angry at the "$" token. *)
Infix "#" := Basics.apply (at level 75, right associativity).

(** * Useful Notations *)
Notation "a '&&&&' b"
  := (if a then if b then true else false else false)
       (at level 60, right associativity).

Notation "a '||||' b"
  := (if a then true else if b then true else false)
       (at level 70, right associativity).

(** * Useful Tactics *)

Ltac inv H := inversion H; clear H; subst.

Ltac inv_eq :=
        match goal with
        | H: _ = _ |- _ => inv H
        end.
(**[]*)

Ltac inv_Forall_cons :=
  match goal with
  | H: Forall _ (_ :: _) |- _ => inv H
  end.
(**[]*)

Ltac ind_list_Forall :=
  match goal with
  | H: Forall _ ?l
    |- _ => induction l; try inv_Forall_cons
  end.
(**[]*)

Ltac rewrite_goal_l :=
  match goal with
  | H: ?a = ?b |- context [ ?a ] => repeat rewrite H; clear H
  end.

Ltac rewrite_goal_r :=
  match goal with
  | H: ?a = ?b |- context [ ?b ] => repeat rewrite <- H; clear H
  end.

Ltac rewrite_true :=
  match goal with
  | H: _ = true |- _ => rewrite_goal_l
  | H: true = _ |- _ => rewrite_goal_r
  end.

Ltac destruct_andb :=
  match goal with
  | H: (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H as [? ?]
  end.

Ltac destruct_orb :=
  match goal with
  | H: (_ || _)%bool = true |- _ => apply Bool.orb_true_iff in H as [? ?]
  end.

Ltac reflect_split :=
  match goal with
  | |- Bool.reflect ?P ?trm
    => destruct trm eqn:?; constructor;
      try match goal with
          | H: _ = false |- ~ _
            => intros ?
          end
  end.

(** * Useful Data Types *)

Inductive either (A B : Type) : Type :=
| Left (a : A)
| Right (b : B).
(**[]*)

Arguments Left {_ _}.
Arguments Right {_ _}.

(** * Useful Functions And Lemmas *)

Lemma ex_equiv_dec_refl :
  forall (X : Type) (x : X) (R : X -> X -> Prop) `{EqDec X R},
    exists l, equiv_dec x x = left l.
Proof.
  intros; destruct (equiv_dec x x) as [Hx | Hx];
  unfold equiv, complement in *; eauto.
  assert (R x x) by reflexivity; contradiction.
Qed.

Ltac equiv_dec_refl_tactic :=
  match goal with
  | |- context [equiv_dec ?x ?x]
    => destruct (equiv_dec x x) as [? | ?];
      unfold equiv, complement in *; try contradiction
  end.

Lemma equiv_dec_refl :
  forall (X Y : Type) (x : X) (y1 y2 : Y) (R : X -> X -> Prop) `{EqDec X R},
    (if equiv_dec x x then y1 else y2) = y1.
Proof.
  intros. destruct (equiv_dec x x) as [Hxx | Hxx]; auto.
  assert (Hx : R x x) by reflexivity. contradiction.
Qed.

Lemma lifted_andb_refl_r :
  forall {X : Type} (x : X) (R : X -> X -> Prop) `{EqDec X R} (b : bool),
    equiv_dec x x &&&& b = b.
Proof.
  intros; destruct (equiv_dec x x) as [Hxx | Hxx]; destruct b; auto.
  assert (Hx : R x x) by reflexivity. contradiction.
Qed.

Lemma lifted_andb_true :
  forall {X : Type} (x1 x2 : X) (R : X -> X -> Prop) `{EqDec X R} (b : bool),
    equiv_dec x1 x2 &&&& b = true -> equiv x1 x2 /\ b = true.
Proof.
  intros X x1 x2 R EQR EQDECR b H.
  destruct (equiv_dec x1 x2) as [Hx | Hx]; destruct b;
  simpl in *; try discriminate; intuition.
Qed.

Ltac destruct_lifted_andb :=
  match goal with
  | H: _ &&&& _ = true |- _ => apply lifted_andb_true in H as [? ?]
  end.

(** Temporary bind. *)
Definition bind_option {A B : Type}
           (ma : option A) (f : A -> option B) : option B :=
  match ma with
  | None => None
  | Some a => f a
  end.

Definition map_option {A B : Type} (ma : option A) (f : A -> B) : option B :=
  bind_option ma (Some ∘ f).

Definition curry3 {A B C D : Type}
           (f : A * B * C -> D) : A -> B -> C -> D :=
  fun a b c => f (a,b,c).
(**[]*)

Definition uncurry3 {A B C D : Type}
           (f : A -> B -> C -> D) '((a,b,c) : A * B * C) : D :=
  f a b c.
(**[]*)

Definition curry4 {A B C D E : Type}
           (f : A * B * C * D -> E) : A -> B -> C -> D -> E :=
  fun a b c d => f (a,b,c,d).
(**[]*)

Definition uncurry4 {A B C D E : Type}
           (f : A -> B -> C -> D -> E) '((a,b,c,d) : A * B * C * D) : E :=
  f a b c d.
(**[]*)

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

Section Forall2_Equivalence.
  Context {A : Type}.

  Variable R : A -> A -> Prop.

  Context `{Equivalence A R}.

  Lemma Forall2_reflexive : Reflexive (Forall2 R).
  Proof.
    intros l; induction l; constructor; auto; reflexivity.
  Qed.

  Lemma Forall2_symmetric : Symmetric (Forall2 R).
  Proof.
    intros ? ? ?;
           match goal with
           | H: Forall2 R _ _ |- _ => induction H
           end; constructor; auto;
      symmetry; assumption.
  Qed.

  Lemma Forall2_transitive : Transitive (Forall2 R).
  Proof.
    intros l1; induction l1 as [| ? ? ?];
      intros [| ? ?] [| ? ?] ? ?;
             repeat match goal with
                    | H: Forall2 R (_ :: _) _ |- _ => inv H
                    | H: Forall2 R _ (_ :: _) |- _ => inv H
                    end;
      constructor; eauto; etransitivity; eauto.
  Qed.

  Global Instance Forall2Equiv : Equivalence (Forall2 R).
  Proof.
    constructor;
      [ apply Forall2_reflexive
      | apply Forall2_symmetric
      | apply Forall2_transitive ]; assumption.
  Defined.
End Forall2_Equivalence.

Lemma Forall_nth_error : forall {A : Type} (P : A -> Prop) l n a,
    Forall P l -> nth_error l n = Some a -> P a.
Proof.
  intros A P l n a HPl Hnth.
  eapply Forall_forall in HPl; eauto.
  eapply nth_error_In; eauto.
Qed.

Lemma In_repeat : forall {A : Type} (a : A) n,
    0 < n -> In a (repeat a n).
Proof.
  intros A a [|] H; try lia; simpl; intuition.
Qed.

Lemma Forall_repeat : forall {A : Type} (P : A -> Prop) n a,
    0 < n -> Forall P (repeat a n) -> P a.
Proof.
  intros A P n a Hn H.
  eapply Forall_forall in H; eauto.
  apply In_repeat; auto.
Qed.

Lemma repeat_Forall : forall {A : Type} (P : A -> Prop) n a,
    P a -> Forall P (repeat a n).
Proof.
  intros A P n a H.
  induction n as [| n IHn]; simpl; constructor; auto.
Qed.

Lemma Forall_firstn : forall {A : Type} (P : A -> Prop) n l,
    Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l H. rewrite <- firstn_skipn with (n := n) in H.
  apply Forall_app in H. intuition.
Qed.

Lemma Forall_skipn : forall {A : Type} (P : A -> Prop) n l,
    Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n l H. rewrite <- firstn_skipn with (n := n) in H.
  apply Forall_app in H. intuition.
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

Section ProdEquivalence.
  Context {A B : Type}.

  Variable RA : A -> A -> Prop.

  Variable RB : B -> B -> Prop.

  Context `{Equivalence A RA}.

  Context `{Equivalence B RB}.

  Let RAB ab1 ab2 := RA (fst ab1) # fst ab2 /\ RB (snd ab1) # snd ab2.

  Lemma prod_reflexive : Reflexive RAB.
  Proof.
    intros [? ?]; cbv; intuition.
  Qed.

  Lemma prod_symmetric : Symmetric RAB.
    intros [? ?] [? ?] [? ?]; cbv in *; intuition.
  Qed.

  Lemma prod_transitive : Transitive RAB.
  Proof.
    intros [? ?] [? ?] [? ?] [? ?] [? ?];
      cbv in *; split; etransitivity; eauto.
  Qed.

  Global Instance ProdEquiv : Equivalence RAB.
  Proof.
    constructor;
      [ apply prod_reflexive
      | apply prod_symmetric
      | apply prod_transitive ]; assumption.
  Defined.
End ProdEquivalence.

(** * Equivalence for Petr4 Base Data Types *)

Instance PositiveEqDec : EqDec positive eq := { equiv_dec := BinPos.Pos.eq_dec }.

Instance NEqDec : EqDec N eq := { equiv_dec := BinNat.N.eq_dec }.

Instance ZEqDec : EqDec Z eq := { equiv_dec := BinInt.Z.eq_dec }.

(** Tag-less strings. *)
Definition string := String.string.

Instance StringEqDec : EqDec string eq := { equiv_dec := Strings.string_dec }.

Section TypeSynonyms.
  Variable (tags_t : Type).

  (** Tagged strings. *)
  Definition p4string : Type := Poulet4.P4String.t tags_t.

  Global Instance P4StringEqDec : EqDec p4string (@P4String.equiv tags_t) :=
    P4String.P4StringEqDec tags_t.
  (**[]*)

(* Not used in P4cub.
  Definition int : Type := Poulet4.P4Int.t tags_t.

  Global Instance P4IntEquivalence : Equivalence (@P4Int.equiv tags_t) :=
    P4Int.IntEquivalence tags_t.
  (**[]*)

  Global Instance P4IntEqDec : EqDec int (P4Int.equiv) :=
    P4Int.IntEqDec tags_t.
  (**[]*)
*)

(* Qualified names will no longer be used in p4cub.
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
    intros [? | ? ?]; simpl; repeat split; reflexivity.
  Qed.

  Lemma equivn_symmetric : Symmetric equivn.
  Proof.
    intros [x | xs x] [y | ys y] H; simpl in *; auto.
    - symmetry. assumption.
    - destruct H as [Hxy H]. split; try (symmetry; assumption).
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
*)
End TypeSynonyms.
