Require Export Coq.Classes.EquivDec.
Require Export Coq.Numbers.BinNums. (** Integers. *)
Require Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Export ListNotations.
Require Import Coq.micromega.Lia.

Require Export Poulet4.Monads.Monad.
Require Export Poulet4.Monads.Option.

(** * Useful Operators *)

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := Basics.compose (at level 40, left associativity).

Infix "$" := Basics.apply (at level 41, right associativity).

(** * Useful Notations *)
Notation "a '&&&&' b"
  := (if a then if b then true else false else false)
       (at level 60, right associativity).

Notation "a '||||' b"
  := (if a then true else if b then true else false)
       (at level 70, right associativity).

(** * Useful Tactics *)

Tactic Notation "unravel" :=
  simpl;
  unfold "∘", "$", "▷",
  mret, mbind, option_ret, option_bind,
  equiv, complement; simpl.

Tactic Notation "unravel" "in" hyp(H) :=
  simpl in H;
  unfold "∘", "$", "▷",
  mret, mbind, option_ret, option_bind,
  equiv, complement in H; simpl in H.

Tactic Notation "unravel" "in" "*" :=
  simpl in *;
  unfold "∘", "$", "▷",
  mret, mbind, option_ret, option_bind,
  equiv, complement in *; simpl in *.

Ltac inv H := inversion H; clear H; subst.

Ltac inv_eq :=
        match goal with
        | H: _ = _ |- _ => inv H
        end.
(**[]*)

Ltac subst_term :=
  match goal with
  | x := _ |- _ => subst x
  end.
(**[]*)

Ltac solve_eqn :=
  match goal with
  | Ha: ?x = ?a, Hb: ?x = ?b
    |- _ => rewrite Ha in Hb; inv Hb
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

Ltac inv_Forall2_cons :=
  match goal with
  | H: Forall2 _ _ (_ :: _) |- _ => inv H
  | H: Forall2 _ (_ :: _) _ |- _ => inv H
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

Lemma Forall_until_eq : forall {A : Type} (P : A -> Prop) prf1 prf2 a1 a2 suf1 suf2,
    Forall P prf1 -> Forall P prf2 -> ~ P a1 -> ~ P a2 ->
    prf1 ++ a1 :: suf1 = prf2 ++ a2 :: suf2 ->
    prf1 = prf2 /\ a1 = a2 /\ suf1 = suf2.
Proof.
  intros A P prf1;
  induction prf1 as [| hp1 tp1 IHtp1 ];
  intros [| hp2 tp2 ] a1 a2 suf1 suf2 Hp1 Hp2 Ha1 Ha2 Heq;
  repeat inv_Forall_cons; simpl in *; inv Heq;
  try contradiction; try auto 3.
  apply IHtp1 in H5; intuition; subst; reflexivity.
Qed.

Lemma map_compose : forall {A B C : Type} (f : A -> B) (g : B -> C) l,
    map (g ∘ f) l = map g (map f l).
Proof.
  intros; induction l; unravel in *; auto.
  rewrite IHl; reflexivity.
Qed.

Lemma split_map : forall {A B : Type} (l : list (A * B)),
    split l = (map fst l, map snd l).
Proof.
  induction l as [| [a b] l IHl]; unravel; auto.
  destruct (split l) as [la lb] eqn:eqsplit.
  inv IHl; reflexivity.
Qed.

Lemma ex_equiv_dec_refl :
  forall (X : Type) (x : X) (R : X -> X -> Prop) `{EqDec X R},
    exists l, equiv_dec x x = left l.
Proof.
  intros; destruct (equiv_dec x x) as [Hx | Hx];
  unravel in *; eauto. assert (R x x) by reflexivity; contradiction.
Qed.

Ltac equiv_dec_refl_tactic :=
  match goal with
  | |- context [equiv_dec ?x ?x]
    => destruct (equiv_dec x x) as [? | ?];
      unravel in *; try contradiction
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
  unravel in *; try discriminate; intuition.
Qed.

Ltac destruct_lifted_andb :=
  match goal with
  | H: _ &&&& _ = true |- _ => apply lifted_andb_true in H as [? ?]
  end.

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

Definition fourple_1 {A B C D : Type}  '((a,_,_,_) : A * B * C * D) : A := a.

Definition fourple_2 {A B C D : Type}  '((_,b,_,_) : A * B * C * D) : B := b.

Definition fourple_3 {A B C D : Type}  '((_,_,c,_) : A * B * C * D) : C := c.

Definition fourple_4 {A B C D : Type}  '((_,_,_,d) : A * B * C * D) : D := d.

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
    intros [] Hnl; unravel in *; try lia.
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
  intros A a [|] H; try lia; unravel; intuition.
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
  induction n as [| n IHn]; unravel; constructor; auto.
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
Proof. intros A B R l1 l2 H; induction H; unravel; auto. Qed.

Lemma Forall2_duh : forall {A B : Type} (P : A -> B -> Prop),
    (forall a b, P a b) ->
    forall la lb, length la = length lb -> Forall2 P la lb.
Proof.
  induction la; destruct lb; intros;
  unravel in *; try discriminate; constructor; auto.
Qed.

Lemma Forall2_map_l : forall {A B C : Type} (f : A -> B) (R : B -> C -> Prop) la lc,
    Forall2 R (map f la) lc <-> Forall2 (R ∘ f) la lc.
Proof.
  induction la as [| a la IHal]; intros [| c lc];
  unravel in *; split; intros; intuition; inv_Forall2_cons;
  constructor; try apply IHal; auto.
Qed.

Lemma Forall2_Forall : forall {A : Type} (R : A -> A -> Prop) l,
    Forall2 R l l <-> Forall (fun a => R a a) l.
Proof.
  induction l; split; intros;
  try inv_Forall_cons;  try inv_Forall2_cons; intuition.
Qed.

Lemma Forall_duh : forall {A : Type} (P : A -> Prop),
    (forall a, P a) -> forall l, Forall P l.
Proof.
  induction l; constructor; auto.
Qed.

Lemma Forall_exists_prefix_only_or_all : forall {A : Type} (P : A -> Prop) (l : list A),
    (forall a, P a \/ ~ P a) ->
    Forall P l \/ exists a prefix suffix, l = prefix ++ a :: suffix /\ Forall P prefix /\ ~ P a.
Proof.
  intros A P l HP;
  induction l as [| h t [IHt | [a [prf [suf [Heq [Hprf Ha]]]]]]];
  intuition; subst.
  - destruct (HP h) as [? | ?]; intuition.
    right. exists h; exists []; exists t; intuition.
  - right. destruct (HP h) as [? | ?].
    + exists a; exists (h :: prf); exists suf; intuition.
    + exists h; exists []; exists (prf ++ a :: suf); intuition.
Qed.

(** Option Predicate *)
Inductive predop {A : Type} (P : A -> Prop) : option A -> Prop :=
| predop_none : predop P None
| predop_some (a : A) : P a -> predop P (Some a).

(** * Option Relations *)
Section Relop.
  Context {A B : Type}.
  Variable R : A -> B -> Prop.

  Inductive relop : option A -> option B -> Prop :=
  | relop_none : relop None None
  | relop_some a b : R a b -> relop (Some a) (Some b).
End Relop.

(** * Option Equivalence *)
Section Relop.
  Context {A : Type}.
  Variable R : A -> A -> Prop.
  Context `{HAR : Equivalence A R}.

  Lemma RelopReflexive : Reflexive (relop R).
  Proof.
    intros [? |]; constructor; reflexivity.
  Qed.

  Lemma RelopSymmetric : Symmetric (relop R).
  Proof.
    intros [? |] [? |] H; inv H; constructor; symmetry; assumption.
  Qed.

  Lemma RelopTransitive : Transitive (relop R).
  Proof.
    intros [? |] [? |] [? |] H12 H23; inv H12; inv H23;
    constructor; etransitivity; eassumption.
  Qed.
End Relop.

Instance OptionEquivalence
         (A : Type) (R : A -> A -> Prop)
         `{Equivalence A R} : Equivalence (relop R).
Proof.
  Local Hint Resolve RelopReflexive : core.
  Local Hint Resolve RelopSymmetric : core.
  Local Hint Resolve RelopTransitive : core.
  constructor; auto.
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

Lemma relop_eq : forall {A : Type} (o1 o2 : option A), relop eq o1 o2 <-> o1 = o2.
Proof.
  intros; split; intros H; inv H; reflexivity.
Qed.

Section ProdEquivalence.
  Context {A B : Type}.

  Variable RA : A -> A -> Prop.

  Variable RB : B -> B -> Prop.

  Context `{Equivalence A RA}.

  Context `{Equivalence B RB}.

  Let RAB ab1 ab2 := RA (fst ab1) $ fst ab2 /\ RB (snd ab1) $ snd ab2.

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

Instance StringEqDec : EqDec string eq := { equiv_dec := Coq.Strings.String.string_dec }.
