Require Export Coq.Numbers.BinNums
        Coq.Bool.Bool
        Poulet4.Utils.Util.ListUtil.
Require Import Coq.micromega.Lia.
Require Import String.

(** * Useful Notations *)

Notation "a '&&&&' b"
  := (if a then if b then true else false else false)
       (at level 60, right associativity).

Notation "a '||||' b"
  := (if a then true else if b then true else false)
       (at level 70, right associativity).

(** * Equivalence Tactics *)

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

Ltac simpl_equiv_dec :=
  match goal with
    H: EqDec _ ?R
    |- context [?H ?v ?v]
    => assert (R v v) by reflexivity;
      destruct (H v v) as [? | ?];
      unravel in *;
      try contradiction
  end.

Ltac simpl_equiv_dec_hyp :=
  match goal with
    H: EqDec _ ?R, E: context [?R ?x ?y]
    |- context [?H ?x ?y]
    => destruct (H x y) as [? | ?];
      unravel in *; try contradiction; unravel
  end.

Ltac destruct_if :=
  match goal with
    |- context [if ?trm then _ else _]
    => destruct trm as [? | ?] eqn:?; unravel in *
  end.

Ltac destruct_if_hyp :=
  match goal with
    h: context [if ?trm then _ else _] |- _
    => destruct trm as [? | ?] eqn:?; unravel in *
  end.

(** * Useful Functions And Lemmas *)

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

Section ListStuff.
  Context {A : Type} {HED : EqDec A eq}.

  Fixpoint eqb_list (l1 l2 : list A) : bool :=
    match l1, l2 with
    | []     , []      => true
    | a1 :: l1, a2 :: l2 => equiv_dec a1 a2 &&&& eqb_list l1 l2
    | _      , _       => false
    end.
  
  Lemma eqb_list_refl : forall l, eqb_list l l = true.
  Proof using Type.
    intro l; induction l as [| h t IHt]; unravel; auto.
    rewrite IHt; equiv_dec_refl_tactic. reflexivity.
  Qed.

  Lemma eqb_list_eq : forall xs ys,
      eqb_list xs ys = true -> xs = ys.
  Proof using Type.
    intro xs; induction xs as [| x xs IHxs];
      intros [| y ys] Hel; unravel in *; try discriminate; auto.
    apply lifted_andb_true in Hel as [Hxy Hxys].
    unravel in *; subst. f_equal; auto.
  Qed.

  Hint Rewrite eqb_list_refl : core.
  Local Hint Resolve eqb_list_eq : core.

  Lemma eqb_list_iff : forall xs ys,
      eqb_list xs ys = true <-> xs = ys.
  Proof using Type.
    intros xs ys; split; intro H; subst;
      autorewrite with core; auto.
  Qed.

  Lemma eqb_list_reflect : forall xs ys,
      reflect (xs = ys) (eqb_list xs ys).
  Proof using Type.
    intros xs ys; reflect_split; subst;
      autorewrite with core in *; auto; try discriminate.
  Defined.
End ListStuff.

Ltac destruct_lifted_andb :=
  match goal with
  | H: _ &&&& _ = true |- _ => apply lifted_andb_true in H as [? ?]
  end.

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

(** Option Predicate *)
Variant predop {A : Type} (P : A -> Prop) : option A -> Prop :=
  | predop_none : predop P None
  | predop_some (a : A) : P a -> predop P (Some a).

Section Predop.
  Context {A B : Type}.
  Variable P : A -> Prop.

  Local Hint Constructors predop : core.

  Lemma predop_pat_fst : forall (o : option (A * B)),
      predop (fun '(a, _) => P a) o <-> predop (fun ab => P (fst ab)) o.
  Proof using.
    intros [[a b] |]; split; intro h; inv h; auto.
  Qed.
  
  Lemma predop_pat_snd : forall (o : option (B * A)),
      predop (fun '(_, a) => P a) o <-> predop (fun ba => P (snd ba)) o.
  Proof using.
    intros [[a b] |]; split; intro h; inv h; auto.
  Qed.
End Predop.

(** * Option Relations *)
Section Relop.
  Context {A B : Type}.
  Variable R : A -> B -> Prop.

  Variant relop : option A -> option B -> Prop :=
  | relop_none : relop None None
  | relop_some a b : R a b -> relop (Some a) (Some b).
End Relop.

Section Relop.
  Local Hint Constructors relop : core.
  
  Lemma relop_impl : forall {A B : Type} (R Q : A -> B -> Prop) oa ob,
      (forall a b, R a b -> Q a b) -> relop R oa ob -> relop Q oa ob.
  Proof.
    intros A B R Q oa ob h H; inv H; auto.
  Qed.

  Lemma relop_map_l : forall {A B C : Type} (R : C -> B -> Prop) (f : A -> C) oa ob,
      relop R (option_map f oa) ob <-> relop (fun a => R (f a)) oa ob.
  Proof.
    intros A B C R f oa ob.
    destruct oa as [a |]; destruct ob as [b |];
      split; cbn; intro h; inv h; auto.
  Qed.

  Lemma relop_sym : forall {A B : Type} (R : A -> B -> Prop) oa ob,
      relop R oa ob <-> relop (fun b a => R a b) ob oa.
  Proof.
    intros R oa ob; split; intro h; inv h; auto.
  Qed.

  Lemma relop_map_r : forall {A B C : Type} (R : A -> C -> Prop) (f : B -> C) oa ob,
      relop R oa (option_map f ob) <-> relop (fun a b => R a (f b)) oa ob.
  Proof.
    intros A B C R f oa ob.
    rewrite relop_sym.
    rewrite relop_map_l.
    rewrite relop_sym.
    reflexivity.
  Qed.

  Lemma relop_map_both :
    forall {A B C D : Type} (R : C -> D -> Prop) (f : A -> C) (g : B -> D) oa ob,
      relop R (option_map f oa) (option_map g ob)
      <-> relop (fun a b => R (f a) (g b)) oa ob.
  Proof.
    intros A B C D R f g oa ob.
    rewrite relop_map_l,relop_map_r.
    reflexivity.
  Qed.
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

Global Instance OptionEquivalence
         (A : Type) (R : A -> A -> Prop)
         `{Equivalence A R} : Equivalence (relop R).
Proof.
  Local Hint Resolve RelopReflexive : core.
  Local Hint Resolve RelopSymmetric : core.
  Local Hint Resolve RelopTransitive : core.
  constructor; auto.
Defined.

Global Instance OptionEqDec
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

Global Instance PositiveEqDec : EqDec positive eq := { equiv_dec := BinPos.Pos.eq_dec }.

Global Instance NEqDec : EqDec N eq := { equiv_dec := BinNat.N.eq_dec }.

Global Instance ZEqDec : EqDec Z eq := { equiv_dec := BinInt.Z.eq_dec }.

Global Instance StringEqDec : EqDec String.string eq := { equiv_dec := string_dec }.
