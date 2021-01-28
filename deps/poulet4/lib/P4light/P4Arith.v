Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPos.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Classes.EquivDec.
(* Require Import Coq.ZArith.BinInt. *)

(** * Decidable Comparison *)
Module DecComp.
  Import Pos.

  Lemma Pos_lt_lt : Lt = Lt.
  Proof. reflexivity. Defined.

  Lemma Pos_eq_lt : Eq <> Lt.
  Proof. intros H; discriminate. Defined.

  Lemma Pos_gt_lt : Gt <> Lt.
  Proof. intros H; discriminate. Defined.

  Definition Pos_lt_dec (p1 p2 : positive) :
    {(p1 < p2)%positive} + {~ (p1 < p2)%positive} :=
    match (p1 ?= p2)%positive as cmp
          return {cmp = Lt} + {cmp <> Lt} with
    | Lt => left Pos_lt_lt
    | Eq => right Pos_eq_lt
    | Gt => right Pos_gt_lt
    end.
  (**[]*)

  Import N.

  Lemma N_lt_lt : Lt = Lt.
  Proof. reflexivity. Defined.

  Lemma N_eq_lt : Eq <> Lt.
  Proof. intros H; discriminate. Defined.

  Lemma N_gt_lt : Gt <> Lt.
  Proof. intros H; discriminate. Defined.

  Definition N_lt_dec (n1 n2 : N) :
    {(n1 < n2)%N} + {~ (n1 < n2)%N} :=
    match (n1 ?= n2)%N as cmp
          return {cmp = Lt} + {cmp <> Lt} with
    | Lt => left _ N_lt_lt
    | Gt => right N_gt_lt
    | Eq => right _ N_eq_lt
    end.
  (**[]*)
End DecComp.

(** * Unsigned Integers *)
Module BitArith.
  Import N.

  (* Definition t (width : positive) : Set := { n : N | (n < 2 ^ pos width)%N }. *)

  Inductive t (width : positive) : Set :=
    Bit (n : N) (H : (n < 2 ^ pos width)%N).
  Arguments Bit {_}.

  Section BitEquivalence.
    Context {w : positive}.

    Inductive equiv : t w -> t w -> Prop :=
    | equiv_bit (a b : N) (HEQ : a = b)
              (Ha : (a < 2 ^ pos w)%N) (Hb : (b < 2 ^ pos w)%N) :
        equiv (Bit a Ha) (Bit b Hb).
    (**[]*)

    Lemma equiv_reflexive : Reflexive equiv.
    Proof. intros [x Hx]; constructor; auto. Qed.

    Lemma equiv_symmetric : Symmetric equiv.
    Proof.
      intros [x Hx] [y Hy] H; inversion H;
        subst; constructor; auto.
    Qed.

    Lemma equiv_transitive : Transitive equiv.
    Proof.
      intros [x Hx] [y Hy] [z Hz] Hxy Hyz;
        inversion Hxy; subst; inversion Hyz; subst;
          constructor; auto.
    Qed.

    Instance BitEquivalence : Equivalence equiv.
    Proof.
      constructor; [ apply equiv_reflexive
                   | apply equiv_symmetric
                   | apply equiv_transitive ].
    Defined.
  End BitEquivalence.

  Definition maxN (w : positive) : N := ((2 ^ pos w) - 1)%N.

  Lemma maxN_bounded : forall w : positive,
      (maxN w < 2 ^ pos w)%N.
  Proof.
    intros w; unfold maxN.
    Fail lia. (* but why? I tried. *)
  Admitted.

  Definition maxt (w : positive) : t w := Bit (maxN w) (maxN_bounded w).

  Definition plus {w : positive} (x1 x2 : t w) : t w :=
    match x1, x2 with
    | Bit n1 _, Bit n2 _ =>
        match DecComp.N_lt_dec (n1 + n2)%N (2 ^ pos w)%N  with
        | left H  => Bit (n1 + n2)%N H
        | right _ => maxt w
        end
    end.
  (**[]*)

  Lemma plus_max : forall {w : positive} (x : t w),
      equiv (plus x (maxt w)) (maxt w).
  Proof.
    intros w [x Hx]; unfold plus.
    destruct (maxt w) as [m Hm] eqn:eqmax.
    destruct (DecComp.N_lt_dec (x + m) (2 ^ pos w)).
    - unfold maxt in eqmax.
      inversion eqmax; subst; clear eqmax; unfold maxN in *.
      destruct x; try lia. constructor; auto.
    - constructor; auto.
  Qed.

  Lemma plus_comm : forall {w : positive} (x1 x2 : t w),
      plus x1 x2 = plus x2 x1.
  Proof.
    intros w [n1 H1] [n2 H2]; unfold plus.
    assert (Hn : (n1 + n2 = n2 + n1)%N); try lia.
    repeat rewrite Hn. reflexivity.
  Qed.

  Lemma plus_assoc : forall {w : positive} (a b c : t w),
      equiv (plus (plus a b) c) (plus a (plus b c)).
  Proof.
    intros w [a Ha] [b Hb] [c Hc]; unfold plus.
    repeat match goal with
           | |- context [ DecComp.N_lt_dec (?x + ?y) ?m ] =>
               destruct (DecComp.N_lt_dec (x + y) m) eqn:?
           end; try lia; try (constructor; auto; lia).
    - destruct (maxt w) as [m Hm] eqn:eqmax.
      pose proof plus_max (Bit a Ha) as H.
      unfold plus in H. rewrite eqmax in H.
      apply equiv_symmetric. assumption.
    - destruct (maxt w) as [m Hm] eqn:eqmax.
      pose proof plus_max (Bit c Hc) as H.
      unfold plus in H. rewrite eqmax in H.
      rewrite (add_comm m c). assumption.
    - destruct (maxt w) as [m Hm] eqn:eqmax.
      pose proof plus_max (Bit a Ha) as HA.
      unfold plus in HA. rewrite eqmax in HA.
      pose proof plus_max (Bit c Hc) as HC.
      unfold plus in HC. rewrite eqmax in HC.
      rewrite (add_comm c m) in HC.
      apply equiv_symmetric in HA.
      apply equiv_transitive with (Bit m Hm); auto.
  Qed.
End BitArith.
