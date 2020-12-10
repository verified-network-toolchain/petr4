Require Import Strings.String.
Require Import OrderedType.
Open Scope string_scope.

(* this is extracted to the OCaml String.t type *)
Definition t := string.

(* A strict total order on bytes (ascii chars). *)
Definition ascii_lt (c c': Ascii.ascii) : Prop :=
  BinNat.N.lt (Ascii.N_of_ascii c) (Ascii.N_of_ascii c').

Lemma ascii_lt_trans:
  forall x y z,
    ascii_lt x y ->
    ascii_lt y z ->
    ascii_lt x z.
Proof.
  unfold ascii_lt.
  intros.
  eauto using BinNat.N.lt_trans.
Qed.

Lemma ascii_lt_not_eq:
  forall x y,
    ascii_lt x y ->
    x <> y.
Proof.
  unfold not, ascii_lt.
  intros x y Hlt Heq.
  subst.
  eapply BinNat.N.lt_irrefl; eauto.
Qed.

Definition ascii_compare:
  forall x y : Ascii.ascii,
    OrderedType.Compare ascii_lt (@eq Ascii.ascii) x y.
Proof.
  intros x y.
  set (x' := Ascii.N_of_ascii x).
  set (y' := Ascii.N_of_ascii y).
  pose proof (BinNat.N.lt_decidable x' y').
  destruct (Bool.reflect_dec _ _ (BinNat.N.ltb_spec0 x' y')).
  - now apply LT.
  - destruct (Ascii.ascii_dec x y).
    + now apply EQ.
    + apply GT.
      apply BinNat.N.le_neq; split.
      * now apply BinNat.N.nlt_ge.
      * pose proof (Ascii.ascii_N_embedding x).
        pose proof (Ascii.ascii_N_embedding y).
        congruence.
Defined.

(* Strict dictionary order on strings, using ascii_lt for ordering
   individual characters. *)
Inductive lt: t -> t -> Prop :=
| LtEmp: forall c s, lt "" (String c s)
| LtFirst: forall c c' s s',
    ascii_lt c c' ->
    lt (String c s) (String c' s')
| LtCons: forall c s s',
    lt s s' ->
    lt (String c s) (String c s').

Definition eqb: String.t -> String.t -> bool :=
  String.eqb.

Theorem eqb_correct:
  forall s1 s2,
    eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros.
  symmetry.
  auto using Bool.reflect_iff, String.eqb_spec.
Qed.

Lemma lt_trans :
  forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
  induction x; destruct y; intros z Hxy Hyz; subst.
  - eauto.
  - inversion Hyz; subst; constructor.
  - inversion Hxy.
  - inversion Hxy; inversion Hyz; subst.
    + constructor; eauto using ascii_lt_trans.
    + constructor; eauto using ascii_lt_trans.
    + now constructor.
    + constructor; eapply IHx; eauto.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
  unfold not.
  induction 1; intros; subst.
  - congruence.
  - eapply ascii_lt_not_eq.
    + eauto.
    + congruence.
  - eapply IHlt.
    congruence.
Qed.

Definition compare:
  forall x y : t, OrderedType.Compare lt eq x y.
Proof.
  induction x, y.
  - apply EQ; constructor.
  - apply LT; constructor.
  - apply GT; constructor.
  - destruct (ascii_compare a a0).
    + apply LT; now constructor.
    + subst.
      destruct (IHx y).
      * apply LT; apply LtCons; eauto.
      * subst; apply EQ; constructor.
      * apply GT; apply LtCons; eauto.
    + apply GT; now constructor.
Defined.

Definition eq_dec (x y: t) : {eq x y} + {~ eq x y} :=
  Bool.reflect_dec _ _ (String.eqb_spec x y).

Module StringOT <: OrderedType.OrderedType.
  Definition t := t.
  Definition eq := @eq t.
  Definition lt := lt.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt_trans := lt_trans.
  Definition lt_not_eq := lt_not_eq.
  Definition compare := compare.
  Definition eq_dec := eq_dec.
  Transparent t eq lt eq_refl eq_sym eq_trans lt_trans lt_not_eq compare eq_dec.
End StringOT.

Definition isValid := "isValid".
Definition setValid := "setValid".
Definition setInvalid := "setInvalid".
Definition pop_front := "pop_front".
Definition push_front := "push_front".
Definition extract := "extract".
Definition accept := "accept".
Definition reject := "reject".
