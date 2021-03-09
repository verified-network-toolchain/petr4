Require Import Coq.Numbers.BinNums.
Require Import Coq.Classes.EquivDec.
Require Import Coq.ZArith.BinInt.

Record t (tags_t: Type) :=
  { tags: tags_t;
    value: Z;
    width_signed: option (nat * bool); }.

Arguments tags [tags_t] _.
Arguments value [tags_t] _.
Arguments width_signed [tags_t] _.

Instance ZEqDec : EqDec Z eq :=
  { equiv_dec := Z.eq_dec }.
(**[]*)

Instance ProdEqDec (A B : Type) `{EqDec A eq} `{EqDec B eq} : EqDec (A * B) eq.
Proof.
  intros [a1 b1] [a2 b2].
  pose proof equiv_dec a1 a2 as HA.
  pose proof equiv_dec b1 b2 as HB.
  unfold equiv in *. unfold complement in *.
  destruct HA as [HA | HA]; destruct HB as [HB | HB]; subst;
    try (right; intros HE; inversion HE; contradiction); auto.
Defined.

Instance OptionEqDec (A : Type) `{EqDec A eq} : EqDec (option A) eq.
Proof.
  intros [a1 |] [a2 |].
  - pose proof equiv_dec a1 a2 as HA.
    unfold equiv in *; unfold complement in *.
    destruct HA as [HA | HA]; subst; auto.
    right; intros HA'; inversion HA'; contradiction.
  - right; intros; discriminate.
  - right; intros; discriminate.
  - unfold equiv; auto.
Defined.

Instance NatBoolEqDec : EqDec (nat * bool) eq.
Proof. apply (ProdEqDec nat bool). Defined.

Instance OptionNatBoolDec : EqDec (option (nat * bool)) eq.
Proof. apply (OptionEqDec (nat * bool)). Defined.

Section IntEquiv.
  Context {tags_t : Type}.

  Definition eqb (n1 n2 : t tags_t) : bool :=
    if value n1 == value n2 then
      if width_signed n1 == width_signed n2 then true else false
    else false.
  (**[]*)

  Definition equiv (n1 n2 : t tags_t) : Prop :=
    value n1 = value n2 /\ width_signed n1 = width_signed n2.
End IntEquiv.

Section IntEquivDec.
  Variable (tags_t : Type).

  Instance IntEquivalence : Equivalence (@equiv tags_t).
  Proof.
    constructor.
    - constructor; auto.
    - intros [] [] [HV HW]; simpl in *; subst; split; auto.
    - intros [] [] [] [HV1 HW1] [HV2 HW2];
        simpl in *; subst; repeat constructor.
  Defined.

  Instance IntEqDec : EqDec (t tags_t) equiv.
  Proof.
    intros [t1 v1 w1] [t2 v2 w2].
    pose proof equiv_dec v1 v2 as HV.
    pose proof equiv_dec w1 w2 as HW.
    unfold Equivalence.equiv in *;
      unfold complement in *; unfold equiv in *; simpl.
    destruct HV as [HV | HV]; destruct HW as [HW | HW]; subst; auto;
      try (right; intros [? ?]; contradiction).
  Defined.
End IntEquivDec.

Module P4IntArithmetic.
  Section Arithmetic.
    Context {tags_t : Type}.

    Definition eq_width (n1 n2 : t tags_t) : Prop := width_signed n1 = width_signed n2.

    (** Assumes [width n1 = width n2]. *)
    Definition add_p4int_assume (n1 n2 : t tags_t) : t tags_t :=
      {| tags := tags n1;
         value := value n1 + value n2;
         width_signed := width_signed n1 |}.
    (**[]*)
  End Arithmetic.
End P4IntArithmetic.
