Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Lemma exp_ge_one : forall n1 n2 : Z, 0 < n1 -> 0 <= n2 -> 1 <= n1 ^ n2.
Proof.
  intros n1 n2 H.
  rewrite <- Z.pow_0_r with n1.
  apply Z.pow_le_mono_r; lia.
Qed.

(** * Unsigned Integers *)
Module BitArith.
  Import Z.

  Section Operations.
    Variable (width : positive).

    Definition upper_bound : Z := 2 ^ Zpos width.

    Definition maxN : Z := upper_bound - 1.

    (** Precondition for operations. *)
    Definition bound (n : Z) : Prop := -1 < n < upper_bound.

    Definition return_bound (n : Z) : Z :=
      if (n >? maxN)
      then maxN
      else if (n <? 0) then 0 else n.
    (**[]*)

    Lemma upper_bound_ge_1 : 1 <= upper_bound.
    Proof. unfold upper_bound; apply exp_ge_one; lia. Qed.

    Lemma return_bound_bound : forall n, bound (return_bound n).
    Proof.
      intros n; unfold return_bound, bound, maxN.
      destruct (n >? upper_bound -1) eqn:?H.
      - pose proof upper_bound_ge_1. lia.
      - rewrite gtb_ltb in H. rewrite ltb_ge in H.
        destruct (n <? 0) eqn: ?H.
        + pose proof upper_bound_ge_1. lia.
        + rewrite ltb_ge in H0. lia.
    Qed.

    (** Bitwise negation. *)
    Definition neg (n : Z) : Z := if eqb n 0 then 0 else upper_bound - n.

    Lemma neg_bound : forall n : Z, bound n -> bound (neg n).
    Proof.
      intros n; unfold bound, neg, maxN. intros.
      pose proof upper_bound_ge_1. destruct (n =? 0) eqn:?H; lia.
    Qed.

    (** Saturating Addition *)
    Definition plus_sat (a b : Z) : Z := return_bound (a + b).

    (** Modular Addition *)
    Definition plus_mod (a b : Z) : Z := (a + b) mod upper_bound.

    Lemma mod_bound: forall n: Z, bound (n mod upper_bound).
    Proof.
      intros. unfold bound. pose proof upper_bound_ge_1.
      pose proof (mod_pos_bound n upper_bound). lia.
    Qed.

    (** Modular Subtraction *)
    Definition minus_mod (a b : Z) : Z := (a - b) mod upper_bound.

    Lemma minus_mod_eq: forall a b : Z, minus_mod a b = plus_mod a (neg b).
    Proof.
      intros. unfold minus_mod, plus_mod, neg. destruct (b =? 0) eqn:?H.
      - rewrite eqb_eq in H. subst. f_equal.
      - rewrite <- Z_mod_plus_full with (b := 1). f_equal. lia.
    Qed.
    (**[]*)

    (** Logical Right Shift *)
    Definition shift_right (a b : Z) : Z := return_bound (shiftr a b).

    (** Left Shift *)
    Definition shift_left (a b : Z) : Z := return_bound (shiftl a b).

    (** Bitwise And *)
    Definition bit_and (a b : Z) := return_bound (land a b).

    (** Bitwise Or *)
    Definition bit_or (a b : Z) := return_bound (lor a b).

    (** Bitwise Xor *)
    Definition bit_xor (a b : Z) := return_bound (lxor a b).
  End Operations.

  (** Bitwise concatination *)
  Definition bit_concat (w1 w2 : positive) (n1 n2 : Z) : Z :=
    return_bound (w1 + w2) (shiftl n1 (pos w2) + n2).
  (**[]*)
End BitArith.

Ltac unfold_bit_operation :=
  match goal with
  (* | |- context [ BitArith.neg _ ] => unfold BitArith.neg *)
  | |- context [ BitArith.plus_sat _ _ ] => unfold BitArith.plus_sat
  (* | |- context [ BitArith.plus_mod _ _ ] => unfold BitArith.plus_mod *)
  | |- context [ BitArith.minus_mod _ _ ] => unfold BitArith.minus_mod
  | |- context [ BitArith.shift_right _ _ ] => unfold BitArith.shift_right
  | |- context [ BitArith.shift_left _ _ ] => unfold BitArith.shift_left
  | |- context [ BitArith.bit_and _ _ ] => unfold BitArith.bit_and
  | |- context [ BitArith.bit_xor _ _ ] => unfold BitArith.bit_xor
  | |- context [ BitArith.bit_or _ _ ] => unfold BitArith.bit_or
  end.

(** * Signed Integers *)
Module IntArith.
  Import Z.

  Lemma exp_ge_one : forall z1 z2,
      (0 < z1)%Z -> (0 <= z2)%Z -> (1 <= z1 ^ z2)%Z.
  Proof.
    intros z1 z2 Hz1 Hz2.
    rewrite <- pow_0_r with z1.
    apply pow_le_mono_r; lia.
  Qed.

  Section Operations.
    Variable (width : positive).

    Definition mod_amt : Z := 2 ^ (pos width).

    Definition upper_bound : Z := 2 ^ (pos width - 1).

    Lemma upper_bound_ge_1 : (1 <= upper_bound)%Z.
    Proof. unfold upper_bound; apply exp_ge_one; lia. Qed.

    Definition maxZ : Z := upper_bound - 1.

    Definition minZ : Z := - upper_bound.

    (** Precondition for operations *)
    Definition bound (z : Z) : Prop := (minZ <= z <= maxZ)%Z.

    Definition return_bound (z : Z) :=
      if (z >? maxZ)%Z then
        maxZ
      else
        if (z <? minZ)%Z then
          minZ
        else
          z.
    (**[]*)

    Lemma return_bound_bound : forall z, bound (return_bound z).
    Proof.
      intros z; unfold return_bound, bound, minZ, maxZ.
      destruct (z >? upper_bound - 1)%Z eqn:eqnz.
      - clear z eqnz; split; try lia.
        pose proof upper_bound_ge_1; lia.
      - rewrite gtb_ltb in eqnz.
        apply ltb_ge in eqnz.
        destruct (z <? - upper_bound)%Z eqn:eqnz'.
        + clear z eqnz eqnz' z; try lia.
          pose proof upper_bound_ge_1; lia.
        + apply ltb_ge in eqnz'. lia.
    Qed.

    (** Negation. *)
    Definition neg (z : Z) : Z := return_bound (Z.opp z).

    (** Saturating Addition *)
    Definition plus_sat (a b : Z) : Z := return_bound (a + b)%Z.

    (** Saturating Subtraction *)
    Definition minus_sat (a b : Z) : Z := return_bound (a - b)%Z.

    (** Modular Addition *)
    Definition plus_mod (a b : Z) : Z := return_bound ((a + b) mod mod_amt)%Z.

    (** Modular Subtraction *)
    Definition minus_mod (a b : Z) : Z := return_bound ((a - b) mod mod_amt)%Z.

    Lemma mod_mod_amt_bound : forall z : Z, bound (z mod mod_amt)%Z.
    Proof.
      intros z; unfold bound, mod_amt, minZ, maxZ.
      pose proof upper_bound_ge_1 as H; unfold upper_bound in *; split.
    Abort.

    (** Arithmetic shift left *)
    Definition shift_left (a b : Z) : Z := return_bound (shiftl a b).

    (** Arithmetic shift right *)
    Definition shift_right (a b : Z) : Z := return_bound (shiftr a b).

    (** Bitwise And *)
    Definition bit_and (a b : Z) : Z := return_bound (land a b).

    (** Bitwise Or *)
    Definition bit_or (a b : Z) : Z := return_bound (lor a b).

    (** Bitwise Xor *)
    Definition bit_xor (a b : Z) : Z := return_bound (lxor a b).
  End Operations.

  (** Bitwise concatination *)
  Definition bit_concat (w2 : positive) (z1 z2 : Z) : Z :=
    shiftl z1 (pos w2) + z2.
  (**[]*)
End IntArith.

Ltac unfold_int_operation :=
  match goal with
  | |- context [ IntArith.neg _ ] => unfold IntArith.neg
  | |- context [ IntArith.plus_sat _ _ ] => unfold IntArith.plus_sat
  | |- context [ IntArith.minus_sat _ _ ] => unfold IntArith.minus_sat
  | |- context [ IntArith.plus_mod _ _ ] => unfold IntArith.plus_mod
  | |- context [ IntArith.minus_mod _ _ ] => unfold IntArith.minus_mod
  | |- context [ IntArith.shift_right _ _ ] => unfold IntArith.shift_right
  | |- context [ IntArith.shift_left _ _ ] => unfold IntArith.shift_left
  | |- context [ IntArith.bit_and _ _ ] => unfold IntArith.bit_and
  | |- context [ IntArith.bit_xor _ _ ] => unfold IntArith.bit_xor
  | |- context [ IntArith.bit_or _ _ ] => unfold IntArith.bit_or
  end.
