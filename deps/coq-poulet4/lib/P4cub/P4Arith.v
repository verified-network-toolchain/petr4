Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPos.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

(** * Unsigned Integers *)
Module BitArith.
  Import N.

  Lemma exp_ge_one : forall n1 n2 : N, (0 < n1)%N -> (1 <= n1 ^ n2)%N.
  Proof.
    intros n1 n2 H.
    rewrite <- pow_0_r with n1.
    apply pow_le_mono_r; lia.
  Qed.

  Section Operations.
    Variable (width : positive).

    Definition upper_bound : N := 2 ^ pos width.

    Definition maxN : N := upper_bound - 1.

    (** Precondition for operations. *)
    Definition bound (n : N) : Prop := (n < upper_bound)%N.

    Definition return_bound (n : N) : N :=
      if (n <? upper_bound)%N then n else maxN.
    (**[]*)

    Lemma return_bound_bound : forall n, bound (return_bound n).
    Proof.
      intros n; unfold return_bound, bound, maxN, upper_bound.
      destruct (n <? 2 ^ pos width)%N eqn:eqnn.
      - apply ltb_lt; auto.
      - apply sub_lt; try lia.
        apply exp_ge_one; lia.
    Qed.

    (** Bitwise negation. *)
    Definition neg (n : N) : N := (maxN - n)%N.

    (** Saturating Addition *)
    Definition plus_sat (a b : N) : N := return_bound (a + b)%N.

    (** Modular Addition *)
    Definition plus_mod (a b : N) : N := (a + b) mod upper_bound.

    (** Modular Subtraction *)
    Definition minus_mod (a b : N) : N :=
      let z := Z.sub (Z.of_N a) (Z.of_N b) in
      let z' := Z.modulo z (Z.of_N upper_bound) in
      Z.to_N z'.
    (**[]*)

    (** Logical Right Shift *)
    Definition shift_right (a b : N) : N := return_bound (shiftr a b).

    (** Bitwise And *)
    Definition bit_and (a b : N) := return_bound (land a b).

    (** Bitwise Or *)
    Definition bit_or (a b : N) := return_bound (lor a b).

    (** Bitwise Xor *)
    Definition bit_xor (a b : N) := return_bound (lxor a b).
  End Operations.

  (** Bitwise concatination *)
  Definition bit_concat (w2 : positive) (n1 n2 : N) : N :=
    shiftl n1 (pos w2) + n2.
  (**[]*)
End BitArith.

Ltac unfold_bit_operation :=
  match goal with
  | |- context [ BitArith.neg _ ] => unfold BitArith.neg
  | |- context [ BitArith.plus_sat _ _ ] => unfold BitArith.plus_sat
  | |- context [ BitArith.plus_mod _ _ ] => unfold BitArith.plus_mod
  | |- context [ BitArith.minus_mod _ _ ] => unfold BitArith.minus_mod
  | |- context [ BitArith.shift_right _ _ ] => unfold BitArith.shift_right
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
      intros z; unfold return_bound, bound, minZ, maxZ, upper_bound.
      destruct (z >? 2 ^ (pos width - 1) - 1)%Z eqn:eqnz.
      - clear z eqnz; split; try lia.
        apply le_0_sub.
        rewrite sub_opp_r.
        assert (Hone : (1 <= 2 ^ (pos width - 1))%Z).
        { apply exp_ge_one; lia. } lia.
      - rewrite gtb_ltb in eqnz.
        apply ltb_ge in eqnz.
        destruct (z <? - 2 ^ (pos width - 1))%Z eqn:eqnz'.
        + clear z eqnz eqnz' z; try lia.
          assert (Hone : (1 <= 2 ^ (pos width - 1))%Z).
          { apply exp_ge_one; lia. } lia.
        + apply ltb_ge in eqnz'. lia.
    Qed.

    (** Negation. *)
    Definition neg (z : Z) : Z := return_bound (Z.opp z).

    (** Saturating Addition *)
    Definition plus_sat (a b : Z) : Z := return_bound (a + b)%Z.

    (** Saturating Subtraction *)
    Definition minus_sat (a b : Z) : Z := return_bound (a - b)%Z.

    (** Modular Addition *)
    Definition plus_mod (a b : Z) : Z := ((a + b) mod mod_amt)%Z.

    (** Modular Subtraction *)
    Definition minus_mod (a b : Z) : Z := ((a - b) mod mod_amt)%Z.

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
