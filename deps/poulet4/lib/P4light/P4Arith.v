Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPos.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.

(** * Unsigned Integers *)
Module BitArith.
  Import N.

  Section Operations.
    Variable (width : positive).

    Definition upper_bound : N := 2 ^ pos width.

    Definition maxN : N := upper_bound - 1.

    (** Precondition for operations. *)
    Definition bound (n : N) : Prop := (n < upper_bound)%N.

    Definition return_bound (n : N) : N :=
      if (n <? upper_bound)%N then n else maxN.
    (**[]*)

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

(** * Signed Integers *)
Module IntArith.
  Import Z.

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
