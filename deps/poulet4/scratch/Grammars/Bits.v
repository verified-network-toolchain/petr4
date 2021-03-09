Require Import Ascii.

Require Import Grammars.Grammar.
Require Import Grammars.Lib.
Require Import Vector.

Definition bit := glit true <|> glit false.

Definition bits (n: nat) : Set := prod bool n.

Definition bits_n (n : nat) : grammar (bits n) := repeat_prod n bit.

Fixpoint zero_bits (n: nat) : bits n :=
  match n with
  | 0 => tt
  | S n' => (false, zero_bits n')
  end.

Fixpoint one_bits {w: nat} : bits (S w) :=
  match w with
  | 0 => (true, tt)
  | S w' => (false, one_bits)
  end.

