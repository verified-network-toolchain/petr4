Require Import Ascii.

Require Import Grammars.Grammar.
Require Import Grammars.Lib.
Require Import Vector.

Definition bit (n: nat) : Set := prod bool n.

Definition bits (n : nat) : grammar (bit n) :=
  repeat_prod n (glitr "1" true <|> glitr "0" false).